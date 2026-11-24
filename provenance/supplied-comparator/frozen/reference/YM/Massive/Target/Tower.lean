import YM.Massive.Finite.Core
import YM.QCD.Flume.Collect
import YM.QCD.Step.Gallery
import YM.RG.Block
import YM.QCD.Grass.SD
import Mathlib.Analysis.Complex.Order

/-!
# Statement: spacings, RG scheme and densities

A scale scheme using a stiffness *window* (cf. `work/bend.tex`, "approximate kinetic
read"). The coupling is a Wilsonian coordinate, data of the scheme and trajectory,
not an intrinsically uniquely determined function of the law. Require arbitrarily fine
calibration tolerance, set before asking for a sufficiently large reference β. β enters
both in the actual gauge action at the cutoff and in the soft kernel for blocking
from each `m+1` to `m`; along with the asserted UV slope, we require it to be tracking
the **actual** (unquenched!) flat-field stiffness even at the unit of length (`m=0`),
where `β 0 = βRef` and the stiffness may differ from it by at most the prescribed tolerance.
This specifies a scheme for the physical conclusions; not specifying internal aspects of
an RG proof, like predictor jets, a normalization algorithm to select a β within a window,
or prices on polymer representations. In particular **not** claiming exact tuning
in a scheme defining the coupling by equality to a Hessian. See also README.

`Run.massRead` is another (scheme-dependent) check on the RG path. It does NOT define
the renormalized masses in the statement; those must use calibrated local-field PCAC identities.

Use full, unnormalized density everywhere in the run, unconditional Haar &
Berezin. `Run.Actual` requires normalization to be *possible* at every level.
Positive bare mass is *not* assumed. Large-coupling and mass-coordinate conditions
are separate from `Actual`. Even sides, periods etc. are stated separately too.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter MeasureTheory
open QCD QCD.Lat Lattice Wilson QCD.Grass YM.Next.Free RG
open scoped Matrix BigOperators Topology ContDiff

variable {j k F : ℕ} {c f n : Side}

/-- Keep the mass-admitting kernel (called with stride and **both** indices).
The raw theory operations here use `P.patch` but not `P.wing`.
`Kit.sheath` penalty one, `Flume.tied` counting mean incl the seams at zero
as in `Acre.Rails.advance`. `P.visit` is just (`P.patch`, choice, h).
For spec with variable strides we do the very same kernel on full fields;
not an operation restricted to even Grassmann inputs. -/
def soften (P : Flight j k) (h : f.val = c.val * P.L.val) (X : Density f F) :
    Grid f → Fields c F := fun U => Kit.sheath 1 (Kit.choir F (Flume.tied P h 0 U)) (X U)

def coarse (P : Flight j k) (K : KernelChoices) (h : f.val = c.val * P.L.val) : StepData c f :=
  ⟨P.patch,K,h⟩

def rescale (w : ℝ) : Fields c F →ₐ[ℂ] Fields c F := by
  classical
  exact changeVars (Matrix.diagonal fun _ => (w:ℂ))

def transfer (P : Flight j k) (K : KernelChoices) (h : f.val = c.val * P.L.val)
    (β w : ℝ) (X : Density f F) : Density c F :=
  (rescale w) ∘ ((coarse P K h).push β (soften P h X))

structure Scheme where
  choices : KernelChoices
  J : ℕ → ℕ
  step (m : ℕ) : Flight (J (m+1)) (J m)
  admissible (m : ℕ) : (step m).patch.Branches choices su

namespace Scheme
variable (S : Scheme)

def ratio (S : Scheme) : ℕ → Side
 | 0 => 1
 | m+1 => S.ratio m * (S.step m).L

/-- Period R in reference units; same on all 4 axes, # sites per axis. -/
def side (R : Side) (m : ℕ) := R * S.ratio m

def spacing (m : ℕ) := ((S.ratio m).val : ℝ)⁻¹

@[simp] theorem side_zero (R) : S.side R 0 = R := mul_one _
@[simp] theorem spacing_zero : S.spacing 0 = 1 := by simp [spacing,ratio]

theorem sides_next (R m) : (S.side R (m+1)).val = (S.side R m).val * (S.step m).L.val := by
  rw [side,side,ratio,← mul_assoc,PNat.mul_coe]

end Scheme

variable {S : Scheme} {N : ℕ} {R : Side}

/-- Unnormalized, so that support estimates for local insertions can use this
*same* denominator in every spacetime expectation. Data read only at levels `m≤N`,
precision on β along the run is imposed separately. `w m` rescales the new
(coarser) spinors in step `m+1→m`. -/
structure Run (S : Scheme) (N : ℕ) (R : Side) (F : ℕ) where
  β : ℕ → ℝ
  w : ℕ → ℝ
  u : Flavor F → ℝ
  density (m : ℕ) : Density (S.side R m) F

namespace Run
open scoped ComplexOrder
variable (A : Run S N R F)

def regulator : Regulator (S.side R N) F := ⟨A.β N,0,A.u⟩

def block (m : ℕ) := transfer (F:=F) (S.step m) S.choices (S.sides_next R m) (A.β (m+1)) (A.w m)

/-- Conditions for actual (not ignoring spin or replacing gauge theory by an approximation)
transport of a density over the trajectory. -/
structure Carried (f : (m : ℕ) → Density (S.side R m) F) (terminal : ℕ) : Prop where
  integrable {m} (ht : terminal ≤ m) (hm : m ≤ N) : Integrable (f m) (prior su (S.side R m))
  atStep {m} (ht : terminal ≤ m) (hm : m < N) : Integrable (soften (S.step m) (S.sides_next R m) (f (m+1)))
      (prior su (S.side R (m+1)))
  eqn {m} (ht : terminal ≤ m) (hm : m < N) : f m = A.block m (f (m+1))

/-- Use of `0<Z` is in complex real-axis order (positive real, zero imaginary). -/
structure Actual : Prop where
  start : A.density N = A.regulator.density
  travels : A.Carried A.density 0
  beta_pos {m} (h : m ≤ N) : 0 < A.β m
  w_pos {m} (h : m < N) : 0 < A.w m
  even {m} (h : m ≤ N) (U) : Grass.Plus (A.density m U)
  gauge {m} (h : m ≤ N) (U) (k : Lat.Frame (S.side R m)) :
    slots F k (A.density m (gauge k U)) = A.density m U
  normal {m} (h : m ≤ N) : 0 < joint (A.density m)

end Run

/-- All the limits in the statement refer to *one* such object. -/
structure Sequence where
  S : Scheme
  N : ℕ → ℕ
  R : ℕ → Side
  A (i : ℕ) : Run S (N i) (R i) 6

namespace Stiffness

def waveNumber (n : Side) : ℝ := 2 * Real.pi / n.val

def profile {n : Side} (χ : ℝ → ℝ) (a b : Axis) (T : su.Color) (t : ℝ) : Grid n := fun X =>
  if a = X.2 then su.lieExp ((t * χ (waveNumber n * ((X.1 b).val : ℝ))) • T) else 1

def body (f : Density n F) (U : Grid n) : ℂ := Grass.coef ∅ (f U)

def action (f : Density n F) (U : Grid n) : ℝ := - Real.log (body f U).re

def read (f : Density n F) (a b : Axis) (T : su.Color) : ℝ :=
  (iteratedDeriv 2 (action f ∘ profile Real.cos a b T) 0 +
    iteratedDeriv 2 (action f ∘ profile Real.sin a b T) 0) /
      ((Fintype.card (Site n) : ℝ) * waveNumber n ^ 2)

open scoped ComplexOrder in
structure Window (f : Density n F) (β ε : ℝ) : Prop where
  real : ∀ᶠ U in 𝓝 (1 : Grid n), 0 < body f U
  smooth (a b : Axis) (h : a ≠ b) (T : su.Color) :
    ContDiffAt ℝ 2 (action f ∘ profile Real.cos a b T) 0 ∧
    ContDiffAt ℝ 2 (action f ∘ profile Real.sin a b T) 0
  band (a b : Axis) (h : a ≠ b) (T : su.Color) (hT : ‖T‖ = 1) : |read f a b T - β| ≤ ε

end Stiffness

namespace Run

/-- Smallest `(+,+,+,+)` AP plane (local representatives `[0,n)`, seams at zero). -/
def plane (x : Site n) : ℂ :=
  Complex.exp (Complex.I * ↑(Real.pi / n.val * ∑ i, ((x i).val : ℝ)))

/-- For even D, `negQuadratic D (r,c)` reads M in exponent `-bar M psi` (FLAT links).
Always require nonzero body there too. -/
def negQuadratic (D : Density n F) (r c : Modes n F) : ℂ :=
  -Grass.coef ∅ (Grass.vary (Sum.inl c) (Grass.vary (Sum.inr r) (D 1))) / Stiffness.body D 1

/-- A scalar check on the mass signal at a step, from the actual density's
`bar × psi` kernel at link identity. Per site *and* fiber. -/
def massRead (A : Run S N R F) (m : ℕ) (i : Flavor F) : ℂ :=
  let n := S.side R m
  (∑ x : Site n, ∑ y : Site n, ∑ v : Fiber,
      star (plane x) * negQuadratic (A.density m) ((x,v),i) ((y,v),i) * plane y) /
    ((Fintype.card (Site n) : ℂ) * (Fintype.card Fiber : ℕ))

end Run

def betaSlope : ℝ := su.slopeConstant - 6 / (2 * Real.pi^2)

namespace Sequence
variable (C : Sequence)
/-- The block-history version of the UV slope. -/
def Slope : Prop := 0 < betaSlope ∧ ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop, ∀ i,
    m ≤ C.N i → |(C.A i).β m / Real.log ((C.S.spacing m)⁻¹) - betaSlope| ≤ η

/-- w near one at weak coupling; fixed-scale β bounded on every level. -/
structure Path (βRef ε : ℝ) : Prop where
  choices : C.S.choices.penalty = 1
  initialStage : 4 ≤ C.S.J 0
  infinite : Tendsto (fun i => (C.R i).val) atTop atTop
  uv : StrictMono C.N
  physical : Tendsto (fun i => C.S.spacing (C.N i)) atTop (𝓝[>] 0)
  even (i) : Even (C.R i).val
  atLeast (i) : 4 ≤ (C.R i).val
  normalized (i) : (C.A i).Actual
  separate (i) : Injective (C.A i).u
  reference (i) : (C.A i).β 0 = βRef
  compare {i m} (h : m ≤ C.N i) : Stiffness.Window ((C.A i).density m) ((C.A i).β m) ε
  beta_min {i m} (h : m ≤ C.N i) : 1 ≤ (C.A i).β m
  size (m) : ∃ B : ℝ, ∀ i, m ≤ C.N i → (C.A i).β m ≤ B
  near {i m} (h : m < C.N i) : |(C.A i).w m - 1| ≤ ε
  runs : C.Slope

end Sequence
end YM.Massive
