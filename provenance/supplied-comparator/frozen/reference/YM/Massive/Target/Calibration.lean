import YM.Massive.Target.Cylinder
import YM.Massive.Target.Tower

/-!
# Statement: common calibration of the observable system

A lattice section in local (common stencil at each horizon) cylinders. Mixing
then carried out **on the actual Run**. Jet of the transported insertion (i.e.,
look near identity at the ratio of a marked and unmarked density, including Grassmann
terms, *before* integrating that stop). This enforces normalization conditions also
for the fields defining the masses; not fitting separate unknown multiplicative
normalizations for each flavor pair.

Use the freedom of scheme in the choice of some common (all-flavor)
taper, lattice section, wave-function and block scheme etc. Coordinates here are
**unweighted**. Input physical normalization specified by the jet at `base d`, rather
than specifying sizes of counterterms needed at the cutoff. Factors from the step laws
if stripping off engineering scaling of an operator (like `L^{D/2}` per step) aren't
used here; the fields and transport-of-insertion are already in physical units. In
particular even at a positive base, asking for unit jet here specifies the physical
unit, not `a(base)^{-(d/2)}` times the unit. This reparametrizes the off-shell frames
for general base. At base zero `a=1`; this implements the scheme for the mass fields
in `work/massread.tex` (use `Label 8` for P with r=(2,…,2), `Label 6`
for A with r=(2,…,2) - e_µ). Their physics assertion is in another file.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Filter Function Set TensorProduct QCD QCD.Lat QCD.Grass
open Lattice Wilson UV RG
open scoped Topology ContDiff BigOperators TensorProduct Matrix.Norms.Frobenius



def vector (x : Cover) : E4 := WithLp.toLp 2 fun i => (x i : ℝ)

namespace SourceRead
variable {n : Side} {d : ℕ} {D : Finset Cover}

open Cylinder

/-- take h² as the auxiliary scaling variable for jets, so the
spin scaling here is polynomial too. -/
def profile (p : Multi d) (x : Cover) (h : ℝ) : ℂ :=
  ↑(h^(spinWeight p) * ∏ i : Axis, (x i : ℝ)^(power p i) / Nat.factorial (power p i))

def spinLink (h : ℝ) : Matrix (Nearest D 6) (SpinMode d) ℂ := Matrix.of fun i j =>
  if i.1.2=j.1.2 ∧ i.2=j.2 then profile j.1.1 i.1.1.val h else 0

def onStencil (H : Source.Hol su) (x : Cylinder.Formula D 6) (d : ℕ)
    (J : Labels.Jet su) (h : ℝ) : SpinPol d :=
  Grass.adapter (spinLink h) (spinLink h) (Cylinder.evaluate (H.links (d/2) J (h^2)) x)

open scoped Classical in
def scaled (h : ℝ) : Matrix (SpinMode d) (SpinMode d) ℂ :=
  Matrix.diagonal fun i => (h : ℂ)^(spinWeight i.1.1)

def desired (x : Pol d) (J : Labels.Jet su) (h : ℝ) : SpinPol d :=
  TensorProduct.lid ℂ _ <| TensorProduct.map
    (Labels.read (Source.scaleJet J (h^2))).toLinearMap (Grass.adapter (scaled h) (scaled h)).toLinearMap x

def Agrees (f g : ℝ → SpinPol d) : Prop :=
  ContDiffAt ℝ (d : ℕ∞) f 0 ∧ ContDiffAt ℝ (d : ℕ∞) g 0 ∧
    ∀ i ≤ d, iteratedDeriv i f 0 = iteratedDeriv i g 0

/-! Taper fixed once on the unit period. Used only on the full (blocked) volume,
not in the bare-stencil definition. `4 ≤ R` in those uses. In `connection` only
the taper is new compared with Source.partConnection. On the connection about
the chosen root, use at vertices in right-closed centered cell. For a positive link
with end outside, both profile prescriptions in the outer part vanish anyway. -/

structure Taper where
  χ : E4 → ℝ
  smooth : ContDiff ℝ ∞ χ
  near (x : E4) : (∀ i, |x i| ≤ 1/8) → χ x = 1
  outside {x : E4} (i : Axis) (h : 1/4 ≤ |x i|) : χ x = 0
  even (s : Signed) (x : E4) : χ (Ortho.move s.ortho x) = χ x
  interval (x : E4) : χ x ∈ Icc 0 1

def Taper.connection (T : Taper) (n : Side) (d : ℕ) (J : Labels.Jet su) (h : ℝ) (l : Edge Cover)
    (t : ℝ) : su.Color := T.χ ((n.val:ℝ)⁻¹ • (vector l.1 + t • basis l.2)) •
      Source.partConnection (d/2) J (h^2) l t

structure TaperHol where
  T : Taper
  flow (n : Side) (d : ℕ) (J : Labels.Jet su) (h : ℝ) (l : Edge Cover) : ℝ → su.El
  solves n d J h l : Source.SolvesLink (flow n d J h l) (T.connection n d J h l)

def Taper.spin (T : Taper) (h : ℝ) : Matrix (Modes n 6) (SpinMode d) ℂ := Matrix.of fun i j =>
  let x := Lattice.lift i.1.1
  if i.1.2=j.1.2 ∧ i.2=j.2 then
    (T.χ ((n.val:ℝ)⁻¹ • vector x) : ℂ) * ap n x * profile j.1.1 x h else 0

def TaperHol.links (H : TaperHol) (n : Side) (d : ℕ) (J : Labels.Jet su) (h : ℝ) : Grid n := fun l =>
  H.flow n d J h (Lattice.lift l.1,l.2) 1

/-- Ratio only near the identity where unmarked density is invertible. -/
def TaperHol.test (H : TaperHol) (d : ℕ) (f x : Density n 6) (J : Labels.Jet su)
    (h : ℝ) : SpinPol d :=
  let U := H.links n d J h
  Grass.adapter (H.T.spin h) (H.T.spin h) (Ring.inverse (f U) * x U)

def TaperHol.Matches (H : TaperHol) (v : Pol d) (f x : Density n 6) : Prop := ∀ J : Labels.Jet su,
  (∀ᶠ h in 𝓝 0, IsUnit (f (H.links n d J h))) ∧ Agrees (H.test d f x J) (desired v J)
end SourceRead

/-- None for point calibration. r indexes the after-blocking average matcher. -/
abbrev Averaging := Option (Axis → Fin 7)

namespace Averaging

def permute (s : Signed) (u : Averaging) : Averaging := u.map fun f => f ∘ (s.perm.symm)
variable {X : Type} [AddCommGroup X] [Module ℝ X]

def axis (stride M : ℕ) (a : Axis) (x : Cover → X) (b : Cover) := (M:ℝ)⁻¹ •
  ∑ i : Fin M, x (b + (stride : ℤ) • (((i.val : ℤ) - (((M-1)/2 : ℕ):ℤ)) • Lattice.step a))

def filter (u : Averaging) (M : ℕ) (x : Cover → X) : Cover → X := match u with
 | none => x
 | some f => (List.finRange 4).foldl (fun g a => axis 1 M a ((axis (X:=X) 2 M a)^[(f a).val] g)) x

end Averaging

namespace UV
/-- Orientations of all the slots. Explicit fields of this structure require
realizing the *precise* unrenormalized transforms of `Labels`, even before quotient. -/
structure RawSym where
  flavor (d) (u : FlavorTorus) : Label d ≃ₗ[ℂ] Label d
  pin (d) (p : EuPin) : Label d ≃ₗ[ℂ] Label d
  charge (d) : Label d ≃ₗ[ℂ] Label d
  adj (d) (a : Axis) : Label d ≃ₛₗ[starRingEnd ℂ] Label d
  parity (d) : Label d ≃ₗ[ℂ] Label d
  unit (d) : Label d
  flavorActs d u x : (flavor d u x).val = flavorAct u x.val
  pinActs d u x : (pin d u x).val = pinAct u x.val
  chargeActs d x : (charge d x).val = chargeAct x.val
  adjActs d a x : (adj d a x).val = UV.adj a x.val
  parityActs d x : (parity d x).val = parityAct x.val
  unitActs d : (unit d).val = UV.unit d
end UV

structure Calibration (C : Sequence) where
  sym : RawSym
  hol : Source.Hol su
  test : SourceRead.TaperHol
  stencil (d : ℕ) : Finset Cover
  localMap (d : ℕ) : Label d →ₗ[ℂ] Cylinder.Formula (stencil d) 6
  candidate (d : ℕ) (n : Side) (b : Cover) : Label d →ₗ[ℂ] Insertion n 6
  mix (d : ℕ) (v : Averaging) (i : ℕ) : Label d ≃ₗ[ℂ] Label d
  base (d : ℕ) : ℕ

namespace Calibration
variable {C : Sequence} (P : Calibration C)

local notation "B" => C.S.side

def physical {d : ℕ} (u : Averaging) (i : ℕ) (x : Label d) (b : Cover) : Insertion (B (C.R i) (C.N i)) 6 :=
  P.candidate d _ b (P.mix d u i x)

/-- Number of cutoff lattice steps per `base` bond for this normalization
(index i with N i ≥ base). -/
def samples (i d : ℕ) := (C.S.ratio (C.N i)).val / (C.S.ratio (P.base d)).val

def marker {d : ℕ} (x : Label d) (u : Averaging) (i : ℕ) := Averaging.filter u (P.samples i d) (P.physical u i x) 0

def Transported {d : ℕ} (i : ℕ) (x : Label d) (u : Averaging) : Prop :=
  ∃ f : (m : ℕ) → Density (B (C.R i) m) 6,
    f (C.N i) = (C.A i).density (C.N i) * ⇑(P.marker x u i) ∧
    (C.A i).Carried f (P.base d) ∧
    P.test.Matches x.val ((C.A i).density (P.base d)) (f (P.base d))

open Cylinder

structure SectionLaws : Prop where
  localizes (d n b x U) : P.candidate d n b x U = places b (P.localMap d x) U
  invariant (d n b x) : Lat.Invariant (P.candidate d n b x)
  seed d x J : SourceRead.Agrees (SourceRead.onStencil P.hol (P.localMap d x) d J)
      (SourceRead.desired x.val J)
  unit (d n b) : P.candidate d n b (P.sym.unit d)=1
  pin (d n b x p s) (h : EuPin.Lifts p s) : Action.pin p s ⇑(P.candidate d n b x) =
    (P.candidate d n (s.act b) (P.sym.pin d p x))
  charge d n b x : Action.charge ⇑(P.candidate d n b x) = P.candidate d n b (P.sym.charge d x)
  flavor d n b x u : Action.flavor u ⇑(P.candidate d n b x) = P.candidate d n b (P.sym.flavor d u x)
  star d n b x a : Action.adj a ⇑(P.candidate d n b x) =
    P.candidate d n ((Signed.mirror a).act b) (P.sym.adj d a x)
  parity d n b x : Action.parity ⇑(P.candidate d n b x) =
    P.candidate d n b (P.sym.parity d x)
  mesons (d n i j) (M : Spike) (x : Label d) (h : x.val = UV.bilinear i j M 0 0) (U) :
    P.candidate d n 0 x U = ∑ s : Pinor, ∑ t : Pinor, ∑ k : Hue,
                              M s t • (bar ((0,s,k),i) * psi ((0,t,k),j))
  baryons (n i j k) (x : Label 9) (h : x.val = UV.baryon i j k) (U) :
    P.candidate 9 n 0 x U = ∑ σ : Equiv.Perm Hue, Equiv.Perm.sign σ •
      (psi ((0,i,σ 0),0) * psi ((0,j,σ 1),1) * psi ((0,k,σ 2),2))

-- Eqn systems etc. may use larger horizons only after some cutoff.
structure Mixing (d i : ℕ) : Prop where
  live : P.base d ≤ C.N i
  unit v : P.mix d v i (P.sym.unit d) = P.sym.unit d
  pin v x p s (h : EuPin.Lifts p s) : P.sym.pin d p (P.mix d v i x) =
    P.mix d (Averaging.permute s v) i (P.sym.pin d p x)
  charge v : Commute (P.sym.charge d) (P.mix d v i) -- ensure uses desired action under composition
  flavor v u : Commute (P.sym.flavor d u) (P.mix d v i)
  star v a x : P.sym.adj d a (P.mix d v i x) = P.mix d v i (P.sym.adj d a x) -- r stays
  parity v : Commute (P.sym.parity d) (P.mix d v i)
  calibration x u : P.Transported (d:=d) i x u

structure System : Prop where
  sections : P.SectionLaws
  origin {d : ℕ} (h : d ≤ 8) : P.base d = 0
  mixing (d) : ∀ᶠ i in atTop, P.Mixing d i

end Calibration
end YM.Massive
