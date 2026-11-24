import YM.Massive.Target.Euclidean
import YM.Massive.Target.Wick

/-!
# Statement: PCAC mass scheme, short-distance field ranks and stress test

On one space `Fields.W`. The derivative map (all spectators, separated kernel) is shared,
also after vacuum selection. In particular the mass and stress assertions in terms of W
then apply to the selected theory too (need the kernel properties & no further null labels).

Don't impose equality of bare and physical masses. Read actual coefficients b_ij of
A_ij → P_ij in the continuum, in the unweighted level-zero projection scheme in `Calibration`.
LS, and adjust normalization of P only *afterwards*. Use like relative normalization for the vector
identity. Require that agreement with a scalar mass signal in the actual blocked densities be
proved to a precision that can be used with this scheme to determine physical positive & unequal
masses; rooting that assertion e.g. in a mass-admitting tuning/shooting argument would suffice
but no detailed specification of internal running parameters is imposed here.

Weak basis comparison is a physical short distance limit on all moment systems
in the field content statement, including point comparison off collisions. We specify accuracy
as attaining every ε>0 eventually on those tests, not a rate in terms of parameters of a particular
proof. In particular specify rank/weak basis on W_d (so all elements of W_d, using projection
from any of the indicated average- or point-calibrated systems), with equivariant isomorphism on
all components and the specified unique-line test in precisely that filtration. Don't ask about
all possible stress/scaling systems belonging to a continuum theory.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter MeasureTheory Set
open QCD QCD.Lat Lattice Wilson UV Fields
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ComplexOrder

abbrev Copies := Flavor 6

structure MassFields where
  mesonThree : Copies → Copies → Spike → Label 6
  mesonFour : Copies → Copies → Spike → Label 8
  fixedThree i j M : (mesonThree i j M).val = UV.bilinear i j M 0 0
  fixedFour i j M : (mesonFour i j M).val = UV.bilinear i j M 0 0

namespace MassFields
variable (A : MassFields) (F : Massive.Fields) (i j : Copies)

def isotropic : Averaging := some fun _ => 2

def atVector (a : Axis) : Averaging := some fun b => if a=b then 1 else 2

def axial (a : Axis) : F.W := F.quotient (atVector a) 6 (A.mesonThree i j (gamma a*g5))

def polar (a : Axis) : F.W := F.quotient (atVector a) 6 (A.mesonThree i j (gamma a))

def pseudo : F.W := F.quotient isotropic 8 (A.mesonFour i j g5)

def scalar : F.W := F.quotient isotropic 8 (A.mesonFour i j 1)
end MassFields

structure Signals where
  (rg bVector : Copies → ℝ)  -- bVector=ren masses (result not input)
  (axial polar : Copies → Copies → ℝ)  -- coefficients of the true divergences
  margin : ℝ

namespace Signals
variable (C : Sequence) (s : Signals)

/-- Equally weighted least-squares fit *only off diagonal*. Include both orders. -/
def loss (b : Copies → Copies → ℝ) (u : Copies → ℝ) := ∑ i, ∑ j,
  if i=j then 0 else (b i j-u i-u j)^2

def bMass := s.bVector

structure Read : Prop where
  reach (i : Copies) : Tendsto (fun j => (C.A j).massRead 0 i) atTop (𝓝 (s.rg i : ℂ))
  room : 0 < s.margin
  signalPos (i) : s.margin ≤ s.rg i
  separated i j (h : i ≠ j) : s.margin ≤ |s.rg i - s.rg j|
  axialPaid i j (h : i ≠ j) : |s.axial i j - (s.rg i+s.rg j)| ≤ s.margin / 100
  polarPaid i j (h : i ≠ j) : |s.polar i j - (s.rg i-s.rg j)| ≤ s.margin / 100

structure Masses : Prop where
  fitted : ∀ u, loss s.axial s.bMass ≤ loss s.axial u
  unique : ∀ u, u ≠ s.bMass → loss s.axial s.bMass < loss s.axial u
  positive : ∀ i, 0 < s.bMass i
  distinct : Injective s.bMass
  signAxial i j (h : i ≠ j) : 0 < s.axial i j
  signPolar i j (h : i ≠ j) : 0 < s.polar i j * (s.bMass i - s.bMass j)

variable (F : Massive.Fields) (A : MassFields)
open MassFields

def divergence (F : Massive.Fields) (v : Axis → F.W) := ∑ a, F.partialD a (v a)

def renP (i j : Copies) : F.W := (↑(s.axial i j / (s.bMass i + s.bMass j)) : ℂ) • A.pseudo F i j

def renS (i j : Copies) : F.W := (↑(s.polar i j / (s.bMass i - s.bMass j)) : ℂ) • A.scalar F i j

def properVector (v : Axis → F.W) : Prop := ∀ a p, EuPin.IsRotation p → F.action p (v a) =
  ∑ b, (p.coord.val b a : ℂ) • v b

def properScalar (v : F.W) := ∀ p, EuPin.IsRotation p → F.action p v = v

structure Pair (i j : Copies) : Prop where
  AP (a) : A.axial F i j a ≠ 0
  VS (a) : A.polar F i j a ≠ 0
  pseudo : A.pseudo F i j ≠ 0
  scalar : A.scalar F i j ≠ 0
  pseudoFiltration : A.pseudo F i j ∈ F.level 6
  scalarFiltration : A.scalar F i j ∈ F.level 6
  APvar : properVector F (A.axial F i j)
  VSvar : properVector F (A.polar F i j)
  psVar : properScalar F (A.pseudo F i j)
  scVar : properScalar F (A.scalar F i j)
  trueA : divergence F (A.axial F i j) = (s.axial i j : ℂ) • A.pseudo F i j
  trueV : divergence F (A.polar F i j) = (s.polar i j : ℂ) • A.scalar F i j
  pcac : divergence F (A.axial F i j) = (↑(s.bMass i+s.bMass j) : ℂ) • s.renP F A i j
  vector : divergence F (A.polar F i j) = (↑(s.bMass i-s.bMass j) : ℂ) • s.renS F A i j

structure PCAC : Prop where
  axialCross i j : s.axial i j = s.axial j i
  polarCross i j : s.polar i j = - s.polar j i
  pairs i j (h : i ≠ j) : s.Pair F A i j

end Signals

abbrev Momentum (F : Massive.Fields) := Axis → Axis → F.W

namespace Physics
variable (F : Massive.Fields)

def tensor (p : EuPin) (T : Momentum F) := ∀ a b, F.action p (T a b) =
  ∑ i : Axis, ∑ j : Axis, (↑(p.coord.val i a * p.coord.val j b) : ℂ) • T i j

def identity : Momentum F := fun a b => if a=b then F.unit else 0

/-- The system is complexified; C-even and flavor neutral are important here. -/
structure Candidate (T : Momentum F) : Prop where
  level a b : T a b ∈ F.level 8
  symmetric a b : T a b = T b a
  parity a b : F.homogeneous false (T a b)
  charge a b : F.charge (T a b) = T a b
  neutral a b p : F.flavor p (T a b) = T a b
  orientations p : (∃ s, EuPin.Lifts p s) → tensor F p T
  conserved b : Signals.divergence F (fun a => T a b)=0

structure Stress (T : Momentum F) : Prop where
  candidate : Candidate F T
  fullRotation p : tensor F p T
  reality (a b i : Axis) : F.adj i (T a b) = ((if i=a then -1 else 1 : ℂ) *
        (if i=b then -1 else 1)) • T a b
  nontrivial : ∀ z : ℂ, T ≠ z • identity F
  invariant : Candidate F (identity F)
  unique (U : Momentum F) : Candidate F U ↔ ∃ x y : ℂ, U = x • T + y • identity F
  nonzeroTranslation : ∃ a, F.partialD a ≠ 0
  nonzeroRotation : ∃ a, F.lie a ≠ 0

variable {F}
/-- v is the affine translation/rotation test (puncture-relative, not about the origin). -/
def shell {n : ℕ} (T : Momentum F) (S : Kernel F) (x : Points (n+1))
    (p : Fin (n+1) → F.W) (χ : E4 → ℝ) (v : E4 → E4) :=
  -∑ a : Axis, ∑ b : Axis, ∫ y : E4,
    ((YM.Analysis.D (basis a) χ y * v (y-x 0) b : ℝ) : ℂ) *
    S (n+2) (Points.cons y x) (Fin.cons (T a b) p)

def Window {n : ℕ} (x : Points (n+1)) (χ : E4 → ℝ) := ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
  χ =ᶠ[𝓝 (x 0)] (fun _ => 1) ∧ ∀ i : Fin n, x i.succ ∉ tsupport χ

structure Ward (T : Momentum F) (S : Kernel F) : Prop where
  integrable n (x : Points (n+1)) (hx : x ∈ conf (n+1)) p (χ : E4 → ℝ) (h : Window x χ)
      (v : E4 → E4) (he : Continuous v) (a b : Axis) :
    Integrable (fun y : E4 => ((YM.Analysis.D (basis a) χ y * v (y-x 0) b : ℝ) : ℂ) *
      S (n+2) (Points.cons y x) (Fin.cons (T a b) p))
  translation n (x : Points (n+1)) (hx : x ∈ conf (n+1)) p (χ : E4 → ℝ) (h : Window x χ)
      (a : Axis) : shell T S x p χ (fun _ => basis a) = S _ x (update p 0 (F.partialD a (p 0)))
  rotation n (x : Points (n+1)) (hx : x ∈ conf (n+1)) p (χ : E4 → ℝ) (h : Window x χ)
      (g : Ortho.Skew) : shell T S x p χ (M4.move g.val) = S _ x (update p 0 (F.lie g (p 0)))

end Physics

open UV.Free

structure Bases (F : Massive.Fields) where
  radius : ℕ → ℝ
  frame (k d : ℕ) : UV.Free.Symbol d ≃ₗ[ℂ] ↥(F.level d)

namespace Bases
variable {F : Massive.Fields} {C : Sequence}
variable (X : Bases F)

def choice (k : ℕ) {d : ℕ} (x : Label d) : F.W := (X.frame k d (projection x)).val

-- pullback test of orientation of the stress line, topology pinned via the frame at k=0.
-- put scale in `r^4`; the minus sign uses the normalization in work/local.tex, with orientation
-- equivalent up to a common normalization (and addition of identity tensor).
def stressAt (T : F.W) (h : T ∈ F.level 8) (k : ℕ) : F.W :=
  (X.frame 0 8 ((X.frame k 8).symm ((↑((X.radius k)^4) : ℂ) • (⟨T,h⟩ : F.level 8)))).val

structure Content (P : Calibration C) (T : Momentum F) : Prop where
  positive (k) : 0 < X.radius k
  probes : Tendsto X.radius atTop (𝓝 0)
  -- bases comparing W with the projection from *all* of the free reference system,
  -- with its charge orientations, reality and flavor. Taking them equivariant for
  -- Spin also (physical representation at every comparison).
  equivariant k d p (x : UV.Label d) : X.choice k (P.sym.pin d p x)= F.action p (X.choice k x)
  charge k d (x : UV.Label d) : X.choice k (P.sym.charge d x) = F.charge (X.choice k x)
  flavor k d u (x : UV.Label d) : X.choice k (P.sym.flavor d u x) = F.flavor u (X.choice k x)
  reality k d a (x : UV.Label d) : X.choice k (P.sym.adj d a x) = F.adj a (X.choice k x)
  parity k d (x : UV.Label d) : X.choice k (P.sym.parity d x) = F.parity (X.choice k x)
  fixedUnit k d : X.choice k (P.sym.unit d)=F.unit
  -- stressAt depends on T, not arbitrary candidate or bare-polynomial analogy
  total a b : ∃ (t : UV.Label 8) (h : T a b ∈ F.level 8), t.val = UV.totalStress a b ∧
    Tendsto (X.stressAt (T a b) h) atTop (𝓝 (- X.choice 0 t))
  visible : ∃ t : UV.Label 8, (∃ a b : Axis, a ≠ b ∧ t.val = UV.totalStress a b) ∧
    projection t ≠ 0
  baryons (i j k) : ∃ x : UV.Label 9, x.val = UV.baryon i j k ∧ projection x ≠ 0
  odd : ∃ i j k, ∃ x : UV.Label 9, x.val = UV.baryon i j k ∧
    F.quotient none 9 x ≠ 0 ∧ F.homogeneous true (F.quotient none 9 x) ∧
    ∀ u : UV.FlavorTorus, F.flavor u (F.quotient none 9 x) =
      ((u 0).val * (u 1).val * (u 2).val) • F.quotient none 9 x
  descends n (x : Points n) (hx : x ∈ conf n) (d : Fin n → ℕ) (A B : (i : Fin n) → UV.Label (d i))
      (h : ∀ i : Fin n, projection (d := d i) (A i)=projection (d := d i) (B i)) : wick d x A = wick d x B
  detects d (x : UV.Label d) (hx : projection x ≠ 0) (r : ℝ) (hr : 0 < r) :
    0 < wick (fun _ : Fin 2 => d) (points ![0,r • basis timeAxis]) ![P.sym.adj d timeAxis x,x]

structure Comparison (S : Kernel F) : Prop where
  linearJet n (d : Fin n → ℕ) (u : (i : Fin n) → UV.Label (d i)) (j : ℕ)
      (ε : ℝ) (he : 0 < ε) (K : Set (Points n)) (h : IsCompact K) (hK : K ⊆ conf n) :
    ∀ᶠ k in atTop, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ j (fun z => S n (X.radius k • z) (fun i => X.choice k (u i))) y -
        iteratedFDeriv ℝ j (fun x => wick d x u) y‖ ≤ ε
  -- include literal convergence, without needing conversion at j=0
  point n (d : Fin n → ℕ) (u : (i : Fin n) → UV.Label (d i)) (x : Points n) (h : x ∈ conf n) :
    Tendsto (fun k => S n (X.radius k • x) (fun i => X.choice k (u i))) atTop (𝓝 (wick d x u))

end Bases
end YM.Massive
