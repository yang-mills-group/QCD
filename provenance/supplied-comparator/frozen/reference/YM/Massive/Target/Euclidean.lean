import YM.Massive.Target.Calibration
import YM.Euclid.Differential

/-!
# Statement: Euclidean field system

Read all arities on one space `Fields.W` filtered by finite engineering
horizons (inclusions use actual submodules), with slot detection on the *same*
separated correlators. No completeness, summable infinite linear combinations,
or multiplication in W across horizons asserted. Norms there supply e.g.
ordinary Euclidean continuity comparisons on each finite-dimensional cap; don't
confuse W with the positive inner product space for word vectors in reconstruction.

RP is stated in a points formulation incl any such finite word strictly on one side
(of any arity, and with any order of its distinct points). Bounded slabs
condition stated as an actual Gram bound for the operator of `prepend`ing a
slab word (with margins & the requisite time shift). The claim will include a
Wightman realization, not requiring only these necessary/used properties of S.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function QCD QCD.Lat Lattice Wilson UV MeasureTheory Filter Set
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder ContDiff

structure Fields where
  W : Type
  [ab : NormedAddCommGroup W]
  [space : NormedSpace ℂ W]
  level (d : ℕ) : Submodule ℂ W
  quotient (r : Averaging) (d : ℕ) : UV.Label d →ₗ[ℂ] W
  unit : W
  adj (a : Axis) : W ≃ₛₗ[starRingEnd ℂ] W
  parity : W ≃ₗ[ℂ] W
  charge : W ≃ₗ[ℂ] W
  flavor : UV.FlavorTorus →* (W ≃ₗ[ℂ] W)
  action : EuPin →* (W ≃ₗ[ℂ] W)
  partialD (a : Axis) : W →ₗ[ℂ] W
  lie (A : Ortho.Skew) : W →ₗ[ℂ] W

attribute [instance] Fields.ab Fields.space
-- scalar restriction W normed ℝ: beware diamonds
noncomputable instance (F : Fields) : NormedSpace ℝ F.W := .restrictScalars ℝ ℂ _

namespace Fields
variable {C : Sequence} (F : Fields)

def homogeneous (p : Bool) (v : F.W) := if p then F.parity v = -v else F.parity v=v

structure System (P : Calibration C) : Prop where
  identification d r : LinearMap.range (F.quotient r d) = F.level d
  finite (d) : FiniteDimensional ℂ (F.level d)
  increases : Monotone F.level
  exhaustive (x : F.W) : ∃ d, x ∈ F.level d
  units d r : F.quotient r d (P.sym.unit d) = F.unit
  commutes d r x a : F.adj a (F.quotient r d x) = F.quotient r d (P.sym.adj d a x)
  pinActs d r x p s (h : EuPin.Lifts p s) : F.action p (F.quotient r d x) =
    F.quotient (Averaging.permute s r) d (P.sym.pin d p x)
  charge d r x : F.charge (F.quotient r d x) = F.quotient r d (P.sym.charge d x)
  flavor d r x u : F.flavor u (F.quotient r d x) = F.quotient r d (P.sym.flavor d u x)
  parity d r x : F.parity (F.quotient r d x) = F.quotient r d (P.sym.parity d x)
  reflected a : Function.Involutive (F.adj a)
  folded : Function.Involutive F.parity
  doublesBack : Function.Involutive F.charge
  flavorActs (x : F.W) : Continuous fun p => F.flavor p x
  flavorTurns (u : FlavorTorus) a : Function.Commute (F.flavor u) (F.adj a)
  properActs (x : F.W) : Continuous fun p => F.action p x
  lift {d} x (h : x ∈ F.level d) p : F.action p x ∈ F.level d
  sign (p : EuPin) (h : p.coord=1) (hm : p.matrix= -1) : F.action p = F.parity
  keepFlavor (p : EuPin) u : Function.Commute (F.action p) (F.flavor u)
  infinitesimal (A : Ortho.Skew) (x : F.W) (p) (h : EuPin.Path A p) :
    HasDerivAt (fun t => F.action (p t) x) (F.lie A x) 0
  derivatives (a : Axis) (d : ℕ) (x : F.W) (h : x ∈ F.level d) : F.partialD a x ∈ F.level (d+2)

abbrev Kernel := (n : ℕ) → Points n → MultilinearMap ℂ (fun _ : Fin n => F.W) ℂ

abbrev Placements := List (E4 × F.W)

variable {F}
variable (S : Kernel F)

def located (l : Placements F) : Points l.length := points fun i => (l.get i).1

def pointMoment (l : Placements F) : ℂ := S _ (located l) fun i => (l.get i).2

def reflect (a : Axis) (l : Placements F) : Placements F :=
  l.reverse.map fun x => (Ortho.move (Signed.reflect a) x.1,F.adj a x.2)

def gram (a : Axis) {n : ℕ} (l : Fin n → Placements F) (u : Fin n → ℂ) :=
  ∑ i, ∑ j, star (u i) * pointMoment S (reflect a (l i) ++ l j) * u j

def distinct (l : Placements F) := located l ∈ conf _

def positive (l : Placements F) (a : Axis) := distinct l ∧ ∀ u ∈ l, 0 < u.1 a

def slab (a : Axis) (r d : ℝ) (p : Placements F) := spaced r (located p) ∧
  ∀ u ∈ p, u.1 a ∈ Icc r (d-r)

def prepend (a : Axis) (d : ℝ) (p q : Placements F) : Placements F := p ++ q.map fun x => (x.1+d • basis a,x.2)

structure Slabs (a : Axis) : Prop where
  operator (j D : ℕ) : ∃ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
    ∀ (d r : ℝ), 0 < d → 0 < r → r ≤ 1 → ∀ p : Placements F, p.length=j → slab a r d p →
      (∀ x ∈ p, x.2 ∈ F.level D ∧ ‖x.2‖ ≤ 1) → ∀ (n : ℕ) (l : Fin n → Placements F),
        (∀ i, positive (l i) a) → ∀ u, gram S a (prepend a d p ∘ l) u ≤ ↑((A*r⁻¹^m)^2) * gram S a l u

/-- Translation invariant, proper Euclidean rotations, positive in every cap.
Candidate uses same adj prescriptions and slot faithfulness after vacuum selection too. -/
structure Euclidean : Prop where
  translation n (x : Points n) (hx : x ∈ conf n) z u : S n (points fun i => x i+z) u = S n x u
  rotation n (x : Points n) (hx : x ∈ conf n) (p : EuPin) (hp : p.IsRotation) u :
    S n (points fun i => Ortho.move p.coord (x i)) (F.action p ∘ u) = S n x u
  conjugate a (l : Placements F) (h : distinct l) : pointMoment S (reflect a l) = star (pointMoment S l)
  parity n (x : Points n) (hx : x ∈ conf n) u : S n x (F.parity ∘ u) = S n x u
  swap (l r : Placements F) (x y : E4 × F.W) (h : distinct (l ++ x :: y :: r)) p q
      (hp : F.homogeneous p x.2) (hq : F.homogeneous q y.2) :
    pointMoment S (l ++ x :: y :: r) = (if p && q then -1 else 1) * pointMoment S (l ++ y :: x :: r)
  empty : S 0 0 0 = 1
  unit n (x : Points (n+1)) (hx : x ∈ conf _) (p : Fin n → F.W) :
    S _ x (Fin.cons F.unit p) = S n (Points.tail x) p
  smooth n (u : Fin n → F.W) : ContDiffOn ℝ ∞ (fun x => S n x u) (conf n)
  capped n (u : Fin n → F.W) (j : ℕ) : ∃ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
    ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
      ‖iteratedFDeriv ℝ j (fun y => S n y u) x‖ ≤ A * r⁻¹^m
  derivatives n (u : Fin n → F.W) (i : Fin n) (x : Points n) (hx : x ∈ conf _) (a : Axis) :
    YM.Analysis.D (Points.direction i a) (fun x => S n x u) x = S n x (update u i (F.partialD a (u i)))
  rp a n (l : Fin n → Placements F) (he : ∀ i, positive (l i) a) (u : Fin n → ℂ) : 0 ≤ gram S a l u
  bounded a : Slabs S a
  faithful (x : F.W) (h : x ≠ 0) : ∃ r : ℝ, 0 < r ∧
    0 < S 2 (points ![0,r • basis timeAxis]) ![F.adj timeAxis x,x]

-- adj_n subtle when choosing time-separations: are signs consistent between normals for odd? review

namespace Limit
variable (C : Sequence)
variable (P : Calibration C)
variable {n : ℕ}

def regulatorPositions (i : ℕ) (x : Fin n → Cover) := points fun j => C.S.spacing (C.N i) • vector (x j)

def evaluation (d : Fin n → ℕ) (u : (i : Fin n) → Label (d i)) (r : Fin n → Averaging) (x : Fin n → Cover) (i : ℕ) :=
  (C.A i).regulator.average (List.ofFn fun a => P.physical (r a) i (u a) (x a)).prod

end Limit
open Limit
-- All products of the *local physical primaries* already converge in one and the same actual extraction,
-- not products of their averages over cells. On any compact off collisions. `eventually` localized at
-- any requested arities/horizons. Include a mesh nonvacuity criterion.
structure Scaling (C : Sequence) (P : Calibration C) : Prop where
  flavor u p (h : distinct p) : pointMoment S (p.map fun x => (x.1,F.flavor u x.2)) = pointMoment S p
  improper (s : EuPin) p (h : distinct p) :
    pointMoment S (p.map fun x => (Ortho.move s.coord x.1,F.action s x.2)) = pointMoment S p
  charge p (h : distinct p) : pointMoment S (p.map fun x => (x.1,F.charge x.2)) = pointMoment S p
  coverage n (x : Points n) : ∃ r : ℕ → Fin n → Cover,
    Tendsto (fun i => regulatorPositions C i (r i)) atTop (𝓝 x)
  uniform n (d : Fin n → ℕ) (u : (i : Fin n) → Label (d i)) (r : Fin n → Averaging)
      (K : Set (Points n)) (hK : IsCompact K) (he : K ⊆ conf n) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x : Fin n → Cover, regulatorPositions C i x ∈ K →
      ‖evaluation C P d u r x i - S n (regulatorPositions C i x) (fun j => F.quotient (r j) _ (u j))‖ ≤ ε

end Fields
end YM.Massive
