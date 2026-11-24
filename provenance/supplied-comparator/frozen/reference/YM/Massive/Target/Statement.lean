import YM.Massive.Target.Wightman

/-!
# Main target: Continuum Massive QCD (UNPROVED)

See also `YM/Massive/README.md`.
This states the goal without introducing an axiom. The UV running, mass
and interaction conclusions are substantive physical requirements and not
hypotheses. The level-coordinate and field normalization scheme (with a window
formulation of the gauge coupling, see `Tower` and limitations in README) is
part of the statement.

Settings: d_spacetime=4 (time axis 3), SU3 in defining representation,
six (`Fin 6`) fundamental Dirac fermions. Bare stencil/mask and fermion
algebra conventions as in `QCD`, *not* `QCDVacuum`. As part of one and the same
scaling path from the normalized finite-volume theories, at a fixed inverse-square
coupling parameter `βRef` at length 1 (tolerance ε picked before asking for
it sufficiently large), need the **whole** space of primaries. We
interpret `work/claim.tex`'s existence goal with allowance for changes
in RG/estimate schemes, not asking to verify every claim of the proposed proof.
Include explicit PCAC and flavor systems along with Stress uniqueness &
orientation test and local charge action of that stress. Reflection positivity
and the real-time conclusion both required.

Spacetime-limit order: one sequence of cutoffs and physical periods, with
point moments and arbitrary joints. Require achieving that scaling limit
with an ensemble of phases; full fields and Ward relations don't change in vacuum
selection. Color charged fields are NOT requested. Particle masses, spectral gap
and confinement are not requested.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Filter
open scoped Topology

/-- Conditions of the existence claim. -/
def TheoryAt (βRef ε : ℝ) : Prop := ∃ (C : Sequence) (P : Calibration C) (F : Fields)
    (m : MassFields) (s : Signals) (B : Bases F) (T : Momentum F) (S : Fields.Kernel F) (V : Vacua F),
  0 < βRef ∧
  Geometry ∧
  C.Path βRef ε ∧
  P.System ∧
  s.Read C ∧
  F.System P ∧
  Fields.Scaling S C P ∧
  Fields.Euclidean S ∧
  s.PCAC F m ∧
  s.Masses ∧
  Physics.Stress F T ∧
  Physics.Ward T S ∧
  B.Content P T ∧
  B.Comparison S ∧
  (∃ w : Continuation F, w.Produces S) ∧
  V.Decomposes S T B

def Goal : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ β in atTop, TheoryAt β ε

#print axioms Goal
end YM.Massive
