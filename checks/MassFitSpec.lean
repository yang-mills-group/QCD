import YM.Massive.Target.Physics
import Mathlib.Tactic

/-! Independent specification of the unique all-pairs least-squares fit.
The loss is the actual submitted definition. This formula was derived from
the 30-by-6 ordered-pair design matrix, not from the submitted fitting proof.
-/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive
open scoped BigOperators

def closedFit (b : Copies → Copies → ℝ) (i : Copies) : ℝ :=
  (∑ j, if i = j then 0 else b i j + b j i) / 8 -
  (∑ k, ∑ j, if k = j then 0 else b k j) / 40

def MassFitCorrect : Prop := ∀ b : Copies → Copies → ℝ,
  (∀ u, Signals.loss b (closedFit b) ≤ Signals.loss b u) ∧
  (∀ u, u ≠ closedFit b → Signals.loss b (closedFit b) < Signals.loss b u)

def referenceMass (i : Copies) : ℝ := (i.val : ℝ) + 1

-- Perturb only the unordered pair (4,5), absent from the six-pair star/triangle.
def exampleB (i j : Copies) : ℝ := referenceMass i + referenceMass j +
  if (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) then 1/1000 else 0

def SixPairDifference : Prop :=
  Signals.loss exampleB (closedFit exampleB) < Signals.loss exampleB referenceMass

end YMReview.QCD
