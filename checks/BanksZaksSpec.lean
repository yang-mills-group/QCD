import FlavorSpec

/-! Algebraic tests of the specified two-loop truncation. No theorem here identifies
this polynomial with the beta function of the submitted continuum construction. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

/-- Flow with respect to log μ, for a=g²/(16π²). -/
def twoLoopBeta (f a : ℝ) : ℝ := -2 * a^2 * (oneLoopCoefficient f + twoLoopCoefficient f * a)
def bzRoot (f : ℝ) : ℝ := -oneLoopCoefficient f / twoLoopCoefficient f
def bzDerivative (f : ℝ) : ℝ := -2 * (bzRoot f)^2 * twoLoopCoefficient f

def BanksZaksTest : Prop :=
  (∀ f : ℕ, (∃ a : ℝ, 0 < a ∧ 0 < oneLoopCoefficient f ∧ twoLoopBeta f a = 0)
    ↔ 9 ≤ f ∧ f ≤ 16) ∧
  (∀ a : ℝ, 0 < a → twoLoopBeta 6 a < 0) ∧
  bzRoot 16 = 1/302 ∧
  (∀ f : ℕ, 9 ≤ f → f ≤ 16 →
    0 < bzRoot f ∧ twoLoopBeta f (bzRoot f) = 0 ∧
    HasDerivAt (twoLoopBeta f) (bzDerivative f) (bzRoot f) ∧ 0 < bzDerivative f) ∧
  (∀ f : ℕ, 9 ≤ f → ¬ trajectoryBudget f)

end YMReview.QCD
