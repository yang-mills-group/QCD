import MassFitSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive
open scoped BigOperators

-- Coefficients of each ordered reading in the actual all-pairs fit.
def fitWeight (i k l : Copies) : ℝ :=
  if k = l then 0 else if k = i ∨ l = i then 1/10 else -1/40

def FitStability : Prop := ∀ (b : Copies → Copies → ℝ) (r : Copies → ℝ) (δ : ℝ),
  0 ≤ δ → (∀ k l, k ≠ l → |b k l - (r k + r l)| ≤ δ) →
  (∀ i, |closedFit b i - r i| ≤ 3 * δ / 2) ∧
  (∀ i j, |(closedFit b i - closedFit b j) - (r i - r j)| ≤ 2 * δ)
end YMReview.QCD
