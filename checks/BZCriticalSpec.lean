import BZInvariantSpec

/-! The IR critical exponent of the specified two-loop reference flow. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

def BZCriticalTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f →
  twoLoopCoefficient f < 0 → ∀ a : ℝ → ℝ, TruncatedTrajectory f a →
  Tendsto (fun t => Real.log (bzRoot f-a t)/t) atBot (𝓝 (bzDerivative f)) ∧
  Tendsto (deriv (fun t => Real.log (bzRoot f-a t))) atBot (𝓝 (bzDerivative f))

end YMReview.QCD
