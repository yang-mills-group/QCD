import BZInvariantSpec
import TwoLoopSpec

/-! UV coefficients derived from the specified scalar two-loop equation.
This is a reference flow, not the submitted lattice trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

def referenceWilsonRunning (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (6/(16*Real.pi^2))*(a t)⁻¹

def BZUVRunningTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f →
  twoLoopCoefficient f < 0 → ∀ a : ℝ → ℝ, TruncatedTrajectory f a →
  Tendsto (fun t => referenceWilsonRunning a t/t) atTop (𝓝 (12*gBeta0 f)) ∧
  Tendsto (secondOrderRead (12*gBeta0 f) (referenceWilsonRunning a))
    atTop (𝓝 (wilsonLogLog f))

end YMReview.QCD
