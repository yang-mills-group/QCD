import TwoLoopSpec
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Even the first two asymptotic terms do not determine a differential beta
function without derivative or step-scaling control. This is a scalar control,
not a countermodel to the complete submitted QCD target. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter Set
open scoped Topology

def oscillatingRunning (A k e t : ℝ) : ℝ := logCorrected A k t + e*Real.sin t

def DifferentialRunningTest : Prop := ∀ A k e : ℝ, 0 < A → 0 ≤ k → 0 < e → e < A →
  Tendsto (fun t => oscillatingRunning A k e t/t) atTop (𝓝 A) ∧
  Tendsto (secondOrderRead A (oscillatingRunning A k e)) atTop (𝓝 k) ∧
  (∀ t, 0 < t → HasDerivAt (oscillatingRunning A k e)
    (A+k/t+e*Real.cos t) t ∧ 0 < deriv (oscillatingRunning A k e) t) ∧
  ¬ ∃ l : ℝ, Tendsto (deriv (oscillatingRunning A k e)) atTop (𝓝 l)

end YMReview.QCD
