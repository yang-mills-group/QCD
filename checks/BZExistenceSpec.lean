import BZTrajectorySpec
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Existence for the specified scalar two-loop ODE, not existence of a QFT. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

def positiveLog (c x : ℝ) : ℝ := x+c*Real.log x

def BZGlobalTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  ∃ a : ℝ → ℝ, TruncatedTrajectory f a ∧
    Tendsto a atBot (𝓝 (bzRoot f)) ∧ Tendsto a atTop (𝓝 0)

def BZInitialValueTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  ∀ a₀ : ℝ, 0 < a₀ → a₀ < bzRoot f →
  ∃ a : ℝ → ℝ, TruncatedTrajectory f a ∧ a 0 = a₀ ∧
    Tendsto a atBot (𝓝 (bzRoot f)) ∧ Tendsto a atTop (𝓝 0)

end YMReview.QCD
