import BanksZaksSpec
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

/-! Dynamics of a specified massless two-loop truncation. Existence of a global
trajectory in the open interval is a hypothesis; no continuum QFT is constructed. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

def TruncatedTrajectory (f : ℝ) (a : ℝ → ℝ) : Prop :=
  (∀ t, 0 < a t ∧ a t < bzRoot f) ∧
  (∀ t, HasDerivAt a (twoLoopBeta f (a t)) t)

def BZTrajectoryTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f →
  twoLoopCoefficient f < 0 → ∀ a : ℝ → ℝ, TruncatedTrajectory f a →
  Tendsto a atBot (𝓝 (bzRoot f)) ∧ Tendsto a atTop (𝓝 0)

end YMReview.QCD
