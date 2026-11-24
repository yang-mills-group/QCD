import BanksZaksSpec
import Mathlib.Topology.Order.IntermediateValue

/-! Conditional remainder control and a specified three-loop MS-bar benchmark.
Neither is derived from the submitted QCD construction or a diagram calculation. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Set

def correctedBracket (f : ℝ) (R : ℝ → ℝ) (a : ℝ) : ℝ :=
  oneLoopCoefficient f + twoLoopCoefficient f*a + R a
def BZRemainderTest : Prop := ∀ (f δ : ℝ) (R : ℝ → ℝ),
  0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 → 0 ≤ δ →
  δ < oneLoopCoefficient f/2 →
  ContinuousOn R (Icc (bzRoot f/2) (3*bzRoot f/2)) →
  (∀ a ∈ Icc (bzRoot f/2) (3*bzRoot f/2), |R a| ≤ δ) →
  ∃ a ∈ Ioo (bzRoot f/2) (3*bzRoot f/2), correctedBracket f R a = 0 ∧
    |a-bzRoot f| ≤ δ/(-twoLoopCoefficient f)

/-- Standard massless SU(3) coefficient in MS-bar; higher coefficients are scheme dependent. -/
def threeLoopCoefficient (f : ℝ) : ℝ := 2857/2 - 5033*f/18 + 325*f^2/54
def threeLoopBracket (f a : ℝ) : ℝ :=
  oneLoopCoefficient f + twoLoopCoefficient f*a + threeLoopCoefficient f*a^2
def threeLoopBeta (f a : ℝ) : ℝ := -2*a^2*threeLoopBracket f a

def ThreeLoopBenchmarkTest : Prop :=
  (∃ a ∈ Ioo (1/318:ℝ) (1/316), threeLoopBeta 16 a = 0) ∧
  (∀ a : ℝ, 0 < a → a ≤ 1 → threeLoopBeta 6 a < 0) ∧
  (∃ a ∈ Ioo (1:ℝ) 2, threeLoopBeta 6 a = 0)

end YMReview.QCD
