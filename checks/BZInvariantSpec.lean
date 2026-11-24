import BZExistenceSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD

def bzOffset (f : ℝ) : ℝ := -twoLoopCoefficient f/oneLoopCoefficient f
def bzClock (f a : ℝ) : ℝ := positiveLog (bzOffset f) (a⁻¹-bzOffset f)

def BZFiniteScaleTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  ∀ a : ℝ → ℝ, TruncatedTrajectory f a → ∀ s t : ℝ,
    bzClock f (a t)-bzClock f (a s) = 2*oneLoopCoefficient f*(t-s)

def BZUniquenessTest : Prop := ∀ f : ℝ, 0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  ∀ a b : ℝ → ℝ, TruncatedTrajectory f a → TruncatedTrajectory f b → a 0 = b 0 → a = b

end YMReview.QCD
