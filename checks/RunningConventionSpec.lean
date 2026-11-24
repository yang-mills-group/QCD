import BanksZaksSpec
import TwoLoopSpec

/-! Conditional chain-rule tests. The hypothesis is the specified perturbative ODE,
not a claimed consequence of the submitted existence theorem. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD

def gTwoLoopBeta (f g : ℝ) : ℝ := -gBeta0 f*g^3 - gBeta1 f*g^5
def normalizedCoupling (g : ℝ) : ℝ := g^2/(16*Real.pi^2)
def wilsonInverseCoupling (g : ℝ) : ℝ := 6/g^2

def RunningConventionTest : Prop := ∀ (f : ℝ) (g : ℝ → ℝ) (t : ℝ),
  g t ≠ 0 → HasDerivAt g (gTwoLoopBeta f (g t)) t →
  HasDerivAt (fun s => normalizedCoupling (g s))
    (twoLoopBeta f (normalizedCoupling (g t))) t ∧
  HasDerivAt (fun s => wilsonInverseCoupling (g s))
    (12*gBeta0 f + 72*gBeta1 f/wilsonInverseCoupling (g t)) t

end YMReview.QCD
