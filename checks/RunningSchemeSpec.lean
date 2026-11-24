import FlavorSpec
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div

/-! A finite polynomial jet checks scheme transformation algebra.
No actual QCD observable is identified with this change of variable. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Polynomial

def couplingScheme (s t : ℝ) : Polynomial ℝ := X+C s*X^2+C t*X^3
def betaPolynomial (b₀ b₁ b₂ : ℝ) : Polynomial ℝ :=
  -2*(C b₀*X^2+C b₁*X^3+C b₂*X^4)
def transformedThird (b₀ b₁ b₂ s t : ℝ) : ℝ := b₂-s*b₁+(t-s^2)*b₀
def schemeDefect (b₀ b₁ b₂ d₀ d₁ d₂ s t : ℝ) : Polynomial ℝ :=
  (couplingScheme s t).derivative*betaPolynomial b₀ b₁ b₂ -
    (betaPolynomial d₀ d₁ d₂).comp (couplingScheme s t)

def RunningSchemeTest : Prop := ∀ b₀ b₁ b₂ d₀ d₁ d₂ s t : ℝ,
  (∀ n : ℕ, n ≤ 4 → (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff n=0) ↔
    d₀=b₀ ∧ d₁=b₁ ∧ d₂=transformedThird b₀ b₁ b₂ s t

end YMReview.QCD
