import RunningSchemeSpec

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YMReview.QCD
open Polynomial

theorem scheme_low_coefficients (b₀ b₁ b₂ d₀ d₁ d₂ s t : ℝ) :
    (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff 0=0 ∧
    (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff 1=0 ∧
    (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff 2=2*(d₀-b₀) ∧
    (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff 3=2*(d₁-b₁)+4*s*(d₀-b₀) ∧
    (schemeDefect b₀ b₁ b₂ d₀ d₁ d₂ s t).coeff 4=
      2*(d₂-b₂)+6*s*d₁-4*s*b₁+2*s^2*d₀+4*t*d₀-6*t*b₀ := by
  norm_num [schemeDefect,couplingScheme,betaPolynomial,Polynomial.add_comp,
    Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,pow_succ,
    Polynomial.coeff_one,Polynomial.coeff_X]
  constructor
  · ring
  · constructor <;> ring

theorem running_scheme_test : RunningSchemeTest := by
  intro b₀ b₁ b₂ d₀ d₁ d₂ s t
  obtain ⟨h0,h1,h2,h3,h4⟩ := scheme_low_coefficients b₀ b₁ b₂ d₀ d₁ d₂ s t
  constructor
  · intro h
    have he2 := h 2 (by omega)
    have he3 := h 3 (by omega)
    have he4 := h 4 (by omega)
    rw [h2] at he2
    rw [h3] at he3
    rw [h4] at he4
    have hd0 : d₀=b₀ := by linarith
    subst d₀
    have hd1 : d₁=b₁ := by nlinarith
    subst d₁
    refine ⟨rfl,rfl,?_⟩
    unfold transformedThird
    nlinarith
  · rintro ⟨rfl,rfl,rfl⟩ n hn
    interval_cases n
    · exact h0
    · exact h1
    · rw [h2]; ring
    · rw [h3]; ring
    · rw [h4]; unfold transformedThird; ring

end YMReview.QCD
#print axioms YMReview.QCD.scheme_low_coefficients
#print axioms YMReview.QCD.running_scheme_test
