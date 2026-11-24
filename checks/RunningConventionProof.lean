import RunningConventionSpec
import BanksZaksProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD

theorem g_flow_to_normalized_flow (f : ℝ) {g : ℝ → ℝ} {t : ℝ}
    (hg : HasDerivAt g (gTwoLoopBeta f (g t)) t) :
    HasDerivAt (fun s => normalizedCoupling (g s))
      (twoLoopBeta f (normalizedCoupling (g t))) t := by
  convert! (hg.pow 2).div_const (16*Real.pi^2) using 1
  unfold normalizedCoupling twoLoopBeta gTwoLoopBeta gBeta0 gBeta1
  ring

theorem g_flow_to_wilson_flow (f : ℝ) {g : ℝ → ℝ} {t : ℝ} (hgt : g t ≠ 0)
    (hg : HasDerivAt g (gTwoLoopBeta f (g t)) t) :
    HasDerivAt (fun s => wilsonInverseCoupling (g s))
      (12*gBeta0 f + 72*gBeta1 f/wilsonInverseCoupling (g t)) t := by
  convert! (hasDerivAt_const t (6:ℝ)).div (hg.pow 2) (pow_ne_zero 2 hgt) using 1
  unfold wilsonInverseCoupling gTwoLoopBeta
  dsimp only [Pi.pow_apply]
  field_simp
  ring

theorem running_convention_test : RunningConventionTest := by
  intro f g t hgt hg
  exact ⟨g_flow_to_normalized_flow f hg,g_flow_to_wilson_flow f hgt hg⟩

theorem six_loop_coefficients : oneLoopCoefficient 6 = 7 ∧ twoLoopCoefficient 6 = 26 := by
  norm_num [oneLoopCoefficient,twoLoopCoefficient]

theorem sixteen_alpha_fixed_point : 4*Real.pi*bzRoot 16 = 2*Real.pi/151 := by
  rw [sixteen_flavor_root]
  ring

theorem one_loop_truncation_misses_six_flavor_term (a : ℝ) (ha : 0 < a) :
    twoLoopBeta 6 a < -2*oneLoopCoefficient 6*a^2 := by
  rw [six_loop_coefficients.1]
  unfold twoLoopBeta
  rw [six_loop_coefficients.1,six_loop_coefficients.2]
  nlinarith [pow_pos ha 3]

end YMReview.QCD
#print axioms YMReview.QCD.g_flow_to_normalized_flow
#print axioms YMReview.QCD.g_flow_to_wilson_flow
#print axioms YMReview.QCD.running_convention_test
#print axioms YMReview.QCD.six_loop_coefficients
#print axioms YMReview.QCD.sixteen_alpha_fixed_point
#print axioms YMReview.QCD.one_loop_truncation_misses_six_flavor_term
