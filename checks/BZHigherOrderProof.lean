import BZHigherOrderSpec
import BanksZaksProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Set

theorem corrected_root_distance {f δ a : ℝ} {R : ℝ → ℝ}
    (h1 : twoLoopCoefficient f < 0) (hR : |R a| ≤ δ)
    (hz : correctedBracket f R a = 0) : |a-bzRoot f| ≤ δ/(-twoLoopCoefficient f) := by
  have he := bz_root_equation (ne_of_lt h1)
  have hm : twoLoopCoefficient f*(a-bzRoot f) = -R a := by
    unfold correctedBracket at hz
    linarith
  have hab := congrArg abs hm
  rw [abs_mul,abs_of_neg h1,abs_neg] at hab
  apply (le_div_iff₀ (neg_pos.mpr h1)).mpr
  nlinarith

theorem bz_remainder_test : BZRemainderTest := by
  intro f δ R h0 h1 _ hδ hcont hbound
  have hr := bz_root_positive h0 h1
  have he := bz_root_equation (ne_of_lt h1)
  have hlo : 0 < correctedBracket f R (bzRoot f/2) := by
    have hb := (abs_le.mp (hbound _ ⟨le_rfl,by linarith⟩)).1
    unfold correctedBracket
    nlinarith
  have hhi : correctedBracket f R (3*bzRoot f/2) < 0 := by
    have hb := (abs_le.mp (hbound _ ⟨by linarith,le_rfl⟩)).2
    unfold correctedBracket
    nlinarith
  have hc : ContinuousOn (correctedBracket f R) (Icc (bzRoot f/2) (3*bzRoot f/2)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.add hcont
  obtain ⟨a,ha,hz⟩ := intermediate_value_Ioo' (by linarith : bzRoot f/2 ≤ 3*bzRoot f/2)
    hc (show (0:ℝ) ∈ Ioo (correctedBracket f R (3*bzRoot f/2))
      (correctedBracket f R (bzRoot f/2)) from ⟨hhi,hlo⟩)
  exact ⟨a,ha,hz,corrected_root_distance h1 (hbound a ⟨ha.1.le,ha.2.le⟩) hz⟩

theorem three_loop_sixteen_bracket :
    ∃ a ∈ Ioo (1/318:ℝ) (1/316), threeLoopBeta 16 a = 0 := by
  have hc : Continuous (threeLoopBracket 16) := by unfold threeLoopBracket; fun_prop
  have hl : 0 < threeLoopBracket 16 (1/318) := by
    norm_num [threeLoopBracket,oneLoopCoefficient,twoLoopCoefficient,threeLoopCoefficient]
  have hu : threeLoopBracket 16 (1/316) < 0 := by
    norm_num [threeLoopBracket,oneLoopCoefficient,twoLoopCoefficient,threeLoopCoefficient]
  obtain ⟨a,ha,hz⟩ := intermediate_value_Ioo' (by norm_num : (1/318:ℝ) ≤ 1/316)
    hc.continuousOn (show (0:ℝ) ∈ Ioo (threeLoopBracket 16 (1/316))
      (threeLoopBracket 16 (1/318)) from ⟨hu,hl⟩)
  exact ⟨a,ha,by unfold threeLoopBeta; rw [hz,mul_zero]⟩

theorem three_loop_six_no_small_root (a : ℝ) (ha : 0 < a) (h1 : a ≤ 1) :
    threeLoopBeta 6 a < 0 := by
  have he : threeLoopBracket 6 a = 7+26*a-65/2*a^2 := by
    norm_num [threeLoopBracket,oneLoopCoefficient,twoLoopCoefficient,threeLoopCoefficient]
    ring
  have hp : 0 < threeLoopBracket 6 a := by
    rw [he]
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h1)]
  exact mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos ha] : -2*a^2 < 0) hp

theorem three_loop_six_strong_root : ∃ a ∈ Ioo (1:ℝ) 2, threeLoopBeta 6 a = 0 := by
  have hc : Continuous (threeLoopBracket 6) := by unfold threeLoopBracket; fun_prop
  have hl : 0 < threeLoopBracket 6 1 := by
    norm_num [threeLoopBracket,oneLoopCoefficient,twoLoopCoefficient,threeLoopCoefficient]
  have hu : threeLoopBracket 6 2 < 0 := by
    norm_num [threeLoopBracket,oneLoopCoefficient,twoLoopCoefficient,threeLoopCoefficient]
  obtain ⟨a,ha,hz⟩ := intermediate_value_Ioo' (by norm_num : (1:ℝ) ≤ 2)
    hc.continuousOn (show (0:ℝ) ∈ Ioo (threeLoopBracket 6 2) (threeLoopBracket 6 1) from ⟨hu,hl⟩)
  exact ⟨a,ha,by unfold threeLoopBeta; rw [hz,mul_zero]⟩

theorem three_loop_benchmark_test : ThreeLoopBenchmarkTest :=
  ⟨three_loop_sixteen_bracket,three_loop_six_no_small_root,three_loop_six_strong_root⟩

end YMReview.QCD
#print axioms YMReview.QCD.corrected_root_distance
#print axioms YMReview.QCD.bz_remainder_test
#print axioms YMReview.QCD.three_loop_sixteen_bracket
#print axioms YMReview.QCD.three_loop_six_no_small_root
#print axioms YMReview.QCD.three_loop_six_strong_root
#print axioms YMReview.QCD.three_loop_benchmark_test
