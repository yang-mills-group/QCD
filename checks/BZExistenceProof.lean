import BZExistenceSpec
import BZTrajectoryProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter Set
open scoped Topology

theorem positive_log_derivative (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (positiveLog c) (1+c/x) x := by
  simpa only [div_eq_mul_inv] using! (hasDerivAt_id x).add ((Real.hasDerivAt_log hx.ne').const_mul c)

theorem positive_log_strictMono {c : ℝ} (hc : 0 < c) : StrictMonoOn (positiveLog c) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (positive_log_derivative c hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    rw [(positive_log_derivative c hx0).deriv]
    positivity

theorem positive_log_surjective {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∃ x : ℝ, 0 < x ∧ positiveLog c x = y := by
  let l := Real.exp ((min y 0-2)/c)
  let u := max 1 (y+1)
  have hl : 0 < l := Real.exp_pos _
  have hl1 : l < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by linarith [min_le_right y 0]) hc
  have hu : 1 ≤ u := le_max_left ..
  have hlu : l ≤ u := hl1.le.trans hu
  have hL : positiveLog c l < y := by
    have he : c*Real.log l = min y 0-2 := by
      dsimp [l]
      rw [Real.log_exp]
      field_simp
    unfold positiveLog
    rw [he]
    linarith [min_le_left y 0]
  have hU : y < positiveLog c u := by
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
    have hy : y+1 ≤ u := le_max_right ..
    unfold positiveLog
    nlinarith
  have hcont : ContinuousOn (positiveLog c) (Icc l u) := by
    intro x hx
    exact (positive_log_derivative c (hl.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨x,hx,he⟩ := intermediate_value_Ioo hlu hcont ⟨hL,hU⟩
  exact ⟨x,hl.trans hx.1,he⟩

def positiveLogInverse (c : ℝ) (hc : 0 < c) (y : ℝ) : ℝ :=
  Classical.choose (positive_log_surjective hc y)

theorem positive_log_inverse_positive {c : ℝ} (hc : 0 < c) (y : ℝ) :
    0 < positiveLogInverse c hc y := (Classical.choose_spec (positive_log_surjective hc y)).1

theorem positive_log_inverse_right {c : ℝ} (hc : 0 < c) (y : ℝ) :
    positiveLog c (positiveLogInverse c hc y) = y :=
  (Classical.choose_spec (positive_log_surjective hc y)).2

theorem positive_log_inverse_continuous {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ContinuousAt (positiveLogInverse c hc) y := by
  have hm := positive_log_strictMono hc
  apply tendsto_order.2
  constructor
  · intro b hb
    by_cases hb0 : 0 < b
    · have hby := hm hb0 (positive_log_inverse_positive hc y) hb
      rw [positive_log_inverse_right hc y] at hby
      filter_upwards [lt_mem_nhds hby] with z hz
      by_contra! hle
      have he := hm.monotoneOn (positive_log_inverse_positive hc z) hb0 hle
      rw [positive_log_inverse_right hc z] at he
      exact (not_le_of_gt hz) he
    · exact Eventually.of_forall fun z => lt_of_le_of_lt (by linarith) (positive_log_inverse_positive hc z)
  · intro b hb
    have hb0 : 0 < b := (positive_log_inverse_positive hc y).trans hb
    have hyb := hm (positive_log_inverse_positive hc y) hb0 hb
    rw [positive_log_inverse_right hc y] at hyb
    filter_upwards [gt_mem_nhds hyb] with z hz
    by_contra! hle
    have he := hm.monotoneOn hb0 (positive_log_inverse_positive hc z) hle
    rw [positive_log_inverse_right hc z] at he
    exact (not_le_of_gt hz) he

theorem positive_log_inverse_derivative {c : ℝ} (hc : 0 < c) (y : ℝ) :
    HasDerivAt (positiveLogInverse c hc) (1+c/positiveLogInverse c hc y)⁻¹ y := by
  have hp := positive_log_inverse_positive hc y
  exact HasDerivAt.of_local_left_inverse (positive_log_inverse_continuous hc y)
    (positive_log_derivative c hp) (ne_of_gt (by positivity))
    (Eventually.of_forall (positive_log_inverse_right hc))

theorem truncated_trajectory_exists {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) : ∃ a : ℝ → ℝ, TruncatedTrajectory f a := by
  let c := -twoLoopCoefficient f/oneLoopCoefficient f
  have hc : 0 < c := div_pos (neg_pos.mpr h1) h0
  let X : ℝ → ℝ := fun t => positiveLogInverse c hc (2*oneLoopCoefficient f*t)
  let a : ℝ → ℝ := fun t => (c+X t)⁻¹
  have hX (t : ℝ) : 0 < X t := positive_log_inverse_positive hc _
  have hsum (t : ℝ) : 0 < c+X t := add_pos hc (hX t)
  have hroot : c⁻¹ = bzRoot f := by
    dsimp [c,bzRoot]
    field_simp
  refine ⟨a,?_,?_⟩
  · intro t
    refine ⟨inv_pos.mpr (hsum t),?_⟩
    rw [← hroot]
    exact (inv_lt_inv₀ (hsum t) hc).mpr (by linarith [hX t])
  · intro t
    have hdX : HasDerivAt X ((1+c/X t)⁻¹*(2*oneLoopCoefficient f)) t :=
      (positive_log_inverse_derivative hc (2*oneLoopCoefficient f*t)).comp t
        (by simpa only [id_eq,mul_one] using! (hasDerivAt_id t).const_mul (2*oneLoopCoefficient f))
    have hda := (hdX.const_add c).inv (hsum t).ne'
    have he : twoLoopCoefficient f = -oneLoopCoefficient f*c := by
      dsimp [c]
      field_simp
    have hxt := hX t
    have hst := hsum t
    have hden : 1+c/X t ≠ 0 := ne_of_gt (by positivity)
    convert! hda using 1
    unfold twoLoopBeta
    dsimp only [a]
    rw [he]
    field_simp [hxt.ne',hst.ne',hden]
    ring

theorem bz_global_test : BZGlobalTest := by
  intro f h0 h1
  obtain ⟨a,ha⟩ := truncated_trajectory_exists h0 h1
  exact ⟨a,ha,truncated_trajectory_ir_limit h1 ha,truncated_trajectory_uv_limit h1 ha⟩

theorem bz_initial_value_test : BZInitialValueTest := by
  intro f h0 h1 a₀ ha₀ har
  obtain ⟨a,ha,hir,huv⟩ := bz_global_test f h0 h1
  obtain ⟨l,hl⟩ := (hir.eventually (lt_mem_nhds har)).exists
  obtain ⟨u,hu⟩ := (huv.eventually (gt_mem_nhds ha₀)).exists
  have hm := truncated_trajectory_antitone h1 ha
  have hlu : l ≤ u := by
    by_contra! hh
    have he := hm hh.le
    linarith
  have hcont : Continuous a := continuous_iff_continuousAt.mpr fun t => (ha.2 t).continuousAt
  obtain ⟨s,_,hs⟩ := intermediate_value_Ioo' hlu hcont.continuousOn ⟨hu,hl⟩
  let b : ℝ → ℝ := fun t => a (t+s)
  have hb : TruncatedTrajectory f b := by
    refine ⟨fun t => ha.1 (t+s),fun t => ?_⟩
    simpa only [Function.comp_apply,mul_one] using!
      (ha.2 (t+s)).comp t ((hasDerivAt_id t).add_const s)
  exact ⟨b,hb,by simpa only [b,zero_add] using hs,
    truncated_trajectory_ir_limit h1 hb,truncated_trajectory_uv_limit h1 hb⟩

end YMReview.QCD
#print axioms YMReview.QCD.positive_log_derivative
#print axioms YMReview.QCD.positive_log_strictMono
#print axioms YMReview.QCD.positive_log_surjective
#print axioms YMReview.QCD.positive_log_inverse_positive
#print axioms YMReview.QCD.positive_log_inverse_right
#print axioms YMReview.QCD.positive_log_inverse_continuous
#print axioms YMReview.QCD.positive_log_inverse_derivative
#print axioms YMReview.QCD.truncated_trajectory_exists
#print axioms YMReview.QCD.bz_global_test
#print axioms YMReview.QCD.bz_initial_value_test
