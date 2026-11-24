import TwoLoopSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

theorem log_over_scale_vanishes : Tendsto (fun t:ℝ => Real.log t/t) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

theorem arbitrary_loglog_same_leading_slope (A k : ℝ) :
    Tendsto (fun t => logCorrected A k t/t) atTop (𝓝 A) := by
  have h := (tendsto_const_nhds (x := A)).add (log_over_scale_vanishes.const_mul k)
  have h' : Tendsto (fun t:ℝ => A+k*(Real.log t/t)) atTop (𝓝 A) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  unfold logCorrected
  field_simp

theorem loglog_read_recovers_coefficient (A k : ℝ) :
    Tendsto (secondOrderRead A (logCorrected A k)) atTop (𝓝 k) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  simp [secondOrderRead,logCorrected,hl]

theorem leading_slope_does_not_fix_two_loop : LeadingSlopeDoesNotFixTwoLoop :=
  fun A k => ⟨arbitrary_loglog_same_leading_slope A k,loglog_read_recovers_coefficient A k⟩

theorem distinct_loglog_limits {A k j : ℝ} (hkj : k ≠ j) :
    ¬ Tendsto (secondOrderRead A (logCorrected A k)) atTop (𝓝 j) := by
  intro hj
  exact hkj (tendsto_nhds_unique (loglog_read_recovers_coefficient A k) hj)

theorem log_corrected_eventually_positive {A : ℝ} (hA : 0 < A) (k : ℝ) :
    ∀ᶠ t:ℝ in atTop, 0 < logCorrected A k t := by
  have h := (arbitrary_loglog_same_leading_slope A k).eventually (lt_mem_nhds hA)
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with t ht ht0
  exact (div_pos_iff_of_pos_right ht0).mp ht

theorem second_order_read_stable : SecondOrderReadStable := by
  intro L w v A k E hL hwv hv
  have hlog := Real.tendsto_log_atTop.comp hL
  have herr : Tendsto (fun i => (w i-v i)/Real.log (L i)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => E/Real.log (L i)) ?_
      (tendsto_const_nhds.div_atTop hlog)
    filter_upwards [hwv,hlog.eventually_gt_atTop 0] with i hi hli
    change 0 < Real.log (L i) at hli
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hli]
    exact div_le_div_of_nonneg_right hi hli.le
  convert! herr.add hv using 1
  · ext i
    ring
  · simp

theorem log_corrected_derivative (A k : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logCorrected A k) (A+k/t) t := by
  convert! ((hasDerivAt_id t).const_mul A).add ((Real.hasDerivAt_log ht).const_mul k) using 1
  simp only [div_eq_mul_inv]
  ring

/-- The next-order flow detector sees k, although the leading slope test does not. -/
theorem next_order_flow_detector (A k : ℝ) :
    Tendsto (fun t => logCorrected A k t * ((A+k/t)-A)) atTop (𝓝 (A*k)) := by
  convert! (arbitrary_loglog_same_leading_slope A k).mul_const k using 1
  ext t
  ring

theorem six_flavor_loglog_benchmark : wilsonLogLog 6 = 39/(28*Real.pi^2) := by
  unfold wilsonLogLog gBeta0 gBeta1 oneLoopCoefficient twoLoopCoefficient
  have hp := Real.pi_ne_zero
  field_simp
  ring

theorem two_loop_flow_selects_loglog {f k : ℝ} (h0 : gBeta0 f ≠ 0) :
    (12*gBeta0 f)*k = 72*gBeta1 f ↔ k = wilsonLogLog f := by
  unfold wilsonLogLog
  constructor <;> intro h
  · field_simp
    nlinarith
  · rw [h]
    field_simp
    ring

theorem two_loop_stiffness_bridge : TwoLoopStiffnessBridge := by
  intro C β ε h htwo a b hab T hT
  have hL : Tendsto (uvLogScale C) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h.physical)
  exact second_order_read_stable (uvLogScale C)
    (fun i => YM.Massive.Stiffness.read ((C.A i).density (C.N i)) a b T)
    (fun i => (C.A i).β (C.N i)) YM.Massive.betaSlope (wilsonLogLog 6) ε hL
    (Eventually.of_forall fun i => (h.compare (i:=i) (m:=C.N i) le_rfl).band a b hab T hT)
    htwo

end YMReview.QCD
#print axioms YMReview.QCD.log_over_scale_vanishes
#print axioms YMReview.QCD.arbitrary_loglog_same_leading_slope
#print axioms YMReview.QCD.loglog_read_recovers_coefficient
#print axioms YMReview.QCD.leading_slope_does_not_fix_two_loop
#print axioms YMReview.QCD.distinct_loglog_limits
#print axioms YMReview.QCD.log_corrected_eventually_positive
#print axioms YMReview.QCD.second_order_read_stable
#print axioms YMReview.QCD.log_corrected_derivative
#print axioms YMReview.QCD.next_order_flow_detector
#print axioms YMReview.QCD.six_flavor_loglog_benchmark
#print axioms YMReview.QCD.two_loop_flow_selects_loglog
#print axioms YMReview.QCD.two_loop_stiffness_bridge
