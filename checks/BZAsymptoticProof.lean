import BZAsymptoticSpec
import BZInvariantProof
import TwoLoopProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

theorem implicit_log_flow_leading {X : ℝ → ℝ} {A c D : ℝ} (hA : 0 < A)
    (hX : Tendsto X atTop atTop)
    (he : ∀ t, X t+c*Real.log (X t)=A*t+D) :
    Tendsto (fun t => X t/t) atTop (𝓝 A) := by
  have hl := log_over_scale_vanishes.comp hX
  have hd : Tendsto (fun t => D/X t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hX
  have hh : Tendsto (fun t => (1+c*(Real.log (X t)/X t)-D/X t)/A)
      atTop (𝓝 (1/A)) := by
    convert! (((tendsto_const_nhds (x:=1)).add (hl.const_mul c)).sub hd).div_const A using 1
    simp
  have hi : Tendsto (fun t => t/X t) atTop (𝓝 (1/A)) := by
    apply hh.congr'
    filter_upwards [hX.eventually_gt_atTop 0] with t ht
    have ht' : X t ≠ 0 := ne_of_gt ht
    have he' := he t
    field_simp [ht',hA.ne']
    nlinarith
  simpa using hi.inv₀ (one_div_ne_zero hA.ne')

theorem implicit_log_flow_subleading {X : ℝ → ℝ} {A c D : ℝ} (hA : 0 < A)
    (hX : Tendsto X atTop atTop)
    (he : ∀ t, X t+c*Real.log (X t)=A*t+D) :
    Tendsto (fun t => (X t-A*t)/Real.log t) atTop (𝓝 (-c)) := by
  have hr := implicit_log_flow_leading hA hX he
  have hlogratio := (Real.continuousAt_log hA.ne').tendsto.comp hr
  have hz := hlogratio.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun t => Real.log (X t)/Real.log t) atTop (𝓝 1) := by
    have hh : Tendsto (fun t => 1+Real.log (X t/t)/Real.log t) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x:=1)).add hz
    apply hh.congr'
    filter_upwards [hX.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with t hx ht
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt (lt_trans zero_lt_one ht))]
    have hlt := ne_of_gt (Real.log_pos ht)
    field_simp
    ring_nf
  have hd : Tendsto (fun t:ℝ => D/Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh : Tendsto (fun t => D/Real.log t-c*(Real.log (X t)/Real.log t))
      atTop (𝓝 (-c)) := by simpa using hd.sub (hl.const_mul c)
  apply hh.congr'
  filter_upwards [] with t
  have he' := he t
  have hx : X t-A*t=D-c*Real.log (X t) := by linarith
  rw [hx]
  ring_nf

theorem bz_inverse_uv_expansion {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) {a : ℝ → ℝ} (ha : TruncatedTrajectory f a) :
    Tendsto (fun t => (a t)⁻¹/t) atTop (𝓝 (2*oneLoopCoefficient f)) ∧
    Tendsto (fun t => ((a t)⁻¹-2*oneLoopCoefficient f*t)/Real.log t)
      atTop (𝓝 (-bzOffset f)) := by
  have hai : Tendsto (fun t => (a t)⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr
      ⟨truncated_trajectory_uv_limit h1 ha,Eventually.of_forall (fun t => (ha.1 t).1)⟩
  let X : ℝ → ℝ := fun t => (a t)⁻¹-bzOffset f
  have hX : Tendsto X atTop atTop := by
    simpa only [X,sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-bzOffset f) hai
  have he (t : ℝ) : X t+bzOffset f*Real.log (X t) =
      (2*oneLoopCoefficient f)*t+bzClock f (a 0) := by
    have h := bz_finite_scale_test f h0 h1 a ha 0 t
    change positiveLog (bzOffset f) (X t)-bzClock f (a 0) = _ at h
    simp only [positiveLog,sub_zero] at h
    linarith
  have hA : 0 < 2*oneLoopCoefficient f := mul_pos (by norm_num) h0
  have hlead := implicit_log_flow_leading hA hX he
  have hsub := implicit_log_flow_subleading hA hX he
  have hc : Tendsto (fun t:ℝ => bzOffset f/t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hclog : Tendsto (fun t:ℝ => bzOffset f/Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  constructor
  · convert! hlead.add hc using 1
    · ext t; dsimp [X]; ring_nf
    · simp
  · convert! hsub.add hclog using 1
    · ext t; dsimp [X]; ring_nf
    · simp

theorem bz_uv_running_test : BZUVRunningTest := by
  intro f h0 h1 a ha
  have hp := Real.pi_ne_zero
  obtain ⟨hl,hs⟩ := bz_inverse_uv_expansion h0 h1 ha
  constructor
  · convert! hl.const_mul (6/(16*Real.pi^2)) using 1
    · ext t; unfold referenceWilsonRunning; ring_nf
    · unfold gBeta0; ring_nf
  · convert! hs.const_mul (6/(16*Real.pi^2)) using 1
    · ext t; unfold secondOrderRead referenceWilsonRunning gBeta0; ring_nf
    · unfold wilsonLogLog gBeta0 gBeta1 bzOffset
      field_simp [h0.ne']

end YMReview.QCD
#print axioms YMReview.QCD.implicit_log_flow_leading
#print axioms YMReview.QCD.implicit_log_flow_subleading
#print axioms YMReview.QCD.bz_inverse_uv_expansion
#print axioms YMReview.QCD.bz_uv_running_test
