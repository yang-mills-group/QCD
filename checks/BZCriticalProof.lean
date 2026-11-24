import BZCriticalSpec
import BZInvariantProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

theorem bz_gap_log_derivative {f : ℝ} (h1 : twoLoopCoefficient f < 0)
    {a : ℝ → ℝ} (ha : TruncatedTrajectory f a) (t : ℝ) :
    HasDerivAt (fun s => Real.log (bzRoot f-a s))
      (-2*twoLoopCoefficient f*(a t)^2) t := by
  have hg := sub_pos.mpr (ha.1 t).2
  have hd := ((ha.2 t).const_sub (bzRoot f)).log hg.ne'
  convert! hd using 1
  rw [two_loop_factorization (ne_of_lt h1)]
  field_simp
  ring

theorem bz_gap_log_speed_limit {f : ℝ} (h1 : twoLoopCoefficient f < 0)
    {a : ℝ → ℝ} (ha : TruncatedTrajectory f a) :
    Tendsto (deriv (fun t => Real.log (bzRoot f-a t))) atBot (𝓝 (bzDerivative f)) := by
  have hh := ((truncated_trajectory_ir_limit h1 ha).pow 2).const_mul (-2*twoLoopCoefficient f)
  have hv : -2*twoLoopCoefficient f*(bzRoot f)^2=bzDerivative f := by unfold bzDerivative; ring
  rw [hv] at hh
  apply hh.congr'
  exact Eventually.of_forall fun t => (bz_gap_log_derivative h1 ha t).deriv.symm

theorem bz_gap_exponential_rate {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) {a : ℝ → ℝ} (ha : TruncatedTrajectory f a) :
    Tendsto (fun t => Real.log (bzRoot f-a t)/t) atBot (𝓝 (bzDerivative f)) := by
  have hr := bz_root_positive h0 h1
  have hc := bz_offset_positive h0 h1
  have hai := (truncated_trajectory_ir_limit h1 ha).inv₀ hr.ne'
  have hroot : (bzRoot f)⁻¹=bzOffset f := by
    rw [← bz_offset_inverse h0.ne' (ne_of_lt h1),inv_inv]
  let X : ℝ → ℝ := fun t => (a t)⁻¹-bzOffset f
  have hX : Tendsto X atBot (𝓝 0) := by
    simpa only [hroot,sub_self] using hai.sub_const (bzOffset f)
  let D := bzClock f (a 0)
  have he (t : ℝ) : X t+bzOffset f*Real.log (X t)=2*oneLoopCoefficient f*t+D := by
    have h := bz_finite_scale_test f h0 h1 a ha 0 t
    change positiveLog (bzOffset f) (X t)-D = _ at h
    simp only [positiveLog,sub_zero] at h
    linarith
  have herr : Tendsto (fun t => (D-X t)/t) atBot (𝓝 0) :=
    ((tendsto_const_nhds (x:=D)).sub hX).div_atBot tendsto_id
  have hlogX : Tendsto (fun t => Real.log (X t)/t) atBot
      (𝓝 (2*oneLoopCoefficient f/bzOffset f)) := by
    have hh := ((tendsto_const_nhds (x:=2*oneLoopCoefficient f)).add herr).div_const (bzOffset f)
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
    have ht' := ne_of_lt ht
    have he' := he t
    field_simp [ht',hc.ne']
    nlinarith
  have hlogra := (Real.continuousAt_log (mul_pos hr hr).ne').tendsto.comp
    ((truncated_trajectory_ir_limit h1 ha).const_mul (bzRoot f))
  have hz := hlogra.div_atBot tendsto_id
  have heq : 2*oneLoopCoefficient f/bzOffset f=bzDerivative f := by
    unfold bzDerivative bzRoot bzOffset
    field_simp
  have hh := hlogX.add hz
  simp only [add_zero,heq] at hh
  apply hh.congr'
  filter_upwards [] with t
  have hx := bz_clock_coordinate_positive h0 h1 (ha.1 t).1 (ha.1 t).2
  have hgap : bzRoot f-a t=X t*(bzRoot f*a t) := by
    dsimp [X]
    rw [← bz_offset_inverse h0.ne' (ne_of_lt h1)]
    field_simp [(ha.1 t).1.ne',hc.ne']
  rw [hgap,Real.log_mul hx.ne' (mul_pos hr (ha.1 t).1).ne',add_div]
  rfl

theorem bz_critical_test : BZCriticalTest := by
  intro f h0 h1 a ha
  exact ⟨bz_gap_exponential_rate h0 h1 ha,bz_gap_log_speed_limit h1 ha⟩

end YMReview.QCD
#print axioms YMReview.QCD.bz_gap_log_derivative
#print axioms YMReview.QCD.bz_gap_log_speed_limit
#print axioms YMReview.QCD.bz_gap_exponential_rate
#print axioms YMReview.QCD.bz_critical_test
