import DifferentialRunningSpec
import TwoLoopProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter Set
open scoped Topology

theorem bounded_error_over_diverging_scale {ι : Type*} {l : Filter ι} {E : ℝ}
    {r L : ι → ℝ} (hL : Tendsto L l atTop) (hr : ∀ᶠ i in l, |r i| ≤ E) :
    Tendsto (fun i => r i/L i) l (𝓝 0) := by
  refine squeeze_zero_norm' (a:=fun i => E/L i) ?_ (tendsto_const_nhds.div_atTop hL)
  filter_upwards [hr,hL.eventually_gt_atTop 0] with i hi hli
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hli]
  exact div_le_div_of_nonneg_right hi hli.le

theorem oscillation_bound (e t : ℝ) : |e*Real.sin t| ≤ |e| := by
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (abs_nonneg e)

theorem oscillation_preserves_leading (A k e : ℝ) :
    Tendsto (fun t => oscillatingRunning A k e t/t) atTop (𝓝 A) := by
  have he := bounded_error_over_diverging_scale tendsto_id
    (Eventually.of_forall (oscillation_bound e))
  have h := (arbitrary_loglog_same_leading_slope A k).add he
  simpa only [oscillatingRunning,add_div,add_zero] using! h

theorem oscillation_preserves_loglog (A k e : ℝ) :
    Tendsto (secondOrderRead A (oscillatingRunning A k e)) atTop (𝓝 k) := by
  have he := bounded_error_over_diverging_scale Real.tendsto_log_atTop
    (Eventually.of_forall (oscillation_bound e))
  have h := (loglog_read_recovers_coefficient A k).add he
  simp only [add_zero] at h
  convert! h using 1
  ext t
  unfold secondOrderRead oscillatingRunning
  ring

theorem oscillating_running_derivative (A k e : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (oscillatingRunning A k e) (A+k/t+e*Real.cos t) t :=
  (log_corrected_derivative A k ht).add ((Real.hasDerivAt_sin t).const_mul e)

theorem oscillating_running_derivative_positive {A k e t : ℝ}
    (hk : 0 ≤ k) (he : 0 ≤ e) (heA : e < A) (ht : 0 < t) :
    0 < deriv (oscillatingRunning A k e) t := by
  rw [(oscillating_running_derivative A k e ht.ne').deriv]
  have hm := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) he
  have hd := div_nonneg hk ht.le
  nlinarith

theorem oscillating_derivative_has_no_limit {A k e : ℝ} (he : e ≠ 0) :
    ¬ ∃ l : ℝ, Tendsto (deriv (oscillatingRunning A k e)) atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  let p : ℕ → ℝ := fun n => ((n+1:ℕ):ℝ)*(2*Real.pi)
  let q : ℕ → ℝ := fun n => p n+Real.pi
  have hp : Tendsto p atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const (by positivity)
  have hq : Tendsto q atTop atTop := tendsto_atTop_add_const_right _ Real.pi hp
  have hp0 (n : ℕ) : p n ≠ 0 := by dsimp [p]; positivity
  have hq0 (n : ℕ) : q n ≠ 0 := by dsimp [q,p]; positivity
  have hpc (n : ℕ) : Real.cos (p n) = 1 := Real.cos_nat_mul_two_pi (n+1)
  have hqc (n : ℕ) : Real.cos (q n) = -1 := Real.cos_nat_mul_two_pi_add_pi (n+1)
  have hplim : Tendsto (fun n => deriv (oscillatingRunning A k e) (p n)) atTop (𝓝 (A+e)) := by
    have h := ((tendsto_const_nhds (x:=A)).add ((tendsto_const_nhds (x:=k)).div_atTop hp)).add_const e
    simp only [add_zero] at h
    convert! h using 1
    ext n
    rw [(oscillating_running_derivative A k e (hp0 n)).deriv,hpc,mul_one]
  have hqlim : Tendsto (fun n => deriv (oscillatingRunning A k e) (q n)) atTop (𝓝 (A-e)) := by
    have h := ((tendsto_const_nhds (x:=A)).add ((tendsto_const_nhds (x:=k)).div_atTop hq)).sub_const e
    simp only [add_zero] at h
    convert! h using 1
    ext n
    rw [(oscillating_running_derivative A k e (hq0 n)).deriv,hqc,mul_neg_one]
    ring
  have h1 : A+e = l := tendsto_nhds_unique hplim (hl.comp hp)
  have h2 : A-e = l := tendsto_nhds_unique hqlim (hl.comp hq)
  apply he
  linarith

theorem differential_running_test : DifferentialRunningTest := by
  intro A k e _ hk he heA
  refine ⟨oscillation_preserves_leading A k e,oscillation_preserves_loglog A k e,?_,
    oscillating_derivative_has_no_limit he.ne'⟩
  intro t ht
  exact ⟨oscillating_running_derivative A k e ht.ne',
    oscillating_running_derivative_positive hk he.le heA ht⟩

end YMReview.QCD
#print axioms YMReview.QCD.bounded_error_over_diverging_scale
#print axioms YMReview.QCD.oscillation_bound
#print axioms YMReview.QCD.oscillation_preserves_leading
#print axioms YMReview.QCD.oscillation_preserves_loglog
#print axioms YMReview.QCD.oscillating_running_derivative
#print axioms YMReview.QCD.oscillating_running_derivative_positive
#print axioms YMReview.QCD.oscillating_derivative_has_no_limit
#print axioms YMReview.QCD.differential_running_test
