import BZTrajectorySpec
import BanksZaksProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter Set
open scoped Topology

theorem bounded_function_cannot_have_positive_tail_speed {v d : ℝ → ℝ} {c M : ℝ}
    (hc : 0 < c) (hv : ∀ t, HasDerivAt v (d t) t)
    (hs : ∀ t, 0 ≤ t → c ≤ d t) (hb : ∀ t, 0 ≤ t → v t ≤ M) : False := by
  have h0 := hb 0 le_rfl
  let T := (M-v 0+1)/c
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hd : Differentiable ℝ v := fun t => (hv t).differentiableAt
  have h := (convex_Ici (0:ℝ)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn
    (fun t ht => by rw [(hv t).deriv]; exact hs t (le_of_lt (by simpa using ht)))
    0 (by simp) T hT hT
  have he : c*T = M-v 0+1 := by dsimp [T]; field_simp
  have hB := hb T hT
  simp only [sub_zero] at h
  linarith

theorem beta_speed_lower {f l u a : ℝ} (h1 : twoLoopCoefficient f < 0)
    (hl : 0 ≤ l) (hla : l ≤ a) (hau : a ≤ u) (hu : u ≤ bzRoot f) :
    (-2*twoLoopCoefficient f)*l^2*(bzRoot f-u) ≤ -twoLoopBeta f a := by
  have hk : 0 ≤ -2*twoLoopCoefficient f := by linarith
  have hs : l^2 ≤ a^2 := by nlinarith
  have hg : bzRoot f-u ≤ bzRoot f-a := by linarith
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left hs hk) hg (sub_nonneg.mpr hu)
    (mul_nonneg hk (sq_nonneg a))
  rw [two_loop_factorization (ne_of_lt h1)]
  nlinarith [h]

theorem truncated_trajectory_antitone {f : ℝ} (h1 : twoLoopCoefficient f < 0)
    {a : ℝ → ℝ} (h : TruncatedTrajectory f a) : Antitone a := by
  apply (strictAnti_of_deriv_neg (fun t => ?_)).antitone
  rw [(h.2 t).deriv]
  exact bz_flow_below h1 (h.1 t).1 (h.1 t).2

theorem truncated_trajectory_ir_limit {f : ℝ} (h1 : twoLoopCoefficient f < 0)
    {a : ℝ → ℝ} (h : TruncatedTrajectory f a) : Tendsto a atBot (𝓝 (bzRoot f)) := by
  have hm := truncated_trajectory_antitone h1 h
  have hb : BddAbove (range a) := ⟨bzRoot f,by rintro _ ⟨t,rfl⟩; exact (h.1 t).2.le⟩
  let L : ℝ := ⨆ t, a t
  have haL (t : ℝ) : a t ≤ L := le_ciSup hb t
  have hL : L ≤ bzRoot f := ciSup_le fun t => (h.1 t).2.le
  have he : L = bzRoot f := by
    by_contra hne
    have hgap : L < bzRoot f := lt_of_le_of_ne hL hne
    let c := (-2*twoLoopCoefficient f)*(a 0)^2*(bzRoot f-L)
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos (mul_pos (by linarith) (sq_pos_of_pos (h.1 0).1)) (sub_pos.mpr hgap)
    apply bounded_function_cannot_have_positive_tail_speed (v:=fun t => a (-t))
      (d:=fun t => -twoLoopBeta f (a (-t))) (M:=L) hc
    · intro t
      simpa only [Function.comp_apply,mul_neg_one] using! (h.2 (-t)).comp t (hasDerivAt_id t).neg
    · intro t ht
      exact beta_speed_lower h1 (h.1 0).1.le (hm (by linarith)) (haL (-t)) hL
    · intro t _
      exact haL (-t)
  simpa only [← he] using (tendsto_atBot_ciSup hm hb)

theorem truncated_trajectory_uv_limit {f : ℝ} (h1 : twoLoopCoefficient f < 0)
    {a : ℝ → ℝ} (h : TruncatedTrajectory f a) : Tendsto a atTop (𝓝 0) := by
  have hm := truncated_trajectory_antitone h1 h
  have hb : BddBelow (range a) := ⟨0,by rintro _ ⟨t,rfl⟩; exact (h.1 t).1.le⟩
  let L : ℝ := ⨅ t, a t
  have hLa (t : ℝ) : L ≤ a t := ciInf_le hb t
  have hL : 0 ≤ L := le_ciInf fun t => (h.1 t).1.le
  have he : L = 0 := by
    by_contra hne
    have hpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
    let c := (-2*twoLoopCoefficient f)*L^2*(bzRoot f-a 0)
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos (mul_pos (by linarith) (sq_pos_of_pos hpos)) (sub_pos.mpr (h.1 0).2)
    apply bounded_function_cannot_have_positive_tail_speed (v:=fun t => -a t)
      (d:=fun t => -twoLoopBeta f (a t)) (M:=0) hc
    · intro t
      exact (h.2 t).neg
    · intro t ht
      exact beta_speed_lower h1 hL (hLa t) (hm ht) (h.1 0).2.le
    · intro t _
      exact neg_nonpos.mpr (h.1 t).1.le
  simpa only [← he] using (tendsto_atTop_ciInf hm hb)

theorem bz_trajectory_test : BZTrajectoryTest := by
  intro f _ h1 a h
  exact ⟨truncated_trajectory_ir_limit h1 h,truncated_trajectory_uv_limit h1 h⟩

end YMReview.QCD
#print axioms YMReview.QCD.bounded_function_cannot_have_positive_tail_speed
#print axioms YMReview.QCD.beta_speed_lower
#print axioms YMReview.QCD.truncated_trajectory_antitone
#print axioms YMReview.QCD.truncated_trajectory_ir_limit
#print axioms YMReview.QCD.truncated_trajectory_uv_limit
#print axioms YMReview.QCD.bz_trajectory_test
