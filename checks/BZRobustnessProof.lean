import BZRobustnessSpec
import BZHigherOrderProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Set

theorem plateau_continuous (f h : ℝ) : Continuous (plateauRemainder f h) := by
  unfold plateauRemainder
  fun_prop

theorem plateau_bound {f h : ℝ} (h1 : twoLoopCoefficient f < 0) (hh : 0 ≤ h) (a : ℝ) :
    |plateauRemainder f h a| ≤ (-twoLoopCoefficient f)*h := by
  have hclamp : |max (-h) (min h (a-bzRoot f))| ≤ h := by
    apply abs_le.mpr
    exact ⟨le_max_left ..,max_le (by linarith) (min_le_left ..)⟩
  unfold plateauRemainder
  rw [abs_mul,abs_of_pos (neg_pos.mpr h1)]
  exact mul_le_mul_of_nonneg_left hclamp (neg_nonneg.mpr h1.le)

theorem plateau_zero {f h a : ℝ} (h1 : twoLoopCoefficient f ≠ 0)
    (ha : |a-bzRoot f| ≤ h) : correctedBracket f (plateauRemainder f h) a=0 := by
  obtain ⟨hl,hu⟩ := abs_le.mp ha
  unfold correctedBracket plateauRemainder
  rw [min_eq_right hu,max_eq_right hl]
  have he := bz_root_equation h1
  nlinarith

theorem bound_alone_not_unique : BoundAloneNotUnique := by
  intro f δ h0 h1 hd hd0
  let h := δ/(-twoLoopCoefficient f)
  have hh : 0 < h := div_pos hd (neg_pos.mpr h1)
  have hr := bz_root_positive h0 h1
  have he := bz_root_equation (ne_of_lt h1)
  have hprod : (-twoLoopCoefficient f)*h=δ := by dsimp [h]; field_simp [ne_of_lt h1]
  have hsmall : h < bzRoot f/2 := by
    apply (mul_lt_mul_iff_right₀ (neg_pos.mpr h1)).mp
    nlinarith
  refine ⟨plateauRemainder f h,plateau_continuous f h,?_,
    bzRoot f,bzRoot f+h/2,⟨by linarith,by linarith⟩,
    ⟨by linarith,by linarith⟩,by linarith,?_,?_⟩
  · intro a
    simpa only [hprod] using plateau_bound h1 hh.le a
  · exact plateau_zero (ne_of_lt h1) (by simpa using hh.le)
  · apply plateau_zero (ne_of_lt h1)
    rw [add_sub_cancel_left,abs_of_pos (half_pos hh)]
    linarith

theorem corrected_bracket_derivative {f a r : ℝ} {R : ℝ → ℝ}
    (hR : HasDerivAt R r a) :
    HasDerivAt (correctedBracket f R) (twoLoopCoefficient f+r) a := by
  simpa only [mul_one] using!
    (((hasDerivAt_id a).const_mul (twoLoopCoefficient f)).const_add (oneLoopCoefficient f)).add hR

theorem corrected_beta_derivative_at_zero {f a r : ℝ} {R : ℝ → ℝ}
    (hR : HasDerivAt R r a) (hz : correctedBracket f R a=0) :
    HasDerivAt (correctedBeta f R) (-2*a^2*(twoLoopCoefficient f+r)) a := by
  have h := (((hasDerivAt_id a).pow 2).const_mul (-2)).mul (corrected_bracket_derivative (f:=f) hR)
  convert! h using 1
  rw [hz]
  simp only [Pi.pow_apply,id_eq]
  ring

theorem bz_robustness_test : BZRobustnessTest := by
  intro f δ ρ R R' h0 h1 hd hd0 _ hρ hdR hb
  have hcont : ContinuousOn R (Icc (bzRoot f/2) (3*bzRoot f/2)) :=
    fun a ha => (hdR a ha).continuousAt.continuousWithinAt
  obtain ⟨a,ha,hz,hdist⟩ := bz_remainder_test f δ R h0 h1 hd hd0 hcont (fun x hx => (hb x hx).1)
  have hr := bz_root_positive h0 h1
  have hapos : 0 < a := (half_pos hr).trans ha.1
  have hac : a ∈ Icc (bzRoot f/2) (3*bzRoot f/2) := ⟨ha.1.le,ha.2.le⟩
  have hneg (b : ℝ) (hbc : b ∈ Icc (bzRoot f/2) (3*bzRoot f/2)) :
      twoLoopCoefficient f+R' b < 0 := by
    have h := (abs_le.mp (hb b hbc).2).2
    linarith
  have hm : StrictAntiOn (correctedBracket f R) (Icc (bzRoot f/2) (3*bzRoot f/2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..)
    · intro b hb
      exact (corrected_bracket_derivative (hdR b hb)).continuousAt.continuousWithinAt
    · intro b hb
      have hbc := interior_subset hb
      rw [(corrected_bracket_derivative (hdR b hbc)).deriv]
      exact hneg b hbc
  refine ⟨a,ha,by unfold correctedBeta; rw [hz,mul_zero],hdist,?_,
    corrected_beta_derivative_at_zero (hdR a hac) hz,?_⟩
  · intro b hb hzero
    have hbpos : 0 < b := (half_pos hr).trans_le hb.1
    have hzb : correctedBracket f R b=0 := by
      unfold correctedBeta at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (by positivity)
    exact hm.injOn hb hac (hzb.trans hz.symm)
  · exact mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos hapos]) (hneg a hac)

theorem sixteen_three_loop_remainder_bounds (a : ℝ)
    (ha : a ∈ Icc (bzRoot 16/2) (3*bzRoot 16/2)) :
    |threeLoopCoefficient 16*a^2| ≤ 1/25 ∧ |2*threeLoopCoefficient 16*a| ≤ 15 := by
  rw [sixteen_flavor_root] at ha
  norm_num [threeLoopCoefficient] at *
  obtain ⟨hl,hu⟩ := ha
  constructor
  · nlinarith [sq_nonneg a, mul_nonneg (by linarith : 0 ≤ a) (by linarith : 0 ≤ 1/201-a)]
  · rw [abs_of_pos (by linarith : 0 < a)]
    linarith

theorem three_loop_corrected_beta (f a : ℝ) :
    correctedBeta f (fun x => threeLoopCoefficient f*x^2) a = threeLoopBeta f a := by
  rfl

theorem three_loop_robustness_test : ThreeLoopRobustnessTest := by
  let R : ℝ → ℝ := fun a => threeLoopCoefficient 16*a^2
  let R' : ℝ → ℝ := fun a => 2*threeLoopCoefficient 16*a
  have hd (a : ℝ) : HasDerivAt R (R' a) a := by
    convert! ((hasDerivAt_id a).pow 2).const_mul (threeLoopCoefficient 16) using 1
    dsimp [R,R']
    ring
  obtain ⟨a,ha,hz,_,hu,hdz,hpos⟩ := bz_robustness_test 16 (1/25) 15 R R'
    (by norm_num [oneLoopCoefficient]) (by norm_num [twoLoopCoefficient])
    (by norm_num) (by norm_num [oneLoopCoefficient]) (by norm_num)
    (by norm_num [twoLoopCoefficient]) (fun a _ => hd a)
    (fun a ha => sixteen_three_loop_remainder_bounds a ha)
  obtain ⟨b,hb,hbz⟩ := three_loop_sixteen_bracket
  have hbc : b ∈ Icc (bzRoot 16/2) (3*bzRoot 16/2) := by
    rw [sixteen_flavor_root]
    constructor <;> linarith [hb.1,hb.2]
  have he : b=a := hu b hbc hbz
  subst b
  exact ⟨a,hb,hz,hu,hdz,hpos⟩

end YMReview.QCD
#print axioms YMReview.QCD.plateau_continuous
#print axioms YMReview.QCD.plateau_bound
#print axioms YMReview.QCD.plateau_zero
#print axioms YMReview.QCD.bound_alone_not_unique
#print axioms YMReview.QCD.corrected_bracket_derivative
#print axioms YMReview.QCD.corrected_beta_derivative_at_zero
#print axioms YMReview.QCD.bz_robustness_test
#print axioms YMReview.QCD.sixteen_three_loop_remainder_bounds
#print axioms YMReview.QCD.three_loop_corrected_beta
#print axioms YMReview.QCD.three_loop_robustness_test
