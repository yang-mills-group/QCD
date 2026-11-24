import BanksZaksSpec
import FlavorProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

theorem one_loop_positive_iff (f : ℕ) : 0 < oneLoopCoefficient f ↔ f ≤ 16 := by
  unfold oneLoopCoefficient
  constructor
  · intro h
    by_contra! hf
    have hn : (17:ℝ) ≤ f := by exact_mod_cast (show 17 ≤ f by omega)
    linarith
  · intro h
    have hn : (f:ℝ) ≤ 16 := by exact_mod_cast h
    linarith

theorem two_loop_negative_iff (f : ℕ) : twoLoopCoefficient f < 0 ↔ 9 ≤ f := by
  unfold twoLoopCoefficient
  constructor
  · intro h
    by_contra! hf
    have hn : (f:ℝ) ≤ 8 := by exact_mod_cast (show f ≤ 8 by omega)
    linarith
  · intro h
    have hn : (9:ℝ) ≤ f := by exact_mod_cast h
    linarith

theorem bz_root_equation {f : ℝ} (h : twoLoopCoefficient f ≠ 0) :
    oneLoopCoefficient f + twoLoopCoefficient f * bzRoot f = 0 := by
  unfold bzRoot
  field_simp
  ring

theorem bz_root_positive {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) : 0 < bzRoot f :=
  div_pos_of_neg_of_neg (neg_neg_of_pos h0) h1

theorem bz_root_is_zero {f : ℝ} (h : twoLoopCoefficient f ≠ 0) :
    twoLoopBeta f (bzRoot f) = 0 := by
  unfold twoLoopBeta
  rw [bz_root_equation h, mul_zero]

theorem two_loop_factorization {f : ℝ} (h : twoLoopCoefficient f ≠ 0) (a : ℝ) :
    twoLoopBeta f a = (-2 * a^2 * twoLoopCoefficient f) * (a - bzRoot f) := by
  have he := bz_root_equation h
  unfold twoLoopBeta
  nlinarith [he]

theorem positive_zero_unique {f a : ℝ} (ha : 0 < a)
    (h1 : twoLoopCoefficient f ≠ 0) (hz : twoLoopBeta f a = 0) : a = bzRoot f := by
  rw [two_loop_factorization h1] at hz
  have hn : -2 * a^2 * twoLoopCoefficient f ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)

theorem two_loop_integer_window (f : ℕ) :
    (∃ a : ℝ, 0 < a ∧ 0 < oneLoopCoefficient f ∧ twoLoopBeta f a = 0)
      ↔ 9 ≤ f ∧ f ≤ 16 := by
  constructor
  · rintro ⟨a,ha,h0,hz⟩
    have h1 : twoLoopCoefficient f < 0 := by
      have hn : -2 * a^2 ≠ 0 := by positivity
      have he : oneLoopCoefficient f + twoLoopCoefficient f * a = 0 :=
        (mul_eq_zero.mp hz).resolve_left hn
      nlinarith
    exact ⟨(two_loop_negative_iff f).mp h1,(one_loop_positive_iff f).mp h0⟩
  · rintro ⟨h9,h16⟩
    have h0 := (one_loop_positive_iff f).mpr h16
    have h1 := (two_loop_negative_iff f).mpr h9
    exact ⟨bzRoot f,bz_root_positive h0 h1,h0,bz_root_is_zero (ne_of_lt h1)⟩

theorem six_flavor_no_two_loop_zero (a : ℝ) (ha : 0 < a) : twoLoopBeta 6 a < 0 := by
  have hp : 0 < 7 + 26*a := by positivity
  change -2 * a^2 * (oneLoopCoefficient 6 + twoLoopCoefficient 6 * a) < 0
  rw [show oneLoopCoefficient 6 = 7 by norm_num [oneLoopCoefficient],
    show twoLoopCoefficient 6 = 26 by norm_num [twoLoopCoefficient]]
  exact mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos ha] : -2*a^2 < 0) hp

theorem sixteen_flavor_root : bzRoot 16 = 1/302 := by
  norm_num [bzRoot,oneLoopCoefficient,twoLoopCoefficient]

theorem bz_beta_derivative (f a : ℝ) :
    HasDerivAt (twoLoopBeta f)
      (-2 * (2*a*(oneLoopCoefficient f + twoLoopCoefficient f*a) + a^2*twoLoopCoefficient f)) a := by
  convert! ((((hasDerivAt_id a).pow 2).mul
    (((hasDerivAt_id a).const_mul (twoLoopCoefficient f)).const_add (oneLoopCoefficient f))).const_mul (-2)) using 1 <;>
    first | rfl | (ext x; dsimp only [twoLoopBeta,Pi.mul_apply,Pi.pow_apply,id_eq]; ring) |
      (dsimp only [Pi.mul_apply,Pi.pow_apply,id_eq]; ring)

theorem bz_derivative_at_root {f : ℝ} (h : twoLoopCoefficient f ≠ 0) :
    HasDerivAt (twoLoopBeta f) (bzDerivative f) (bzRoot f) := by
  have hd := bz_beta_derivative f (bzRoot f)
  convert! hd using 1
  rw [bz_root_equation h]
  unfold bzDerivative
  ring

theorem bz_derivative_positive {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) : 0 < bzDerivative f := by
  have hr := bz_root_positive h0 h1
  unfold bzDerivative
  exact mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos hr]) h1

theorem bz_flow_below {f a : ℝ} (h1 : twoLoopCoefficient f < 0)
    (ha : 0 < a) (hr : a < bzRoot f) : twoLoopBeta f a < 0 := by
  rw [two_loop_factorization (ne_of_lt h1)]
  apply mul_neg_of_pos_of_neg _ (sub_neg.mpr hr)
  exact mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos ha]) h1

theorem bz_flow_above {f a : ℝ} (h1 : twoLoopCoefficient f < 0)
    (ha : 0 < a) (hr : bzRoot f < a) : 0 < twoLoopBeta f a := by
  rw [two_loop_factorization (ne_of_lt h1)]
  apply mul_pos _ (sub_pos.mpr hr)
  exact mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos ha]) h1

theorem bz_weak_limit : Tendsto bzRoot (𝓝 (33/2)) (𝓝 0) := by
  have h0 : Tendsto oneLoopCoefficient (𝓝 (33/2)) (𝓝 0) := by
    change Tendsto (fun f:ℝ => 11 - 2*f/3) _ _
    convert! (tendsto_const_nhds.sub ((tendsto_const_nhds.mul tendsto_id).div_const 3) :
      Tendsto (fun f:ℝ => 11 - 2*f/3) (𝓝 (33/2)) (𝓝 (11 - 2*(33/2)/3))) using 1
    norm_num
  have h1 : Tendsto twoLoopCoefficient (𝓝 (33/2)) (𝓝 (-107)) := by
    change Tendsto (fun f:ℝ => 102 - 38*f/3) _ _
    convert! (tendsto_const_nhds.sub ((tendsto_const_nhds.mul tendsto_id).div_const 3) :
      Tendsto (fun f:ℝ => 102 - 38*f/3) (𝓝 (33/2)) (𝓝 (102 - 38*(33/2)/3))) using 1
    norm_num
  simpa only [neg_zero,zero_div] using! h0.neg.div h1 (by norm_num : (-107:ℝ) ≠ 0)

theorem bz_window_fails_trajectory_budget (f : ℕ) (h9 : 9 ≤ f) : ¬ trajectoryBudget f := by
  rw [trajectory_budget_integer_range]
  omega

theorem banks_zaks_test : BanksZaksTest := by
  refine ⟨two_loop_integer_window,six_flavor_no_two_loop_zero,sixteen_flavor_root,?_,
    bz_window_fails_trajectory_budget⟩
  intro f h9 h16
  have h0 := (one_loop_positive_iff f).mpr h16
  have h1 := (two_loop_negative_iff f).mpr h9
  exact ⟨bz_root_positive h0 h1,bz_root_is_zero (ne_of_lt h1),
    bz_derivative_at_root (ne_of_lt h1),bz_derivative_positive h0 h1⟩

end YMReview.QCD
#print axioms YMReview.QCD.one_loop_positive_iff
#print axioms YMReview.QCD.two_loop_negative_iff
#print axioms YMReview.QCD.bz_root_equation
#print axioms YMReview.QCD.bz_root_positive
#print axioms YMReview.QCD.bz_root_is_zero
#print axioms YMReview.QCD.two_loop_factorization
#print axioms YMReview.QCD.positive_zero_unique
#print axioms YMReview.QCD.two_loop_integer_window
#print axioms YMReview.QCD.six_flavor_no_two_loop_zero
#print axioms YMReview.QCD.sixteen_flavor_root
#print axioms YMReview.QCD.bz_beta_derivative
#print axioms YMReview.QCD.bz_derivative_at_root
#print axioms YMReview.QCD.bz_derivative_positive
#print axioms YMReview.QCD.bz_flow_below
#print axioms YMReview.QCD.bz_flow_above
#print axioms YMReview.QCD.bz_weak_limit
#print axioms YMReview.QCD.bz_window_fails_trajectory_budget
#print axioms YMReview.QCD.banks_zaks_test
