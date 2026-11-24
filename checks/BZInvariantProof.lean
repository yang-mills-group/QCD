import BZInvariantSpec
import BZExistenceProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Set

theorem bz_offset_positive {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) : 0 < bzOffset f := div_pos (neg_pos.mpr h1) h0

theorem bz_offset_inverse {f : ℝ} (h0 : oneLoopCoefficient f ≠ 0)
    (h1 : twoLoopCoefficient f ≠ 0) : (bzOffset f)⁻¹ = bzRoot f := by
  unfold bzOffset bzRoot
  field_simp

theorem bz_offset_coefficient {f : ℝ} (h0 : oneLoopCoefficient f ≠ 0) :
    twoLoopCoefficient f = -oneLoopCoefficient f*bzOffset f := by
  unfold bzOffset
  field_simp

theorem bz_clock_coordinate_positive {f a : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) (ha : 0 < a) (har : a < bzRoot f) :
    0 < a⁻¹-bzOffset f := by
  have h := (inv_lt_inv₀ (bz_root_positive h0 h1) ha).mpr har
  rw [← bz_offset_inverse h0.ne' (ne_of_lt h1),inv_inv] at h
  exact sub_pos.mpr h

theorem bz_clock_derivative {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) {a : ℝ → ℝ} (ha : TruncatedTrajectory f a) (t : ℝ) :
    HasDerivAt (fun s => bzClock f (a s)) (2*oneLoopCoefficient f) t := by
  have hap := (ha.1 t).1
  have hy := bz_clock_coordinate_positive h0 h1 hap (ha.1 t).2
  have hd := (positive_log_derivative (bzOffset f) hy).comp t
    (((ha.2 t).inv hap.ne').sub_const (bzOffset f))
  have hca : 1-bzOffset f*a t ≠ 0 := by
    have hm := mul_pos hy hap
    rw [sub_mul,inv_mul_cancel₀ hap.ne'] at hm
    exact hm.ne'
  convert! hd using 1
  unfold twoLoopBeta
  rw [bz_offset_coefficient h0.ne']
  field_simp [hap.ne',hy.ne',hca]
  ring

theorem bz_clock_injective {f : ℝ} (h0 : 0 < oneLoopCoefficient f)
    (h1 : twoLoopCoefficient f < 0) : Set.InjOn (bzClock f) (Ioo 0 (bzRoot f)) := by
  intro a ha b hb he
  have h := (positive_log_strictMono (bz_offset_positive h0 h1)).injOn
    (bz_clock_coordinate_positive h0 h1 ha.1 ha.2)
    (bz_clock_coordinate_positive h0 h1 hb.1 hb.2) he
  apply inv_injective
  linarith

theorem bz_finite_scale_test : BZFiniteScaleTest := by
  intro f h0 h1 a ha s t
  let z : ℝ → ℝ := fun t => bzClock f (a t)-2*oneLoopCoefficient f*t
  have hz (t : ℝ) : HasDerivAt z 0 t := by
    simpa only [mul_one,sub_self] using!
      (bz_clock_derivative h0 h1 ha t).sub ((hasDerivAt_id t).const_mul (2*oneLoopCoefficient f))
  have he := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) t s
  dsimp [z] at he
  linarith

theorem bz_uniqueness_test : BZUniquenessTest := by
  intro f h0 h1 a b ha hb hab
  ext t
  apply bz_clock_injective h0 h1 (ha.1 t) (hb.1 t)
  have hea := bz_finite_scale_test f h0 h1 a ha 0 t
  have heb := bz_finite_scale_test f h0 h1 b hb 0 t
  rw [hab] at hea
  linarith

end YMReview.QCD
#print axioms YMReview.QCD.bz_offset_positive
#print axioms YMReview.QCD.bz_offset_inverse
#print axioms YMReview.QCD.bz_offset_coefficient
#print axioms YMReview.QCD.bz_clock_coordinate_positive
#print axioms YMReview.QCD.bz_clock_derivative
#print axioms YMReview.QCD.bz_clock_injective
#print axioms YMReview.QCD.bz_finite_scale_test
#print axioms YMReview.QCD.bz_uniqueness_test
