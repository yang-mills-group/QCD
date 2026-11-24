import FlavorDeterminantSpec
import ScreeningProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM
open scoped BigOperators

theorem repeated_logdet {I : Type*} [Fintype I] [DecidableEq I]
    (F : ℕ) (M : Matrix I I ℂ) :
    Real.log ‖(Matrix.blockDiagonal (fun _ : Fin F => M)).det‖ =
      (F:ℝ)*Real.log ‖M.det‖ := by
  rw [Matrix.det_blockDiagonal]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_pow,Real.log_pow]

theorem repeated_rectify_factor {n : Lattice.Side} (F : ℕ) (C : QCD.su.Color)
    (M : QCD.Run.St n) (x : QCD.Rudder.Weath n) :
    repeatedRectify F C M x = (F:ℝ)*QCD.Pearl.rectifyR C M x := by
  unfold repeatedRectify QCD.Pearl.rectifyR
  simp_rw [repeated_logdet,deriv_const_mul_field']
  ring

theorem repeated_response_factor (F : ℕ) (C : QCD.su.Color) (n : Lattice.Side) :
    repeatedResponse F C n = (F:ℝ)*fermionResponse C n := by
  unfold repeatedResponse fermionResponse QCD.Pearl.priceR
  dsimp only
  rw [repeated_rectify_factor,repeated_rectify_factor]
  ring

theorem flavor_determinant_test : FlavorDeterminantTest := by
  intro F C hC
  simp_rw [repeated_response_factor]
  exact many_flavor_screening F C hC

theorem response_flavor_increment (F : ℕ) (C : QCD.su.Color) (n : Lattice.Side) :
    repeatedResponse (F+1) C n - repeatedResponse F C n = fermionResponse C n := by
  rw [repeated_response_factor,repeated_response_factor]
  push_cast
  ring

theorem zero_flavor_response (C : QCD.su.Color) (n : Lattice.Side) :
    repeatedResponse 0 C n = 0 := by
  rw [repeated_response_factor]
  norm_num

end YMReview.QCD
#print axioms YMReview.QCD.repeated_logdet
#print axioms YMReview.QCD.repeated_rectify_factor
#print axioms YMReview.QCD.repeated_response_factor
#print axioms YMReview.QCD.flavor_determinant_test
#print axioms YMReview.QCD.response_flavor_increment
#print axioms YMReview.QCD.zero_flavor_response
