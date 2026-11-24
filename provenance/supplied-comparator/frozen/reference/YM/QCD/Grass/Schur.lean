import YM.QCD.Grass.Fubini

/-! # Integrating Grassmann variables at a step

Done by shears rather than exchanging sequences of derivatives or choosing a Wick
inverse for modes that are not being integrated. The test identity and marginal with arbitrary
insertions is useful when the fields are charged, or there is a zero remaining determinant.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Finset Function Module NormedSpace
open scoped BigOperators Topology Matrix

variable {A B : Type*} [Fintype A] [Fintype B]

lemma form_blocks (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    form (Matrix.fromBlocks M 0 0 N) = near A B (form M) + far A B (form N) := by
  simp [form,Fintype.sum_sum_type,near,far]

lemma gauss_blocks (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    gauss (Matrix.fromBlocks M 0 0 N) = near A B (gauss M) * far A B (gauss N) := by
  have hp : Plus (far A B (form N)) := (pass_grade ..).trans (congrArg (far A B) (form_plus N))
  unfold gauss; rw [map_weight,map_weight,form_blocks, algebra_exp_add (hp.central _)]

section decidable
variable [DecidableEq A] [DecidableEq B]

def shear (S : Matrix A B ℂ) (T : Matrix B A ℂ) : Dirac (A ⊕ B) →ₐ[ℂ] Dirac (A ⊕ B) :=
  adapter (Matrix.fromBlocks 1 S 0 1) (Matrix.fromBlocks 1 T.transpose 0 1)

lemma shear_far (S : Matrix A B ℂ) (T : Matrix B A ℂ) (x : Dirac B) :
    shear S T (far A B x) = far A B x := by
  refine AlgHom.congr_fun (φ₁:=(shear S T).comp (far A B)) (ext_atoms fun i => ?_) x
  cases i with
  | inl i =>
    change adapter _ _ (pass _ (psi i)) = pass _ (psi i)
    rw [pass_psi,adapt_psi]
    simp [Fintype.sum_sum_type,Matrix.one_apply,ite_smul]
  | inr i =>
    change adapter _ _ (pass _ (bar i)) = pass _ (bar i)
    rw [pass_bar,adapt_bar]
    simp [Fintype.sum_sum_type,Matrix.one_apply,ite_smul]

lemma shear_rows (S : Matrix A B ℂ) (T : Matrix B A ℂ) (x : Dirac (A ⊕ B)) :
    ber (A ⊕ B) (shear S T x) = ber _ x := by
  rw [shear, volume_map, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]; simp

lemma shear_integral (S : Matrix A B ℂ) (T : Matrix B A ℂ) (x : Dirac (A ⊕ B)) :
    marginal A B (shear S T x)=marginal A B x := by
  apply (perfect B).injective; apply LinearMap.ext; intro y
  rw [perfect_apply,perfect_apply, marginal_test,marginal_test,
    ← shear_far S T y, ← map_mul, shear_rows,shear_far]

variable (H : Matrix A A ℂ) (P : Matrix A B ℂ) (Q : Matrix B A ℂ) (R : Matrix B B ℂ)

lemma shear_gauss (h : IsUnit H.det) :
    shear (-(H⁻¹*P)) (-(Q*H⁻¹)) (gauss (Matrix.fromBlocks H P Q R)) =
      near A B (gauss H) * far A B (gauss (R-Q*H⁻¹*P)) := by
  rw [shear,gauss_map,← gauss_blocks]
  congr 1
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_transpose,Matrix.transpose_zero,
    Matrix.fromBlocks_multiply]
  simp [← Matrix.mul_assoc H, Matrix.mul_nonsing_inv _ h, Matrix.mul_assoc Q H⁻¹ H,Matrix.nonsing_inv_mul _ h, sub_eq_add_neg, Matrix.mul_assoc Q H⁻¹ P, add_comm]

/-- Exact partial integration; leaves arbitrary massless or charged sources. -/
lemma push (h : IsUnit H.det) (x : Dirac (A ⊕ B)) :
    marginal A B (gauss (Matrix.fromBlocks H P Q R) * x) =
      marginal A B (near A B (gauss H) * shear (-(H⁻¹*P)) (-(Q*H⁻¹)) x) * gauss (R-Q*H⁻¹*P) := by
  rw [← shear_integral (-(H⁻¹*P)) (-(Q*H⁻¹)),map_mul (shear _ _),shear_gauss _ _ _ _ h,
    ← pullout]
  have hp : Plus (far A B (gauss (R-Q*H⁻¹*P))) := (pass_grade ..).trans (congrArg _ (gauss_plus _))
  rw [mul_assoc,(hp.central (shear (-(H⁻¹*P)) (-(Q*H⁻¹)) x)).symm.eq, mul_assoc]

lemma marginal_schur (h : IsUnit H.det) :
    marginal A B (gauss (Matrix.fromBlocks H P Q R)) = H.det • gauss (R-Q*H⁻¹*P) := by
  rw [← shear_integral (-(H⁻¹*P)) (-(Q*H⁻¹)),shear_gauss _ _ _ _ h, margins,det_amplitude]

end decidable

end YM.QCD.Grass
