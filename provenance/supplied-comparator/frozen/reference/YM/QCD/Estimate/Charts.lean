import YM.QCD.Estimate.Accretive

/-! # convenient rectangular spectral arithmetic -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Cost
open Matrix ContinuousLinearMap Finset WithLp
open scoped Matrix.Norms.L2Operator Matrix Topology InnerProductSpace
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

abbrev lead : Matrix A B ℂ ≃ₗ[ℂ] (Vec B →L[ℂ] Vec A) := toEuclideanLin.trans LinearMap.toContinuousLinearMap
lemma lead_norm (M : Matrix A B ℂ) : ‖M‖=‖lead M‖ := rfl
lemma lead_op (M : Mx A) : lead M=op M := rfl
lemma leanBound (M : Matrix A B ℂ) (x : Vec B) : ‖lead M x‖ ≤ ‖M‖*‖x‖ := (lead M).le_opNorm _
lemma lead_mul (X : Matrix A B ℂ) (Y : Matrix B C ℂ) : lead (X*Y)=(lead X).comp (lead Y) := by
  ext1 v; change toLp 2 _ = toLp 2 _
  change toLp 2 ((X*Y)*ᵥ ofLp v) = toLp 2 (X *ᵥ (Y *ᵥ ofLp v)); rw [mulVec_mulVec]
lemma lead_act (X : Matrix A B ℂ) (Y : Matrix B C ℂ) (v) : lead (X*Y) v=lead X (lead Y v) := by rw [lead_mul]; rfl
lemma lead_star (X : Matrix A B ℂ) : lead Xᴴ = ContinuousLinearMap.adjoint (lead X) := by
  rw [lead, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply, Matrix.toLin_conjTranspose,LinearMap.adjoint_toContinuousLinearMap] -- check
  rfl
lemma cross_square (X : Matrix A B ℂ) (v) : form (Xᴴ*X) v=‖lead X v‖^2 := by
  rw [form,← lead_op, lead_act, lead_star, adjoint_inner_right]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
lemma north (X : Matrix A B ℂ) i j : ‖X i j‖ ≤ ‖X‖ := by
  let e : Vec B := toLp 2 (Pi.single j 1)
  have hh : ‖e‖=1 := by simp [e]
  have ht := leanBound X e
  rw [hh,mul_one] at ht
  refine le_trans ?_ ht
  rw [← sq_le_sq₀ (by positivity) (by positivity),EuclideanSpace.norm_sq_eq]
  have hu : (lead X e) i = X i j := by change (X*ᵥ (Pi.single j 1)) i=X i j; simp [mulVec,dotProduct,Pi.single_apply,mul_ite]
  rw [← hu]; exact single_le_sum (fun q _ => sq_nonneg ‖lead X e q‖) (mem_univ i)

end YM.QCD.Cost
