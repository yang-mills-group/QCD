import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Real-part coercivity tables

All operator norms in this file are Euclidean, not the `YM.Gauge` Frobenius convention.
Includes the real determinant sign test without assuming invertibility at the semidefinite face.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cost
open Finset Function Filter Module Complex ContinuousLinearMap
open scoped Matrix.Norms.L2Operator InnerProductSpace Topology

variable {A : Type*} [Fintype A] [DecidableEq A]
abbrev Vec (A : Type*) := EuclideanSpace ℂ A
abbrev Mx (A : Type*) := Matrix A A ℂ
abbrev op : Mx A ≃⋆ₐ[ℂ] (Vec A →L[ℂ] Vec A) := Matrix.toEuclideanCLM

def form (D : Mx A) (x : Vec A) := (inner ℂ x (op D x)).re

lemma square (D : Mx A) (x : Vec A) : form (star D * D) x = ‖op D x‖^2 := by
  unfold form; rw [map_mul,map_star,mul_apply_eq_comp]
  change (inner ℂ x (adjoint (op D) (op D x))).re = _
  rw [adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma add_form (X Y : Mx A) (x : Vec A) : form (X+Y) x=form X x+form Y x := by simp [form,inner_add_right]

lemma identity (x : Vec A) : form 1 x = ‖x‖^2 := by
  rw [form,map_one,one_apply_eq_self]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma star_form (D : Mx A) (x : Vec A) : form (star D) x=form D x := by
  unfold form; rw [map_star, show star (op D)=adjoint (op D) from rfl, adjoint_inner_right,
    ← inner_conj_symm]; exact conj_re ..
lemma real_form (X : Mx A) (c : ℝ) (x : Vec A) : form ((c:ℂ) • X) x=c*form X x := by
  rw [form,map_smul, ContinuousLinearMap.smul_apply,inner_smul_right]; simp [form]

lemma unitary_moves (U : Mx A) (h : U ∈ unitary _) (x : Vec A) : ‖op U x‖ = ‖x‖ := by
  have he := square U x; rw [h.1,identity] at he; exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he.symm

/-- Singular determinant evaluated on a chosen Gram eigenbasis. -/
lemma measures (D : Mx A) :
    ∃ x : OrthonormalBasis (Fin (Fintype.card A)) ℂ (Vec A),
      ‖D.det‖^2=∏ i, ‖op D (x i)‖^2 := by
  let K := star D * D
  let E : Module.End ℂ (Vec A) := (op K).toLinearMap
  have he : E.IsSymmetric := by
    intro x y; change ⟪op K x,y⟫_ℂ = ⟪x,op K y⟫_ℂ
    have h : op K=adjoint (op K) := by
      change op K=star (op K); rw [← map_star]; simp only [K,star_mul,star_star]
    conv_lhs => rw [h]
    rw [adjoint_inner_left]
  have hn : Module.finrank ℂ (Vec A)=Fintype.card A := finrank_euclideanSpace ..
  let b := he.eigenvectorBasis hn
  refine ⟨b,?_⟩
  have h (i) : he.eigenvalues hn i=‖op D (b i)‖^2 := by
    have hu := square D (b i)
    change (inner ℂ (b i) (E (b i))).re = _ at hu
    rw [show E (b i) = _ from he.apply_eigenvectorBasis hn i,inner_smul_right,b.inner_eq_one,mul_one] at hu
    exact hu
  have hd : LinearMap.det E= K.det := LinearMap.det_toLpLin ..
  rw [he.det_eq_prod_eigenvalues hn] at hd
  simp_rw [h] at hd
  have e : ‖K.det‖=‖D.det‖^2 := by simp [K, Matrix.star_eq_conjTranspose, sq]
  rw [← e,← hd]; simp [norm_prod]

lemma min_det {D : Mx A} (c : ℝ) (hc : 0 ≤ c) (h : ∀ x, c*‖x‖ ≤ ‖op D x‖) :
    c ^ Fintype.card A ≤ ‖D.det‖ := by
  obtain ⟨x,hx⟩ := measures D
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hx,pow_right_comm]
  refine (le_of_eq ?_).trans (prod_le_prod (s:=univ) (f:=fun _ => c^2) (fun i _ => by positivity) (fun i _ => ?_))
  · simp
  exact pow_le_pow_left₀ hc (by simpa using h (x i)) _

lemma max_det {D : Mx A} (c : ℝ) (h : ∀ x, ‖op D x‖ ≤ c*‖x‖) (hc : 0 ≤ c) :
    ‖D.det‖ ≤ c ^ Fintype.card A := by
  obtain ⟨x,hx⟩ := measures D
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), hx,pow_right_comm]
  refine (prod_le_prod (s:=univ) (g:=fun _ => c^2) (fun i _ => sq_nonneg _) (fun i _ => ?_)).trans (le_of_eq (by simp))
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using h (x i)) _

/-- re-part coercivity. -/
def Floor (c : ℝ) (D : Mx A) : Prop := ∀ x, c*‖x‖^2 ≤ form D x

namespace Floor
variable {c d : ℝ} {D M : Mx A}
lemma add (hc : Floor c D) (hd : Floor d M) : Floor (c+d) (D+M) := by
  intro x; rw [add_form,add_mul]; exact add_le_add (hc _) (hd _)
lemma nonneg_mul (h : Floor c D) (hr : 0 ≤ d) : Floor (d*c) ((d:ℂ) • D) := by
  intro x; rw [real_form, mul_assoc]; exact mul_le_mul_of_nonneg_left (h _) hr
lemma idem : Floor 1 (1 : Mx A) := fun x => by rw [identity,one_mul]
lemma for_scalar : Floor c ((c:ℂ) • (1:Mx A)) := fun x => by rw [real_form,identity]
lemma lower (h : Floor c D) (hd : d ≤ c) : Floor d D := fun x => (mul_le_mul_of_nonneg_right hd (sq_nonneg _)).trans (h x)
lemma price (h : Floor c D) (x) : c*‖x‖ ≤ ‖op D x‖ := by
  by_cases hx : x=0
  · subst x; simp
  apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hx)
  rw [mul_assoc,← sq,mul_comm ‖op D x‖]; exact (h x).trans ((RCLike.re_le_norm (inner ℂ x (op D x))).trans (norm_inner_le_norm _ _))

lemma unit (h : Floor c D) (hc : 0 < c) : IsUnit D.det := by
  apply IsUnit.mk0 D.det
  exact norm_pos_iff.mp ((pow_pos hc _).trans_le (min_det _ hc.le h.price))
lemma reciprocal (h : Floor c D) (hc : 0 < c) : ‖D⁻¹‖ ≤ c⁻¹ := by
  rw [Matrix.cstar_norm_def]
  apply (op D⁻¹).opNorm_le_bound (by positivity); intro x
  have hp := h.price (op D⁻¹ x)
  rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_nonsing_inv _ (h.unit hc),map_one,one_apply_eq_self] at hp
  rw [mul_comm (c⁻¹), ← div_eq_mul_inv]; exact (le_div_iff₀ hc).2 ((le_of_eq (mul_comm _ _)).trans hp)
end Floor

/-- gamma-five type hermiticity (J^2=1). -/
def Chiral (J D : Mx A) : Prop := star D = J*D*J

lemma determinant_real {J : Mx A} (hj : J*J=1) {D : Mx A} (h : Chiral J D) : (D.det.re : ℂ) = D.det := by
  apply Complex.conj_eq_iff_re.mp
  change star D.det = _
  rw [← Matrix.det_conjTranspose, ← Matrix.star_eq_conjTranspose]
  rw [(show star D=_ from h), Matrix.det_mul, Matrix.det_mul, mul_comm J.det, mul_assoc,← Matrix.det_mul,hj,Matrix.det_one,mul_one]

lemma gradient {J D : Mx A} (hj : J*J=1) (h : Chiral J D) (a b : ℝ) :
    Chiral J ((a:ℂ) • D + (b:ℂ) • 1) := by
  unfold Chiral
  rw [star_add,star_smul,star_smul,(show star D=_ from h),star_one,mul_add,add_mul]
  simp [hj]

lemma det_pos {J D : Mx A} (hj : J*J=1) (h : Chiral J D) {c : ℝ}
    (hc : 0 < c) (hp : Floor c D) : 0 < D.det.re := by
  let L (r : ℝ) := (((1-r:ℝ):ℂ) • D) + (r : ℂ) • (1:Mx A)
  have hu (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) : (L r).det.re ≠ 0 := by
    have hl := (hp.nonneg_mul (sub_nonneg.mpr hr.2)).add (Floor.for_scalar (c:=r) (A:=A))
    have hq : 0 < (1-r)*c+r := by
      rcases eq_or_lt_of_le hr.1 with he|he
      · subst r; simpa
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hr.2) hc.le) he
    have hz := determinant_real hj (D:=L r) (gradient hj h ..)
    intro e; exact (hl.unit hq).ne_zero (hz.symm.trans (e ▸ Complex.ofReal_zero))
  by_contra! he
  have hx : Continuous (fun r => (L r).det.re) := by unfold L; fun_prop
  obtain ⟨r,hr,hk⟩ := intermediate_value_Icc zero_le_one hx.continuousOn (show (0:ℝ)∈Set.Icc _ _ from
    ⟨by simpa [L], by simp [L]⟩)
  exact hu r hr hk

lemma det_closed {J D : Mx A} (hj : J*J=1) (h : Chiral J D) (hp : Floor 0 D) : 0 ≤ D.det.re := by
  let f (r : ℝ) := (D + (r : ℂ) • (1 : Mx A)).det.re
  have ht : Continuous f := by unfold f; fun_prop
  have he := (isClosed_Ici (a:=(0:ℝ))).mem_of_tendsto (ht.continuousAt.continuousWithinAt : Tendsto f (𝓝[>] (0:ℝ)) _)
  have hu : f 0 ∈ Set.Ici 0 := he (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (det_pos hj (show Chiral J (D+ (r:ℂ) • (1 : Mx A)) by simpa using gradient hj h 1 r)
      (show (0:ℝ) < 0 + r by simpa using (show 0 < r from hr)) (hp.add Floor.for_scalar)).le)
  simpa [f] using hu

end YM.QCD.Cost
