import YM.QCD.Estimate.DetLog

/-! # uniform contraction window -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cost
open Finset Function Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
variable {c d w q : ℝ} {A : Type*} [Fintype A] [DecidableEq A]

def notch (w : ℝ) (D : Mx A) := 1-(w:ℂ) • D
lemma contracts (D : Mx A) (h : Floor c D) (hv : ‖D‖ ≤ d) (hw : 0<w) (hq : 0 ≤ q)
    (he : 1-2*w*c+w^2*d^2 ≤ q^2) : ‖notch w D‖ ≤ q := by
  rw [Matrix.cstar_norm_def]; apply (op (notch w D)).opNorm_le_bound hq
  intro x
  let y := (w:ℂ) • op D x
  have hB : ‖op D x‖ ≤ d * ‖x‖ := (leanBound D x).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg x))
  have hp : w*c*‖x‖^2 ≤ (inner ℂ x y).re := by
    change _≤(inner ℂ x ((w:ℂ) • op D x)).re
    rw [inner_smul_right]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h x) hw.le
  have ht : ‖y‖^2 ≤ w^2*d^2*‖x‖^2 := by
    dsimp only [y]; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hw.le, mul_pow,mul_assoc,← mul_pow d]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB _) (sq_nonneg _)
  rw [notch,map_sub,map_smul,ContinuousLinearMap.sub_apply, map_one,one_apply_eq_self]
  change ‖x-y‖ ≤ q*‖x‖
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,norm_sub_sq (𝕜:=ℂ)]
  change _ - 2*(inner ℂ x y).re + _ ≤ _
  nlinarith only [ht,hp,mul_le_mul_of_nonneg_right he (sq_nonneg ‖x‖)]

lemma choose_rate (c d : ℝ) (hc : 0<c) (hd : 0<d) : ∃ w q : ℝ, 0<w ∧ 0 ≤ q ∧ q<1 ∧ 1-2*w*c+w^2*d^2 ≤ q^2 := by
  obtain ⟨w,hw,he⟩ := exists_between (show 0<c/d^2 from by positivity)
  let F := 1-2*w*c+w^2*d^2
  have ht : w*d^2 < c := (lt_div_iff₀ (by positivity)).mp he
  have hv : F < 1 := by unfold F; nlinarith [mul_lt_mul_of_pos_left ht hw]
  refine ⟨w,Real.sqrt (max 0 F),hw,Real.sqrt_nonneg _,Real.sqrt_lt' zero_lt_one |>.mpr (by rw [one_pow]; exact max_lt zero_lt_one hv),?_⟩ -- check
  rw [Real.sq_sqrt (le_max_left ..)]; exact le_max_right ..

lemma chip (D : Mx A) (hw : w ≠ 0) (hp : IsUnit D.det) (h : ‖notch w D‖ < 1) :
    HasSum (fun n : ℕ => (w:ℂ) • notch w D ^ n) D⁻¹ := by
  have he : HasSum (fun n : ℕ => notch w D ^ n) ((1-notch w D)⁻¹) := by rw [Matrix.nonsing_inv_eq_ringInverse]; exact hasSum_geom_series_inverse _ h
  have hW : (w:ℂ)≠0 := by exact_mod_cast hw
  have hk : 1-notch w D = (w:ℂ) • D := by unfold notch; abel
  have hh : ((w:ℂ) • D)⁻¹ = (w:ℂ)⁻¹ • D⁻¹ := by
    apply Matrix.inv_eq_right_inv; rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hW,one_smul,Matrix.mul_nonsing_inv _ hp]
  have H := he.const_smul (w:ℂ) -- check
  rw [hk,hh,smul_smul,mul_inv_cancel₀ hW,one_smul] at H
  exact H
lemma marks (D : Mx A) (hw : 0<w) (h : ‖notch w D‖<1) :
    Real.log ‖D.det‖= -(∑ i, ∑' n, (plank (notch w D) i n).re) - Fintype.card A*Real.log w := by
  let X := notch w D
  have he := logdet X h
  rw [show 1-X=(w:ℂ) • D by dsimp only [X,notch]; abel, Matrix.det_smul] at he
  have hp : ‖D.det‖≠0 := fun H => by rw [norm_eq_zero.mp H,mul_zero] at he; exact Complex.exp_ne_zero _ he.symm
  replace he := congrArg (fun x : ℂ => Real.log ‖x‖) he
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hw.le,Real.log_mul (pow_ne_zero _ hw.ne') hp, Real.log_pow,Complex.norm_exp, Real.log_exp, Complex.neg_re, Complex.re_sum] at he
  simp_rw [Complex.re_tsum (planked X h _)] at he
  rw [← he]; ring -- check
end YM.QCD.Cost
