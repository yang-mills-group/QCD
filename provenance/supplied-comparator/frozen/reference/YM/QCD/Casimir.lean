import YM.QCD.Simple

/-! # Real adjoint index and slope normalization -/

set_option autoImplicit false
noncomputable section
namespace YM.QCD
namespace Roots
open Complex Finset Module
open scoped Matrix.Norms.Frobenius InnerProductSpace

abbrev Idx := Root ⊕ Root ⊕ Fin 2 -- lean notation check

def blade : Idx → su.Alg
  | .inl i => ⟨plane i 1, plane_lie _ _⟩
  | .inr (.inl i) => ⟨plane i I, plane_lie _ _⟩
  | .inr (.inr i) => ⟨H (coroot i.succ), H_lie (coroot_units _)⟩

def extract (X : Mat) : Idx → ℝ
  | .inl i => (X (a i) (b i)).re
  | .inr (.inl i) => (X (a i) (b i)).im
  | .inr (.inr i) => weights X i.castSucc

lemma blades (X : su.Alg) : (∑ i, extract X.val i • blade i) = X := by
  apply Subtype.ext
  change su.lie.subtype (∑ i, extract X.val i • blade i) = X.val
  rw [map_sum]; simp_rw [map_smul, Fintype.sum_sum_type, Submodule.subtype_apply]
  let A := X.val
  let z := fun i : Root => A (a i) (b i)
  change (∑ i : Root, (z i).re • plane i 1) + ((∑ i : Root, (z i).im • plane i I) + ∑ i : Fin 2,
    weights A i.castSucc • H (coroot i.succ)) = A
  rw [← add_assoc, ← sum_add_distrib, Fin.sum_univ_two, add_comm]
  convert (decompose X.property).symm using 2
  · exact (diagonals (units X.property)).symm
  apply sum_congr rfl
  intro i _; rw [← plane_smul, ← plane_smul, ← plane_add, real_smul, real_smul,
    mul_one, Complex.re_add_im]

private lemma detect (s : Idx → ℝ) (e : ∑ i, s i • blade i = 0) : ∀ i, s i = 0 := by
  have he := congrArg su.lie.subtype e
  rw [map_zero,map_sum,Fintype.sum_sum_type,Fintype.sum_sum_type] at he
  simp_rw [map_smul] at he
  change (∑ i : Root, s (.inl i) • plane i 1) + ((∑ i : Root, s (.inr (.inl i)) • plane i I) +
    ∑ i : Fin 2, s (.inr (.inr i)) • H (coroot i.succ)) = 0 at he
  have hd (p : Root) : s (Sum.inl p)=0 ∧ s (Sum.inr (Sum.inl p))=0 := by
    have h0 := congrFun (congrFun he (a p)) (b p)
    suffices hs : (s (.inl p) : ℂ) + ↑(s (.inr (.inl p))) * I = 0 from
      ⟨by simpa using congrArg Complex.re hs, by simpa using congrArg Complex.im hs⟩
    fin_cases p <;> simpa [H,plane,a,b, Fin.sum_univ_succ, coroot, Matrix.single, Matrix.diagonal_apply,
      Complex.real_smul] using! h0
  rintro (i | i | i)
  · exact (hd i).1
  · exact (hd i).2
  simp_rw [(fun k => (hd k).1), (fun k => (hd k).2), zero_smul, sum_const_zero, zero_add] at he
  have h0 := congrArg Complex.im (congrFun (congrFun he i.castSucc) i.castSucc)
  fin_cases i <;> simpa [Fin.sum_univ_succ, H, coroot, a,b,Pi.single_apply] using! h0

def eight : Basis Idx ℝ su.Alg := Basis.mk (Fintype.linearIndependent_iff.mpr detect) (by
  intro x _; rw [← blades x]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩))

def eightColors : Basis Idx ℝ su.Color := eight.map su.colorIso.symm

@[simp] theorem blade_color (i : Idx) : su.colorMat (eightColors i) = (blade i).val := by
  change (su.colorIso (eightColors i)).val = _
  rw [eightColors, Basis.map_apply, LinearEquiv.apply_symm_apply, eight, Basis.mk_apply]

private def value (h : Hue → ℝ) : Idx → ℝ
  | .inl p => -((h (a p) - h (b p))^2)
  | .inr (.inl p) => -((h (a p) - h (b p))^2)
  | .inr (.inr _) => 0

private lemma eigen (h : Hue → ℝ) (he : ∑ i, h i = 0) (i : Idx) :
    let c := su.projectColor (H h)
    su.ad c (su.ad c (eightColors i)) = value h i • eightColors i := by
  dsimp only
  apply su.colorMat_injective
  rw [Gauge.colorMat_ad, Gauge.colorMat_ad, su.colorMat_project_self (H_lie he), map_smul, blade_color]
  have hh (p : Root) (z : ℂ) : br (H h) (br (H h) (plane p z)) =
      (-((h (a p) - h (b p))^2) : ℝ) • plane p z := by
    rw [spin, spin, ← plane_smul]; congr 1
    rw [real_smul,Complex.ofReal_neg,Complex.ofReal_pow]
    linear_combination (norm := ring) ((↑(h (a p) - h (b p)):ℂ) ^ 2 * z) * Complex.I_mul_I
  rcases i with p | p | q
  · exact hh ..
  · exact hh ..
  change br (H h) (br (H h) (H (coroot _))) = (0:ℝ) • H _
  rw [zero_smul]; ext i j; rw [twice]
  by_cases h : i = j
  · subst i; simp
  simp [H,h]

lemma lie_dimension : su.lieDim = 8 := by simp [Gauge.lieDim, Module.finrank_eq_card_basis eight]

theorem casimir : su.casimir = 18 := by
  let h := coroot 0
  let c := su.projectColor (H h)
  have h0 : LinearMap.trace ℝ su.Color (su.ad c * su.ad c) = -12 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ eightColors]
    have diag (i : Idx) : (LinearMap.toMatrix eightColors eightColors (su.ad c * su.ad c)) i i = value h i := by
      rw [LinearMap.toMatrix_apply, End.mul_apply, show su.ad c (su.ad c (eightColors i)) = _ from
        eigen h (coroot_units _) i]
      simp
    simp only [Matrix.trace, Matrix.diag_apply, diag]; rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    norm_num [value,h,a,b,coroot, Fin.sum_univ_succ, Pi.single_apply, show (2:Hue) ≠ 0 by decide, show (2:Hue) ≠ 1 by decide]
  have hv := su.trace_color c c
  rw [show su.colorMat c = _ from su.colorMat_project_self (H_lie (coroot_units 0))] at hv
  change -(H h * H h).trace.re = (↑(2+1:ℕ):ℝ)*⟪c,c⟫_ℝ at hv
  have hb : -(H h * H h).trace.re = 2 := by
    norm_num [H,h,Matrix.trace, coroot, a, b, Matrix.diagonal_mul, Fin.sum_univ_succ,
      Complex.mul_re, Pi.single_apply, show (2:Hue) ≠ 0 by decide, show (2:Hue) ≠ 1 by decide]
  have e : ⟪c,c⟫_ℝ = 2/3 := by rw [hb] at hv; push_cast at hv; linarith
  have ha := Gauge.trace_adjoint simple c c
  rw [e,h0] at ha; linarith

end Roots
end YM.QCD
