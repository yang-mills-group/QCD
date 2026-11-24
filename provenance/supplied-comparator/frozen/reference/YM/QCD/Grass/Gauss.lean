import YM.QCD.Grass.Berezin

/-!
# Dirac Berezin Gaussian

Degenerate matrices included. Row convention and l¹ bound.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Finset Function NormedSpace
open scoped BigOperators Topology Matrix

variable {A B : Type*} [Fintype A] [Fintype B]

/-- transform the two independent slots, row convention `Bᵢⱼ xⱼ`. -/
def adapter (S T : Matrix A B ℂ) := changeVars (Matrix.fromBlocks S 0 0 T)
lemma adapt_psi (S T : Matrix A B ℂ) (i : A) : adapter S T (psi i)=∑ j, S i j • psi j := by
  unfold adapter psi; rw [change_atom, Fintype.sum_sum_type]; simp
lemma adapt_bar (S T : Matrix A B ℂ) (i : A) : adapter S T (bar i)=∑ j, T i j • bar j := by
  unfold adapter bar; rw [change_atom, Fintype.sum_sum_type]; simp
lemma volume_map [DecidableEq A] (S T : Matrix A A ℂ) (x : Dirac A) :
    ber A (adapter S T x)=S.det*T.det*ber A x := by
  rw [adapter,ber_rows,Matrix.det_fromBlocks_zero₂₁]

/-- `-bar M psi` (already sign for exponential) -/
def form (M : Matrix A A ℂ) : Dirac A := ∑ i, ∑ j, M i j • (psi j * bar i)

def gauss (M : Matrix A A ℂ) : Dirac A := exp (form M)

lemma form_add (M N : Matrix A A ℂ) : form (M+N) = form M + form N := by simp [form,add_smul,sum_add_distrib]

lemma form_two (M : Matrix A A ℂ) : form M ∈ layer (Pairs A) 2 :=
  Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (layer_mul (atom_mem _) (atom_mem _))

lemma form_plus (M : Matrix A A ℂ) : Plus (form M) := by simp only [Plus, form,map_sum, map_smul,map_mul,psi,bar,grade_atom,neg_mul_neg]

lemma gauss_plus (M : Matrix A A ℂ) : Plus (gauss M) := by
  unfold Plus gauss; rw [map_weight, (show grade (form M) = _ from form_plus _)]
lemma gauss_add (M N : Matrix A A ℂ) : gauss (M+N) = gauss M * gauss N := by
  unfold gauss; rw [form_add]; exact algebra_exp_add ((form_plus N).central _)

lemma form_map (S T : Matrix A B ℂ) (M : Matrix A A ℂ) :
    adapter S T (form M) = form (Tᵀ * (M * S)) := by
  unfold form
  simp_rw [map_sum,map_smul,map_mul,adapt_psi,adapt_bar]
  -- slot order i,j (A), u,v (B)
  have h (i j : A) : (∑ u : B, S j u • psi u) * (∑ v : B, T i v • bar v) =
      ∑ v : B, ∑ u : B, (T i v*S j u) • (psi u*bar v) := by
    rw [mul_sum]; apply sum_congr rfl; intro v _
    rw [sum_mul]; exact sum_congr rfl fun u _ => by rw [mul_smul_comm, smul_mul_assoc, mul_smul]
  simp_rw [h,Matrix.mul_apply,Matrix.transpose_apply,mul_sum,sum_smul,smul_sum,smul_smul]
  let F := fun (i j : A) (v u : B) => (T i v*(M i j*S j u)) • (psi u*bar v)
  rw [show (∑ i : A, ∑ j : A, ∑ v : B, ∑ u : B, (M i j * (T i v * S j u)) • (psi u*bar v)) =
      ∑ i : A, ∑ j : A, ∑ v : B, ∑ u : B,F i j v u by
    unfold F; simp only [mul_left_comm (T _ _) (M _ _)]]
  change ∑ i, ∑ j, ∑ v, ∑ u, F i j v u = ∑ v, ∑ u, ∑ i, ∑ j, F i j v u
  have he := sum_comm (s:=univ) (t:=univ) (f:=fun (x : A × A) (y : B × B) => F x.1 x.2 y.1 y.2)
  simpa only [Fintype.sum_prod_type] using he

lemma gauss_map (S T : Matrix A B ℂ) (M : Matrix A A ℂ) :
    adapter S T (gauss M) = gauss (Tᵀ * (M * S)) := by unfold gauss; rw [map_weight,form_map]

lemma last_square (i j k : A) : (psi j*bar i)*(psi k * bar i)=0 := by
  rw [← mul_assoc, mul_assoc (psi j), atom_flip (A:=Pairs A) (Sum.inr i) (Sum.inl k), mul_neg, neg_mul,
    ← mul_assoc (psi j), mul_assoc, atom_square, mul_zero,neg_zero]

lemma row_square (i : A) (M : Matrix A A ℂ) :
    (∑ j : A, M i j • (psi j*bar i)) * (∑ j : A, M i j • (psi j*bar i)) = 0 := by simp [mul_sum,sum_mul,smul_mul_assoc,mul_smul_comm,last_square]

lemma diagonal_parts (s : Finset A) : exp (∑ i ∈ s, pair i) = ∑ t ∈ s.powerset, vol t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi,algebra_exp_add ((pair_grade i).central _).symm, radius_two (pair i) (last_square i i i), ih,
      add_mul, one_mul,mul_sum, powerset_insert, sum_union]
    · rw [sum_image]
      · congr 1; exact sum_congr rfl fun t ht => (vol_step t i (fun hh => hi ((mem_powerset.mp ht) hh))).symm
      intro t ht u hu e
      have hx : i ∉ t := fun hx => hi ((mem_powerset.mp ht) hx)
      have hy : i ∉ u := fun hx => hi ((mem_powerset.mp hu) hx)
      simpa [hx,hy] using congrArg (·.erase i) e
    rw [Finset.disjoint_left]; intro a ha H; rcases mem_image.mp H with ⟨t,ht,rfl⟩
    exact hi ((mem_powerset.mp ha) (mem_insert_self ..))

lemma unit_amp [DecidableEq A] : ber A (gauss 1) = 1 := by
  unfold gauss
  have hz : form (1:Matrix A A ℂ)=∑ i, pair i := by simp [form,Matrix.one_apply,ite_smul,pair]
  rw [hz,diagonal_parts,map_sum,sum_eq_single univ] -- incl zero dim
  · exact ber_top
  · intro t _ h; exact discarded (vol_degree _) (by change Fintype.card (A ⊕ A) ≠ _; rw [Fintype.card_sum]; intro e; exact h (eq_univ_of_card t (by omega)))
  simp

theorem det_amplitude [DecidableEq A] (M : Matrix A A ℂ) : ber A (gauss M) = M.det := by
  have he : adapter M 1 (gauss 1) = gauss M := by rw [gauss_map,Matrix.transpose_one]; simp
  rw [← he,volume_map,unit_amp,Matrix.det_one]; simp

@[fun_prop] lemma continuous_gauss : Continuous (gauss : Matrix A A ℂ → Dirac A) := by
  apply exp_cont.comp
  unfold form; fun_prop

lemma gauss_norm (M : Matrix A A ℂ) : ‖gauss M‖ ≤ ∏ i, (1 + ∑ j, ‖M i j‖) := by
  classical
  let row i := ∑ j, M i j • (psi j * bar i)
  have h (s : Finset A) : ‖exp (∑ i ∈ s, row i)‖ ≤ ∏ i ∈ s, (1 + ∑ j, ‖M i j‖) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hi' : Plus (row i) := by simp only [Plus,row,map_sum,map_smul,map_mul,psi,bar,grade_atom,neg_mul_neg]
      rw [sum_insert hi,algebra_exp_add (hi'.central _).symm, radius_two _ (row_square _ _), prod_insert hi]
      refine (norm_mul_le ..).trans (mul_le_mul ?_ ih (norm_nonneg _) (by positivity))
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq norm_one) ((norm_sum_le _ _).trans ?_))
      refine sum_le_sum fun j _ => ?_
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) <| (norm_mul_le ..).trans (by simp only [psi,bar,norm_atom,one_mul,le_rfl])
  exact h _

lemma observed_norm (M : Matrix A A ℂ) (x : Dirac A) :
    ‖ber A (gauss M * x)‖ ≤ (∏ i, (1 + ∑ j, ‖M i j‖)) * ‖x‖ :=
  (price _).trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gauss_norm M) (norm_nonneg _)))

end YM.QCD.Grass
