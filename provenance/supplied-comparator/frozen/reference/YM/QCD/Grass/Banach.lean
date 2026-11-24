import YM.QCD.Grass.Foundation

/-! # l¹ norm for finite Grassmann algebra -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Module Finset Function
open scoped BigOperators ComplexConjugate Topology

variable (A : Type*) [Fintype A]
private def carrier : Alg A ≃ₗ[ℂ] PiLp 1 (fun _ : Finset A => ℂ) :=
  (blades A).equivFun.trans (WithLp.linearEquiv 1 ℂ _).symm

instance ng : NormedAddCommGroup (Alg A) := NormedAddCommGroup.induced _ _ _ (carrier A).injective

instance nsc : NormedSpace ℂ (Alg A) := .induced _ _ _ (carrier A)

variable {A}
lemma norm_def (x : Alg A) : ‖x‖ = ∑ s, ‖coef s x‖ := by
  change ‖carrier A x‖ = _
  simp_rw [PiLp.norm_eq_of_L1]
  exact Finset.sum_congr rfl fun i _ => by simp [carrier,coef]

@[simp] lemma norm_mono (s : Finset A) : ‖mono s‖ = 1 := by
  classical
  rw [norm_def, sum_eq_single s]
  · simp
  · intro t _ h; rw [read_other _ _ h]; simp
  simp

@[simp] lemma norm_atom (i : A) : ‖atom i‖ = 1 := by rw [← mono_single]; simp only [norm_mono]

lemma basic_mul (s t : Finset A) : ‖mono s * mono t‖ ≤ 1 := by
  classical
  by_cases h : Disjoint s t
  · rcases mono_mul_sign _ _ h with h | h <;> rw [h] <;> simp
  rw [mono_mul_zero _ _ h]; simp

lemma piece_le (x : Alg A) (s : Finset A) : ‖coef s x‖ ≤ ‖x‖ := by
  classical
  rw [norm_def]
  exact single_le_sum (fun i _ => norm_nonneg (coef i x)) (mem_univ s)

instance : NormedRing (Alg A) where
  dist_eq := SeminormedAddGroup.dist_eq
  norm_mul_le x y := by
    calc
      ‖x*y‖ = ‖∑ s : Finset A, ∑ t : Finset A, coef s x • mono s * (coef t y • mono t)‖ := by
        simp_rw [← mul_sum, ← sum_mul, write x, write y]
      _ ≤ ∑ s : Finset A, ∑ t : Finset A, ‖coef s x • mono s * (coef t y • mono t)‖ :=
        (norm_sum_le ..).trans (sum_le_sum fun i _ => norm_sum_le ..)
      _ ≤ ∑ s : Finset A, ∑ t : Finset A, ‖coef s x‖ * ‖coef t y‖ := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        rw [smul_mul_assoc,mul_smul_comm,norm_smul,norm_smul]
        rw [← mul_assoc]
        exact mul_le_of_le_one_right (by positivity) (basic_mul i j)
      _ = ‖x‖ * ‖y‖ := by rw [norm_def x,norm_def y,sum_mul]; simp_rw [mul_sum]

instance : NormOneClass (Alg A) := ⟨by rw [← mono_empty,norm_mono]⟩

instance : NormedAlgebra ℂ (Alg A) where
  norm_smul_le := norm_smul_le

-- use this same norm for Bochner calculations
instance : NormedAlgebra ℝ (Alg A) := .restrictScalars ℝ ℂ _
-- prefer existing data on rationals? verify below
instance : NormedAlgebra ℚ (Alg A) := .restrictScalars ℚ ℂ _

instance : CompleteSpace (Alg A) := FiniteDimensional.complete ℂ _

@[fun_prop] theorem continuous_coef (s : Finset A) : Continuous (fun x => coef s x) :=
  (coef s).continuous_of_finiteDimensional

lemma continuous_by_coef {X : Type*} [TopologicalSpace X] (f : X → Alg A)
    (h : ∀ s : Finset A, Continuous fun x => coef s (f x)) : Continuous f := by
  rw [show f = (fun x => ∑ s, coef s (f x) • mono s) from funext fun x => (write (f x)).symm]
  exact continuous_finsetSum _ fun i _ => (h i).smul continuous_const

open NormedSpace

lemma algebra_exp_add {x y : Alg A} (h : Commute x y) : exp (x+y)=exp x * exp y := exp_add_of_commute h
lemma exp_cont : Continuous (exp : Alg A → Alg A) := exp_continuous
lemma radius_two (x : Alg A) (hx : x*x=0) : exp x = 1 + x := by
  simp only [exp_eq_tsum ℂ]
  rw [tsum_eq_sum (s:=range 2) ?_]; · simp [sum_range_succ]
  intro n hn
  have hp : x^n=0 := pow_eq_zero_of_le (show 2 ≤ n from le_of_not_gt (mt mem_range.mpr hn)) (by rw [pow_two]; exact hx)
  rw [hp]; simp
lemma map_weight {B : Type*} [Fintype B] (f : Alg A →ₐ[ℂ] Alg B) (x : Alg A) : f (exp x) = exp (f x) :=
  map_exp f f.toLinearMap.continuous_of_finiteDimensional x
end YM.QCD.Grass
