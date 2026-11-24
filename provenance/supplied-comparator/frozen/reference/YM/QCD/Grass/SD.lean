import YM.QCD.Grass.Fubini
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Grassmann integration by parts, no inverse covariance needed
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Function Finset NormedSpace
open scoped BigOperators Matrix Topology
variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

def probe (i : X) : Module.Dual ℂ (Seed X) := (thetaBasis X).coord i
def vary (i : X) : Alg X →ₗ[ℂ] Alg X := CliffordAlgebra.contractLeft (probe i)

lemma vary_head (i j : X) (x : Alg X) : vary i (atom j*x)=((probe i) (thetaBasis X j)) • x-atom j*vary i x :=
  CliffordAlgebra.contractLeft_ι_mul ..
lemma vary_one (i : X) : vary i 1=0 := CliffordAlgebra.contractLeft_one ..
lemma vary_atom (i j : X) : vary i (atom j)=probe i (thetaBasis X j) • 1 := by
  simpa only [vary_one,mul_one,mul_zero,sub_zero] using vary_head i j 1
@[simp] lemma vary_self (i : X) : vary i (atom i)=1 := by rw [vary_atom]; simp [probe]
lemma vary_off (i j : X) (h : i≠j) : vary i (atom j)=0 := by rw [vary_atom]; simp [probe,h,h.symm]

lemma vary_list (i : X) (l : List X) (x : Alg X) : vary i ((l.map atom).prod*x)=vary i (l.map atom).prod*x+grade (l.map atom).prod*vary i x := by
  induction l with
  | nil => simp [vary_one]
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons,mul_assoc,vary_head,ih,map_mul,grade_atom,smul_mul_assoc]
    rw [sub_mul,smul_mul_assoc,mul_add,mul_assoc,neg_mul]; abel
lemma vary_mul (i : X) (x y : Alg X) : vary i (x*y)=vary i x*y+grade x*vary i y := by
  have hs (s : Finset X) : vary i (mono s*y)=vary i (mono s)*y + grade (mono s)*vary i y := by
    obtain ⟨w,-,-,he⟩ := expression s
    rw [he]; simpa only [List.map_ofFn] using vary_list i (List.ofFn w) y
  rw [← write x]; simp only [map_sum,map_smul,sum_mul,smul_mul_assoc,hs,smul_add,sum_add_distrib]

lemma test_layer (l : List X) : (l.map atom).prod ∈ layer X l.length := by
  induction l with
  | nil => simpa using homogeneous (∅: Finset X)
  | cons a l h => simp only [List.map_cons,List.prod_cons,List.length_cons, add_comm l.length]; exact layer_mul (atom_mem _) h
lemma lower_layer (i : X) (l : List X) : vary i (l.map atom).prod ∈ layer X (l.length-1) := by
  induction l with
  | nil => simp [vary_one]
  | cons a l h =>
    simp only [List.map_cons,List.prod_cons,vary_head,List.length_cons,Nat.add_sub_cancel]
    apply Submodule.sub_mem _ (Submodule.smul_mem _ _ (test_layer _))
    by_cases hl : l=[]
    · subst l; simp [vary_one]
    have he : 1+(l.length-1)=l.length := by have := List.length_pos_iff.mpr hl; omega
    exact he ▸ layer_mul (atom_mem a) h
lemma lowers (i : X) (s : Finset X) : vary i (mono s) ∈ layer X (s.card-1) := by
  obtain ⟨w,-,-,he⟩ := expression s
  rw [he]; simpa only [List.map_ofFn,List.length_ofFn] using lower_layer i (List.ofFn w)
lemma integration (x : Dirac A) (i : Pairs A) : ber A (vary i x)=0 := by
  rw [← write x]; simp only [map_sum,map_smul]; apply sum_eq_zero
  intro j _
  haveI : Nonempty (Pairs A) := ⟨i⟩
  have he : j.card ≤ Fintype.card (Pairs A) := card_le_univ _
  rw [discarded (lowers ..) (by have := Fintype.card_pos (α:=Pairs A); omega),smul_zero]

lemma vary_pow (i : X) (n : ℕ) (x : Alg X) (h : Plus x) : vary i (x^n)=n • (x^(n-1)*vary i x) := by
  induction n with
  | zero => simp [vary_one]
  | succ n ih =>
    rw [pow_succ',vary_mul,ih,(show grade x=_ from h)]
    by_cases he : n=0; · subst n; simp
    rw [(h.central (vary i x)).pow_right]; -- check
    rw [add_smul,one_smul,mul_smul_comm,← mul_assoc, Nat.add_sub_cancel, ← pow_succ', Nat.sub_add_cancel (by omega)]; abel
lemma varies_exp (i : X) (x : Alg X) (h : Plus x) : vary i (exp x)=exp x * vary i x := by
  let f (t : ℕ) := (t.factorial:ℂ)⁻¹ • x^t
  have hf : HasSum f (exp x) := exp_series_hasSum_exp' x
  have he (n) : vary i (f (n+1))=f n * vary i x := by
    unfold f; rw [map_smul, vary_pow _ _ _ h, Nat.add_sub_cancel,smul_mul_assoc,
      ← Nat.cast_smul_eq_nsmul ℂ (n+1), smul_smul]
    congr 1; rw [Nat.factorial_succ,Nat.cast_mul]; field_simp
  have hv : HasSum (fun t => vary i (f t)) (vary i (exp x)) := hf.map (vary i).toAddMonoidHom (vary i).continuous_of_finiteDimensional
  rw [← hv.tsum_eq, ← hv.summable.sum_add_tsum_nat_add 1]
  rw [sum_range_one, show vary i (f 0)=0 by simp [f,vary_one],zero_add]; simp_rw [he]; exact (hf.mul_right _).tsum_eq

lemma form_row (i : A) (M : Matrix A A ℂ) : vary (Sum.inr i) (form M) = -(∑ j : A, M i j • psi j) := by
  classical
  unfold form
  simp only [map_sum,map_smul]
  have he (u j : A) : vary (Sum.inr i) (psi j*bar u)= -(if i=u then psi j else 0) := by
    rw [vary_head]
    by_cases h : i=u
    · subst u; simp [probe,psi,bar,Pairs]
    rw [vary_off (X:=Pairs A) _ _ (by simp [h])]; simp [probe,h]
  rw [sum_eq_single i]
  · simp_rw [he i, if_true,smul_neg,sum_neg_distrib]
  · intro j _ hj; simp [he j,Ne.symm hj]
  simp

/-- Left Dirac identities all insertion degrees. -/
lemma answer (i : A) (M : Matrix A A ℂ) (x : Dirac A) :
    ber A (gauss M*((∑ j, M i j • psi j)*x)) = ber A (gauss M*vary (Sum.inr i) x) := by
  have he := integration (gauss M*x) (Sum.inr i)
  rw [vary_mul,show grade (gauss M)=gauss M from gauss_plus M,gauss,varies_exp _ _ (form_plus M),form_row,mul_neg,neg_mul,mul_assoc,map_add,map_neg] at he
  exact (eq_of_neg_add_eq_zero he) -- check
lemma survives {f : X → Y} (h : Injective f) (i : X) (x : Alg X) :
    vary (f i) (embed f x)=embed f (vary i x) := by
  have hh (l : List X) : vary (f i) (embed f (l.map atom).prod) = embed f (vary i (l.map atom).prod) := by
    induction l with
    | nil => simp [vary_one]
    | cons a l ih =>
      simp only [List.map_cons,List.prod_cons,map_mul,embed_atom,vary_head,ih,map_sub,map_smul]
      by_cases hv : i=a
      · subst a; simp [probe]
      classical
      simp [probe,hv,Ne.symm hv,h.eq_iff]
  have hp (s : Finset X) : vary (f i) (embed f (mono s)) = embed f (vary i (mono s)) := by obtain ⟨w,-,-,he⟩ := expression s; rw [he]; simpa only [List.map_ofFn] using hh (List.ofFn w)
  rw [← write x]; simp only [map_sum,map_smul,hp]
lemma test_survives {f : X → Y} (h : Injective f) (i : X) (x : Dirac X) :
    vary (Sum.inr (f i)) (pass f x)=pass f (vary (Sum.inr i) x) := by
  exact survives (X:=Pairs X) (Y:=Pairs Y) (f:=Sum.map f f) (Sum.map_injective.mpr ⟨h,h⟩) (Sum.inr i) x
end YM.QCD.Grass
