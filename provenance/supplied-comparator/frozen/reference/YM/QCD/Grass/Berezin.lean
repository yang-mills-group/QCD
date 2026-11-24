import YM.QCD.Grass.Substitute
import Mathlib.Data.Finset.NoncommProd

/-!
# Dirac variable pairs and Berezin volume

`psi` and the independent `bar`. Use `∫ prod_i psi_i bar_i = 1`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Finset Function
open scoped BigOperators Topology

abbrev Pairs (A : Type*) := A ⊕ A
abbrev Dirac (A : Type*) := Alg (Pairs A)

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

abbrev psi (i : A) : Dirac A := atom (Sum.inl i)
abbrev bar (i : A) : Dirac A := atom (Sum.inr i)

def pair (i : A) := psi i * bar i
lemma pair_grade (i : A) : Plus (pair i) := by simp only [Plus, pair, psi, bar,map_mul,grade_atom,neg_mul_neg]

/-- extent generalized to subsets (wires might pass through other flavors) -/
def vol (s : Finset A) : Dirac A := s.noncommProd pair (fun i _ j _ _ => (pair_grade j).central _)

lemma vol_plus (s : Finset A) : Plus (vol s) :=
  Finset.noncommProd_induction s pair _ Plus (fun _ _ hx hy => Hom.mul (p:=false) (q:=false) hx hy) (by simp [Plus]) (fun i _ => pair_grade i)

@[simp] lemma vol_empty : vol (∅: Finset A) = 1 := by simp [vol]
lemma vol_step [DecidableEq A] (s : Finset A) (i : A) (h : i ∉ s) : vol (insert i s) = pair i * vol s := by simp [vol,h]

lemma pair_union [DecidableEq A] (s t : Finset A) (h : Disjoint s t) : vol (s ∪ t) = vol s * vol t :=
  Finset.noncommProd_union_of_disjoint h ..

private lemma vol_sign (s : Finset A) : vol s=mono (s.disjSum s) ∨ vol s=-mono (s.disjSum s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let T := s.disjSum s
    let u := Sum.inl (β:=A) i
    let v := Sum.inr (α:=A) i
    have hv : Disjoint {v} T := by simp [v,T,hi]
    have hu : Disjoint {u} (insert v T) := by simp [u,v,T,hi]
    have hz : (insert i s).disjSum (insert i s) = insert u (insert v T) := by
      ext (x|x) <;> simp [u,v,T]
    have h₁ := mono_mul_sign _ _ hv
    have h₂ := mono_mul_sign _ _ hu
    simp_rw [Finset.disjUnion_eq_union,singleton_union,mono_single] at h₁ h₂
    rw [vol_step _ _ hi, hz]
    change (atom u * atom v) * vol s = _ ∨ (atom u * atom v) * vol s = _
    change vol s=mono T ∨ vol s=-mono T at ih
    rcases ih with h|h <;> rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;>
      simp only [h,mul_assoc,mul_neg,h₁,h₂,neg_neg] <;> tauto

lemma univ_sign : vol (univ : Finset A)=mono univ ∨ vol (univ : Finset A)=-mono univ :=
  vol_sign _

lemma vol_degree (s : Finset A) : vol s ∈ layer (Pairs A) (s.card + s.card) := by
  have hp : (s.disjSum s).card = s.card + s.card := card_disjSum ..
  have he : mono (s.disjSum s) ∈ layer (Pairs A) _ := hp ▸ homogeneous _ -- check
  rcases vol_sign s with h|h <;> rw [h]
  · exact he
  exact Submodule.neg_mem _ he

lemma vol_ne (s : Finset A) : vol s ≠ 0 := by
  have hv : ‖vol s‖=1 := by rcases vol_sign s with h|h <;> rw [h] <;> simp
  intro he; simp [he] at hv

/-- Berezin top extraction in invariant paired normalization. -/
def ber (A : Type*) [Fintype A] : Dirac A →ₗ[ℂ] ℂ := coef univ (vol (univ : Finset A)) • (coef univ)

@[simp] lemma ber_top : ber A (vol univ) = 1 := by rcases univ_sign (A:=A) with h|h <;> simp [ber,h]

lemma price (x : Dirac A) : ‖ber A x‖ ≤ ‖x‖ := by
  rcases univ_sign (A:=A) with h|h <;> simpa [ber,h] using piece_le x univ

lemma ber_change (f : Seed (Pairs A) →ₗ[ℂ] Seed (Pairs A)) (x : Dirac A) :
    ber A (exterior f x) = LinearMap.det f * ber A x := by simp [ber, coef_top_change]; ring

lemma ber_rows [DecidableEq (Pairs A)] (f : Matrix (Pairs A) (Pairs A) ℂ) (x : Dirac A) :
    ber A (changeVars f x) = f.det * ber A x := by rw [changeVars,ber_change,changes]

lemma discarded {x : Dirac A} {n : ℕ} (hx : x ∈ layer (Pairs A) n) (he : Fintype.card (Pairs A) ≠ n) :
    ber A x = 0 := by simp only [ber,LinearMap.smul_apply, spectrum hx _ he,smul_zero]

lemma odd_loss {x : Dirac A} (hx : Minus x) : ber A x = 0 := by
  have he : ber A (grade x)=ber A x := by
    rw [← write x]; simp only [map_sum,map_smul,grade_mono,ber,LinearMap.smul_apply]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : i = univ
    · subst i; simp [Fintype.card_sum, Pairs, pow_add, ← mul_pow]
    have hv : univ ≠ i := Ne.symm h
    simp [read_other _ _ hv]
  rw [(show grade x=_ from hx),map_neg] at he
  exact neg_eq_self.mp he

@[fun_prop] lemma continuous_ber : Continuous (ber A) := (ber A).continuous_of_finiteDimensional

lemma top_is (x : Dirac A) (hx : x ∈ layer (Pairs A) (Fintype.card (Pairs A))) :
    x = ber A x • vol (univ : Finset A) := by
  have he := ceiling hx
  rcases univ_sign (A:=A) with h|h <;> simpa [ber,h] using he

def pass (f : A → B) : Dirac A →ₐ[ℂ] Dirac B := embed (Sum.map f f)

@[simp] lemma pass_psi (f : A → B) (i : A) : pass f (psi i) = psi (f i) := by rw [pass,psi,embed_atom]; rfl
@[simp] lemma pass_bar (f : A → B) (i : A) : pass f (bar i) = bar (f i) := by rw [pass,bar,embed_atom]; rfl
@[simp] lemma pass_pair (f : A → B) (i : A) : pass f (pair i) = pair (f i) := by simp [pair]

lemma pass_layer (f : A → B) {n : ℕ} {x : Dirac A} (hx : x ∈ layer (Pairs A) n) : pass f x ∈ layer (Pairs B) n :=
  embed_layer _ hx
lemma pass_grade (f : A → B) (x : Dirac A) : grade (pass f x) = pass f (grade x) := embed_grade _ _

lemma pass_comp (f : A → B) (g : B → C) : (pass g).comp (pass f) = pass (g ∘ f) := by
  apply ext_atoms; intro i; cases i <;> simp [pass]

lemma pass_vol (e : A ↪ B) (s : Finset A) : pass e (vol s) = vol (s.map e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [vol_step _ _ hi, map_mul, ih,pass_pair,map_insert,vol_step _ _ (by simpa using hi)]

lemma passed (e : A ≃ B) (x : Dirac A) : ber B (pass e x) = ber A x := by
  classical
  have hp := Fintype.card_congr (Equiv.sumCongr e e)
  rw [← write x]; simp only [map_sum,map_smul]
  refine sum_congr rfl fun i _ => ?_
  by_cases he : i = univ
  · subst i
    have hv : mono (univ : Finset (Pairs A)) ∈ layer (Pairs A) (Fintype.card (Pairs A)) := homogeneous _
    rw [top_is _ hv]; simp_rw [map_smul]
    rw [show (pass e) (vol univ) = _ from (pass_vol e.toEmbedding univ), Finset.map_univ_equiv,ber_top,ber_top]
  have hq : Fintype.card (Pairs A) ≠ i.card := fun h => he (eq_univ_of_card i h.symm)
  rw [discarded (homogeneous _) hq,discarded (pass_layer _ (homogeneous _)) (hp ▸ hq)]

end YM.QCD.Grass
