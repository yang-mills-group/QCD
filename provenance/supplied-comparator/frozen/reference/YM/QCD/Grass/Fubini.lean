import YM.QCD.Grass.Gauss

/-! # Partial Berezin integration

Both factors have EVEN top degree. Integrate out the first, retaining actual elements of the
second algebra (not merely a statement modulo constants).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Finset Function Module
open scoped BigOperators Topology Matrix

variable (A : Type*) (B : Type*) [Fintype A] [Fintype B]

def pairing : Dirac A →ₗ[ℂ] Dirac A →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => ber A (x*y)) (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp)

theorem detects : Injective (pairing A) := by
  classical
  refine LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr ?_)
  intro x h
  have hp (y : Dirac A) : ber A (x*y)=0 := LinearMap.congr_fun (LinearMap.mem_ker.mp h) y
  have hv (s : Finset (Pairs A)) : coef s x = 0 := by
    have he := hp (mono sᶜ)
    have hz {i : Finset (Pairs A)} (hi : i ≠ s) : ber A (mono i * mono sᶜ)=0 := by
      by_cases hu : Disjoint i sᶜ
      · have hl : i ⊆ s := by simpa using subset_compl_iff_disjoint_left.mpr hu.symm
        have hh : Fintype.card (Pairs A) ≠ i.card + (sᶜ).card := by
          have hx := card_lt_card (ssubset_of_subset_of_ne hl hi)
          have ha := card_le_univ s; rw [card_compl]; omega
        exact discarded (layer_mul (homogeneous _) (homogeneous _)) hh
      rw [mono_mul_zero _ _ hu,map_zero]
    have hn : ber A (mono s * mono sᶜ) ≠ 0 := by
      have H : mono s * mono sᶜ=mono univ ∨ mono s * mono sᶜ=-mono univ := by
        simpa [disjUnion_eq_union] using mono_mul_sign s sᶜ disjoint_compl_right
      rcases univ_sign (A:=A) with h₀|h₀ <;> rcases H with h|h <;> simp [h,ber,h₀]
    rw [← write x, sum_mul, map_sum, sum_eq_single s] at he
    · rw [smul_mul_assoc,map_smul,smul_eq_mul] at he
      exact (mul_eq_zero.mp he).resolve_right hn
    · intro i _ hi; rw [smul_mul_assoc,map_smul,hz hi, smul_zero]
    simp
  rw [← write x]; simp [hv]

def perfect : Dirac A ≃ₗ[ℂ] Dual ℂ (Dirac A) := LinearEquiv.ofBijective (pairing A)
  ⟨detects _, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    classical
    rw [Module.finrank_eq_card_basis (blades (Pairs A)),
      Module.finrank_eq_card_basis (blades (Pairs A)).dualBasis])).mp (detects _)⟩

@[simp] lemma perfect_apply (x y : Dirac A) : perfect A x y = ber A (x*y) := rfl

def near : Dirac A →ₐ[ℂ] Dirac (A ⊕ B) := pass Sum.inl

def far : Dirac B →ₐ[ℂ] Dirac (A ⊕ B) := pass Sum.inr

lemma generation : near A B (vol univ) * far A B (vol univ) = vol univ := by
  classical
  let e : A ↪ A ⊕ B := Embedding.inl
  let f : B ↪ A ⊕ B := Embedding.inr
  change pass e _ * pass f _ = _
  have hz : Disjoint (univ.map e) (univ.map f) := disjoint_left.mpr (by
    intro x hx hy
    obtain ⟨i,-,rfl⟩ := mem_map.mp hx; obtain ⟨j,-,hj⟩ := mem_map.mp hy
    cases (show Sum.inr j = Sum.inl i from hj))
  have hp : univ.map e ∪ univ.map f = univ := eq_univ_of_forall (by
    intro x; cases x with
    | inl i => exact mem_union_left _ (mem_map.mpr ⟨i,mem_univ _,rfl⟩)
    | inr j => exact mem_union_right _ (mem_map.mpr ⟨j,mem_univ _,rfl⟩))
  rw [pass_vol, pass_vol, ← pair_union _ _ hz, hp]

lemma split (x : Dirac A) (y : Dirac B) : ber (A ⊕ B) (near A B x * far A B y)=ber A x * ber B y := by
  classical
  rw [← write x, ← write y]
  simp only [map_sum, map_smul, mul_sum,sum_mul]
  -- order here determined by simp
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have hh (s : Finset (Pairs A)) (t : Finset (Pairs B))
      (hn : s ≠ univ ∨ t ≠ univ) :
      ber (A ⊕ B) (near A B (mono s)*far A B (mono t))=0 := by
    have h : s.card ≤ Fintype.card (Pairs A) := card_le_univ s
    have he : t.card ≤ Fintype.card (Pairs B) := card_le_univ t
    apply discarded (layer_mul (pass_layer _ (homogeneous s)) (pass_layer _ (homogeneous t)))
    change Fintype.card (Pairs (A ⊕ B)) ≠ _
    rw [show Fintype.card (Pairs (A ⊕ B)) = Fintype.card (Pairs A)+Fintype.card (Pairs B) by
      simp [Pairs]; omega]
    rintro hq
    rcases hn with hn|hn
    · exact hn (eq_univ_of_card _ (by omega))
    exact hn (eq_univ_of_card _ (by omega))
  have hv (s : Finset (Pairs A)) (t : Finset (Pairs B)) :
      ber (A ⊕ B) (near A B (mono s)*far A B (mono t))=ber A (mono s)*ber B (mono t) := by
    by_cases hs : s = univ
    · subst s; by_cases ht : t = univ
      · subst t
        rw [top_is _ (homogeneous (univ : Finset (Pairs A))), top_is _ (homogeneous (univ : Finset (Pairs B)))]
        simp only [map_smul,smul_mul_assoc,mul_smul_comm,generation,ber_top,smul_eq_mul]; ring
      rw [hh _ _ (Or.inr ht), discarded (homogeneous _) (fun e => ht (eq_univ_of_card _ e.symm)),mul_zero]
    rw [hh _ _ (Or.inl hs), discarded (homogeneous s) (fun e => hs (eq_univ_of_card _ e.symm)),zero_mul]
  simp only [smul_mul_assoc,mul_smul_comm,map_smul,hv,smul_eq_mul]; ring

/-- General test of complementary variables. -/
lemma complementary {C : Type*} [Fintype C] (f : A → C) (g : B → C) (h : Bijective (Sum.elim f g))
    (x : Dirac A) (y : Dirac B) : ber C (pass f x * pass g y)=ber A x * ber B y := by
  let e := Equiv.ofBijective (Sum.elim f g) h
  rw [← split A B x y, ← passed e (near A B x * far A B y), map_mul (pass _)]
  congr 2
  · exact (AlgHom.congr_fun (pass_comp Sum.inl (⇑e)) x).symm
  exact (AlgHom.congr_fun (pass_comp Sum.inr (⇑e)) y).symm

/-- integrate out first set in `A ⊕ B` -/
def marginal : Dirac (A ⊕ B) →ₗ[ℂ] Dirac B := (perfect B).symm.toLinearMap.comp
  ((far A B).toLinearMap.dualMap.comp (pairing (A ⊕ B)))

lemma marginal_test (x : Dirac (A ⊕ B)) (y : Dirac B) :
    ber B (marginal A B x * y) = ber (A ⊕ B) (x * far A B y) := by
  rw [← perfect_apply]
  simp only [marginal,LinearMap.comp_apply,LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; rfl

lemma marginal_full (x : Dirac (A ⊕ B)) : ber B (marginal A B x) = ber (A ⊕ B) x := by simpa using marginal_test A B x 1

lemma margins (x : Dirac A) (y : Dirac B) : marginal A B (near A B x*far A B y) = ber A x • y := by
  apply (perfect B).injective; apply LinearMap.ext; intro z
  rw [perfect_apply, perfect_apply, marginal_test,mul_assoc,← map_mul,split]; simp

lemma pullout (x : Dirac (A ⊕ B)) (y : Dirac B) : marginal A B (x * far A B y) = marginal A B x * y := by
  apply (perfect B).injective; apply LinearMap.ext; intro z
  rw [perfect_apply, perfect_apply, marginal_test, mul_assoc,mul_assoc,marginal_test, map_mul (far A B)]

/-- A joint blade always splits up to sign. -/
lemma split_mono (s : Finset (Pairs (A ⊕ B))) : ∃ i : Finset (Pairs A), ∃ j : Finset (Pairs B),
    mono s = near A B (mono i) * far A B (mono j) ∨ mono s = -(near A B (mono i) * far A B (mono j)) := by
  classical
  let f : Pairs A ↪ Pairs (A ⊕ B) := Embedding.sumMap Embedding.inl Embedding.inl
  let g : Pairs B ↪ Pairs (A ⊕ B) := Embedding.sumMap Embedding.inr Embedding.inr
  let t := univ.filter (fun x => f x ∈ s)
  let u := univ.filter (fun x => g x ∈ s)
  have h : Disjoint (t.map f) (u.map g) := disjoint_left.mpr (by
    intro x hh hu
    obtain ⟨i,-,rfl⟩ := mem_map.mp hh; obtain ⟨j,-,hj⟩ := mem_map.mp hu
    cases i <;> cases j <;> simp [f,g] at hj)
  have hp : (t.map f).disjUnion (u.map g) h = s := by
    ext x; cases x with
    | inl y => cases y <;> simp [t,u,f,g, Pairs]
    | inr y => cases y <;> simp [t,u,f,g, Pairs]
  refine ⟨t,u,?_⟩
  change mono s = embed f (mono t)*embed g (mono u) ∨ mono s = -(embed f (mono t)*embed g (mono u))
  rcases embed_blade f t with hz|hz <;> rcases embed_blade g u with ht|ht <;>
    rcases mono_mul_sign _ _ h with h'|h' <;> simp only [hz,ht,h',hp,neg_mul,mul_neg,neg_neg] <;> tauto

lemma marginal_norm (x : Dirac (A ⊕ B)) : ‖marginal A B x‖ ≤ ‖x‖ := by
  have hs (s : Finset (Pairs (A ⊕ B))) : ‖marginal A B (mono s)‖ ≤ 1 := by
    obtain ⟨i,j,h|h⟩ := split_mono A B s <;> simpa [h, margins,norm_smul] using (price (mono i))
  conv_lhs => rw [← write x, map_sum]
  refine (norm_sum_le _ _).trans ?_; rw [norm_def x]; apply sum_le_sum
  intro s _; rw [map_smul,norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hs s)

@[fun_prop] lemma continuous_marginal : Continuous (marginal A B) :=
  (marginal A B).continuous_of_finiteDimensional

end YM.QCD.Grass
