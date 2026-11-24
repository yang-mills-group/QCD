import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Complex exterior algebra of a finite set of fermion variables

Order doesn't need to be provided; fix a blade orientation internally (thus a norm too).
Berezin uses its own normalizations; don't take Clifford algebra `star` for complex or reflected
adjoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Module Finset Function
open scoped BigOperators ComplexConjugate Topology ContDiff

abbrev Seed (A : Type*) := A → ℂ
abbrev Alg (A : Type*) := ExteriorAlgebra ℂ (Seed A)

variable {A : Type*} [Fintype A]

abbrev line := ExteriorAlgebra.ι ℂ (M := Seed A)
abbrev thetaBasis (A : Type*) [Fintype A] : Basis A ℂ (Seed A) := Pi.basisFun ..

/-- one generator per variable -/
def atom (i : A) := line (thetaBasis A i)

omit [Fintype A] in
lemma line_line (x y : Seed A) : line x * line y = -(line y * line x) := by
  apply eq_neg_of_add_eq_zero_left
  exact ExteriorAlgebra.ι_add_mul_swap x y

omit [Fintype A] in
lemma line_square (x : Seed A) : line x * line x = 0 := ExteriorAlgebra.ι_sq_zero _
lemma atom_flip (i j : A) : atom i * atom j = -(atom j * atom i) := line_line ..
@[simp] lemma atom_square (i : A) : atom i * atom i = 0 := line_square _

/-- Homogeneous degree submodule. -/
abbrev layer (A : Type*) (n : ℕ) := ExteriorAlgebra.exteriorPower ℂ n (Seed A)

lemma atom_mem (i : A) : atom i ∈ layer A 1 := by unfold atom layer ExteriorAlgebra.exteriorPower; rw [pow_one]; exact LinearMap.mem_range_self ..

omit [Fintype A] in
lemma layer_mul {n m : ℕ} {x y : Alg A} (hx : x ∈ layer A n) (hy : y ∈ layer A m) : x*y ∈ layer A (n+m) := by
  unfold layer ExteriorAlgebra.exteriorPower; rw [pow_add]; exact Submodule.mul_mem_mul hx hy

-- orientation (order not used on the wire)
variable (A)
@[implicit_reducible] def orientation : LinearOrder A := by classical exact linearOrderOfSTO WellOrderingRel

def blades : Basis (Finset A) ℂ (Alg A) :=
  letI := orientation A
  (thetaBasis A).ExteriorAlgebra

variable {A}
def mono (s : Finset A) : Alg A := blades A s

def coef (s : Finset A) : Alg A →ₗ[ℂ] ℂ := (blades A).coord s

@[simp] lemma read (s : Finset A) : coef s (mono s) = 1 := by classical simp [coef, mono]
lemma read_other (s t : Finset A) (h : s ≠ t) : coef s (mono t) = 0 := by
  classical simp [coef, mono,h]

lemma write (x : Alg A) : ∑ s, coef s x • mono s = x := (blades A).sum_repr x

@[simp] lemma mono_empty : mono (∅ : Finset A) = 1 := by
  letI := orientation A
  change (thetaBasis A).ExteriorAlgebra _ = _
  rw [ExteriorAlgebra.basis_apply]; exact ExteriorAlgebra.ιMulti_zero_apply ..

lemma homogeneous (s : Finset A) : mono s ∈ layer A s.card := by
  letI := orientation A
  change (thetaBasis A).ExteriorAlgebra _ ∈ _
  rw [ExteriorAlgebra.basis_apply]; exact ExteriorAlgebra.ιMulti_range ℂ _ ⟨_, rfl⟩

lemma expression (s : Finset A) :
    ∃ f : Fin s.card → A, Injective f ∧ (∀ i, i ∈ s ↔ i ∈ Set.range f) ∧
      mono s = (List.ofFn (atom ∘ f)).prod := by
  letI := orientation A
  let q := Set.powersetCard.ofCard (s := s) rfl
  let f : Fin s.card ↪o A := Set.powersetCard.ofFinEmbEquiv.symm q
  refine ⟨f, f.injective, fun i => (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem q i).symm, ?_⟩
  change (thetaBasis A).ExteriorAlgebra _ = _
  rw [ExteriorAlgebra.basis_apply_ofCard (thetaBasis A) (show s.card = s.card from rfl)]
  rfl

@[simp] lemma mono_single (a : A) : mono {a} = atom a := by
  obtain ⟨f,-,h,e⟩ := expression ({a} : Finset A)
  have hz : ∀ i, f i = a := fun i => mem_singleton.mp ((h _).mpr ⟨i, rfl⟩)
  rw [e,show atom ∘ f = fun _ => atom a from funext fun i => by simp [hz]]
  simp

lemma mono_mul_zero (s t : Finset A) (h : ¬ Disjoint s t) : mono s * mono t = 0 := by
  letI := orientation A
  exact ExteriorAlgebra.basis_mul_of_not_disjoint (thetaBasis A) (Set.powersetCard.ofCard (s := s) rfl)
    (Set.powersetCard.ofCard (s := t) rfl) h

/-- use existential sign to hide the internal order -/
lemma mono_mul_sign (s t : Finset A) (h : Disjoint s t) :
    mono s * mono t = mono (s.disjUnion t h) ∨ mono s * mono t = -mono (s.disjUnion t h) := by
  letI := orientation A
  let u := Set.powersetCard.ofCard (s := s) rfl
  let v := Set.powersetCard.ofCard (s := t) rfl
  have hv : Disjoint u.val v.val := h
  let e := Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hv)
  have he : mono s * mono t = e • mono (s.disjUnion t h) :=
    ExteriorAlgebra.basis_mul_of_disjoint (thetaBasis A) u v hv
  rcases Int.units_eq_one_or e with hp | hp <;> simp [he,hp]

lemma spectrum {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) (s : Finset A) (h : s.card ≠ n) : coef s x = 0 := by
  letI := orientation A
  let b := (thetaBasis A).exteriorPower n
  let φ := (layer A n).subtype
  let y : layer A n := ⟨x,hx⟩
  change coef s (φ y) = 0
  conv_lhs => rw [← b.sum_repr y, map_sum, map_sum]
  apply sum_eq_zero; intro i _
  simp only [map_smul]
  have he : φ (b i) = mono i.val := (ExteriorAlgebra.basis_eq_coe_basis (thetaBasis A) i).symm
  rw [he,read_other s _ (fun he => h (he ▸ i.property)), smul_zero]

lemma overflow {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) (h : Fintype.card A < n) : x = 0 := by
  rw [← write x]; exact sum_eq_zero fun s _ => by rw [spectrum hx _ (lt_of_le_of_lt (card_le_univ s) h).ne, zero_smul]

lemma ceiling {x : Alg A} (hx : x ∈ layer A (Fintype.card A)) : x = coef univ x • mono univ := by
  classical
  conv_lhs => rw [← write x, sum_eq_single univ (fun t _ ht => by
    rw [spectrum hx t (fun e => ht (eq_univ_of_card t e)), zero_smul]) (by simp)]

/-- All elements are sums of generator terms. -/
lemma line_atoms (x : Seed A) : line x = ∑ i, x i • atom i := by
  conv_lhs => rw [← (thetaBasis A).sum_repr x, map_sum]
  simp_rw [map_smul]; exact sum_congr rfl fun i _ => by simp [thetaBasis,atom]

instance (A : Type*) [Fintype A] : FiniteDimensional ℂ (Alg A) := Module.Finite.of_basis (blades _)

end YM.QCD.Grass
