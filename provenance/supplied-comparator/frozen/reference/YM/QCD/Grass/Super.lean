import YM.QCD.Grass.Banach
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Parity and complex conjugation for Grassmann variables

The plain dagger here fixes generators. Compose later with Dirac/stencil maps for physical
reflections.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Grass
open Function Module Finset
open scoped BigOperators Topology ComplexConjugate

variable {A : Type*} [Fintype A]

lemma ext_atoms {C : Type*} [Ring C] [Algebra ℂ C] {f g : Alg A →ₐ[ℂ] C}
    (h : ∀ i, f (atom i) = g (atom i)) : f = g := by
  apply ExteriorAlgebra.hom_ext
  ext1 x
  change f (line x)=g (line x)
  rw [line_atoms, map_sum, map_sum]; simp_rw [map_smul, h]

abbrev grade : Alg A →ₐ[ℂ] Alg A := CliffordAlgebra.involute

lemma grade_twice (x : Alg A) : grade (grade x) = x := CliffordAlgebra.involute_involute _
lemma grade_atom (i : A) : grade (atom i) = - atom i := CliffordAlgebra.involute_ι _

/-- Parity as required by reflection tests. -/
def Plus (x : Alg A) : Prop := grade x = x

def Minus (x : Alg A) : Prop := grade x = - x

def Hom (p : Bool) (x : Alg A) : Prop := if p then Minus x else Plus x

lemma line_across (u : Seed A) (x : Alg A) : line u * x = grade x * line u := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => rw [AlgHom.commutes]; exact (Algebra.commutes _ _).symm
  | ι v => rw [show grade (line v) = -(line v) from CliffordAlgebra.involute_ι _]; exact (line_line ..).trans (neg_mul ..).symm
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | mul x y hx hy => rw [map_mul, ← mul_assoc (line u), hx, mul_assoc, hy, mul_assoc]

lemma Plus.central {x : Alg A} (h : Plus x) (y : Alg A) : Commute y x := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap s => exact Algebra.commutes s x
  | ι v => exact line_across v x |>.trans (congrArg (· * line v) h)
  | add x y hx hy => exact hx.add_left hy
  | mul x y hx hy => exact hx.mul_left hy

lemma Minus.slides {x : Alg A} (h : Minus x) (y : Alg A) : y * x = x * grade y := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap s => rw [AlgHom.commutes]; exact Algebra.commutes _ _
  | ι v => rw [show grade (line v) = -(line v) from CliffordAlgebra.involute_ι _,
      line_across v x, (show grade x = _ from h), mul_neg, neg_mul]
  | add y z hy hz => rw [map_add, mul_add,add_mul,hy,hz]
  | mul y z hy hz => rw [map_mul, mul_assoc,hz, ← mul_assoc, hy, mul_assoc]

lemma Hom.swap {x y : Alg A} {p q : Bool} (hx : Hom p x) (hy : Hom q y) :
    y*x = if (p && q) then -(x*y) else x*y := by
  cases p
  · exact Plus.central (x:=x) hx y
  cases q
  · exact (Plus.central (x:=y) hy x).symm
  change y*x = -(x*y); rw [Minus.slides hx, (show grade y = -y from hy), mul_neg]

lemma Hom.mul {x y : Alg A} {p q : Bool} (hx : Hom p x) (hy : Hom q y) :
    Hom (p ^^ q) (x*y) := by
  cases p <;> cases q <;> simp_all [Hom, Plus, Minus]

lemma Hom.smul {x : Alg A} {p : Bool} (hx : Hom p x) (c : ℂ) : Hom p (c • x) := by
  cases p <;> simp_all [Hom, Plus, Minus]

lemma Hom.add {x y : Alg A} {p : Bool} (hx : Hom p x) (hy : Hom p y) : Hom p (x+y) := by
  cases p <;> simp_all [Hom, Plus, Minus,add_comm]

lemma Hom.zero (p) : Hom p (0:Alg A) := by cases p <;> simp [Hom, Plus, Minus]

lemma Hom.sum {p} {ι : Type*} {s : Finset ι} {f : ι → Alg A} (h : ∀ i ∈ s, Hom p (f i)) :
    Hom p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Hom.zero _
  | @insert i s hi ih =>
    rw [sum_insert hi]; exact Hom.add (h _ (mem_insert_self ..))
      (ih (fun k hk => h k (mem_insert_of_mem hk)))

def plus (x : Alg A) := (2:ℂ)⁻¹ • (x+grade x)

def minus (x : Alg A) := (2:ℂ)⁻¹ • (x-grade x)

lemma plus_grade (x : Alg A) : Plus (plus x) := by simp [Plus, plus,add_comm]
lemma minus_grade (x : Alg A) : Minus (minus x) := by
  unfold Minus minus; rw [map_smul,map_sub,grade_twice,← neg_sub,smul_neg]
lemma both (x : Alg A) : plus x + minus x = x := by
  rw [plus,minus,← smul_add,show x+grade x+(x-grade x)=(2:ℂ) • x by rw [two_smul]; abel,
    inv_smul_smul₀ (by norm_num)]

lemma grade_mono (s : Finset A) : grade (mono s) = (-1:ℂ)^s.card • mono s := by
  obtain ⟨f,-,-,he⟩ := expression s
  let l := List.ofFn (thetaBasis A ∘ f)
  have hu : mono s = (l.map fun v => line v).prod := by rw [he]; simp only [l,List.map_ofFn]; rfl
  rw [hu]; exact (CliffordAlgebra.involute_prod_map_ι l).trans (by simp only [l,List.length_ofFn] )

/-! Complex conjugation, not Clifford star. -/

def cc : Alg A →ₛₗ[starRingEnd ℂ] Alg A where
  toFun x := ∑ s, star (coef s x) • mono s
  map_add' x y := by simp only [map_add, star_add, add_smul,sum_add_distrib]
  map_smul' c x := by simp [smul_sum,mul_smul]

@[fun_prop] lemma continuous_cc : Continuous (fun x : Alg A => cc x) := by
  change Continuous (fun x : Alg A => ∑ s, star (coef s x) • mono s)
  fun_prop

@[simp] lemma cc_mono (s : Finset A) : cc (mono s)=mono s := by
  classical
  change ∑ _, _ = _
  rw [sum_eq_single s]
  · simp
  · intro i _ hi; rw [read_other _ _ hi, star_zero, zero_smul]
  simp

@[simp] lemma cc_one : cc (1 : Alg A)=1 := by rw [← mono_empty, cc_mono]
lemma cc_atom (i : A) : cc (atom i) = atom i := by rw [← mono_single, cc_mono]

lemma cc_mul (x y : Alg A) : cc (x*y) = cc x * cc y := by
  rw [← write x, ← write y]; simp only [sum_mul,mul_sum, map_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have hp : cc (mono i * mono j) = mono i * mono j := by
    classical
    by_cases h : Disjoint i j
    · rcases mono_mul_sign i j h with h'|h' <;> rw [h'] <;> simp
    simp only [mono_mul_zero _ _ h,map_zero]
  simp only [smul_mul_assoc,mul_smul_comm,map_smulₛₗ,cc_mono,hp]

@[simp] lemma cc_cc (x : Alg A) : cc (cc x)=x := by
  rw [← write x]; simp

lemma keeps_layers_by_mono {B : Type*} [Fintype B] {σ : ℂ →+* ℂ} (f : Alg A →ₛₗ[σ] Alg B)
    (h : ∀ s, f (mono s) ∈ layer B s.card) {n : ℕ} {x : Alg A} (hx : x ∈ layer A n) : f x ∈ layer B n := by
  rw [← write x,map_sum]; apply Submodule.sum_mem
  intro i _; by_cases he : i.card = n
  · rw [map_smulₛₗ]; exact (layer B _).smul_mem _ (he ▸ h i)
  rw [spectrum hx _ he, zero_smul,map_zero]; exact Submodule.zero_mem _

lemma cc_degree {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) : cc x ∈ layer A n :=
  keeps_layers_by_mono _ (fun s => cc_mono s |>.symm ▸ homogeneous s) hx

abbrev rev : Alg A →ₗ[ℂ] Alg A := CliffordAlgebra.reverse

def dagger : Alg A →ₛₗ[starRingEnd ℂ] Alg A := rev.comp cc

@[fun_prop] lemma continuous_dagger : Continuous (fun x : Alg A => dagger x) :=
  rev.continuous_of_finiteDimensional.comp continuous_cc
lemma dagger_degree {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) : dagger x ∈ layer A n := by
  have he := cc_degree hx
  change rev (cc x) ∈ _
  have hp := Submodule.mem_map_of_mem (f:=rev) he
  rwa [layer, ExteriorAlgebra.exteriorPower, CliffordAlgebra.submodule_map_pow_reverse,
    CliffordAlgebra.ι_range_map_reverse] at hp
lemma dagger_one : dagger (1:Alg A)=1 := by
  unfold dagger; rw [LinearMap.comp_apply, cc_one]; exact CliffordAlgebra.reverse.map_one
lemma dagger_atom (i : A) : dagger (atom i) = atom i := by
  unfold dagger; rw [LinearMap.comp_apply,cc_atom]; exact CliffordAlgebra.reverse_ι _
lemma dagger_mul (x y : Alg A) : dagger (x*y)=dagger y * dagger x := by
  change rev _ = _; rw [cc_mul]; exact CliffordAlgebra.reverse.map_mul ..

lemma dagger_invol (x : Alg A) : dagger (dagger x) = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp [Algebra.algebraMap_eq_smul_one, dagger_one]
  | ι v => rw [line_atoms (A:=A)]; simp [dagger_atom]
  | add x y hx hy => simp [hx,hy]
  | mul x y hx hy => simp [hx,hy,dagger_mul]

lemma dagger_parity (x : Alg A) : grade (dagger x)=dagger (grade x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp [Algebra.algebraMap_eq_smul_one,dagger_one]
  | ι v => rw [line_atoms (A:=A)]; simp [dagger_atom,grade_atom]
  | add x y hx hy => simp [hx,hy]
  | mul x y hx hy => simp [dagger_mul,hx,hy]

lemma dagger_exp (x : Alg A) : dagger (NormedSpace.exp x) = NormedSpace.exp (dagger x) := by
  let f : Alg A →+* (Alg A)ᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (dagger x)
      map_mul' := fun x y => congrArg MulOpposite.op (dagger_mul x y)
      map_one' := congrArg MulOpposite.op dagger_one
      map_add' := fun x y => congrArg MulOpposite.op (map_add _ _ _)
      map_zero' := congrArg MulOpposite.op (map_zero _) }
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact NormedSpace.map_exp f (MulOpposite.continuous_op.comp continuous_dagger) _

end YM.QCD.Grass
