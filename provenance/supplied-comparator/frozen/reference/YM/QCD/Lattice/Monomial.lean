import YM.QCD.Lattice.Gamma

/-!
# matrices with fibers following one site bijection
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Lat
open Finset Function
open scoped Matrix.Norms.Frobenius BigOperators Topology

variable {X Y Z I J K : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def rides (e : X ≃ Y) (U : X → Matrix I J ℂ) : Matrix (X × I) (Y × J) ℂ :=
  Matrix.of fun i j => if e i.1=j.1 then U i.1 i.2 j.2 else 0

lemma rr (e : X ≃ Y) (U : X → Matrix I J ℂ) i j :
    rides e U i j= if e i.1=j.1 then U i.1 i.2 j.2 else 0 := rfl

lemma adj_ride (e : X ≃ Y) (U : X → Matrix I J ℂ) : (rides e U).conjTranspose =
    rides e.symm (fun y => (U (e.symm y)).conjTranspose) := by
  ext ⟨i,k⟩ ⟨j,l⟩; rw [rr,Matrix.conjTranspose_apply,rr]
  by_cases hv : i=e j
  · subst i; simp
  simp [e.symm_apply_eq, hv, Ne.symm hv]

lemma ride_ad (e : X ≃ X) (U : X → Matrix I I ℂ) : star (rides e U) =
    rides e.symm (fun y => star (U (e.symm y))) := adj_ride ..

lemma ride_mul [Fintype Y] [Fintype J] (e : X ≃ Y) (f : Y ≃ Z)
    (U : X → Matrix I J ℂ) (V : Y → Matrix J K ℂ) : rides e U * rides f V =
    rides (e.trans f) fun x => U x * V (e x) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rw [Matrix.mul_apply,Fintype.sum_prod_type, sum_eq_single (e i)]
  · by_cases hj : f (e i)=j <;> simp [rides,hj, Matrix.mul_apply]
  · rintro b _ h; simp [rides,h.symm]
  simp

lemma ridden [DecidableEq I] : rides (Equiv.refl X) (fun _ => (1:Matrix I I ℂ)) = 1 := by
  ext ⟨i,k⟩ ⟨j,l⟩; by_cases hv : i=j <;> simp [rides, Matrix.one_apply,hv]

lemma unitary_ride [Fintype X] [Fintype I] [DecidableEq I] (e : Equiv.Perm X)
    {U : X → Matrix I I ℂ} (h : ∀ i, U i ∈ unitary _) : rides e U ∈ unitary _ := by
  constructor
  · rw [ride_ad,ride_mul]; simp_rw [Equiv.symm_trans_self, fun i => (h i).1]; exact ridden
  rw [ride_ad,ride_mul]; simp_rw [Equiv.self_trans_symm, Equiv.symm_apply_apply, fun i => (h i).2]; exact ridden

lemma ride_add (e : X ≃ Y) (U V : X → Matrix I J ℂ) : rides e U + rides e V = rides e (U+V) := by
  ext i j; by_cases h : e i.1=j.1 <;> simp [rides,h]
lemma ride_sub (e : X ≃ Y) (U V : X → Matrix I J ℂ) : rides e U - rides e V = rides e (U-V) := by
  ext i j; by_cases h : e i.1=j.1 <;> simp [rides,h]
lemma ride_zero (e : X ≃ Y) : rides e (fun _ => (0: Matrix I J ℂ)) = 0 := by ext; simp [rides]
lemma ride_smul (c : ℂ) (e : X ≃ Y) (U : X → Matrix I J ℂ) : c • rides e U = rides e (c • U) := by
  ext i j; by_cases h : e i.1=j.1 <;> simp [rides,h]

lemma ride_vec [Fintype Y] [Fintype J] (e : X ≃ Y) (U : X → Matrix I J ℂ) (w : Y × J → ℂ) i :
    ((rides e U).mulVec w) i = ((U i.1).mulVec (fun k => w (e i.1,k))) i.2 := by
  simp [Matrix.mulVec,dotProduct,rides,Fintype.sum_prod_type,ite_mul]

@[fun_prop] lemma ride_c [Fintype X] [Fintype Y] [Fintype I] [Fintype J] {S : Type*} [TopologicalSpace S] (f : X ≃ Y) (U : S → X → Matrix I J ℂ)
    (h : ∀ x, Continuous fun z => U z x) : Continuous fun z => rides f (U z) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [rr]; split
  · fun_prop
  exact continuous_const

end YM.QCD.Lat
