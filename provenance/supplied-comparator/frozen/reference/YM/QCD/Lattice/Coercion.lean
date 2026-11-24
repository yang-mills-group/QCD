import YM.QCD.Estimate.Accretive
import YM.QCD.Lattice.Stencil

/-! # Wilson real part and norm bounds

Euclidean operator norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Lattice Wilson Cost Finset
open scoped Matrix.Norms.L2Operator BigOperators Topology

variable {n : Side}

def diff (t : Site n) (U : Grid n) (a : Axis) (x : Vec (Row n)) := op (1-shift t U a) x

lemma diff_cost (t : Site n) (U : Grid n) (a : Axis) (x : Vec (Row n)) :
    Cost.form (1-singleHop t U a) x = ‖diff t U a x‖^2 / 2 := by
  have he : (1-singleHop t U a)+star (1-singleHop t U a)=star (1-shift t U a)*(1-shift t U a) := by
    have hp : singleHop t U a+star (singleHop t U a)=shift t U a+star (shift t U a) := by
      rw [advance_star,singleHop]; set l := onSpin n (lo a); set h := onSpin n (hi a); set s := shift t U a
      rw [show l*s + h*star s + (l*star s+h*s)=(l+h)*s+(l+h)*star s by rw [add_mul,add_mul]; abel,
        show l+h=1 from (on_spin_add ..).trans (by rw [projectors,on_spin_one]),one_mul,one_mul]
    have hv := (shift_u t U a).1
    rw [star_sub,star_sub,star_one,sub_mul,one_mul,mul_sub,mul_one,hv]
    rw [show 1-singleHop t U a+(1-star (singleHop t U a))=1+1-(singleHop t U a+star (singleHop t U a)) by abel, hp]; abel
  have h := Cost.square (1-shift t U a) x
  rw [← he,Cost.add_form,Cost.star_form] at h; unfold diff; linarith

lemma realpart (t : Site n) (U : Grid n) (m : ℝ) (x : Vec (Row n)) :
    Cost.form (bareD t U m) x = m * ‖x‖^2 + ∑ a : Axis, ‖diff t U a x‖^2 / 2 := by
  rw [bareD, Cost.add_form, Cost.real_form, Cost.identity]
  congr 1
  suffices ∀ s : Finset Axis, Cost.form (∑ a ∈ s, (1-singleHop t U a)) x=∑ a∈s, ‖diff t U a x‖^2/2 from this _
  intro s; induction s using Finset.induction_on with
  | empty => simp [Cost.form]
  | insert i s hi ih => rw [sum_insert hi,sum_insert hi,Cost.add_form,diff_cost,ih]

lemma level (t : Site n) (U : Grid n) (m : ℝ) : Cost.Floor m (bareD t U m) :=
  fun x => by rw [realpart]; exact le_add_of_nonneg_right (sum_nonneg fun _ _ => by positivity)

lemma realD (t : Site n) (U : Grid n) (m : ℝ) : ((bareD t U m).det.re : ℂ)=(bareD t U m).det :=
  Cost.determinant_real chi_sq (gamma5 ..)
lemma det_sign (t : Site n) (U : Grid n) {m : ℝ} (hm : 0 ≤ m) : 0 ≤ (bareD t U m).det.re :=
  Cost.det_closed chi_sq (gamma5 ..) ((level t U _).lower hm)
lemma det_strict (t : Site n) (U : Grid n) {m : ℝ} (hm : 0 < m) : 0 < (bareD t U m).det.re :=
  Cost.det_pos chi_sq (gamma5 ..) hm (level t U _)

lemma rotation_price {I : Type*} [Fintype I] [DecidableEq I] {V : Mx I} (h : V ∈ unitary _) : ‖V‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def]
  exact (op V).opNorm_le_bound (by norm_num) fun x => by rw [one_mul]; exact le_of_eq (unitary_moves _ h x)

lemma bare_size (t : Site n) (U : Grid n) (m : ℝ) : ‖bareD t U m‖ ≤ |m| + 8 := by
  have hone : ‖(1 : Sheet n)‖ ≤ 1 := rotation_price (Submonoid.one_mem _)
  have hs (a : Axis) : ‖1-singleHop t U a‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [rotation_price (hop_u t U a)])
  unfold bareD; refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans ?_))
  · rw [norm_smul]; simp only [Complex.norm_real,Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg _) hone
  exact (sum_le_sum fun a _ => hs a).trans (le_of_eq (by simp [Axis]; ring))

lemma det_upper (t : Site n) (U : Grid n) (m : ℝ) : ‖(bareD t U m).det‖ ≤ (|m| + 8) ^ Fintype.card (Row n) :=
  Cost.max_det _ (fun x => ((op (bareD t U m)).le_opNorm x).trans (by rw [← Matrix.cstar_norm_def]; gcongr; exact bare_size ..)) (by positivity)

end YM.QCD.Lat
