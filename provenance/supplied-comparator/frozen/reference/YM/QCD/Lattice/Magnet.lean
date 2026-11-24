import YM.QCD.Lattice.Coercion

/-!
# Uniform determinant lower patch

Two families of links are confined to fixed open sets, giving magnetic frustration. Avoids any
need for continuity neighborhoods that shrink like inverse volume at a fixed background with a
near-zero longwave mode. Norm convention here l² operator.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Lattice Wilson Function Filter Complex Set WithLp Cost
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace Topology

variable {n : Side}

def cyc : Mat := !![0,1,0;0,0,1;1,0,0]
def peg : Mat := !![1,0,0;0,I,0;0,0,-I]

lemma cyc_u : cyc ∈ unitary Mat := by
  apply Matrix.mem_unitaryGroup_iff.mpr; ext i j; fin_cases i <;> fin_cases j <;>
    simp [cyc,Matrix.mul_apply,Fin.sum_univ_succ]
lemma peg_u : peg ∈ unitary Mat := by
  apply Matrix.mem_unitaryGroup_iff.mpr; ext i j; fin_cases i <;> fin_cases j <;>
    simp [peg,Matrix.mul_apply,Fin.sum_univ_succ]

private lemma cyc_det : cyc.det = 1 := by simp [Matrix.det_fin_three,cyc]
private lemma peg_det : peg.det = 1 := by simp [Matrix.det_fin_three,peg]

def pole := (⟨⟨cyc,cyc_u⟩,cyc_det⟩ : su.El)
def tent := (⟨⟨peg,peg_u⟩,peg_det⟩ : su.El)

private lemma frustrates : IsUnit (touch (cyc*peg-peg*cyc)).det := by
  unfold touch; rw [Matrix.det_kronecker]; apply IsUnit.mul (by simp)
  apply IsUnit.pow; apply isUnit_iff_ne_zero.mpr
  simp [Matrix.det_fin_three,cyc,peg]; norm_num [Complex.ext_iff]

@[fun_prop] lemma touch_cont : Continuous touch := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold touch; rw [show (fun M => _)=_ from rfl] -- try
  simp_rw [Matrix.kroneckerMap_apply]; fun_prop

def curl (x y : su.El × su.El) := touch (colour x.1 * colour x.2 - colour y.2 * colour y.1)

lemma wiggle : ∃ (S T : Set su.El), IsOpen S ∧ IsOpen T ∧ pole ∈ S ∧ tent ∈ T ∧
    ∃ d : ℝ, 0 < d ∧ ∀ v : Vec Fiber, ∀ x ∈ S ×ˢ T, ∀ y ∈ S ×ˢ T, d * ‖v‖ ≤ ‖op (curl x y) v‖ := by
  let o : su.El × su.El := (pole,tent)
  let F : (su.El × su.El) × (su.El × su.El) → Bundle := fun x => curl x.1 x.2
  let L := F (o,o)
  have hL : IsUnit L.det := frustrates
  let c := ‖op (L⁻¹)‖+1
  have hc : 0 < c := by dsimp only [c]; positivity
  let d : ℝ := c⁻¹/2
  have hd : 0 < d := by unfold d; positivity
  have he : Continuous (fun x => ‖L - F x‖) := by unfold F curl; fun_prop
  have hu : {x | ‖L-F x‖ < d} ∈ 𝓝 (o,o) := he.continuousAt (Iio_mem_nhds (by simpa only [show F (o,o)=L from rfl, sub_self,norm_zero]))
  obtain ⟨V,hv,W,hw,h⟩ := mem_nhds_prod_iff.mp hu
  obtain ⟨S,hS,T,hT,H⟩ := mem_nhds_prod_iff.mp (inter_mem hv hw)
  obtain ⟨s,hs,hS,hx⟩ := mem_nhds_iff.mp hS; obtain ⟨t,ht,hT,hy⟩ := mem_nhds_iff.mp hT
  refine ⟨s,t,hS,hT,hx,hy,d,hd,?_⟩
  intro v x hx y hy
  have hB : ‖L-F (x,y)‖ ≤ d := le_of_lt (show _ < _ from h
    ⟨(H (Set.prod_mono hs ht hx)).1, (H (Set.prod_mono hs ht hy)).2⟩)
  have hp : c⁻¹*‖v‖ ≤ ‖op L v‖ := by
    rw [mul_comm,← div_eq_mul_inv]
    refine (div_le_iff₀ hc).2 ?_
    conv_lhs => rw [← show op L⁻¹ (op L v)=v by rw [← mul_apply_eq_comp, ← map_mul,
      Matrix.nonsing_inv_mul _ hL,map_one,one_apply_eq_self]]
    refine ((op L⁻¹).le_opNorm _).trans ?_
    rw [mul_comm _ c]; exact mul_le_mul_of_nonneg_right (by dsimp only [c]; simp) (norm_nonneg _)
  have hq : ‖op L v‖-‖op (F (x,y)) v‖ ≤ d*‖v‖ := by
    refine (norm_sub_norm_le _ _).trans ?_
    have hk := ((op (L-F (x,y))).le_opNorm v).trans (mul_le_mul_of_nonneg_right (show ‖op (L-F (x,y))‖ ≤ d from hB) (norm_nonneg v))
    simpa only [map_sub, ContinuousLinearMap.sub_apply] using hk
  change d*‖v‖ ≤ ‖op (F (x,y)) v‖
  unfold d at *; linarith

section fibers
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def fiber (v : Vec (X × Y)) (x : X) : Vec Y := toLp 2 fun i => v (x,i)

lemma norms (v : Vec (X × Y)) : ‖v‖^2=∑ x, ‖fiber v x‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl

lemma travel_vec (e : Equiv.Perm X) (f : X → Mx Y) (v : Vec (X × Y)) (x : X) :
    fiber (op (rides e f) v) x = op (f x) (fiber v (e x)) := by
  ext i
  exact ride_vec e f v.ofLp (x,i)

lemma orthocost (e : Equiv.Perm X) (f : X → Mx Y) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ x v, d*‖v‖ ≤ ‖op (f x) v‖) (v : Vec (X × Y)) : d*‖v‖ ≤ ‖op (rides e f) v‖ := by
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _),mul_pow,norms v,norms,
    ← Equiv.sum_comp e (fun x => ‖fiber v x‖^2),Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _; rw [travel_vec, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (h _ _) _
end fibers

def aligns (S T : Set su.El) (U : Grid n) :=
    ∀ x : Site n, U (x,0) ∈ S ∧ U (x,1) ∈ T

private lemma knot (t : Site n) (U : Grid n) {S T : Set su.El} (hU : aligns S T U) {d : ℝ} (hd : 0 < d)
    (h : ∀ v : Vec Fiber, ∀ x ∈ S ×ˢ T, ∀ y ∈ S ×ˢ T, d * ‖v‖ ≤ ‖op (curl x y) v‖) (v : Vec (Row n)) :
    d*‖v‖ ≤ ‖op (shift t U 0*shift t U 1-shift t U 1*shift t U 0) v‖ := by
  simp_rw [shift, ride_mul,touch_mul]
  rw [show (forward (n:=n) 1).trans (forward 0)=(forward 0).trans (forward 1) by ext1 x; simp [add_right_comm], ride_sub]; apply orthocost _ _ _ hd.le
  intro x b
  change _ ≤ ‖op (touch (thread t U 0 x * thread t U 1 (forward 0 x)) - touch (thread t U 1 x * thread t U 0 (forward 1 x))) b‖ -- check ride_mul already touch: diff touch minus, not touch diff
  have ha := h b (U (x,0), U (x+step 0,1)) ⟨(hU _).1, (hU _).2⟩ (U (x+step 1,0), U (x,1))
    ⟨(hU _).1,(hU _).2⟩
  simp_rw [hop, thread,seam_across _ _ (by decide : (1:Axis) ≠ 0),seam_across _ _ (by decide : (0:Axis) ≠ 1),
    Matrix.smul_mul,Matrix.mul_smul,touch, Matrix.kronecker_smul, smul_smul,mul_comm (seam t x 1) (seam t x 0), ← smul_sub]
  have negTouch (X Y : Mat) : touch X-touch Y = touch (X-Y) := by ext ⟨i,j⟩ ⟨k,l⟩; simp [touch,mul_sub]
  rcases seam_cases t x 0 with h|h <;> rcases seam_cases t x 1 with he|he <;>
    simp only [h,he,mul_one,one_mul,neg_mul_neg, one_smul,neg_smul, map_neg,ContinuousLinearMap.neg_apply,norm_neg] <;>
    change _ ≤ ‖op (touch _ - touch _) _‖ <;> rw [negTouch] <;> exact ha

lemma displacement (t : Site n) (U : Grid n) (v : Vec (Row n)) (a b : Axis) :
    ‖op (shift t U a * shift t U b) v - v‖ ≤ ‖diff t U b v‖ + ‖diff t U a v‖ := by
  let x := op (shift t U a); let y := op (shift t U b)
  have h i : ‖op (shift t U i) v - v‖ = ‖diff t U i v‖ := by simp [diff,norm_sub_rev]
  rw [← h a, ← h b, map_mul,mul_apply_eq_comp,show x (y v)-v=x (y v-v)+(x v-v) by rw [map_sub]; abel]
  exact (norm_add_le _ _).trans (by rw [show ‖x (y v-v)‖=‖y v-v‖ from Cost.unitary_moves _ (shift_u ..) _])

lemma squeezed (t : Site n) (U : Grid n) {d : ℝ} (hd : 0 ≤ d) (v : Vec (Row n))
    (h : d*‖v‖ ≤ ‖op (shift t U 0*shift t U 1-shift t U 1*shift t U 0) v‖) :
    (d^2 / 16)*‖v‖^2 ≤ ∑ a : Axis, ‖diff t U a v‖^2/2 := by
  let X := op (shift t U 0*shift t U 1) v; let Y := op (shift t U 1*shift t U 0) v
  let b := fun a => ‖diff t U a v‖
  rw [map_sub,ContinuousLinearMap.sub_apply,show X-Y=(X-v)-(Y-v) by abel] at h
  have he : d * ‖v‖ ≤ (b 1+b 0)+(b 0+b 1) :=
    h.trans ((norm_sub_le _ _).trans (add_le_add (displacement ..) (displacement ..)))
  have hp : (d^2 / 16)*‖v‖^2 ≤ b 0^2/2+b 1^2/2 := by
    have hk := pow_le_pow_left₀ (show 0≤d*‖v‖ from by positivity) he 2
    rw [mul_pow] at hk; nlinarith [sq_nonneg (b 1-b 0)]
  refine hp.trans ?_
  let s : Finset Axis := {0,1}
  have hj : b 0^2/2+b 1^2/2=∑ i∈s,b i^2/2 := by simp [s]
  rw [hj]; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => by positivity)

/-- a *common*, positive-measure per link witness (sign and magnitude retained) -/
theorem patch : ∃ (S T : Set su.El), IsOpen S ∧ IsOpen T ∧ pole ∈ S ∧ tent ∈ T ∧ ∃ c : ℝ, 0<c ∧
    ∀ (n : Side) (t : Site n) (m : ℝ), -c ≤ m → ∀ U : Grid n, aligns S T U →
      Cost.Floor c (bareD t U m) ∧ c ^ Fintype.card (Row n) ≤ (bareD t U m).det.re := by
  obtain ⟨S,T,hS,hT,hs,ht,d,hd,H⟩ := wiggle
  let c := d^2/32
  have hc : 0<c := by unfold c; positivity
  refine ⟨S,T,hS,hT,hs,ht,c,hc,?_⟩; intro n t m hm U hU
  have he : Cost.Floor c (bareD t U m) := by
    intro v; rw [realpart]
    have hb := squeezed t U hd.le v (knot t U hU hd H v)
    have hy := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖v‖)
    unfold c at *; linarith
  have hp := det_pos chi_sq (gamma5 ..) hc he
  have hh := Cost.min_det c hc.le he.price
  nth_rw 1 [← realD t U m] at hh; simpa [abs_of_nonneg hp.le,he] using And.intro he hh

end YM.QCD.Lat
