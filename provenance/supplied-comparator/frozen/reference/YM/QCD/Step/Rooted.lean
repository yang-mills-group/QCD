import YM.QCD.Step.Bale

/-! # coercivity after fermionic block mass, all fields (rough bound in L) -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Lat Lattice Cost Wilson Function Finset WithLp ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Matrix Topology InnerProductSpace
variable {c f : Side} (r : Ratio c f)

def reach (L : Side) := 4 * L.val
lemma covers (L : Side) (o : Lattice.Order) (j : Site L) : (route 0 (lift j) o).length ≤ reach L := by
  have he (l : List Axis) : (axisRoute 0 (lift j) l).length ≤ l.length*L.val := by
    induction l with
    | nil => simp [axisRoute]
    | cons i l ih =>
      have ht := lift_centers j i
      change List.length (straight i _ ++ axisRoute _ _ l) ≤ _
      simp only [List.length_append,straight, List.length_replicate, Pi.zero_apply, sub_zero,
        List.length_cons, Nat.add_mul,Nat.one_mul]; omega
  simpa [route,reach,allAxes] using he (allAxes o)

def yieldL (L : Side) := scale L*Fintype.card (Site L)
lemma yield_pos (L) : 0<yieldL L := mul_pos (scale_pos _) (by positivity)

def paint := (yieldL r.count:ℂ) • scoop r
lemma painter : paint r=(scale r.count:ℂ) • ∑ _ : Site r.count, scoop r := by
  rw [paint,yieldL,Complex.ofReal_mul,Complex.ofReal_natCast,sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
lemma painter_Q : paint r=(votes:ℂ)⁻¹ • ∑ _ : Lattice.Order, paint r := by
  rw [sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast poll_pos.ne'),one_smul]

lemma mismatch (t : Site f) (U : Grid f) (o : Lattice.Order) (j : Site r.count) (x : Vec (Row f)) :
    ‖lead (stripe r t U o j - scoop r) x‖ ≤ reach r.count * estate t U x := by
  rw [map_sub,sub_apply,stripe,lead_act,← map_sub,lead_op]
  refine (leanBound _ _).trans ?_; rw [price_scoop,one_mul]
  exact (walk_budget ..).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast covers r.count o j) (Real.sqrt_nonneg _))

lemma varying (t : Site f) (U : Grid f) (o) (x : Vec (Row f)) :
    ‖lead (vane r t U o-paint r) x‖ ≤ yieldL r.count * (reach r.count*estate t U x) := by
  rw [painter,vane, ← smul_sub, ← sum_sub_distrib,map_smul, ContinuousLinearMap.smul_apply,map_sum,_root_.sum_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (scale_pos _).le]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => mismatch r t U o i x)) (scale_pos _).le).trans ?_
  simp only [sum_const,card_univ, nsmul_eq_mul, yieldL,mul_assoc,le_refl]
lemma exceeds (t : Site f) (U : Grid f) (x) : ‖lead (Q r t U-paint r) x‖ ≤ yieldL r.count * (reach r.count*estate t U x) := by
  conv_lhs => rw [painter_Q, Q, ← smul_sub, ← sum_sub_distrib]
  rw [map_smul, ContinuousLinearMap.smul_apply,map_sum,_root_.sum_apply,norm_smul,norm_inv,Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => varying r t U i x)) (by positivity)).trans (le_of_eq ?_)
  rw [sum_const,card_univ, nsmul_eq_mul, ← mul_assoc,inv_mul_cancel₀ poll_pos.ne',one_mul]
lemma lengthen (t : Site f) (U : Grid f) (x) :
    ‖lead (scoop r) x‖ ≤ (yieldL r.count)⁻¹*‖lead (Q r t U) x‖+reach r.count*estate t U x := by
  have he := exceeds r t U x
  rw [map_sub,sub_apply,norm_sub_rev] at he
  have hu := (norm_sub_norm_le _ _).trans he
  rw [paint,map_smul,ContinuousLinearMap.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (yield_pos _).le] at hu
  apply le_of_mul_le_mul_left _ (yield_pos r.count); rw [mul_add,← mul_assoc, mul_inv_cancel₀ (yield_pos _).ne',one_mul]
  exact sub_le_iff_le_add'.mp hu

lemma tranches (t : Site f) (U : Grid f) (x) :
    ‖x‖ ≤ (r.count.val:ℝ)^2 * ((yieldL r.count)⁻¹ * ‖lead (Q r t U) x‖ + 2*(reach r.count*estate t U x)) := by
  let q := (yieldL r.count)⁻¹ * ‖lead (Q r t U) x‖; have hq : 0≤q := by unfold q; have := yield_pos r.count; positivity
  let b := reach r.count*estate t U x; have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have he (j : Site r.count) : ‖lead (stripe r t U 1 j) x‖ ≤ q+2*b := by
    have hv := mismatch r t U 1 j x
    rw [map_sub,sub_apply] at hv
    have hh := (norm_sub_norm_le _ _).trans hv
    have ht : ‖lead (scoop r) x‖ ≤ q+b := lengthen r t U x
    change _ ≤ b at hh; linarith
  rw [← sq_le_sq₀ (by positivity) (show 0 ≤ (r.count.val:ℝ)^2 * (q+2*b) from by positivity), ← concurs r t U 1]
  exact (sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (he j) _).trans (le_of_eq (by rw [sum_const,card_univ, nsmul_eq_mul,site_card]; push_cast; ring))

def hefty (b : ℝ) (t : Site f) (U : Grid f) (m : ℝ) := bareD t U m+(b:ℂ) • ((Q r t U)ᴴ*(Q r t U))
def drag (L : Side) := (L.val:ℝ)^2 * (yieldL L)⁻¹
def grin (L : Side) := (L.val:ℝ)^2 * (2 * reach L)
def fixCost (b : ℝ) (L : Side) := 2*drag L^2 / b + 4*grin L^2 + 1
def fraction (b : ℝ) (L : Side) := (fixCost b L)⁻¹
lemma fix_pos {b : ℝ} (h : 0<b) (L : Side) : 0 < fixCost b L := by unfold fixCost; positivity
lemma frac_pos {b : ℝ} (h : 0<b) (L : Side) : 0 < fraction b L := inv_pos.mpr (fix_pos h _)

lemma gradient (t : Site f) (U : Grid f) b m (x : Vec (Row f)) :
    form (hefty r b t U m) x = m*‖x‖^2+ (estate t U x^2/2 + b*‖lead (Q r t U) x‖^2) := by
  rw [hefty,add_form,real_form,realpart,cross_square,← add_assoc]; congr 2
  rw [estate,Real.sq_sqrt (by positivity),sum_div]
lemma cushions {b : ℝ} (h : 0<b) (t : Site f) (U : Grid f) (m : ℝ) :
    Floor (m+fraction b r.count) (hefty r b t U m) := by
  let L := r.count; let E := fixCost b L
  have hp : 0<E := fix_pos h _
  intro x
  let q := ‖lead (Q r t U) x‖; let G := estate t U x
  have hx : ‖x‖ ≤ drag L*q+grin L*G := (tranches ..).trans (le_of_eq (by unfold drag grin q G L; ring))
  have hv := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hk : 2*drag L^2 ≤ E*b := by unfold E fixCost; field_simp; nlinarith [sq_nonneg (grin L)] -- check
  have ht : 2*grin L^2 ≤ E/2 := by unfold E fixCost; nlinarith [show 0≤2 * drag L ^ 2 / b by positivity]
  rw [gradient,add_mul,add_le_add_iff_left, fraction,mul_comm E⁻¹, ← div_eq_mul_inv, div_le_iff₀ hp]
  change ‖x‖^2 ≤ (G^2/2+b*q^2)*E
  nlinarith only [hv,mul_le_mul_of_nonneg_right hk (sq_nonneg q),mul_le_mul_of_nonneg_right ht (sq_nonneg G),sq_nonneg (drag L*q-grin L*G)]

lemma hBound {b : ℝ} (h : 0≤b) (t : Site f) (U : Grid f) m :
    ‖hefty r b t U m‖ ≤ |m|+8 + b*slope r.count^2 := by
  unfold hefty; apply (norm_add_le ..).trans (add_le_add (bare_size ..) _)
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg h, Matrix.l2_opNorm_conjTranspose_mul_self, ← sq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (votes_cost ..) _) h
@[fun_prop] lemma continuous_hefty {b m : ℝ} {t : Site f} : Continuous fun U => hefty r b t U m := by unfold hefty; fun_prop
end YM.QCD.Kit
