import YM.QCD.Lattice.Cut
import YM.QCD.Estimate.Charts
import YM.Lattice.Route
import YM.Lattice.Subdivision

/-! # root paths for covariant blocking, arbitrary background -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Lat Lattice Cost Wilson Function Finset WithLp
open scoped Matrix.Norms.L2Operator BigOperators Topology
variable {c f : Side}

def leg (t : Site f) (U : Grid f) (a : Step) := if a.neg then star (shift t U a.dir) else shift t U a.dir
def routeM (t : Site f) (U : Grid f) (w : Walk) : Sheet f := (w.map (leg t U)).prod
lemma leg_u (t : Site f) (U : Grid f) (a : Step) : leg t U a ∈ unitary _ := by
  unfold leg; split
  · exact ⟨by rw [star_star]; exact (shift_u ..).2, by rw [star_star]; exact (shift_u ..).1⟩
  exact shift_u ..
lemma circle (t : Site f) (U : Grid f) (w : Walk) : routeM t U w ∈ unitary _ := by
  induction w with
  | nil => simpa [routeM] using Submonoid.one_mem (unitary (Sheet f))
  | cons a w ih => exact Submonoid.mul_mem _ (leg_u t U a) ih
lemma appendM (t : Site f) (U : Grid f) (w z) : routeM t U (w++z)=routeM t U w*routeM t U z := by simp [routeM]
lemma gaugeLeg (t : Site f) (U : Grid f) (k : Frame f) (a : Step) :
    leg t (gauge k U) a=siteRot k*leg t U a*star (siteRot k) := by
  unfold leg; split <;> rw [site_transform]; simp [mul_assoc]
lemma gaugeM (t : Site f) (U : Grid f) (k : Frame f) (w) :
    routeM t (gauge k U) w=siteRot k*routeM t U w*star (siteRot k) := by
  induction w with
  | nil => simp [routeM,(siteRot_u k).2]
  | cons a w ih =>
    change leg t _ a * routeM t (gauge k U) w=siteRot k*(leg t _ a * routeM t U w)*star (siteRot k)
    rw [gaugeLeg,ih, ← mul_assoc, ← mul_assoc (_ * star _) (siteRot k), mul_assoc (_ * _) (star _), (siteRot_u k).1, mul_one, mul_assoc (siteRot k) (leg t U a)] -- check
lemma spinLeg (t : Site f) (U : Grid f) (X : Spike) (a : Step) : Commute (leg t U a) (onSpin f X) := by
  unfold leg; split; exact back_spin ..; exact shift_spin .. -- semicolon
lemma spinM (t : Site f) (U : Grid f) (X : Spike) (w) : Commute (routeM t U w) (onSpin f X) := by
  induction w
  · exact Commute.one_left _
  next a w ih => exact (spinLeg t U X a).mul_left ih

lemma stop_plus (x y : Site f) (w) : stop (x+y) w=x+stop y w := by
  induction w generalizing y <;> simp_all [stop,add_assoc]
lemma terminal (w) (a : Cover) : stop (wrap f a) w=wrap f (stop a w) := by
  induction w generalizing a
  · rfl
  next d w ih => rw [stop,stop,← wrap_vec f,← map_add, ih]
lemma wrap_stop (x : Site f) (w : Walk) : stop x w=x+wrap f (stop 0 w) := by
  nth_rw 1 [← add_zero x,← (wrap f).map_zero]; rw [stop_plus, terminal]
lemma block_stop (r : Ratio c f) (x : Site c) (y : Site r.count) (o) : stop (r.embed x) (route 0 (lift y) o)=r.assemble (x,y) := by rw [wrap_stop,route_end]; rfl

lemma travel_data (t : Site f) (U : Grid f) (w) : ∃ (e : Equiv.Perm (Site f)) (D : Site f → Bundle),
    (∀ x : Site f, e x = stop x w) ∧ routeM t U w=rides e D ∧ ∀ x, D x ∈ unitary _ := by
  induction w with
  | nil => exact ⟨Equiv.refl _,fun _ => 1, fun _ => rfl,ridden.symm, fun _ => Submonoid.one_mem _⟩
  | cons a w ih =>
    obtain ⟨e,D,hg,hs,h⟩ := ih
    change ∃ _ _, _ ∧ leg t U a * routeM t U w=_ ∧ _
    rcases a with ⟨i,_|_⟩
    · simp only [leg,Bool.false_eq_true,if_false,shift,hs,ride_mul]
      exact ⟨_,_,fun x => hg _, rfl, fun x => Submonoid.mul_mem _ (touch_u (thread_u ..)) (h _)⟩
    simp only [leg, if_true, opp,hs,ride_mul]; refine ⟨_,_,fun x => ?_, rfl, fun x => Submonoid.mul_mem _ ?_ (h _)⟩
    · rw [Equiv.trans_apply,hg,back,sub_eq_add_neg]; rfl
    rw [← touch_star]; exact Unitary.star_mem (touch_u (thread_u ..)) -- check

lemma leg_travels (t : Site f) (U : Grid f) (x : Vec (Row f)) (a : Step) : ‖op (leg t U a) x-x‖=‖diff t U a.dir x‖ := by
  unfold leg; split
  · calc
      _ = ‖op (shift t U a.dir) (op (star (shift t U a.dir)) x-x)‖ := (unitary_moves _ (shift_u ..) _).symm
      _ = _ := by rw [map_sub,← mul_apply_eq_comp,← map_mul,(shift_u ..).2, map_one,one_apply_eq_self]; simp [diff]
  simp [diff, norm_sub_rev]

def estate (t : Site f) (U : Grid f) (x : Vec (Row f)) := Real.sqrt (∑ i, ‖diff t U i x‖^2)
lemma dividends (t : Site f) (U : Grid f) (x : Vec (Row f)) (i) : ‖diff t U i x‖ ≤ estate t U x := by
  rw [estate, ← sq_le_sq₀ (norm_nonneg _) (by positivity), Real.sq_sqrt (by positivity)]
  exact single_le_sum (fun a _ => sq_nonneg ‖diff t U a x‖) (mem_univ i)
lemma walk_budget (t : Site f) (U : Grid f) (x : Vec (Row f)) (w : Walk) :
    ‖op (routeM t U w) x-x‖ ≤ (w.length:ℝ)*estate t U x := by
  induction w with
  | nil => simp [routeM]
  | cons a w ih =>
    set X := op (leg t U a); set Y := op (routeM t U w)
    rw [show routeM _ _ _=leg t U a * routeM t U w from rfl,map_mul, mul_apply_eq_comp]
    rw [show X (Y x)-x=X (Y x-x)+(X x-x) by rw [map_sub]; abel]
    exact (norm_add_le _ _).trans ((add_le_add (unitary_moves _ (leg_u ..) _ |>.le.trans ih) ((leg_travels t U x a).le.trans (dividends ..))).trans (le_of_eq (by simp [add_mul])))
@[fun_prop] lemma continuous_route (t : Site f) (w) : Continuous (fun U : Grid f => routeM t U w) := by
  induction w with
  | nil => exact continuous_const
  | cons a w ih =>
    change Continuous (fun U => leg t U a*routeM t U w); apply Continuous.mul _ ih
    unfold leg; split <;> fun_prop
end YM.QCD.Kit
