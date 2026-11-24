import YM.QCD.Step.Trail

/-!
# analytic estimates with both link sockets in the tube

Crude block constants here: fixed-L estimate only. Not tending L to infinity in these.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Finset Function Filter Lat Wilson Lattice Cost
open scoped Matrix Matrix.Norms.L2Operator Topology BigOperators ContDiff
variable {c f : Side}
section
abbrev Tray (f : Side) := Edge (Site f) → Mat
/-- No unitarity, transpose or determinant conditions -/
abbrev Pulse (f : Side) := Tray f×Tray f
def settled (U : Grid f) : Pulse f := (colour ∘ U, fun a => star (colour (U a)))
lemma load (P : Pulse f) i (B : Pulse f) : ‖P.1 i-B.1 i‖ ≤ ‖P-B‖ ∧ ‖P.2 i-B.2 i‖ ≤ ‖P-B‖ :=
  ⟨(show ‖(P-B).1 i‖ ≤ _ from (norm_le_pi_norm (P-B).1 i).trans (norm_fst_le _)),
   (show ‖(P-B).2 i‖ ≤ _ from (norm_le_pi_norm (P-B).2 i).trans (norm_snd_le _))⟩ -- maybe `(P-B)` elaboration

def TouchL : Mat →L[ℂ] Bundle := LinearMap.toContinuousLinearMap {
   toFun := touch
   map_add' := fun a b => (touch_add a b).symm
   map_smul' := fun a b => Matrix.kronecker_smul .. }
def sail (t : Site f) (a : Axis) : Pulse f →ₗ[ℂ] Sheet f where
   toFun P := rides (forward a) (fun i => seam t i a • TouchL (P.1 (i,a)))
   map_add' x y := by rw [ride_add]; simp [smul_add, Pi.add_def]
   map_smul' p x := by rw [RingHom.id_apply,ride_smul]; simp [Pi.smul_def]; congr 1; funext i; rw [smul_comm]
def tread (t : Site f) (a : Axis) : Pulse f→ₗ[ℂ] Sheet f where
   toFun P := rides (forward a).symm (fun i => let x := i-step a; seam t x a • TouchL (P.2 (x,a)))
   map_add' x y := by rw [ride_add]; simp [smul_add, Pi.add_def]
   map_smul' p x := by rw [RingHom.id_apply,ride_smul]; simp [Pi.smul_def]; congr 1; funext i; rw [smul_comm]
lemma melt (U : Grid f) t a : sail t a (settled U)=shift t U a := by
  unfold sail shift; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]; congr 1; funext i
  exact (Matrix.kronecker_smul ..).symm
lemma melt' (U : Grid f) t a : tread t a (settled U)=star (shift t U a) := by
  rw [opp]; unfold tread; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; congr 1; funext i
  rw [thread,star_smul,seam_real]
  exact (Matrix.kronecker_smul ..).symm

def march (t : Site f) (d : Step) := if d.neg then tread t d.dir else sail t d.dir
lemma marching (U : Grid f) t d : march t d (settled U)=leg t U d := by unfold march leg; split; apply melt'; apply melt
lemma rides_size (k : ℝ) (hk : 0≤k) (F : Site f→Bundle) (e : Equiv.Perm (Site f)) (h : ∀ i, ‖F i‖≤k) : ‖rides e F‖ ≤ k := by
  rw [Matrix.cstar_norm_def]; refine (op (rides e F)).opNorm_le_bound hk (fun x => ?_)
  rw [← sq_le_sq₀ (by positivity) (by positivity), norms (X:=Site f) (Y:=Fiber),mul_pow, norms x, ← Equiv.sum_comp e (fun p => ‖fiber x p‖^2), mul_sum]; apply sum_le_sum
  intro i _; rw [travel_vec,← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((leanBound ..).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))) _
lemma touch_site (t : Site f) (x) (a) (B : Mat) : ‖seam t x a • TouchL B‖ ≤ ‖TouchL‖*‖B‖ := by
  rw [norm_smul, show ‖seam t x a‖=1 by cases seam_cases t x a <;> simp_all,one_mul]; exact TouchL.le_opNorm _
lemma march_budget (t : Site f) (d : Step) (x y : Pulse f) : ‖march t d x - march t d y‖ ≤ ‖TouchL‖*‖x-y‖ := by
  rw [← map_sub]; let z : Pulse f:=x-y; unfold march; split
  · apply rides_size _ (by positivity); intro i
    change ‖seam t (i-step d.dir) d.dir • TouchL (z.2 _)‖≤_
    exact (touch_site ..).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm z.2 _).trans (norm_snd_le _)) (norm_nonneg TouchL))
  apply rides_size _ (by positivity); intro i
  change ‖seam t i _ • TouchL (z.1 _)‖ ≤ _
  exact (touch_site ..).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm z.1 _).trans (norm_fst_le _)) (norm_nonneg TouchL))

def plaza (t : Site f) (w : Walk) (P : Pulse f) := (w.map (fun d => march t d P)).prod
lemma plaza_leg (U : Grid f) (t w) : plaza t w (settled U)=routeM t U w := by unfold plaza; simp_rw [marching]; rfl
@[fun_prop] lemma smoothM (t : Site f) (w : Walk) : ContDiff ℂ ω (plaza t w) := by
  induction w with
  | nil => exact contDiff_const
  | cons a w ih =>
    change ContDiff _ _ (fun P => march t a P * plaza t w P)
    exact (LinearMap.toContinuousLinearMap (march t a)).contDiff.mul ih
lemma plazas (t : Site f) (w : Walk) (x : Pulse f) (U : Grid f) {p : ℝ} (h : ‖TouchL‖*‖x-settled U‖ ≤ p) :
    ‖plaza t w x - plaza t w (settled U)‖ ≤ (1+p)^w.length - 1 := by
  have hv : 0 ≤ p := (show 0 ≤ ‖TouchL‖*‖x-settled U‖ from by positivity).trans h
  induction w with
  | nil => simp [plaza]
  | cons a w ih =>
    let A:=march t a x; let B:=march t a (settled U); let X:=plaza t w x; let Y:=plaza t w (settled U)
    have he : ‖A-B‖≤p := (march_budget t a x _).trans h
    have hs : ‖B‖≤1 := by change ‖march t a _‖ ≤ _; rw [marching]; exact rotation_price (leg_u ..)
    have ht : ‖A‖ ≤ 1+p := by linarith [(norm_sub_norm_le A B).trans he]
    have hr : ‖Y‖ ≤ 1 := by change ‖plaza t w _‖ ≤ _; rw [plaza_leg]; exact rotation_price (circle ..)
    rw [List.length_cons]; change ‖A*X-B*Y‖≤_
    rw [show A*X-B*Y=A*(X-Y)+(A-B)*Y by noncomm_ring]
    refine (norm_add_le _ _).trans ((add_le_add ((norm_mul_le A (X-Y)).trans (mul_le_mul ht ih (norm_nonneg _) (by positivity))) ((norm_mul_le (A-B) Y).trans (mul_le_mul he hr (norm_nonneg _) hv))).trans (le_of_eq ?_))
    rw [pow_succ]; ring

lemma flipping (t : Site f) (U : Grid f) (w : Walk) : routeM t U (Lattice.reverse w)=star (routeM t U w) := by
  have he d : leg t U (Step.rev d)= star (leg t U d) := by cases d with | mk i d => cases d <;> simp [leg,Step.rev]
  induction w with
  | nil => simp [Lattice.reverse,routeM]
  | cons a w ih =>
    rw [show Lattice.reverse (a::w) = Lattice.reverse w ++ [Step.rev a] by simp [Lattice.reverse],appendM,ih]
    rw [show routeM t U [Step.rev a]=_ from (show routeM t U [Step.rev a]=star (leg t U a) by simp [routeM,he]), show routeM t U (a::w)=leg t U a*routeM t U w from rfl, star_mul]
end
end YM.QCD.Kit
