import YM.QCD.Flume.Arch
import YM.QCD.Free.Rotation
import YM.QCD.Step.Match

/-!
# Half-shifted alias geometry, including windings and mobile coarse starts
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Topology BigOperators Matrix
variable {c f n : Side} {j k : ℕ}

/-- cover phases exactly those of the fermion menu -/
def tuning (p : Site n) : Momentum:= fun i => (menu p i:ℂ)
lemma keyboard (p : Site n) : tuning p∈baseCube:= ⟨(physical_iff _).mpr fun _=> rfl, carded p⟩
lemma shiftPhase (p : Site n) : tuning p=mon p+(fun _=> -(↑Real.pi:ℂ)/n.val) := by
  ext i; unfold tuning mon menu spacer fixed Laurent.reciprocal; simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul]; push_cast; ring
lemma tune_nonzero (p : Site n) : tuning p≠0:=by
  intro h; have he := fixed_lower (lift p) 0
  have ht:= congr_fun h 0
  change ((spacer n * fixed (lift p) 0:ℝ):ℂ)=0 at ht
  rw [Complex.ofReal_eq_zero] at ht
  rw [(mul_eq_zero.mp ht).resolve_left (fine n).ne',abs_zero] at he; linarith [Real.pi_pos]

/-- coarse/fine aliases with odd dilations, punctures excluded by all antiperiods -/
def twins (r : Ratio c f) (p : Site c) (l : Site r.count) := wrap f (lift p+c.val • lift l)
lemma twin_lift (r : Ratio c f) (ho : Odd r.count.val) (p : Site c) (l : Site r.count) : lift (twins r p l)=lift p+c.val • lift l := by
  refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩
  obtain ⟨h1,h2⟩:=lift_centers p i; obtain ⟨h3,h4⟩:=centers_odd l ho i; have hC : (0:ℤ) < c.val:=by exact_mod_cast c.property
  rw [r.exact_size]; push_cast; simp only [Pi.add_apply,nsmul_eq_mul,Pi.mul_apply, Pi.natCast_apply]; constructor <;> nlinarith
lemma full_tune (r : Ratio c f) (ho : Odd r.count.val) (p : Site c) (l : Site r.count) : tuning (twins r p l)=aliasAt (tuning p) l:= by
  funext i; rw [alias_value]; unfold tuning menu
  simp_rw [twin_lift r ho,Pi.smul_apply,smul_eq_mul,spacer,fixed, Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]
  push_cast; have he : (f.val:ℂ)=(c.val:ℂ)*(r.count.val:ℂ):=by exact_mod_cast r.exact_size
  rw [he]; field_simp [side_ne c,side_ne r.count]; ring

def tunes (r : Ratio c f) (ho : Odd r.count.val) : (Site c × Site r.count) ≃ Site f :=
  Equiv.ofBijective (fun p=>twins r p.1 p.2) ((Fintype.bijective_iff_injective_and_card _).mpr (by
    refine ⟨?_,by rw [Fintype.card_prod,site_card,site_card,site_card,r.exact_size,mul_pow]⟩
    rintro ⟨u,i⟩ ⟨w,a⟩ h
    have hx := congr_arg lift h
    dsimp only at hx; rw [twin_lift r ho,twin_lift r ho] at hx
    have hu : u=w := by simpa only [map_add, wrap_lift,joint_heads,add_zero] using congr_arg (wrap c) hx
    subst w
    have hs := add_left_cancel hx; congr 1; apply lift_inj; funext b
    have he := congr_fun hs b; simp only [Pi.smul_apply,nsmul_eq_mul] at he; exact mul_left_cancel₀ (show (c.val:ℤ)≠0 by exact_mod_cast c.property.ne') he))

/-- use nonnegative lifts with seam at 0. -/
def rep (x : Site n) : Cover:= fun i=> (x i).val
@[simp] lemma rep_eq (x : Site n) : wrap n (rep x)=x:=by funext i; simp [rep,wrap]

lemma rep_phase (p x : Site n) : mode (tuning p) (rep x)=wind x*cell p x:=by
  rw [shiftPhase,mode_phase]
  rw [show mode (mon p) (rep x)=cell p x from respects _ _ _ (by simp)]
  congr! 0 -- inspect
  rw [mul_comm]; congr 1
  unfold mode wind rep cis; congr 1
  push_cast; simp only [← Finset.mul_sum]; ring
lemma wave_root (p x : Site n) : scarf p x=(n.val:ℂ)⁻¹ ^2*mode (tuning p) (rep x):= by rw [rep_phase,scarf,mul_assoc]
lemma scarf_ne (p x : Site n):scarf p x ≠ 0 := by rw [wave_root]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (side_ne _))) (Complex.exp_ne_zero _)
lemma center_lift (r : Ratio c f) (x : Site c) : rep (r.embed x) = r.count.val • rep x:=by
  have he : r.embed x=wrap f (r.count.val • rep x):=by rw [← r.embed_wrap,rep_eq]
  funext i
  rw [he]
  change (↑((↑((r.count.val • rep x) i): Per f).val):ℤ)=_
  simp only [Pi.smul_apply, nsmul_eq_mul, rep, Int.cast_mul,Int.cast_natCast]; rw [← Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt]
  · push_cast; rfl
  rw [r.exact_size,mul_comm]; gcongr; exact ZMod.val_lt (x i)
lemma welcome (r : Ratio c f) (ho : Odd r.count.val) (p : Site c) (l : Site r.count) (x : Site c):
    scarf (twins r p l) (r.embed x)=((r.count.val:ℂ)⁻¹^2)*scarf p x:=by
  have he : (f.val:ℂ)=(c.val:ℂ)*(r.count.val:ℂ):=by exact_mod_cast r.exact_size
  rw [wave_root,center_lift, full_tune r ho,← mode_scale, alias_scale,mode_phase,mode_periodic, wave_root,he,mul_one,mul_inv,mul_pow]; ring

/- Crossing parity includes every winding, no shortest-path convention needed. -/
def seamPath (x : Site n) (w : Walk) : ℂ:= match w with
| []=>1
| a::q=> (if a.neg then seam 0 (x-step a.dir) a.dir else seam 0 x a.dir)*seamPath (x+a.vec) q
lemma realSeam (x : Site n) (w):star (seamPath x w)=seamPath x w ∧ seamPath x w*seamPath x w=1:=by
  induction w generalizing x with
  | nil=>exact ⟨star_one _,one_mul _⟩
  | cons a w ih=>
    have he (y : Site n) (a:Axis):star (seam 0 y a)=seam 0 y a ∧ seam 0 y a*seam 0 y a=1:= by unfold seam; split <;> simp
    rw [seamPath]; split
    all_goals exact ⟨by rw [star_mul,(ih _).1,(he _ _).1,mul_comm],by rw [mul_mul_mul_comm,(he _ _).2,(ih _).2,one_mul]⟩
lemma scarf_a (p x : Site n) (i:Axis):seam 0 x i*scarf p (x+step i)=scarf p x*mode (tuning p) (step i):=by rw [onestep,Exterior.factor,mul_comm Complex.I]; rfl
lemma scarf_b (p x : Site n) (i:Axis):seam 0 (x-step i) i*scarf p (x-step i)=scarf p x*mode (tuning p) (-step i):=by
  have he:= scarf_a p (x-step i) i; rw [sub_add_cancel] at he
  have hx (x : Site n):seam 0 x i*seam 0 x i=1:=by unfold seam; split <;> simp
  rw [mode_opposite]; field_simp; rw [mul_assoc, ← he,← mul_assoc,hx,one_mul]
lemma cover_along (x y : Cover) (w : Walk) : stop (x+y) w=x+stop y w:= by induction w generalizing y <;> simp_all [stop,add_assoc]
lemma follows (p x : Site n) (w: Walk):seamPath x w* scarf p (Lattice.stop x w)=scarf p x*mode (tuning p) (Lattice.stop 0 w):=by
  induction w generalizing x with
  | nil=> simp [seamPath,stop]
  | cons a w ih=>
    have hh := ih (x+a.vec)
    rw [stop,stop, zero_add,← add_zero (a.vec:Cover),cover_along a.vec 0, mode_shift]; rw [seamPath,mul_assoc,hh]
    rcases a with ⟨i,_|_⟩
    · simp only [Bool.false_eq_true,↓reduceIte, Step.vec]; rw [← mul_assoc,scarf_a,mul_assoc]
      -- inspect
    simp only [↓reduceIte, Step.vec,← sub_eq_add_neg]; rw [← mul_assoc,scarf_b,mul_assoc]
end YM.QCD.Flume
