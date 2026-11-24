import YM.Wilson.Symmetry
import YM.QCD.Lattice.Monomial

/-!
# Antiperiodic Wilson Dirac stencil, Euclidean

Period lattice `n`; define on all finite tori (even `n ≥ 4` planned in reflection arguments).
Counting units. Parameter `m` is an explicit dimensionless *bare* mass-counterterm coordinate;
zero gives the tree massless stencil. A massless renormalized theory would still require tuning.
Twists place one negative fermion seam in each of the four circles. We don't twist the gauge
measure.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Lattice Wilson
open Finset Function
open scoped Kronecker Matrix Matrix.Norms.Frobenius BigOperators

abbrev Fiber := Pinor × Hue
abbrev Bundle := Matrix Fiber Fiber ℂ
abbrev Row (n : Side) := Site n × Fiber
abbrev Grid (n : Side) := Config su n
abbrev Sheet (n : Side) := Matrix (Row n) (Row n) ℂ
abbrev Frame (n : Side) := Site n → su.El

variable {n : Side}

/-- seam t means the link ending at coordinate `t` crossing from `t-1`.
all four antiperiodic simultaneously. -/
def seam (t : Site n) (x : Site n) (a : Axis) : ℂ := if x a + 1 = t a then -1 else 1

lemma seam_cases (t x : Site n) (a) : seam t x a = 1 ∨ seam t x a = -1 := by unfold seam; split <;> tauto
@[simp] lemma seam_sq (t x : Site n) (a) : seam t x a * seam t x a = 1 := by rcases seam_cases t x a with h|h <;> rw [h] <;> simp
@[simp] lemma seam_real (t x : Site n) (a) : star (seam t x a) = seam t x a := by rcases seam_cases t x a with h|h <;> rw [h] <;> simp
lemma seam_across (t x : Site n) {a b} (h : a ≠ b) : seam t (x+step b) a = seam t x a := by simp [seam,h]

/-- Write as 3-by-3 matrices. -/
def colour (u : su.El) : Mat := su.mat u
@[simp] lemma colour_mul (u v : su.El) : colour (u*v)=colour u * colour v := su.mat_mul ..
@[simp] lemma colour_inv (u : su.El) : colour u⁻¹ = star (colour u) := su.mat_inv ..
@[fun_prop] lemma colour_cont : Continuous colour := su.continuous_mat

/-- Twisted SU(3) link in the fundamental representation -/
def thread (t : Site n) (U : Grid n) (a : Axis) (x : Site n) : Mat := seam t x a • colour (U (x,a))

lemma thread_u (t : Site n) (U : Grid n) (a x) : thread t U a x ∈ unitary _ := by
  unfold thread; set M : Mat := colour _ with hM
  have hm : M∈unitary _ := ⟨su.mat_star_mul _,su.mat_mul_star _⟩
  rcases seam_cases t x a with h|h
  · rw [h,one_smul]; exact hm
  rw [h,neg_smul,one_smul]; constructor <;> simp only [star_neg,neg_mul_neg] <;> first | exact hm.1 | exact hm.2

lemma thread_change (t : Site n) (U : Grid n) (k : Frame n) (a x) :
    thread t (gauge k U) a x=colour (k x)*thread t U a x*star (colour (k (x+step a))) := by
  unfold thread
  simp only [Lattice.gauge, colour_mul,colour_inv,Matrix.mul_smul,Matrix.smul_mul]

def forward (a : Axis) : Equiv.Perm (Site n) := Equiv.addRight (step a)

@[simp] lemma hop (a : Axis) (x : Site n) : forward a x=x+step a := rfl
@[simp] lemma back (a : Axis) (x : Site n) : (forward a).symm x=x-step a := by simp [forward,sub_eq_add_neg]

def touch (x : Mat) : Bundle := (1:Spike) ⊗ₖ x
def wave (x : Spike) : Bundle := x ⊗ₖ (1:Mat)

lemma touch_mul (x y : Mat) : touch x*touch y = touch (x*y) := by unfold touch; rw [← Matrix.mul_kronecker_mul,one_mul]
lemma wave_mul (x y : Spike) : wave x*wave y=wave (x*y) := by unfold wave; rw [← Matrix.mul_kronecker_mul,one_mul]
lemma interlace (x y) : Commute (touch x) (wave y) := by
  show touch x * wave y = wave y * touch x
  unfold touch wave; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]; simp only [mul_one,one_mul]
lemma lace (x y) : wave y * touch x = y ⊗ₖ x := by unfold wave touch; rw [← Matrix.mul_kronecker_mul, mul_one,one_mul]
lemma touch_add (x y : Mat) : touch x + touch y = touch (x+y) := (Matrix.kronecker_add ..).symm
lemma wave_add (x y : Spike) : wave x+wave y=wave (x+y) := (Matrix.add_kronecker ..).symm
lemma touch_one : touch 1 = 1 := Matrix.one_kronecker_one
lemma wave_one : wave 1 = 1 := Matrix.one_kronecker_one
lemma wave_zero : wave 0 = 0 := Matrix.zero_kronecker _
lemma touch_star (x : Mat) : star (touch x) = touch (star x) := by unfold touch; rw [star_kr,star_one]
lemma wave_star (x : Spike) : star (wave x) = wave (star x) := by unfold wave; rw [star_kr,star_one]
lemma touch_u {x : Mat} (hx : x ∈ unitary _) : touch x ∈ unitary _ := by
  constructor
  · rw [touch_star, touch_mul,hx.1]; exact touch_one
  rw [touch_star, touch_mul,hx.2]; exact touch_one

def shift (t : Site n) (U : Grid n) (a : Axis) : Sheet n := rides (forward a) (fun x => touch (thread t U a x))

def onSpin (n : Side) (Y : Spike) : Sheet n := rides (Equiv.refl _) fun _ => wave Y

lemma on_spin_mul (Y Z) : onSpin n Y * onSpin n Z = onSpin n (Y*Z) := by
  unfold onSpin; rw [ride_mul]; simp_rw [wave_mul]; rfl
lemma on_spin_star (Y) : star (onSpin n Y) = onSpin n (star Y) := by unfold onSpin; rw [ride_ad]; simp_rw [wave_star]; rfl
lemma on_spin_one : onSpin n 1 = 1 := by unfold onSpin; simp_rw [wave_one]; exact ridden
lemma on_spin_zero : onSpin n 0 = 0 := by unfold onSpin; simp_rw [wave_zero]; exact ride_zero _
lemma on_spin_add (Y Z) : onSpin n Y+onSpin n Z=onSpin n (Y+Z) := by unfold onSpin; rw [ride_add]; congr 1; funext x; exact wave_add ..

lemma shift_u (t : Site n) (U : Grid n) (a) : shift t U a ∈ unitary _ :=
  unitary_ride _ fun _ => touch_u (thread_u ..)
lemma commutes_ride (X : Spike) (T : Site n→Mat) (e : Equiv.Perm (Site n)) :
    Commute (rides e fun x => touch (T x)) (onSpin n X) := by
  show _ * _ = _ * _
  unfold onSpin
  rw [ride_mul,ride_mul,Equiv.trans_refl,Equiv.refl_trans]
  congr 1; funext x; exact interlace ..

lemma opp (t : Site n) (U : Grid n) (a) : star (shift t U a) =
    rides (forward a).symm (fun y : Site n => touch (star (thread t U a (y-step a)))) := by
  rw [shift,ride_ad]; simp_rw [touch_star,back]

def siteRot (k : Frame n) : Sheet n := rides (Equiv.refl _) (fun x => touch (colour (k x)))

lemma siteRot_u (k : Frame n) : siteRot k ∈ unitary _ := unitary_ride _ fun _ => touch_u ⟨su.mat_star_mul _,su.mat_mul_star _⟩

lemma siteRot_star (k : Frame n) : star (siteRot k)=siteRot k⁻¹ := by
  rw [siteRot,ride_ad]; unfold siteRot
  simp only [Equiv.refl_symm, Equiv.refl_apply,touch_star]; rfl

lemma site_transform (t : Site n) (a) (k : Frame n) (U : Grid n) :
    shift t (gauge k U) a = siteRot k*shift t U a*star (siteRot k) := by
  rw [siteRot_star]; unfold shift siteRot; rw [ride_mul,ride_mul]
  simp only [Equiv.refl_apply, Equiv.refl_trans, Equiv.trans_refl, touch_mul,hop]; congr 1; funext x
  rw [thread_change]; rfl

lemma shift_spin (X : Spike) (t : Site n) (U : Grid n) (a) : Commute (shift t U a) (onSpin n X) := commutes_ride ..
lemma back_spin (X : Spike) (t : Site n) (U : Grid n) (a) : Commute (star (shift t U a)) (onSpin n X) := by rw [opp]; exact commutes_ride ..
lemma rot_spin (X : Spike) (k : Frame n) : Commute (siteRot k) (onSpin n X) := commutes_ride ..

/-- Unitary projected hop. -/
def singleHop (t : Site n) (U : Grid n) (a : Axis) : Sheet n :=
  onSpin n (lo a)*shift t U a + onSpin n (hi a)*star (shift t U a)

lemma advance_star (t : Site n) (U : Grid n) (a) : star (singleHop t U a) =
    onSpin n (lo a)*star (shift t U a) + onSpin n (hi a)*shift t U a := by
  rw [singleHop, star_add,star_mul,star_mul,star_star,on_spin_star,on_spin_star,lo_star,hi_star,
    (shift_spin ..).eq,(back_spin ..).eq]

lemma hop_u (t : Site n) (U : Grid n) (a) : singleHop t U a ∈ unitary _ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [advance_star, singleHop]
  have he (X Y : Spike) (T V : Sheet n) (h : Commute T (onSpin n Y)) :
      (onSpin n X*T)*(onSpin n Y*V)=onSpin n (X*Y)*(T*V) := by rw [← mul_assoc,mul_assoc (onSpin n X), h.eq,← mul_assoc,on_spin_mul,mul_assoc]
  rw [add_mul,mul_add,mul_add, he _ _ _ _ (shift_spin ..), he _ _ _ _ (shift_spin ..), he _ _ _ _ (back_spin ..),he _ _ _ _ (back_spin ..)]
  have h := shift_u t U a
  simp only [lo_sq,hi_sq, vanish, vanish', h.2,h.1,on_spin_zero,mul_one,zero_mul,add_zero,zero_add]
  rw [on_spin_add, projectors, on_spin_one]

/-- Counting units Wilson Dirac matrix. -/
def bareD (t : Site n) (U : Grid n) (m : ℝ) : Sheet n :=
  (m:ℂ) • 1 + ∑ a, (1-singleHop t U a)

lemma spinless (k : Frame n) (X : Spike) (U : Sheet n) :
    onSpin n X*(siteRot k * U * star (siteRot k))=siteRot k*(onSpin n X*U)*star (siteRot k) := by
  rw [← mul_assoc,← mul_assoc,← (rot_spin ..).eq,mul_assoc (siteRot k)] -- check

lemma hop_transform (t : Site n) (a) (k : Frame n) (U : Grid n) : singleHop t (gauge k U) a =
    siteRot k * singleHop t U a * star (siteRot k) := by
  rw [singleHop,site_transform,star_mul,star_mul, star_star, ← mul_assoc (siteRot k) (star (shift _ _ _)), singleHop,
    mul_add,add_mul,spinless,spinless]

lemma bareD_covariant (t : Site n) (U : Grid n) (m : ℝ) (k : Frame n) :
    bareD t (gauge k U) m = siteRot k*bareD t U m*star (siteRot k) := by
  unfold bareD; rw [mul_add,add_mul]
  simp only [Matrix.mul_sum,Matrix.sum_mul, mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul,mul_one]
  simp_rw [(siteRot_u k).2,hop_transform]

def chirality (n : Side) := onSpin n g5
@[simp] lemma chi_star : star (chirality n)=chirality n := by rw [chirality,on_spin_star,g5_star]
@[simp] lemma chi_sq : chirality n*chirality n=1 := by rw [chirality,on_spin_mul,g5_sq,on_spin_one]

lemma hop_chi (t : Site n) (U : Grid n) (a) : star (singleHop t U a)*chirality n=chirality n*singleHop t U a := by
  unfold chirality
  rw [advance_star,singleHop,add_mul,mul_add]
  rw [mul_assoc (onSpin n (lo a)),(back_spin ..).eq,← mul_assoc,on_spin_mul,mul_assoc (onSpin n (hi a)),
    (shift_spin ..).eq,← mul_assoc,on_spin_mul,← swap_hi, ← swap_lo, ← mul_assoc, ← mul_assoc,on_spin_mul,on_spin_mul,add_comm]

lemma gamma5 (t : Site n) (U : Grid n) (m : ℝ) : star (bareD t U m) = chirality n*bareD t U m*chirality n := by
  suffices he : star (bareD t U m)*chirality n=chirality n*bareD t U m by rw [← he,mul_assoc,chi_sq,mul_one]
  unfold bareD
  rw [star_add,add_mul,mul_add,star_smul,star_one,star_sum]
  simp only [Matrix.smul_mul,Matrix.mul_smul, Matrix.sum_mul,Matrix.mul_sum,star_sub,sub_mul,mul_sub,
    star_one,one_mul,mul_one,hop_chi]; simp

end YM.QCD.Lat
