import YM.QCD.Flume.Cost
import YM.Next.FREE_KERNELS.Lever

/-!
# Wilson principal paravectors
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free
open scoped Topology BigOperators
variable {ι : Type*}

def kernel (p : Momentum) : Para := (∑ a, (1-Complex.cos (p a)),fun a => Complex.sin (p a))
lemma kreal (p : Momentum) (hp : physical p) : Native (kernel p) := by
  have he i : Complex.cos (p i)=(Real.cos (p i).re:ℂ) := by rw [Complex.ofReal_cos, cast_real hp]
  have hh i : Complex.sin (p i)=(Real.sin (p i).re:ℂ) := by rw [Complex.ofReal_sin, cast_real hp]
  constructor
  · simp only [kernel,star_sum,star_sub, star_one,he, Complex.star_def,Complex.conj_ofReal]
  exact (physical_iff _).mpr fun i => by simp [kernel,hh]

/-- match to lattice display symbol -/
lemma version (p : Free.Freq) : model (kernel (fun i => (p i:ℂ)))=Free.display p 0 := by
  unfold Free.display Free.wmass Free.sine Free.slash model hiss; simp [kernel,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma positiveK (p : Momentum) (hp : physical p) : 0 ≤ (kernel p).1.re := by
  unfold kernel; dsimp only; rw [Complex.re_sum]; apply sum_nonneg; intro i _
  rw [show Complex.cos (p i)=(Real.cos (p i).re:ℂ) from by rw [Complex.ofReal_cos, cast_real hp]]; simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re]; exact sub_nonneg.mpr (Real.cos_le_one _)

lemma period_k (p : Momentum) (x : Cover) : kernel (p+Laurent.reciprocal x)=kernel p := by
  have hx (i) : (p+Laurent.reciprocal x : Momentum) i=p i+(x i:ℂ)*(2*Real.pi) := by unfold Laurent.reciprocal; simp only [Pi.add_apply]; ring
  simp only [kernel,hx,Complex.cos_add_int_mul_two_pi,Complex.sin_add_int_mul_two_pi]
@[simp] lemma kernel_nil : kernel 0=0 := by simp [kernel]; rfl

lemma cos_chip (z : ℂ) : 2*(1-Complex.cos z)=-(chip z+chip (-z)) := by unfold Complex.cos chip; rw [mul_neg,mul_comm z Complex.I]; ring
lemma sin_chip (z : ℂ) : Complex.sin z=(2*Complex.I)⁻¹*(chip z-chip (-z)) := by
  unfold Complex.sin chip
  field_simp
  rw [pow_two,Complex.I_mul_I]; ring
lemma chip_gap (p : Momentum) : 2*(kernel p).1=divisor 1 p := by
  simp only [kernel, mul_sum,cos_chip]
  unfold divisor; apply sum_congr rfl; intro i _
  simp only [seedQ,narrow_apply, PNat.one_coe, Nat.cast_one,div_one,Pi.neg_apply,one_mul]
  unfold chip
  have he (x : ℂ) : Complex.exp (Complex.I*x)*Complex.exp (Complex.I*(-x))=1 := by rw [← Complex.exp_add,mul_neg, add_neg_cancel,Complex.exp_zero]
  linear_combination -(he (p i))

lemma quadK (p : Momentum) (hp : physical p) : 2*(kernel p).1.re ≤ (quad (kernel p)).re := by
  let u (i : Axis) : ℝ := 1-Real.cos (p i).re
  have hh i : 0 ≤ u i := sub_nonneg.mpr (Real.cos_le_one _)
  have he : (kernel p).1.re=∑ i,u i := by
    unfold kernel; dsimp only; rw [Complex.re_sum]
    refine sum_congr rfl fun i _=> ?_
    rw [show Complex.cos (p i)=(Real.cos (p i).re:ℂ) from by rw [Complex.ofReal_cos, cast_real hp]]; simp only [u,Complex.sub_re,Complex.one_re,Complex.ofReal_re]
  have hi i : ((kernel p).2 i).re=Real.sin (p i).re := by unfold kernel; dsimp only; rw [show Complex.sin (p i)=(Real.sin (p i).re:ℂ) from by rw [Complex.ofReal_sin, cast_real hp], Complex.ofReal_re]
  rw [(kreal p hp).quad_m,Complex.ofReal_re, he,mul_sum]; simp_rw [hi]
  have hj (i : Axis) : 2*u i=u i ^2+Real.sin (p i).re ^2:=by unfold u; nlinarith [Real.sin_sq_add_cos_sq (p i).re]
  simp_rw [hj,sum_add_distrib]; gcongr
  calc
    _ ≤ ∑ i, (u i * ∑ j,u j) := sum_le_sum fun a _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (single_le_sum (fun i _=> hh i) (mem_univ a)) (hh a)
    _ = _ := by rw [← sum_mul,sq]
lemma quadD (p : Momentum) (hp : physical p) : (divisor 1 p).re ≤ (quad (kernel p)).re := by rw [← chip_gap]; simpa only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] using! (quadK p hp)

/-- alias scale of kernel. -/
def tiny (p : Momentum) {L : Side} (l : Site L) := (L.val:ℂ) • kernel (aliasAt p l)
lemma genuine (p : Momentum) {L : Side} (hp : physical p) (l : Site L) : Native (tiny p l) := by unfold tiny; simpa using (kreal (aliasAt p l) (alias_real hp l)).realSc L.val
lemma real_tiny (p : Momentum) {L : Side} (hp : physical p) (l : Site L) : 0 ≤ (tiny p l).1.re := by simp only [tiny,Prod.smul_fst,smul_eq_mul]; rw [← Complex.ofReal_natCast,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact mul_nonneg (by positivity) (positiveK _ (alias_real hp _))

lemma blow_k (p : Momentum) {L : Side} (hp : physical p) (l : Site L) : ‖blow 1 p l‖ ≤ ‖quad (tiny p l)‖ := by
  simp only [tiny,quad_smul,blow,norm_mul]; gcongr
  have hk := quadD (aliasAt p l) (alias_real hp _)
  have he := divisor_normSq 1 (alias_real hp l)
  rw [he] at hk ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact hk.trans (Complex.re_le_norm _)
lemma tiny_firm (L : ι→Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) (hi : ∀ i,l i ≠0) : Firm (fun i => grade (l i)^2) fun i p=>quad (tiny p (l i)) := by
  obtain ⟨η,c,hp,hc,h⟩:= blow_firm L (fun _=>1) ho l hi
  exact ⟨η,c,hp,hc,fun i p hx=> (h i p hx).trans (blow_k p hx.1 _)⟩

lemma tiny_price (L : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) : Scale (fun i=>grade (l i)) fun i p=>tiny p (l i):=by
  have h (a : Axis) (l : ∀ i, Site (L i)) : Moderate (fun i=>grade (l i)) fun i p=> ((L i).val:ℂ)*chip (aliasAt p (l i) a):= by
    have hc := (scaled_seed L (fun _=>1) ho l (fun _=>a)).raise_price (fun i => up_le ..)
    simpa only [seedQ,narrow_apply, PNat.one_coe, Nat.cast_one, div_one,one_mul] using hc
  have hr (a : Axis): Moderate (fun i=>grade (l i)) fun i p=> ((L i).val:ℂ)*chip (-aliasAt p (l i) a):= by
    have ht := (h a (fun i=>-l i)).reverse
    simpa only [grade,pdist_neg,alias_reverse _ (ho _),Pi.neg_apply] using ht
  constructor
  · simp only [tiny,kernel,Prod.smul_fst,smul_eq_mul,mul_sum]
    apply Moderate.sum _ _ (fun i=> (grade_pos _).le)
    intro a _; have he (i : ι) (p : Momentum) : (↑(L i).val:ℂ)*(1-Complex.cos (aliasAt p (l i) a)) = ((-1)/2) * (((L i).val:ℂ)*chip (aliasAt p (l i) a) + ((L i).val:ℂ)*chip (-aliasAt p (l i) a)):=by linear_combination (((L i).val:ℂ)/2)*(cos_chip (aliasAt p (l i) a))
    simp_rw [he]; simpa only [one_mul] using (Moderate.const ((-1)/2)).mul ((h a l).add (hr a))
  intro a; simp only [tiny,kernel,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,sin_chip,mul_left_comm ((L _).val:ℂ),mul_sub ((L _).val:ℂ)]
  simpa only [one_mul] using (Moderate.const (2*Complex.I)⁻¹).mul ((h a l).sub (hr a))

/-- use any thickness assuming realCube zone -/
lemma charge_below (p : Momentum) {L : Side} (hp : p∈realCube zone) : meter.low^2 * lengthSq p ≤ (quad (tiny p (0:Site L))).re := by
  have he := blow_k p hp.1 (0:Site L); rw [blow_zero] at he; rw [← (genuine _ hp.1 _).magnitude]
  exact (divisor_real_bounds (L*1) hp).1.trans ((Complex.re_le_norm _).trans he)
lemma teen (p : Momentum) {L : Side} (hp : p∈realCube zone) (he : p≠0): quad (tiny p (0:Site L))≠ 0:= by
  have h := (mul_pos (pow_pos meter.low_pos 2) (lengthSq_pos he)).trans_le (charge_below (L:=L) p hp); exact fun hi=>by rw [hi] at h; simp at h
lemma vital (p : Momentum) {L : Side} (ho : Odd L.val) (hp : p∈realCube zone) (l : Site L) (he : p≠0 ∨ l≠0) : quad (tiny p l) ≠ 0:= by
  by_cases h : l=0
  · subst l; exact teen p hp (he.resolve_right (by simp))
  apply norm_pos_iff.mp; apply lt_of_lt_of_le _ (blow_k p hp.1 l)
  have hx : aliasAt p l ≠ 0 := by
    obtain ⟨a,ha⟩ := hit_grade l; have hu:= grade_gt h
    have hc := scaled_alias_lower l (mem_cube_real hp zone_pos) a (by intro h; simp_all [up])
    intro hq; rw [hq] at hc; exact not_le_of_gt (mul_pos zone_pos (up_pos ..)) (by simpa [zone] using! hc)
  exact norm_pos_iff.mpr (mul_ne_zero (pow_ne_zero _ (side_ne _)) (divisor_ne _ (alias_in_real zone_pos hp l ho) hx))
lemma reciprocal_scaled (p : Momentum) {L : Side} (l : Site L) : reciprocalP (tiny p l)= (L.val:ℂ)⁻¹ • reciprocalP (kernel (aliasAt p l)):=by
  let A:= kernel (aliasAt p l)
  have ht : turn ((L.val:ℂ) • A : Para)=(L.val:ℂ) • turn A:=by ext <;> simp [turn]
  unfold reciprocalP tiny; rw [ht,quad_smul,smul_smul,smul_smul]; congr 1; rw [mul_inv]; field_simp [side_ne L]

end YM.QCD.Flume
