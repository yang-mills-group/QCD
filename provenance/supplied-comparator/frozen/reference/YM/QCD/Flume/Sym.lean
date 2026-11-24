import YM.QCD.Flume.Rake
import YM.Next.FREE_KERNELS.Heart

/-!
# Free covariance periodicity after removing singularities; signed hypercubic
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {j : ℕ}
lemma native_dir (v : Train j) (p : Momentum) (hp : physical p) : Native (Dir v p) := by
  unfold Dir; rw [← real_den v p hp,← Complex.ofReal_inv]; exact (real_num v p hp).rotated.realSc _
lemma full_inv {v : Train j} {p : Momentum} (hp : p ∈ realCube zone) (h : p≠0) : quad (full v p) ≠ 0:= by rw [clarify _ _ (teen _ hp h),quad_smul,form_den]; have he : chipper v p≠0:=teen p hp h; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero he)) (mul_ne_zero he (shining v p hp))
lemma nonzeroD {v : Train j} {p : Momentum} (hp : p∈realCube zone) (h : p ≠ 0) : quad (Dir v p)≠ 0:= by rw [form_dir]; exact mul_ne_zero (teen _ hp h) (inv_ne_zero (shining v p hp))
lemma full_match {v : Train j} {p : Momentum} (hp : p∈realCube zone) (h : p≠0) : model (full v p)=(model (Dir v p))⁻¹:=by
  apply Eq.symm; apply Matrix.inv_eq_left_inv
  rw [recover v p (teen p hp h)]; exact returned _ (full_inv hp h)
lemma period_dir {p : Momentum} (v : Train j) (x : Cover) (hp : p∈realCube zone) (hx : p+Laurent.reciprocal x ∈ realCube zone) :
    Dir v (p+Laurent.reciprocal x)=Dir v p:=by
  by_cases he : x=0
  · rw [he,show Laurent.reciprocal (0:Cover)=0 by ext; simp [Laurent.reciprocal],add_zero]
  obtain ⟨h₁,h₂⟩:=overlap_regular he hp hx
  rw [recover _ _ (teen _ hp h₁), recover _ _ (teen _ hx h₂),periodic_full]

def pitch (s : Signed) (A : Para):Para:= (A.fst,s.act A.snd)
lemma pitch_add (s : Signed) (A B : Para):pitch s (A+B)=pitch s A+pitch s B := by simp [pitch,Signed.act_add]
lemma pitch_size (s : Signed) (A : Para) (w : ℂ): pitch s (w • A)=w • pitch s A := by
  refine Prod.ext rfl ?_
  funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; simp [pitch,Signed.act_at,mul_ite]
lemma pitch_qu (s : Signed) (A : Para):quad (pitch s A)=quad A:=by
  unfold quad pitch
  congr 1
  rw [← Equiv.sum_comp s.perm (fun i => (s.act A.2 i)^2)]
  refine sum_congr rfl fun i _=>?_ ; rw [Signed.act_at]; split <;> simp
lemma pitch_t (s : Signed) (A : Para):turn (pitch s A)=pitch s (turn A):= by simp [turn,pitch,Signed.act_neg]
lemma pitch_r (s : Signed) (A : Para) : reciprocalP (pitch s A)=pitch s (reciprocalP A):= by rw [reciprocalP,reciprocalP,pitch_qu,pitch_t, pitch_size]
lemma s_solo (s : Signed) (x : ℂ):pitch s (solo x)=solo x:= by simp [pitch,solo]
lemma s_k (s : Signed) (p : Momentum):kernel (s.act p)=pitch s (kernel p):= by
  apply Prod.ext
  · change (∑ a, (1-Complex.cos (s.act p a)))= ∑ a,(1-Complex.cos (p a)); rw [← Equiv.sum_comp s.perm]; apply sum_congr rfl; intro i _; rw [Signed.act_at]; split <;> simp
  change (fun i => Complex.sin (s.act p i))=s.act (fun i => Complex.sin (p i))
  funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; simp only [Signed.act_at]; split <;> simp

def pitchM (s : Signed) : Para →ₗ[ℂ] Para where
 toFun:= pitch s
 map_add':=pitch_add s
 map_smul' x A:=pitch_size s A x

lemma s_spr (s : Signed) (v : Train j) (p : Momentum) : spr v (s.act p)=spr v p:=by
  have he (b : Train j) : carry b (fun _=> (1:ℂ)) (s.act p)=carry b (fun _=>1) p:=by
    unfold carry spool
    congr 1; rw [← Equiv.sum_comp s.actEquiv.toEquiv]; exact sum_congr rfl fun i _=>by change b.smooth (aliasAt (s.act p) (s.act i))^2 • (1:ℂ)=_; rw [alias_signed b.mass_odd, Train.smooth_signed]
  simp only [spr,stripsum,he]
lemma s_full (s : Signed) (v : Train j) (p : Momentum) : full v (s.act p)=pitch s (full v p):=by
  unfold full carry spool
  rw [pitch_add,s_solo,s_spr,pitch_size]
  congr 2
  rw [← Equiv.sum_comp s.actEquiv.toEquiv]
  change _=(pitchM s) (∑ i, (_:Para))
  rw [map_sum]
  exact sum_congr rfl fun i _=>by change v.smooth (aliasAt (s.act p) (s.act i))^2 • reciprocalP (kernel (aliasAt (s.act p) (s.act i)))=pitch _ _; rw [alias_signed v.mass_odd, Train.smooth_signed, s_k, pitch_r,pitch_size]
lemma real_signed (s : Signed) {p : Momentum} {η : ℝ} (hp : p∈realCube η) : s.act p ∈ realCube η:=by
  constructor
  · apply (physical_iff _).mpr; intro i; obtain ⟨a,rfl⟩:=s.perm.surjective i; simp only [Signed.act_at]; split <;> simp [(physical_iff p).mp hp.1 a]
  intro i; obtain ⟨a,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; split <;> simpa using hp.2 a
lemma s_dir (s : Signed) (v : Train j) (p : Momentum) (hp : p∈realCube zone) : Dir v (s.act p)=pitch s (Dir v p):=by
  by_cases he:p=0
  · subst p; simp [pitch]; rfl
  rw [recover _ _ (teen _ (real_signed s hp) (by rw [← show s.act (0:Momentum)=0 from by simp]; exact s.act_injective.ne he)),recover _ _ (teen _ hp he),s_full,pitch_r]
lemma evenD (v : Train j) (p : Momentum) (hp : p∈realCube zone) : Dir v (-p)=turn (Dir v p):=s_dir ⟨1,fun _=>true⟩ v p hp
end YM.QCD.Flume
