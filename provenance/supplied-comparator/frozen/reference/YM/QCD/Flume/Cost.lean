import YM.QCD.Flume.Cliff

/-!
# weights on paravectors
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free
open scoped Topology BigOperators
variable {ι κ : Type*}
structure Scale (w : ι → ℝ) (f : ι → Momentum → Para) : Prop where
 scalar : Moderate w fun i p => (f i p).1
 vector (a) : Moderate w fun i p=> (f i p).2 a

namespace Scale
variable {w x : ι → ℝ} {f g : ι → Momentum → Para}

lemma cash (h : Scale w f) (i) : 0 ≤ w i := h.scalar.nonneg i
lemma raise (h : Scale w f) (hx : w≤x) : Scale x f := ⟨h.scalar.raise_price hx,fun i => (h.vector i).raise_price hx⟩
lemma zero (h : ∀ i, 0 ≤ w i) : Scale w fun _ _=>0 := ⟨Moderate.zero h,fun _ => Moderate.zero h⟩
lemma common (a : Para) : Scale (fun _ : ι => 1) fun _ _ => a := ⟨Moderate.const _,fun _=> Moderate.const _⟩
lemma ad (h : Scale w f) (hg : Scale w g) : Scale w fun i p=> f i p + g i p := ⟨h.scalar.add hg.scalar,fun i=> (h.vector i).add (hg.vector i)⟩
lemma weight (h : Scale w f) {a : ι → Momentum → ℂ} (ha : Moderate x a) : Scale (x*w) fun i p => a i p • f i p :=
  ⟨ha.mul h.scalar,fun i=> ha.mul (h.vector i)⟩
lemma index (h : Scale w f) (e : κ → ι) : Scale (w ∘ e) fun i p=> f (e i) p := ⟨h.scalar.index _,fun _=> (h.vector _).index _⟩
lemma turnback (h : Scale w f) : Scale w fun i p=> turn (f i p) := ⟨h.scalar,fun a=> (h.vector a).neg⟩
lemma illuminates (h : Scale w f) (H : Scale x g) : Moderate (w*x) fun i p => beam (f i p) (g i p) := by
  unfold Para.beam; apply Moderate.add (h.scalar.mul H.scalar)
  exact Moderate.sum (w:=w*x) _ _ (fun i => mul_nonneg (h.cash i) (H.cash i)) fun k _ => (h.vector k).mul (H.vector k)
lemma squares (h : Scale w f) : Moderate (fun i => w i ^2) fun i p=> quad (f i p) := by
  have h := h.illuminates h; simpa only [Para.beam,Para.quad,pow_two] using! h
lemma solo_w {a : ι → Momentum → ℂ} (h : Moderate w a) : Scale w fun i p => solo (a i p) := ⟨h,fun i=> Moderate.zero h.nonneg⟩
lemma gather {α : ι → Type*} (s : ∀ i, Finset (α i)) (m : ∀ i, α i → ℝ)
    (hm : ∃ M : ℝ, 0<M ∧ ∀ i, ∑ k∈s i, m i k ≤ M*w i) (F : ∀ i, α i → Momentum → Para)
    (hf : Scale (fun x : Σ i, {k // k∈ s i} => m x.1 x.2) (fun x => F x.1 x.2)) :
    Scale w (fun i p => ∑ k∈s i, F i k p) := by
  constructor
  · simp_rw [Prod.fst_sum]; exact Moderate.sum_family s m hm _ hf.scalar
  intro a; simp_rw [Prod.snd_sum,Finset.sum_apply]; exact Moderate.sum_family s m hm _ (hf.vector a)
lemma reciprocal (h : Scale w f) (ha : Firm (fun i => w i^2) fun i p => quad (f i p)) (hq : ∀ i, 0<w i) : Scale (fun i => (w i)⁻¹) fun i p=> reciprocalP (f i p) := by
  unfold reciprocalP; have hf := h.turnback.weight (h.squares.inv ha fun i=>pow_pos (hq i) _)
  refine hf.raise fun i=> le_of_eq ?_
  change (w i^2)⁻¹*w i=_; field_simp [(hq i).ne']
end Scale

lemma cube_real_mono {a b : ℝ} (h : a≤b) : realCube a ⊆ realCube b:= fun _ h' => ⟨h'.1,fun i => (h'.2 i).trans_le (by linarith)⟩
lemma cast_real {p} (hp : physical p) (i) : ((p i).re:ℂ)=p i := Complex.ext rfl (Eq.symm ((physical_iff _).mp hp i))
lemma native_additive (A B : Para) (h : Native A) (hb : Native B) : ((beam A B).re:ℂ)=beam A B := by
  simp only [beam,Complex.add_re, Complex.mul_re,Complex.re_sum]; push_cast
  simp_rw [h.caste,hb.caste,h.tangible,hb.tangible,show A.fst.im=0 from Complex.conj_eq_iff_im.mp h.1,
    (physical_iff _).mp h.2]; simp
end YM.QCD.Flume
