import YM.QCD.Step.Breath
import YM.QCD.Estimate.Affine

/-! # compactly supported geometric envelopes for the covariance and logdet -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Grass Lat Lattice Wilson Finset Filter Function Cost
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
variable {c f : Side} (r : Ratio c f) {L : Side} {b m w q : ℝ}

/-- constants independent of volume; not of ratio. -/
structure Weak (L : Side) (b m w q : ℝ) : Prop where
  active : 0 < b
  gap : 0 < m + fraction b L
  pos : 0 < w
  touch : 0 ≤ q
  aimed : q < 1
  hides : 1-2*w*(m+fraction b L) + w^2*(|m|+8 + b*slope L^2)^2 ≤ q^2

lemma funds (L : Side) {b m : ℝ} (hb : 0 < b) (hm : 0 < m+fraction b L) : ∃ w q, Weak L b m w q := by
  obtain ⟨w,q,h₁,h₂,h₃,h₄⟩ := choose_rate (m+fraction b L) (|m|+8+b*slope L^2) hm (by positivity)
  exact ⟨w,q,hb,hm,h₁,h₂,h₃,h₄⟩

namespace Weak
variable {r} (h : Weak r.count b m w q)
include h
lemma assist : InPlay r b m := ⟨h.active,h.gap⟩
lemma draws (t : Site f) (U : Grid f) : ‖notch w (hefty r b t U m)‖ ≤ q :=
    Cost.contracts _ (cushions r h.active t U m) (hBound r h.active.le ..) h.pos h.touch h.hides -- fix
end Weak
variable (b m w) (t : Site f)

def crumbs (n : ℕ) (U : Grid f) := (w:ℂ) • notch w (hefty r b t U m)^n

def wither (n : ℕ) (x : Site f) (U : Grid f) := -(∑ j : Fiber, (plank (notch w (hefty r b t U m)) (x,j) n).re)

def barrel (n : ℕ) (U : Grid f) := (b:ℂ)^2 • (Q r t U*crumbs r b m w t n U * (Q r t U)ᴴ)
def axle (L : Side) (n : ℕ) := (reachQ L+hike L*n)+(reachQ L+reachQ L)

lemma bread (n : ℕ) : Reads eye eye (hike r.count*n) (crumbs r b m w t n) := ((((Reads.single.minus ((readH r b t m).coin (w:ℂ))).power n)).coin _)
lemma feather (n : ℕ) (x : Site f) : LocalOn (view x (hike r.count*(n+1))) (wither r b m w t n x) := by
  have he : Reads eye eye (hike r.count*(n+1)) (fun U:Grid f => notch w (hefty r b t U m)^(n+1)) := (Reads.single.minus ((readH r b t m).coin (w:ℂ))).power (n+1)
  intro U V H
  have ht (j : Fiber) : plank (notch w (hefty r b t U m)) (x,j) n=plank (notch w (hefty r b t V m)) (x,j) n := by
    unfold plank
    rw [show (notch w (hefty r b t U m)^(n+1)) (x,j) (x,j)=(notch w (hefty r b t V m)^(n+1)) (x,j) (x,j) from he.sees _ _ U V H]
  unfold wither; simp_rw [ht]
lemma axle_read (n : ℕ) : Reads (perch r) (perch r) (axle r.count n) (barrel r b m w t n) :=
    (((readQ r t).across (bread r ..)).across (readQ r t).turn).coin _

lemma govern (U : Grid f) (k : Frame f) (n : ℕ) :
    notch w (hefty r b t (gauge k U) m)^n=siteRot k*notch w (hefty r b t U m)^n * star (siteRot k) := by
  have he : notch w (hefty r b t (gauge k U) m)=siteRot k*notch w (hefty r b t U m) *star (siteRot k) := by
    rw [notch,gaugeH]; unfold notch
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,(siteRot_u k).2]
  induction n with
  | zero => rw [pow_zero,pow_zero,mul_one,(siteRot_u k).2]
  | succ n ih =>
    rw [pow_succ,ih,he,pow_succ]
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star _) (siteRot k),(siteRot_u k).1,Matrix.one_mul]

lemma block_sum (D : Sheet f) (k : Frame f) (x : Site f) :
    (∑ j : Fiber, (siteRot k*D*star (siteRot k)) (x,j) (x,j))=∑ j : Fiber, D (x,j) (x,j) := by
  let K := siteRot k; let H:=touch (colour (k x)); let B:=Matrix.of (fun i j => D (x,i) (x,j))
  have he (i y) : (K*D) (x,i) (x,y)=(H*B) i y := by
    rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single x]
    · simp only [K,siteRot,rr, Equiv.refl_apply,if_true]; rfl
    · intro j _ hj; simp only [K,siteRot,rr, Equiv.refl_apply, if_neg (Ne.symm hj), zero_mul,sum_const_zero]
    simp
  have ht (i) : (K*D*star K) (x,i) (x,i)=(H*B*star H) i i := by
    rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single x]
    · rw [Matrix.mul_apply]; apply sum_congr rfl; intro j _; rw [he]; congr 1; change star ((siteRot k) _ _) = _; rw [siteRot,rr, Equiv.refl_apply]; simp only [if_true]; rfl -- parsing (_ _)
    · intro j _ hj; simp [K,siteRot,rides,hj,Ne.symm hj]
    simp
  change ∑ j, (K*D*star K) _ _= _
  rw [sum_congr rfl (fun i _=> ht i)]; change (H*B*star H).trace=B.trace
  have hp : H∈unitary _ := touch_u ⟨su.mat_star_mul _,su.mat_mul_star _⟩
  rw [Matrix.trace_mul_cycle,hp.1, one_mul]
lemma logged (x : Site f) (n : ℕ) (U : Grid f) (k : Frame f) :
    wither r b m w t n x (gauge k U)=wither r b m w t n x U := by
  unfold wither plank; rw [← Complex.re_sum, ← Complex.re_sum,← sum_div,← sum_div]; simp_rw [govern,block_sum]
lemma crumbGauge (n : ℕ) (U : Grid f) (k : Frame f) :
    crumbs r b m w t n (gauge k U)=siteRot k*crumbs r b m w t n U*star (siteRot k) := by
  simp only [crumbs,govern,Matrix.smul_mul,Matrix.mul_smul]
lemma barrelGauge (n : ℕ) (U : Grid f) (k : Frame f) :
    barrel r b m w t n (gauge k U)=siteRot (k∘r.embed)*barrel r b m w t n U*star (siteRot (k∘r.embed)) := by
  unfold barrel; rw [crumbGauge,gaugeQ]
  simp only [Matrix.mul_smul, Matrix.smul_mul]; congr 1
  simp only [Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose (star _),star_star]
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star _) (siteRot k),(siteRot_u k).1, Matrix.one_mul, ← Matrix.mul_assoc (star _) (siteRot k),(siteRot_u k).1, Matrix.one_mul]; rfl
section
variable {b m w} (h : Weak r.count b m w q)
include h
lemma crumbs_sell (n : ℕ) (U : Grid f) : ‖crumbs r b m w t n U‖ ≤ w*q^n := by
  rw [crumbs,norm_smul, Complex.norm_real,Real.norm_of_nonneg h.pos.le]
  apply mul_le_mul_of_nonneg_left _ h.pos.le
  exact (Cost.power_bill ..).trans (pow_le_pow_left₀ (norm_nonneg _) (h.draws t U) n)
lemma wither_sell (n : ℕ) (x : Site f) (U : Grid f) : ‖wither r b m w t n x U‖ ≤ Fintype.card Fiber * q^(n+1) := by
  rw [wither,norm_neg]; refine (norm_sum_le _ _).trans ?_
  have hp := sum_le_sum (s:=univ) fun j _ => (Complex.abs_re_le_norm (plank (notch w (hefty r b t U m)) (x,(j:Fiber)) n)).trans ((plank_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) (h.draws t U) (n+1)))
  simpa [Real.norm_eq_abs] using hp
lemma barge (n : ℕ) (U : Grid f) : ‖barrel r b m w t n U‖ ≤ b^2 * (slope r.count*(w*q^n)*slope r.count) := by
  rw [barrel,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg h.active.le]
  refine mul_le_mul_of_nonneg_left ((Matrix.l2_opNorm_mul (Q r t U * _) (Q r t U)ᴴ).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (mul_nonneg (slope_pos _).le (mul_nonneg h.pos.le (pow_nonneg h.touch _))))) (sq_nonneg b)
  · exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (votes_cost ..) (crumbs_sell r t h ..) (norm_nonneg _) (slope_pos _).le)
  rw [Matrix.l2_opNorm_conjTranspose]; exact votes_cost ..

lemma crumb_series (U : Grid f) : HasSum (fun n => crumbs r b m w t n U) (hefty r b t U m)⁻¹ := chip _ h.pos.ne' (invertH r h.assist ..) ((h.draws t U).trans_lt h.aimed)
lemma withers (U : Grid f) :
    Real.log ((hefty r b t U m).det.re)=(∑ x, ∑' n, wither r b m w t n x U)- Fintype.card (Row f)*Real.log w := by
  let H := hefty r b t U m
  have hv : 0<H.det.re := positiveH r h.assist t U
  have ht : ‖H.det‖=H.det.re := by
    conv_lhs => rw [← determinant_real (J:=chirality _) chi_sq (D:=H) (gammaH r t U)]
    rw [Complex.norm_real,Real.norm_of_nonneg hv.le]
  let X := notch w H
  have hh : ‖X‖ < 1 := (h.draws t U).trans_lt h.aimed
  have he (i) : Summable (fun n => (plank X i n).re) := (Complex.reCLM.summable (planked X hh i))
  change Real.log H.det.re = _; rw [← ht,marks H h.pos hh,Fintype.sum_prod_type,← sum_neg_distrib]; unfold wither; congr 1
  apply sum_congr rfl; intro x _; rw [tsum_neg, Summable.tsum_finsetSum (f:=fun (i : Fiber) n => (plank X (x,i) n).re) (fun i _=>he _)] -- `_` fails
lemma target_series (U : Grid f) : target r b m t U=(b:ℂ) • 1 - ∑' n, barrel r b m w t n U := by
  let F : Cost.Mx (Row f)→ₗ[ℂ] Cost.Mx (Row c) := {
    toFun := fun X => (b:ℂ)^2 • (Q r t U * X * (Q r t U)ᴴ)
    map_add' := fun X Y => by simp [Matrix.mul_add,Matrix.add_mul,smul_add]
    map_smul' := fun i X => by rw [Matrix.mul_smul,Matrix.smul_mul,smul_comm]; rfl }
  unfold target; congr 1; exact ((LinearMap.toContinuousLinearMap F).hasSum (crumb_series r t h U)).tsum_eq.symm
end
end YM.QCD.Kit
