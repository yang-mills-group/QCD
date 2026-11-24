import YM.QCD.Step.Moat

/-! # volume-independent analytic moats, fixed ratio starting D -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Finset Function Filter Lat Wilson Lattice Cost
open scoped Matrix Matrix.Norms.L2Operator Topology BigOperators ContDiff
variable {c f : Side} (r : Ratio c f)

def loft (t : Site f) (P : Pulse f) := (votes:ℂ)⁻¹ • ∑ o : Lattice.Order, (scale r.count:ℂ) • ∑ j : Site r.count,
  scoop r*plaza t (path r o j) P
def descent (t : Site f) (P : Pulse f) := (votes:ℂ)⁻¹ • ∑ o : Lattice.Order, (scale r.count:ℂ) • ∑ j : Site r.count,
  plaza t (Lattice.reverse (path r o j)) P*(scoop r)ᴴ

def piste (t : Site f) (m : ℝ) (P : Pulse f) := (m:ℂ) • (1:Sheet f)+∑ a, (1-(onSpin f (lo a)*march t (posDir a) P + onSpin f (hi a)*march t (negDir a) P))
lemma pista (t : Site f) (m) (U : Grid f) : piste t m (settled U)=bareD t U m := by simp only [piste,marching,bareD,singleHop]; rfl

lemma estateQ (t : Site f) (U : Grid f) : loft r t (settled U)=Q r t U := by simp only [loft,plaza_leg]; rfl
lemma stated (t : Site f) (U : Grid f) : descent r t (settled U)=(Q r t U)ᴴ := by
  unfold descent Q vane
  simp only [plaza_leg, Matrix.conjTranspose_smul,Matrix.conjTranspose_sum,stripe,Matrix.conjTranspose_mul,flipping]
  simp only [Complex.star_def,map_inv₀,map_natCast, Complex.conj_ofReal]; rfl

lemma allowance {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] {x y : Lattice.Order→Site r.count → A} {u : ℝ}
    (h : ∀ o i, ‖x o i-y o i‖ ≤ u) :
    ‖(votes:ℂ)⁻¹ • (∑ o, (scale r.count:ℂ) • ∑ i, x o i) - (votes:ℂ)⁻¹ • (∑ o, (scale r.count:ℂ) • ∑ i,y o i)‖ ≤ yieldL r.count*u := by
  rw [← smul_sub,norm_smul,← sum_sub_distrib,norm_inv,Complex.norm_natCast]
  have he (o) : ‖(scale r.count:ℂ) • (∑ i,x o i) - (scale r.count:ℂ) • ∑ i,y o i‖ ≤ yieldL r.count*u := by -- parentheses!
    rw [← smul_sub,norm_smul, ← sum_sub_distrib,Complex.norm_real,Real.norm_of_nonneg (scale_pos _).le]
    refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => h o i)) (scale_pos _).le).trans (le_of_eq ?_)
    rw [sum_const,card_univ,nsmul_eq_mul,yieldL,mul_assoc]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => he i)) (by positivity)
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul, ← mul_assoc,inv_mul_cancel₀ poll_pos.ne',one_mul]

def hedged (L : Side) (δ : ℝ) := yieldL L*((1+‖TouchL‖*δ)^reach L-1)
lemma guards (t : Site f) (U : Grid f) (P : Pulse f) {δ : ℝ} (hδ : ‖P-settled U‖≤δ) :
    ‖loft r t P-loft r t (settled U)‖ ≤ hedged r.count δ ∧ ‖descent r t P-descent r t (settled U)‖ ≤ hedged r.count δ := by
  have hd := (norm_nonneg _).trans hδ
  have hu (w : Walk) (h : w.length ≤ reach r.count) : ‖plaza t w P-plaza t w (settled U)‖ ≤ (1+‖TouchL‖*δ)^reach r.count -1 :=
    (plazas t w P U (mul_le_mul_of_nonneg_left hδ (norm_nonneg TouchL))).trans (by gcongr; exact le_add_of_nonneg_right (by positivity))
  constructor
  · apply allowance
    intro o i
    rw [← Matrix.mul_sub]; exact (Matrix.l2_opNorm_mul _ _).trans (by rw [price_scoop,one_mul]; exact hu _ (Kit.covers ..))
  apply allowance; intro o i
  rw [← Matrix.sub_mul]; exact (Matrix.l2_opNorm_mul _ _).trans (by rw [Matrix.l2_opNorm_conjTranspose,price_scoop,mul_one]; exact hu _ (by simpa [Lattice.reverse,path] using Kit.covers r.count o i))

lemma projBudget (a : Axis) : ‖onSpin f (lo a)‖ ≤ 1 ∧ ‖onSpin f (hi a)‖ ≤ 1 := by
  have he (S : Spike) (h : star S=S) (hp : S*S=S) : ‖onSpin f S‖≤1 := by
    have ht:=Matrix.l2_opNorm_conjTranspose_mul_self (onSpin f S); rw [← Matrix.star_eq_conjTranspose, on_spin_star,h, on_spin_mul,hp] at ht; nlinarith
  exact ⟨he _ (lo_star a) (lo_sq a), he _ (hi_star a) (hi_sq a)⟩
lemma pistaBounds (t : Site f) m (P : Pulse f) (U : Grid f) :
    ‖piste t m P-piste t m (settled U)‖≤8*(‖TouchL‖*‖P-settled U‖) := by
  let D (a : Axis) (d : Pulse f) := onSpin f (lo a)*march t (posDir a) d + onSpin f (hi a)*march t (negDir a) d; let p:=‖TouchL‖*‖P-settled U‖; let X:=settled U
  have he (a : Axis) (d : Step) (Y : Spike) (h : ‖onSpin f Y‖≤1) (hd : d.dir=a) : ‖onSpin f Y * march t d P-onSpin f Y*march t d X‖ ≤ p := by
    rw [← Matrix.mul_sub]; exact (norm_mul_le ..).trans ((mul_le_mul h (march_budget t d P X) (by positivity) zero_le_one).trans (le_of_eq (one_mul p)))
  have ht (a : Axis) : ‖(1-D a P)-(1-D a X)‖ ≤ p+p := by
    rw [sub_sub_sub_cancel_left,norm_sub_rev]; unfold D
    rw [add_sub_add_comm]
    exact (norm_add_le ..).trans (add_le_add (he a (posDir a) _ (projBudget a).1 rfl) (he a (negDir a) _ (projBudget a).2 rfl))
  rw [piste,piste,add_sub_add_left_eq_sub, ← sum_sub_distrib] -- check
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun a _=>ht a)).trans (le_of_eq (by change ∑ _ : Axis, _ = 8*p; simp [Axis]; ring)))

def chute (t : Site f) (m b : ℝ) (P : Pulse f) := piste t m P+(b:ℂ) • (descent r t P*loft r t P) -- b real infer?
def armor (L : Side) (b δ : ℝ) := 8*(‖TouchL‖*δ) + b*(hedged L δ*(slope L+hedged L δ)+slope L*hedged L δ)
lemma shields (t : Site f) (b m : ℝ) (h : 0≤b) (P : Pulse f) (U : Grid f) {δ : ℝ} (hp : ‖P-settled U‖≤δ) : ‖chute r t m b P - hefty r b t U m‖ ≤ armor r.count b δ := by
  let X:=settled U; let F:= loft r t; let T:= descent r t
  let s:=slope r.count; let a:=hedged r.count δ
  rw [chute,hefty,← pista,← stated,← estateQ r t U] -- rw nested risk
  change ‖piste t m P+(b:ℂ) • (T P*F P) -(piste t m X+(b:ℂ) • (T X*F X))‖ ≤ _
  have he : ‖F P-F X‖≤a ∧ ‖T P-T X‖ ≤ a := guards r t U P hp
  have hh : ‖F X‖ ≤ s := by change ‖loft r t _‖ ≤ _; rw [estateQ]; exact votes_cost ..
  have hA : 0≤a := (norm_nonneg _).trans he.1
  have hv : ‖F P‖ ≤ s+a := by linarith [(norm_sub_norm_le _ _).trans he.1]
  have hz : ‖T X‖ ≤ s := by change ‖descent r t _‖≤_; rw [stated, Matrix.l2_opNorm_conjTranspose]; exact votes_cost ..
  rw [add_sub_add_comm,← smul_sub]; apply (norm_add_le ..).trans (add_le_add ((pistaBounds t m P U).trans (by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg TouchL)) (by norm_num))) _)
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg h,show T P*F P-T X*F X=(T P-T X)*F P + T X*(F P-F X) by rw [Matrix.mul_sub,Matrix.sub_mul]; abel]
  apply mul_le_mul_of_nonneg_left _ h
  exact (norm_add_le ..).trans (add_le_add ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul he.2 hv (norm_nonneg _) hA)) ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hz he.1 (norm_nonneg _) (slope_pos _).le)))
section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
lemma matrixSmooth (X : D → Matrix A B ℂ) (Y : D → Matrix B C ℂ) (h : ContDiff ℂ ω X) (g : ContDiff ℂ ω Y) :
    ContDiff ℂ ω (fun i => X i*Y i) := by
  let L : Matrix A B ℂ →ₗ[ℂ] Matrix B C ℂ →ₗ[ℂ] Matrix A C ℂ := LinearMap.mk₂ ℂ (· * ·) Matrix.add_mul Matrix.smul_mul Matrix.mul_add (fun c x y=> Matrix.mul_smul x c y)
  let W := L.mkContinuous₂ 1 (fun x y => by rw [one_mul]; exact Matrix.l2_opNorm_mul x y)
  exact (W.contDiff.comp h).clm_apply g
end
@[fun_prop] lemma smoothL (t : Site f) : ContDiff ℂ ω (loft r t) := by
  unfold loft; refine ContDiff.const_smul _ (ContDiff.sum (fun o _ => ?_))
  refine ContDiff.const_smul _ (ContDiff.sum fun i _ => matrixSmooth (fun _ : Pulse f=>scoop r) _ contDiff_const (smoothM ..))
@[fun_prop] lemma smoothT (t : Site f) : ContDiff ℂ ω (descent r t) := by
  unfold descent; refine ContDiff.const_smul _ (ContDiff.sum (fun o _ => ?_))
  refine ContDiff.const_smul _ (ContDiff.sum fun i _ => matrixSmooth _ (fun _ : Pulse f=>(scoop r)ᴴ) (smoothM ..) contDiff_const)
@[fun_prop] lemma smoothP (t : Site f) (m : ℝ) : ContDiff ℂ ω (piste t m) := by
  unfold piste; refine contDiff_const.add (ContDiff.sum (fun i _ => ?_)); exact contDiff_const.sub ((contDiff_const.mul (LinearMap.toContinuousLinearMap _).contDiff).add (contDiff_const.mul (LinearMap.toContinuousLinearMap _).contDiff))
@[fun_prop] lemma smoothH (t : Site f) (m b) : ContDiff ℂ ω (chute r t m b) := (smoothP t m).add (ContDiff.const_smul (b:ℂ) (matrixSmooth _ _ (smoothT ..) (smoothL ..)))
end YM.QCD.Kit
