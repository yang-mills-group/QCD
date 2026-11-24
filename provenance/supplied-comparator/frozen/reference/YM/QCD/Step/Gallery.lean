import YM.QCD.Step.Wrapper
import YM.RG.Push

/-!
# push the whole functional (shared gauge kernel) and the first Schur factor

Not a representation bound for the gauge integral; estimates for the high
fermion covariance to be made with the preceding gap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Grass Lat Lattice Wilson Finset Filter Function MeasureTheory
open scoped Matrix Topology Matrix.Norms.L2Operator
variable {A B C : Type*} [DecidableEq A] [Fintype B] [Fintype A] [DecidableEq B] [Fintype C]
variable {c f : Side} {b β m : ℝ}

def choir (F : ℕ) (M : Matrix A B ℂ) := Matrix.blockDiagonal fun _ : Flavor F => M
omit [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype C] in
lemma choir_mul (M : Matrix A B ℂ) (N : Matrix B C ℂ) (F) : choir F (M*N)=choir F M*choir F N := Matrix.blockDiagonal_mul ..
omit [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B] in
lemma choir_star (M : Matrix A B ℂ) (F) : choir F Mᴴ=(choir F M)ᴴ := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hv : a=b
  · subst b; simp [choir] -- check
  simp [choir,Matrix.blockDiagonal_apply',hv,Ne.symm hv]
omit [DecidableEq A] [DecidableEq B] in
lemma choir_smul (M : Matrix A B ℂ) (F) (c : ℂ) : choir F (c • M)=c • choir F M := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hv : a=b
  · subst b; simp [choir]
  simp [choir,Matrix.blockDiagonal_apply',hv]
lemma replicas (M : Matrix A A ℂ) (F) : choir F M=copies F M := rfl

@[fun_prop] lemma choir_cont (F : ℕ) : Continuous (choir F : Matrix A B ℂ → _) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [choir, Matrix.blockDiagonal_apply]; split <;> fun_prop
variable (r : Ratio c f) {F : ℕ}

def sew (b : ℝ) (t : Site f) (U : Grid f) (x : Fields f F) := sheath b (choir F (Q r t U)) x
lemma sow (t : Site f) (U : Grid f) (x : Fields f F) (hp : 0<b) : ber _ (sew r b t U x)=ber _ x := insulate hp.ne' ..
lemma sow_slots (t : Site f) (U : Grid f) (k : Frame f) (x : Fields f F) :
    slots F (k∘r.embed) (sew r b t (gauge k U) x)=sew r b t U (slots F k x) := by
  unfold sew; rw [gaugeQ,choir_mul,choir_mul, replicas (star _) _,copies_star]; exact compat (rotates_law F k) (rotates_law F (k∘r.embed)) _ _ _ -- copies star not defeq?

lemma allD (t : Site f) (U : Grid f) (F : ℕ) :
    copies F (bareD t U m)+(b:ℂ) • ((choir F (Q r t U))ᴴ*choir F (Q r t U))=copies F (hefty r b t U m) := by
  rw [hefty, ← choir_star, ← choir_mul,← choir_smul,replicas]; exact (Matrix.blockDiagonal_add (fun _ => _) (fun _ => _)).symm -- check
lemma factor (t : Site f) (U : Grid f) (F) (hp : InPlay r b m) :
    let A := Modes f F; let B := Modes c F
    sew r b t U (gauss (copies F (bareD t U m)))= ( (b:ℂ)⁻¹ ^ Fintype.card B * (hefty r b t U m).det^F) • gauss (copies F (target r b m t U)) := by
  let D:=choir F (Q r t U); let H := hefty r b t U m
  let X:= copies F H
  have h := invertH r hp t U
  have hu : IsUnit X.det := by change IsUnit (copies F H).det; rw [copies_det]; exact h.pow _
  have he : X⁻¹=copies F H⁻¹ := Matrix.inv_eq_right_inv (by rw [show X=copies F H from rfl, ← copies_mul,Matrix.mul_nonsing_inv _ h,copies_one])
  intro A B
  rw [sew, ← mul_one (gauss _), clothe]
  simp only [joinD, map_one,mul_one,allD]
  change (b:ℂ)⁻¹ ^ Fintype.card B • marginal _ _ (gauss (Matrix.fromBlocks X ((-b:ℂ) • Dᴴ) ((-b:ℂ) • D) ((b:ℂ) • 1))) = _ -- check
  rw [marginal_schur _ _ _ _ hu,he]; dsimp only [X]; rw [copies_det,smul_smul]; congr 2
  simp only [D, ← replicas, ← choir_star,Matrix.smul_mul,Matrix.mul_smul, ← choir_mul,target,smul_smul,neg_mul_neg,← sq]
  have hh : choir F ((b:ℂ) • (1:Matrix (Row c) (Row c) ℂ))=(b:ℂ) • 1 := by rw [choir_smul,replicas,copies_one]
  rw [← choir_smul,← hh]
  simp only [neg_sq] -- check
  exact (Matrix.blockDiagonal_sub _ _).symm -- check

/-! Keep continuous densities for these exact finite steps -/
def prepare (b : ℝ) (t : Site f) (x : Grid f→Fields f F) (U : Grid f) := sew r b t U (x U)
@[fun_prop] lemma prepare_cont (t : Site f) (x : Grid f→Fields f F) (hx : Continuous x) : Continuous (prepare r b t x) := by
  have he : Continuous (fun U : Grid f => (choir F (Q r t U) : Matrix (Modes c F) (Modes f F) ℂ)) := (choir_cont F).comp (continuous_Q r t)
  change Continuous ((fun (p : Matrix (Modes c F) (Modes f F) ℂ × Fields f F) => sheath b p.1 p.2) ∘ fun U => (choir F (Q r t U), x U))
  exact (sheath_cont (b:=b) (A:=Modes f F) (B:=Modes c F)).comp (he.prodMk hx)
variable {r}
lemma prepare_sum (t : Site f) (x : Grid f→Fields f F) (hx : Continuous x) : Integrable (prepare r b t x) (prior su f) :=
  (prepare_cont r t x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def deliver (S : RG.StepData c f) (β b : ℝ) (t : Site f) (x : Grid f→Fields f F) :=
  S.push β (prepare S.ratio b t x)
section
variable (S : RG.StepData c f) (h : S.IsKernel β su) (t : Site f) (x : Grid f→Fields f F) (hx : Continuous x)
include h hx
lemma deliver_pay : Integrable (deliver S β b t x) (prior su c) :=
    RG.StepData.push_integrable h _ (prepare_sum t x hx)
lemma delivered (hp : 0<b) : (∫ V, ber _ (deliver S β b t x V) ∂prior su c) =
    ∫ U, ber (Modes f F) (x U) ∂prior su f := by
  let W : Fields c F →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (ber _)
  change (∫ V, W (deliver S β b t x V) ∂_) = _
  rw [W.integral_comp_comm (deliver_pay S h t x hx)]; unfold deliver
  rw [RG.StepData.push_integral h _ (prepare_sum t x hx), ← W.integral_comp_comm (prepare_sum t x hx)]
  congr 1; funext U; exact sow S.ratio t U (x U) hp
lemma sustain (H : ∀ (U : Grid f) (V : Grid c) k, S.density β (gauge k U) (gauge (k∘S.ratio.embed) V)=S.density β U V)
    (V : Grid c) (k : Frame f) (he : ∀ U, slots F k (x (gauge k U))=x U) :
    slots F (k∘S.ratio.embed) (deliver S β b t x (gauge (k∘S.ratio.embed) V))=deliver S β b t x V := by
  let W : Fields c F →L[ℝ] Fields c F := (LinearMap.toContinuousLinearMap (slots F (k∘S.ratio.embed)).toLinearMap).restrictScalars ℝ
  unfold deliver RG.StepData.push
  let f := fun U => S.density β U (gauge (k∘S.ratio.embed) V) • prepare S.ratio b t x U
  have hf : Integrable f (prior su _) := RG.StepData.push_slice h _ _ (prepare_sum t x hx)
  change W (∫ U, f U ∂prior su _) = _
  rw [← W.integral_comp_comm hf]
  have hm:=prior_gauge k
  nth_rw 1 [← hm.map_eq]; rw [integral_map hm.aemeasurable (f:=fun U => W (f U)) (by rw [hm.map_eq]; exact (W.integrable_comp hf).aestronglyMeasurable)] -- check
  congr 1; funext U
  dsimp only [f]; rw [map_smul]
  change S.density _ _ _ • slots _ _ (sew _ _ _ _ _) = _
  rw [sow_slots, he, H]; rfl
end

def garment (C : Cut f F) (x : Insertion f F) : Grid f → Fields f F := fun U => (bare C.β U:ℂ) • ((C.insertD*x) U)
@[fun_prop] lemma wears (C : Cut f F) (x) : Continuous (garment C x) := by unfold garment; fun_prop
lemma linked (S : RG.StepData c f) (T : Cut f F) (h : S.IsKernel β su) (hp : 0<b) (x : Insertion f F) :
    (∫ V, ber _ (deliver S β b T.t (garment T x) V) ∂prior su c)=T.raw x := by
  rw [delivered S h _ _ (wears ..) hp]; change _=∫ U, T.rate x U ∂prior su f
  congr 1; funext U; unfold garment Cut.rate; rw [map_smul]; rfl
end YM.QCD.Kit
