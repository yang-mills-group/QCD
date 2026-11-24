import YM.QCD.Flume.Sym
import YM.Next.FREE_KERNELS.Strands

/-!
# alias translation preprices. Out paravectors, either forward or barred gamma channel
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j k : ℕ}

lemma scaled_rank (p : Momentum) (hp : p∈cube zone) {L : Side} (l : Site L) : (L.val:ℝ)*‖aliasAt p l‖ ≤ 2*Real.pi*grade l := by
  rw [mul_comm, ← le_div_iff₀ (side_pos _),pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (by positivity) (grade_pos _).le) (by positivity))]
  intro i; rw [le_div_iff₀ (side_pos _),mul_comm]; exact (scaled_alias_upper l hp i).trans (mul_le_mul_of_nonneg_left (up_le ..) (by positivity))

lemma zero_col (f : ι→Momentum→ℂ) (h : Moderate (fun _ : ι=> 1) f) (hz : ∀ i, f i 0=0)
    (L : ι→Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) : Moderate (fun i=> grade (l i)) fun i p=> ((L i).val:ℂ)*f i (aliasAt p (l i)) := by
  obtain ⟨η,C,he,hc,H⟩:=h
  let θ:=min (η/4) zone
  have hθ:0<θ:=lt_min (by positivity) zone_pos
  have hu : θ≤η/4:= min_le_left ..
  let t:=η/2; have ht:0<t:= by unfold t; positivity
  have he' : θ≤η := by linarith
  refine ⟨θ,C/t*(2*Real.pi),hθ,by positivity,fun i=>⟨fun p hp=>?_,fun p hp=>?_⟩⟩
  · have he : Differentiable ℂ (fun p=>aliasAt p (l i)):=by unfold aliasAt; fun_prop
    exact DifferentiableAt.const_mul (( (H i).hol _ (cube_mono he' (alias_in_cube hθ hp (l i) (ho i)))).comp (f:=fun p=>aliasAt p (l i)) p he.differentiableAt) _
  let q:=aliasAt p (l i)
  have hx : q∈cube η:= cube_mono he' (alias_in_cube hθ hp _ (ho i))
  have hL : (L i).val*‖q‖ ≤ 2*Real.pi*grade (l i):= scaled_rank _ (cube_mono (min_le_right ..) hp) _
  rw [norm_mul,Complex.norm_natCast]
  have hw (p : Momentum) (hp : p∈cube η): ‖f i p‖≤C:= by simpa using (H i).bound p hp
  have hb : ‖f i q‖ ≤ C/t*‖q‖ := by
    by_cases hh:‖q‖<t
    · have hu : q∈ball (0:Momentum) t:=by simpa using hh
      have ht' : ball (0: Momentum) t ⊆ cube η:= (Metric.ball_subset_ball (show t≤η-θ from by unfold t; linarith)).trans (ball_inside_cube (cube_zero _ hθ))
      have hg (x : Momentum) (hx:x∈ball (0:Momentum) t) : f i x ∈closedBall (f i 0) C := Metric.mem_closedBall.mpr (by rw [hz,dist_zero_right]; exact hw x (ht' hx))
      simpa [hz] using Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun p hp=> ((H i).hol p (ht' hp)).differentiableWithinAt) hg hu
    push Not at hh; exact (hw q hx).trans (le_trans (le_of_eq (div_mul_cancel₀ _ ht.ne').symm) (mul_le_mul_of_nonneg_left hh (div_nonneg hc.le ht.le)))
  change _*‖f i q‖ ≤ _
  calc
    _ ≤ (L i).val*(C/t*‖q‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C/t*((L i).val*‖q‖) := by ring
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hL (div_nonneg hc.le ht.le)

def day (v : Flight j k) (l : Site v.L) (p : Momentum) : Para:= reciprocalP ((v.L.val:ℂ) • Dir v.wing (aliasAt p l))
lemma counter (hj : 4≤j) (v : ι→ Flight j k) (l : ∀ i, Site (v i).L) (he : ∀ i, l i≠0) : Scale (fun i => (grade (l i))⁻¹) fun i=> day (v i) (l i):= by
  let L:=fun i=> (v i).L
  let d (i : ι) (p : Momentum) := ((L i).val:ℂ) • Dir (v i).wing (aliasAt p (l i))
  have hA:=Dir_budget (j:=j) (by omega) fun i=> (v i).wing
  have hz : Scale (fun i=>grade (l i)) d := by
    constructor
    · exact zero_col _ hA.scalar (by simp) L (fun i=>(v i).odd) l
    exact fun a=> zero_col _ (hA.vector a) (by simp) L (fun i=>(v i).odd) l
  refine hz.reciprocal ?_ (fun i=>grade_pos ..)
  obtain ⟨η,c,hp,hη,hc,h⟩:=size_q (j:=j) (by omega)
  refine ⟨η,c*zone^2,hp,mul_pos hc (pow_pos zone_pos _),fun i p hx=> ?_⟩
  let r:=L i; let q:=aliasAt p (l i)
  have hw:= ((h (v i).wing q (alias_in_real hp hx _ (v i).odd)).1).trans (Complex.re_le_norm _)
  unfold d; dsimp only; rw [quad_smul,norm_mul,norm_pow,Complex.norm_natCast];
  obtain ⟨a,ha⟩:=hit_grade (l i)
  have hξ : zone * grade (l i) ≤ r.val * ‖q a‖:=by
    rw [ha]
    refine scaled_alias_lower _ (mem_cube_real (realCube_mono hη hx) zone_pos) _ ?_
    intro H; have hh:=grade_gt (he i); simp [ha,up,H] at hh
  calc
    _ = c*(zone *grade (l i))^2 := by ring
    _ ≤ c*(r.val*‖q a‖)^2:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos zone_pos (grade_pos _)).le hξ _) hc.le
    _ = (r.val:ℝ)^2*(c*‖q a‖^2):=by ring
    _ ≤ (r.val:ℝ)^2*(c*lengthSq q):= by gcongr; exact single_le_sum (fun j _=>sq_nonneg ‖q j‖) (mem_univ a)
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
lemma day_qual (v : Flight j k) (l : Site v.L) (p : Momentum) (hp : p∈realCube zone) (hi : l≠0 ∨ p≠0) :
    model (day v l p)=(v.L.val:ℂ)⁻¹ • model (full v.wing (aliasAt p l)) := by
  have h (c : ℂ) (hc : c≠0) (x : Para) : reciprocalP (c • x)=c⁻¹ • reciprocalP x:=by
    unfold reciprocalP; rw [show turn (c • x)=c • turn x from by ext <;> simp [turn],quad_smul,smul_smul, smul_smul, mul_inv]
    congr 1; field_simp
  obtain ⟨hm,ht⟩:= alias_regular hp l hi
  rw [day,h _ (side_ne _),model_smul,live_inv (nonzeroD hm ht),full_match hm ht]
lemma day_reverse (v : Flight j k) (l : Site v.L) (p : Momentum) (hp : p∈realCube zone) : day v (-l) (-p)=turn (day v l p):=by
  have h (c : ℂ) (x : Para) : turn (c • x)=c • turn x:=by ext <;> simp [turn]
  rw [day,day,alias_reverse p v.odd,evenD _ _ (alias_in_real zone_pos hp _ v.odd),← h]
  simp only [reciprocalP,quad_turn,turn_turn]; rw [h,turn_turn]
lemma day_native (v : Flight j k) (l : Site v.L) (p : Momentum) (hp : physical p) : Native (day v l p):= by unfold day; simpa using ((native_dir _ _ (alias_real hp _)).realSc v.L.val).reciprocal

/-- model either on gamma or its entrywise conjugate, retaining scalar/vector coefficients -/
def view (c : Bool) (A : Para) := if !c then model A else
    A.1 • 1 + Complex.I • ∑ i,A.2 i • shade (wave (gamma i))
lemma polarized (c : Bool) (A : Para) (h : Native A) : view (!c) (turn A)=shade (view c A):=by
  have he : shade ((A.1:ℂ) • (1:Bundle))=(A.1:ℂ) • 1:=by rw [shade_weight,h.1,shade_nil]
  have hz (f : Axis→Bundle): shade (∑ i,f i)=∑ i, shade (f i):=by ext a b; simp [shade,Matrix.sum_apply]
  have hu (i : Axis):star (A.2 i)=A.2 i := congr_fun h.2 i
  have hy (M : Bundle):shade (shade M)=M:=by ext a b; simp [shade]
  cases c <;> simp only [view,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,shade_add,turn,model,he,hiss, Pi.neg_apply,hz,shade_weight,hu,hy]
  all_goals simp
lemma view_false (A : Para) : view false A=model A:=rfl
lemma coil {w : ι→ℝ} {f : ι→Momentum→Para} (h : Scale w f) (c : Bool) : Pay w fun i p => view c (f i p):=by
  have he (q : Axis → Bundle): Pay w (fun i p=> (f i p).1 • (1:Bundle) + Complex.I • ∑ a, (f i p).2 a • q a):=by
    refine ⟨h.cash,fun a b=>?_⟩; simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]; apply Moderate.add
    · simpa only [mul_one] using h.scalar.mul (Moderate.const _)
    have hp := Moderate.sum Finset.univ _ h.cash (fun l _=> by simpa only [mul_one] using (h.vector l).mul (Moderate.const (q l a b)))
    simpa only [one_mul] using (Moderate.const _).mul hp
  cases c <;> exact he _
end YM.QCD.Flume
