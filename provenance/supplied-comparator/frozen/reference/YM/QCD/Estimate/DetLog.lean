import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import YM.QCD.Estimate.Charts
import YM.QCD.Group
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# path series for logdet (no eigenvalue branch choice)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cost
open Finset Function Filter Set Metric
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma det_gate {M : ℂ → Mx A} {u : ℂ} {B : Mx A} (hM : M u=1)
    (hB : ∀ i j, HasDerivAt (fun x => M x i j) (B i j) u) : HasDerivAt (fun x => (M x).det) B.trace u := by
  classical
  let f (σ : Equiv.Perm A) (t : ℂ) := Equiv.Perm.sign σ • ∏ i, M t (σ i) i
  have ht (σ : Equiv.Perm A) : HasDerivAt (f σ) (if σ = 1 then ∑ i, B i i else 0) u := by
    have hh := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hB (σ i) i)).const_smul
      (Equiv.Perm.sign σ)
    simp only [hM] at hh; unfold f
    split_ifs with hi
    · subst σ; simpa only [Pi.smul_def, Equiv.Perm.sign_one, one_smul, Matrix.one_apply,
        Equiv.Perm.coe_one, id_eq, ↓reduceIte, Finset.prod_const_one,
        ← Finset.prod_fn (s := Finset.univ)] using hh
    have hv (i : A) : (∏ j ∈ Finset.univ.erase i, (1 : Matrix A A ℂ) (σ j) j) = 0 := by
      obtain ⟨j,hj,hs⟩ : ∃ j, j ≠ i ∧ σ j ≠ j := by
        by_contra! hf
        apply hi; ext j
        by_cases hj : j = i
        · subst j; by_contra! hl; exact hl (σ.injective (hf (σ i) hl))
        exact hf j hj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) (by simp [hs])
    simpa only [hv, zero_smul, Finset.sum_const_zero, smul_zero, Pi.smul_def, Finset.prod_apply] using hh
  simp_rw [Matrix.det_apply]; simpa [f, Matrix.trace] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)

lemma jacobi {M : ℂ → Mx A} {u : ℂ} {B : Mx A} (hM : IsUnit (M u).det)
    (hB : ∀ i j, HasDerivAt (fun x => M x i j) (B i j) u) :
    HasDerivAt (fun x => (M x).det) ((M u).det*((M u)⁻¹*B).trace) u := by
  let U x := (M u)⁻¹*M x
  have he i j : HasDerivAt (fun x => U x i j) (((M u)⁻¹*B) i j) u :=
    HasDerivAt.fun_sum fun k _ => (hB k j).const_mul _
  have hs := det_gate (M:=U) (Matrix.nonsing_inv_mul _ hM) he
  have ht x : (M u).det*(U x).det=(M x).det := by dsimp only [U]; rw [← Matrix.det_mul,← mul_assoc,Matrix.mul_nonsing_inv _ hM,one_mul] -- perhaps U.local
  simpa only [ht] using hs.const_mul ((M u).det)

lemma one_bound : ‖(1 : Mx A)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty A with h|h
  · rw [show (1:Mx A)=0 from Subsingleton.elim ..,norm_zero]; norm_num
  rw [Matrix.cstar_norm_def,map_one,norm_one]
lemma power_bill (M : Mx A) (n : ℕ) : ‖M^n‖ ≤ ‖M‖^n := by
  cases n
  · simpa only [pow_zero] using one_bound (A:=A)
  exact norm_pow_le' _ (by omega)
lemma trace_cost (M : Mx A) : ‖M.trace‖ ≤ Fintype.card A*‖M‖ := by
  refine (norm_sum_le _ (fun i => M i i)).trans ?_
  exact (sum_le_sum fun i _ => north M i i).trans (le_of_eq (by simp))

def plank (M : Mx A) (i : A) (n : ℕ) := (M^(n+1)) i i/(n+1:ℂ)
lemma plank_le (M : Mx A) (i n) : ‖plank M i n‖ ≤ ‖M‖^(n+1) := by
  rw [plank,norm_div, show ‖(n+1:ℂ)‖=(n+1:ℝ) by norm_cast]
  refine (div_le_self (norm_nonneg _) (by simp)).trans ((north ..).trans (power_bill ..))
lemma planked (M : Mx A) (h : ‖M‖<1) (i) : Summable (plank M i) :=
  ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg _) h)).of_norm_bounded (plank_le M i)

lemma logdet (M : Mx A) (h : ‖M‖<1) : (1-M).det = Complex.exp (-(∑ i, ∑' n, plank M i n)) := by
  obtain ⟨R,hR,hp⟩ : ∃ R : ℝ, 1<R ∧ R * ‖M‖<1 := by
    apply Frequently.exists (f:=𝓝[>] (1:ℝ))
    have he : Tendsto (fun w : ℝ => w*‖M‖) (𝓝 1) (𝓝 ‖M‖) := by simpa using (tendsto_id (x:=𝓝 (1:ℝ))).mul_const ‖M‖ -- check
    exact ((show ∀ᶠ u in 𝓝[>] (1:ℝ), 1<u from self_mem_nhdsWithin).and ((he.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h))).frequently
  let S := ball (0:ℂ) R
  have hS : IsOpen S := isOpen_ball
  have hc : IsPreconnected S := (convex_ball (0:ℂ) R).isPreconnected
  have hz : (0:ℂ) ∈ S := mem_ball_self (lt_trans zero_lt_one hR)
  have hh (u) (hu : u∈S) : ‖u • M‖ ≤ R*‖M‖ := by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hu).le (norm_nonneg _)
  let f n (u : ℂ) := ∑ i, plank (u • M) i n
  let g (n : ℕ) (u : ℂ) := (((u • M)^n)*M).trace
  let D (u : ℂ) := 1-u • M
  have ha (n : ℕ) (u) : f n u=u^(n+1)*((M^(n+1)).trace / (n+1:ℂ)) := by simp [f,plank,smul_pow, Matrix.trace, mul_sum,sum_div,mul_div_assoc]
  have hg (n : ℕ) (u : ℂ) : g n u=u^n*(M^(n+1)).trace := by dsimp only [g]; rw [ smul_pow, Matrix.smul_mul, Matrix.trace_smul, ← pow_succ]; rfl
  have he (n u) (hu : u ∈ S) : HasDerivAt (f n) (g n u) u := by
    rw [funext (ha n), hg]; convert! (hasDerivAt_pow (n+1) u).mul_const ((M^(n+1)).trace / (n+1:ℂ)) using 1 -- check
    first | rfl | (push_cast; field_simp)
  let C n := (Fintype.card A : ℝ)*((R*‖M‖)^n * ‖M‖)
  have hC : Summable C := ((summable_geometric_of_lt_one (mul_nonneg (by linarith) (norm_nonneg _)) hp).mul_right ‖M‖).mul_left _
  have hG (n) (x) (hx : x ∈ S) : ‖g n x‖ ≤ C n := by
    apply (trace_cost _).trans
    refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (by positivity)
    gcongr; exact (power_bill ..).trans (pow_le_pow_left₀ (norm_nonneg _) (hh _ hx) _)
  let T (u : ℂ) := ∑' n, f n u
  have hT (u) (hu : u ∈ S) : HasDerivAt T (((D u)⁻¹*M).trace) u := by
    have hr := hasDerivAt_tsum_of_isPreconnected hC hS hc he hG hz (by simp [ha]) hu
    let L := Matrix.traceLinearMap A ℂ ℂ -- check
    have hs : HasSum (fun n : ℕ => (u • M)^n) ((D u)⁻¹) := by rw [Matrix.nonsing_inv_eq_ringInverse]; exact hasSum_geom_series_inverse _ ((hh u hu).trans_lt hp)
    have hh := LinearMap.toContinuousLinearMap L |>.hasSum (hs.mul_right M)
    rw [show (∑' n, g n u)=_ from hh.tsum_eq] at hr; exact hr
  let E (u : ℂ) := (D u).det * Complex.exp (T u)
  have hE (u) (hu : u∈ S) : HasDerivAt E 0 u := by
    have hv i j : HasDerivAt (fun x => D x i j) ((-M) i j) u := by
      simpa only [D, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,smul_eq_mul,one_mul,zero_sub] using! ((hasDerivAt_const u ((1:Mx A) i j)).sub ((hasDerivAt_id' u).mul_const (M i j)))
    have hk : IsUnit (D u).det := (isUnit_one_sub_of_norm_lt_one ((hh u hu).trans_lt hp)).map (Matrix.detMonoidHom)
    convert! (jacobi hk hv).mul ((Complex.hasDerivAt_exp (T u)).comp u (hT u hu)) using 1; rw [Matrix.mul_neg,Matrix.trace_neg, Function.comp_apply]; ring
  have h₁ : (1:ℂ) ∈ S := by simp [S,hR]
  have hh := hS.is_const_of_deriv_eq_zero hc (fun x hx => (hE x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hE x hx).deriv) h₁ hz
  have hz' : E 0=1 := by simp_rw [E,T,ha]; simp [D]
  have h₁' : T 1=∑ i, ∑' n, plank M i n := by simp only [T,f,one_smul]; exact Summable.tsum_finsetSum (s:=univ) (fun i _ => planked M h i) -- orientation
  rw [← h₁',Complex.exp_neg]; rw [hz'] at hh; change (1- (1:ℂ) • M).det * _ = 1 at hh; rw [one_smul] at hh; exact eq_inv_of_mul_eq_one_left hh -- check
end YM.QCD.Cost
