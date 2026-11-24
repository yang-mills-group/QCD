import YM.QCD.Lattice.Coercion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Flat Wilson kernel; no doublers in the tree stencil

Inverse singular value budgets use the fermionic size, not merely scalar real parts. This
file is at zero connection, and does *not* prove interacting renormalized species control.
Counting symbol.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Free
open Lattice Finset Lat Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology BigOperators

def cis (x : ℝ) := Complex.exp ((x:ℂ) * Complex.I)
lemma cis_trig (x : ℝ) : cis x = (Real.cos x:ℂ)+Complex.I*(Real.sin x:ℂ) := by
  simp [cis,Complex.exp_mul_I,mul_comm Complex.I] -- check
lemma star_cis (x : ℝ) : star (cis x)=cis (-x) := by simp only [cis_trig, star_add,star_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.star_def,Complex.conj_ofReal, Complex.conj_I,mul_neg]; rw [mul_comm]
@[simp] lemma norm_cis (x : ℝ) : ‖cis x‖=1 := by simp [cis]
lemma cis_add (x y : ℝ) : cis (x+y)=cis x*cis y := by simp [cis, add_mul,Complex.exp_add]

abbrev Freq := Four ℝ

def slash (p : Freq) : Bundle := ∑ a, (p a:ℂ) • wave (gamma a)
lemma slash_star (p : Freq) : star (slash p)=slash p := by
  simp only [slash,star_sum, star_smul,Complex.star_def, Complex.conj_ofReal, wave_star,gamma_star]

def lensq (p : Freq) := ∑ a, p a^2
lemma lensq_ge (p : Freq) : 0≤lensq p := sum_nonneg fun _ _ => sq_nonneg _
lemma lensq_gt {p : Freq} (hp : p≠0) : 0<lensq p := by
  obtain ⟨i,hi⟩ : ∃ i, p i≠0 := by simpa [funext_iff] using hp
  exact (sq_pos_of_ne_zero hi).trans_le (single_le_sum (fun k _ => sq_nonneg (p k)) (mem_univ i))

lemma slash_sq (p : Freq) : slash p * slash p=(lensq p:ℂ) • 1 := by
  have h (k : Finset Axis) :
      (∑ a∈k,(p a:ℂ) • wave (gamma a))*(∑ a∈k,(p a:ℂ) • wave (gamma a)) = (↑(∑ a∈k, p a^2):ℂ) • 1 := by
    induction k using Finset.induction_on with
    | empty => simp
    | insert i k hi ih =>
      have hc : ∀ j∈k, wave (gamma i)*wave (gamma j) = -(wave (gamma j)*wave (gamma i)) := fun j hj => by
        rw [wave_mul, clifford (show i≠j from fun e => hi (e.symm ▸ hj)),wave_mul]; exact kron_neg ..
      set A := (p i:ℂ) • wave (gamma i)
      let B := ∑ a∈k,(p a:ℂ) • wave (gamma a)
      have hab : A*B=-(B*A) := by
        dsimp only [B]; rw [mul_sum,sum_mul, ← sum_neg_distrib]
        refine sum_congr rfl fun j hj => ?_
        dsimp only [A]; rw [Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_smul, hc j hj,
          smul_neg,smul_neg,smul_comm]
      rw [sum_insert hi,sum_insert hi]; change (A+B)*(A+B)=_
      rw [add_mul,mul_add,mul_add, ih,hab]
      dsimp only [A]; rw [Matrix.smul_mul,Matrix.mul_smul,wave_mul,gamma_sq,wave_one,smul_smul,← sq]
      push_cast; rw [add_smul]; abel
  exact h univ

def sine (p : Freq) : Freq := fun a => Real.sin (p a)
def wmass (p : Freq) := ∑ a, (1-Real.cos (p a))
def display (p : Freq) (m : ℝ) : Bundle := ((m + wmass p : ℝ):ℂ) • 1 + Complex.I • slash (sine p)
def square (p : Freq) (m : ℝ) := (m + wmass p)^2+lensq (sine p)

lemma skew_slash (p : Freq) : star (Complex.I • slash p)=-(Complex.I • slash p) := by
  rw [star_smul,slash_star]; simp only [Complex.star_def,Complex.conj_I, neg_smul]
lemma sumSquares (x : ℝ) (p : Freq) :
    star ((x:ℂ) • (1:Bundle)+Complex.I • slash p)*((x:ℂ) • 1+Complex.I • slash p) = (↑(x^2 + lensq p):ℂ) • 1 := by
  rw [star_add,star_smul,star_one,skew_slash]
  simp only [Complex.star_def, Complex.conj_ofReal,add_mul,mul_add,neg_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,slash_sq,smul_smul, ← mul_assoc, Complex.I_mul_I]
  push_cast; simp only [sq,add_smul,neg_smul,neg_neg]; rw [mul_comm Complex.I _]; abel

lemma display_square (p m) : star (display p m) * display p m=(square p m:ℂ) • 1 := sumSquares ..
lemma wpos (p) : 0 ≤ wmass p := sum_nonneg fun _ _ => sub_nonneg.mpr (Real.cos_le_one _)
lemma sq_pos (p m) : 0 ≤ square p m := add_nonneg (sq_nonneg _) (lensq_ge _)
lemma size (p m) (x) : ‖Cost.op (display p m) x‖^2 = square p m * ‖x‖^2 := by rw [← Cost.square, display_square, Cost.real_form,Cost.identity]
lemma size' (p m) (x) : ‖Cost.op (display p m) x‖=Real.sqrt (square p m)*‖x‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp; rw [size,mul_pow,Real.sq_sqrt (sq_pos ..)]
lemma invert {p m} (h : 0 < square p m) : IsUnit (display p m).det := by
  refine IsUnit.mk0 _ (norm_pos_iff.mp ((pow_pos (Real.sqrt_pos.mpr h) (Fintype.card Fiber)).trans_le ?_))
  exact Cost.min_det _ (by positivity) fun x => by rw [size']
lemma scale_inv {A : Type*} [Fintype A] [DecidableEq A] {D : Cost.Mx A} {g : ℝ} (hg : 0 < g) (h : ∀ x, ‖Cost.op D x‖=g*‖x‖) (he : IsUnit D.det) : ‖D⁻¹‖ ≤ g⁻¹ := by
  rw [Matrix.cstar_norm_def]; refine (Cost.op D⁻¹).opNorm_le_bound (by positivity) fun x => le_of_eq ?_
  calc
    _ = g⁻¹*(g*‖Cost.op D⁻¹ x‖) := by rw [← mul_assoc,inv_mul_cancel₀ hg.ne',one_mul]
    _ = _ := by
      rw [← h,← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ he,map_one, one_apply_eq_self]
lemma inverse {p m} (h : 0 < square p m) : ‖(display p m)⁻¹‖ ≤ (Real.sqrt (square p m))⁻¹ :=
  scale_inv (Real.sqrt_pos.mpr h) (size' p m) (invert h)

def Boxed (p : Freq) := ∀ a, |p a| ≤ Real.pi
lemma wilsonLower (p : Freq) (hm : Boxed p) : 4 / Real.pi^2 * lensq p ≤ square p 0 := by
  let c : Axis → ℝ := fun a => 1-Real.cos (p a)
  have hc (a) : 0≤c a := sub_nonneg.mpr (Real.cos_le_one _)
  have h (a) : 4/Real.pi^2 * (p a)^2 ≤ c a ^2+sine p a^2 := by
    have ht := Real.cos_le_one_sub_mul_cos_sq (hm a)
    have hu := Real.sin_sq_add_cos_sq (p a)
    dsimp only [c,sine]; simp only [div_eq_mul_inv] at *; nlinarith [ht]
  have hr : ∑ a, c a^2 ≤ wmass p^2 := calc
    _ ≤ ∑ a, (c a * ∑ b,c b) := sum_le_sum fun a _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (single_le_sum (fun a _ => hc a) (mem_univ a)) (hc a)
    _ = _ := by rw [← sum_mul,sq]; rfl
  simp only [lensq,square,zero_add,mul_sum]
  exact (sum_le_sum fun a _ => h a).trans (by rw [sum_add_distrib]; gcongr)
lemma wilsonLower' (p : Freq) (h : Boxed p) {m : ℝ} (hm : 0≤m) :
    m^2+4 / Real.pi^2 * lensq p ≤ square p m := by
  have he := wilsonLower p h
  simp only [square,zero_add] at *; nlinarith [wpos p]
lemma unique {p : Freq} (h : Boxed p) : (display p 0).det=0 ↔ p=0 := by
  constructor
  · intro e; by_contra! hp
    exact (invert (lt_of_lt_of_le (mul_pos (by positivity) (lensq_gt hp)) (wilsonLower p h))).ne_zero e
  rintro rfl; simp [display,sine,slash,wmass]

/-- pointwise reference Dirac -/
def jet (p : Freq) : Bundle := Complex.I • slash p
lemma jet_inv {p : Freq} (h : p≠0) : IsUnit (jet p).det := by
  have hh : star (jet p)*jet p=(lensq p:ℂ) • 1 := by simpa [jet] using sumSquares 0 p
  refine IsUnit.mk0 _ ?_; intro he
  replace hh := congrArg Matrix.det hh
  simp only [Matrix.det_mul, he,mul_zero, Matrix.det_smul, Matrix.det_one,mul_one] at hh
  have hz := pow_ne_zero (Fintype.card Fiber) (show (lensq p:ℂ)≠0 by exact_mod_cast (lensq_gt h).ne')
  exact hz hh.symm
end YM.QCD.Free
