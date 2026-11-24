import YM.QCD.Free.Menu

/-!
# Unitary mode decomposition
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Free
open Lat Lattice Wilson Finset
open scoped Matrix Kronecker Matrix.Norms.L2Operator BigOperators
variable {n : Side}

abbrev lined (X : Site n→Bundle) := rides (Equiv.refl _) X
lemma lined_law (X Y : Site n→Bundle) : lined X * lined Y=lined (X*Y) := by rw [lined,lined,ride_mul]; rfl
lemma face (p x : Site n) (X : Site n → Bundle) i j :
    (leaf n*lined X) (x,i) (p,j)=scarf p x * X p i j := by
  simp [Matrix.mul_apply,leaf,rides,Fintype.sum_prod_type,mul_ite,ite_mul, Matrix.one_apply,lined,plain]

def peel (X : Sheet n) := star (leaf n)*X*leaf n
lemma peel_add (X Y : Sheet n) : peel (X+Y) = peel X+peel Y := by rw [peel,mul_add,add_mul]; rfl
lemma peel_sub (X Y : Sheet n) : peel (X-Y) = peel X-peel Y := by rw [peel,mul_sub,sub_mul]; rfl
lemma peel_smul (X : Sheet n) (c : ℂ) : peel (c • X) = c • peel X := by rw [peel,mul_smul_comm,smul_mul_assoc]; rfl
lemma peel_mul (X Y : Sheet n) : peel (X*Y)=peel X * peel Y := by
  unfold peel; symm; calc
    _ = star (leaf n)*X*(leaf n*star (leaf n))*Y*leaf n := by simp only [mul_assoc]
    _ = _ := by rw [(leaf_u n).2, mul_one,mul_assoc (star _) X Y]
lemma peel_one : peel (1:Sheet n)=1 := by rw [peel,mul_one,(leaf_u n).1]
lemma peel_star (X : Sheet n) : peel (star X)=star (peel X) := by simp only [peel,star_mul,star_star,mul_assoc]
lemma peel_eq {X Y : Sheet n} (h : X*leaf n=leaf n*Y) : peel X=Y := by rw [peel,mul_assoc,h, ← mul_assoc,(leaf_u n).1,one_mul]
lemma peel_out (X : Sheet n) : X=leaf n*peel X * star (leaf n) := by rw [peel,← mul_assoc,← mul_assoc,(leaf_u n).2,one_mul,mul_assoc,(leaf_u n).2,mul_one]
lemma peel_injective : Function.Injective (peel (n:=n)) := fun x y h => (peel_out x).trans ((congrArg (leaf n*· *star (leaf n)) h).trans (peel_out y).symm)
lemma peel_spin (X : Spike) : peel (onSpin n X)=lined (fun _ => wave X) := by
  apply peel_eq; ext ⟨x,i⟩ ⟨p,j⟩; rw [face]
  rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single x]
  · simp [onSpin,leaf,rides,Matrix.one_apply,plain,ite_mul,mul_comm]
  · intro _ _ hx; simp [onSpin,rides,Ne.symm hx]
  simp

lemma travel (a) (x : Site n) : touch (thread 0 1 a x)=seam 0 x a • 1 := by
  have he : colour 1=1 := rfl
  rw [thread,Pi.one_apply,he,touch,Matrix.kronecker_smul, Matrix.one_kronecker_one]

lemma peel_shift (a : Axis) : peel (shift (0: Site n) 1 a) = lined fun i : Site n => cis (menu i a) • 1 := by
  apply peel_eq; ext ⟨x,i⟩ ⟨p,j⟩; rw [face]
  rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single (x+step a)]
  · simp only [shift, rr,hop, travel,if_true, Matrix.smul_apply, leaf, Matrix.kronecker_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    simp only [sum_ite_eq',mem_univ,if_true,plain, Matrix.of_apply,onestep]
  · intro b _ hx; simp [shift, rides,Ne.symm hx]
  simp

lemma peel_back (a : Axis) : peel (star (shift (0:Site n) 1 a))=lined fun i => star (cis (menu i a)) • 1 := by
  rw [peel_star,peel_shift]; unfold lined
  rw [ride_ad]
  simp [star_cis]

lemma peeled_hop (a : Axis) : peel (1-singleHop (0:Site n) 1 a) = lined fun i =>
    (↑(1-Real.cos (menu i a)):ℂ) • 1 + Complex.I • (Real.sin (menu i a):ℂ) • wave (gamma a) := by
  rw [peel_sub,peel_one,singleHop,peel_add,peel_mul,peel_spin,peel_mul,peel_spin,peel_shift,peel_back,lined_law, lined_law]
  rw [lined,lined,ride_add,show (1:Sheet n)=rides (Equiv.refl _) (fun _ => (1:Bundle)) from ridden.symm,ride_sub]
  congr 1; funext i; set p := menu i a
  change 1-(wave (lo a)*(cis p • 1)+wave (hi a)*(star (cis p) • 1)) = _
  have he := (wave_add (lo a) (hi a)).trans (by rw [projectors,wave_one])
  have hu : wave (lo a)-wave (hi a)=-(wave (gamma a)) := by
    have hv := congrArg (· * wave (gamma a)) (show wave (lo a)+wave (hi a)=1 from he)
    rw [add_mul,wave_mul,wave_mul,odd_lo,even_hi,one_mul,show wave (-(lo a)) = -wave (lo a) from kron_neg ..] at hv
    rw [← hv]; abel
  rw [star_cis,cis_trig,cis_trig,Real.cos_neg,Real.sin_neg, Complex.ofReal_neg,mul_neg]
  simp only [Matrix.mul_smul,mul_one]; set c : ℂ := ↑(Real.cos p); set s : ℂ := ↑(Real.sin p)
  change 1-((c+Complex.I*s) • _+(c+-(Complex.I*s)) • _)= _
  rw [show (c+Complex.I*s) • _+(c+-(Complex.I*s)) • _ = c • (wave (lo a)+wave (hi a))+ (Complex.I*s) • (wave (lo a)-wave (hi a)) from (by rw [smul_add,smul_sub,add_smul,add_smul,neg_smul]; abel : _ = _), he,hu]
  change 1 - (c • 1 + (Complex.I*s) • -(wave (gamma a))) = (↑(1-Real.cos p):ℂ) • _ + _
  rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul, smul_neg,← smul_smul]; dsimp only [c,s,p]; abel

lemma peeled (m : ℝ) : peel (bareD (0:Site n) 1 m)=lined fun i => display (menu i) m := by
  let f (a : Axis) (i : Site n) : Bundle := (↑(1-Real.cos (menu i a)):ℂ) • 1 + Complex.I • (Real.sin (menu i a):ℂ) • wave (gamma a)
  have he (S : Finset Axis) : peel (∑ a∈S, (1-singleHop (0:Site n) 1 a))= lined (∑ a∈S, f a) := by
    induction S using Finset.induction_on with
    | empty => simp [peel]; exact (ride_zero _).symm
    | insert a S ha ih => rw [sum_insert ha,peel_add,ih,peeled_hop,sum_insert ha,lined,lined,ride_add]
  rw [bareD,peel_add,he,peel_smul,peel_one,lined, show (1:Sheet n)=rides (Equiv.refl _) (fun _ => (1:Bundle)) from ridden.symm,ride_smul,ride_add]
  congr 1; funext i
  simp only [f,wmass,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,sum_add_distrib,← Finset.sum_smul,← smul_sum,display,Complex.ofReal_add,add_smul]
  rw [← Complex.ofReal_sum]; simp only [slash,sine,add_assoc]

/-- free propagator counting units. -/
def native {n : Side} (m : ℝ) := bareD (0:Site n) 1 m
lemma right_profile (n : Side) (m : ℝ) (hm : 0≤m) : ∃ X,
    native (n:=n) m * X=1 ∧ peel X = lined (fun i => (display (menu i) m)⁻¹) := by
  let f : Sheet n := lined (fun i => (display (menu i) m)⁻¹)
  let X := leaf n*f*star (leaf n)
  have hs : peel X=f := by rw [peel]; dsimp only [X]; rw [← mul_assoc,← mul_assoc,(leaf_u n).1,one_mul, mul_assoc,(leaf_u n).1,mul_one]
  refine ⟨X,peel_injective ?_, hs⟩
  rw [peel_mul,hs,native,peeled,peel_one]; dsimp only [f]; rw [lined_law]
  have ht (i : Site n) := Matrix.mul_nonsing_inv _ (invert (menu_pos i hm))
  unfold lined; convert ridden using 2 -- check
  exact funext ht

lemma usable (n : Side) (m : ℝ) (hm : 0≤m) : IsUnit (native (n:=n) m).det := by
  obtain ⟨X,hX,_⟩ := right_profile n m hm
  refine IsUnit.mk0 _ ?_; intro h; apply one_ne_zero (α:=ℂ); rw [← Matrix.det_one (n:=Row n),← hX, Matrix.det_mul,h,zero_mul]
lemma peel_green (n : Side) (m : ℝ) (hm : 0≤m) : peel (native (n:=n) m)⁻¹=lined (fun i => (display (menu i) m)⁻¹) := by -- parentheses parser
  obtain ⟨X,hX,h⟩ := right_profile n m hm
  rw [show (native (n:=n) m)⁻¹=X by
    conv_lhs => rw [← mul_one (native m)⁻¹, ← hX, ← mul_assoc,Matrix.nonsing_inv_mul _ (usable n m hm), one_mul], h]
end YM.QCD.Free
