import YM.QCD.Free.Symbol
import YM.Next.FREE_KERNELS.Train

/-!
# complex-momentum Dirac paravectors

Analytic symbol computations are complex. Ellipticity tests later at REAL cube.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Lattice Wilson Function Finset Matrix
open Laurent Bloch YM.Next.Free
open scoped Matrix Kronecker Topology BigOperators

/-- scalar and vector coefficients, entering spin matrices with an i. -/
abbrev Para := ℂ × Momentum

namespace Para

def solo (x : ℂ) : Para := (x,0)
def turn (A : Para) : Para := (A.1,-A.2)
def quad (A : Para) : ℂ := (A.1)^2+∑ i, A.2 i ^2
def beam (A B : Para) : ℂ := A.1 * B.1 + ∑ i, A.2 i * B.2 i
@[simp] lemma turn_turn (A : Para) : turn (turn A)=A := by simp [turn]
@[simp] lemma quad_turn (A : Para) : quad (turn A)=quad A := by simp [quad, turn]
@[simp] lemma quad_zero : quad 0=0 := by simp [quad]
lemma quad_add (A B : Para) : quad (A+B)=quad A+quad B+2*beam A B := by
  unfold quad beam
  simp_rw [Prod.fst_add,Prod.snd_add,Pi.add_apply,add_sq,sum_add_distrib]
  simp_rw [mul_assoc (2:ℂ),← mul_sum]; ring
lemma quad_smul (a : ℂ) (A : Para) : quad (a • A)=a^2*quad A := by
  simp [quad,mul_pow, Finset.mul_sum,mul_add]
lemma beam_smul (a b : ℂ) (A B : Para) : beam (a • A) (b • B)= a*b*beam A B := by
  unfold beam; rw [mul_add,Finset.mul_sum]; simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]; congr 1
  · ring
  refine Finset.sum_congr rfl fun _ _ => by ring

def hiss (x : Momentum) : Bundle := ∑ i, x i • wave (gamma i)

def model (A : Para) : Bundle := A.1 • 1 + Complex.I • hiss A.2
lemma hiss_square (x : Momentum) : hiss x*hiss x=(∑ i, x i^2) • 1 := by
  have he (s : Finset Axis) : (∑ i∈s, x i • wave (gamma i))*(∑ i∈s, x i • wave (gamma i))=(∑ i∈s,x i ^2) • 1:= by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      let M:=x a • wave (gamma a); let C:=∑ i∈s, x i • wave (gamma i)
      have hc : M*C=-(C*M):=by
        unfold C M; rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i hi=> ?_
        rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul,wave_mul,wave_mul,clifford (show a≠i from fun e=>ha (e ▸ hi)),wave]
        rw [show (- (gamma i*gamma a)) ⊗ₖ (1 : Matrix Hue Hue ℂ)=_ from kron_neg (gamma i*gamma a) (1 : Matrix Hue Hue ℂ)] -- check types signature
        simp_rw [smul_neg]; exact congr_arg Neg.neg (smul_comm ..)
      change (M+C)*(M+C)=_
      have hz : M*M=x a ^2 • 1 := by unfold M; rw [Matrix.smul_mul,Matrix.mul_smul,wave_mul,gamma_sq,wave_one,smul_smul,pow_two]
      rw [mul_add,add_mul,hz,add_mul,hc, ih,add_smul]; abel
  exact he _
lemma model_back (A : Para) : model (turn A)*model A=quad A • 1 := by
  unfold model turn
  dsimp only
  rw [show hiss (-A.snd)=-hiss A.snd from by simp [hiss]]
  simp only [mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,neg_mul,hiss_square,smul_smul]
  unfold quad; rw [add_smul,Complex.I_mul_I,pow_two,neg_smul]; simp only [smul_neg,neg_smul,one_smul,neg_neg]; rw [mul_comm Complex.I A.1]; abel
lemma model_forth (A : Para) : model A * model (turn A) = quad A • 1 := by simpa using model_back (turn A)
@[simp] lemma hiss_zero : hiss 0 = 0 := by simp [hiss]
@[simp] lemma model_zero : model 0 = 0 := by simp [model]
@[simp] lemma model_solo (x : ℂ) : model (solo x)=x • 1 := by simp [model,solo]
lemma model_smul (A : Para) (a : ℂ) : model (a • A)=a • model A := by
  unfold model hiss
  simp_rw [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply, smul_assoc a, ← Finset.smul_sum]
  rw [smul_add,smul_comm Complex.I a]
lemma model_add (A B : Para) : model (A+B)=model A+model B := by simp only [model,hiss,Prod.fst_add,Prod.snd_add,Pi.add_apply,add_smul,sum_add_distrib,smul_add]; abel

def signal : Para →ₗ[ℂ] Bundle where
 toFun:=model
 map_add':=model_add
 map_smul' a A := model_smul ..

def reciprocalP (A : Para) : Para := (quad A)⁻¹ • turn A
lemma reciprocates (A : Para) (ha : quad A≠0) : model (reciprocalP A)*model A=1 := by rw [reciprocalP,model_smul,Matrix.smul_mul,model_back,smul_smul,inv_mul_cancel₀ ha,one_smul]
lemma returned (A : Para) (ha : quad A≠0) : model A*model (reciprocalP A)=1 := mul_eq_one_comm.mp (reciprocates A ha)
lemma funds {A : Para} (h : quad A≠0) : IsUnit (model A).det := by
  have he := congr_arg det (returned A h); rw [det_mul,det_one] at he; refine IsUnit.mk0 _ (fun e => ?_); rw [e,zero_mul] at he; exact zero_ne_one he
lemma live_inv {A : Para} (h : quad A≠0) : model (reciprocalP A)=(model A)⁻¹ := (Matrix.inv_eq_left_inv (reciprocates A h)).symm

/-- actual all-coefficient reality -/
def Native (A : Para) := star A.fst=A.fst ∧ physical A.snd
lemma Native.scalar (x : ℝ) : Native (solo (x:ℂ)) := ⟨by simp [solo],by simp [solo,physical]⟩
lemma native_zero : Native 0 := ⟨star_zero _,by simp [physical]⟩
namespace Native
variable {A B : Para}
lemma caste (h : A.Native) : ((A.1.re:ℝ):ℂ)=A.1 := Complex.ext rfl (Eq.symm (Complex.conj_eq_iff_im.mp h.1))
lemma tangible (h : A.Native) (i) : (((A.2 i).re:ℝ):ℂ)=A.2 i := Complex.ext rfl (Eq.symm ((physical_iff _).mp h.2 i))
lemma ad (h : A.Native) (hb : B.Native) : (A+B).Native := by
  rcases h with ⟨h,h'⟩; rcases hb with ⟨hb,hb'⟩
  unfold physical at *
  simp [Para.Native,h,h',hb,hb',physical]
lemma realSc (h : A.Native) (x : ℝ) : ((x:ℂ) • A : Para).Native := by
  rcases h with ⟨h,h'⟩; unfold physical at *; simp [Para.Native,physical,h,h']
lemma recur {ι : Type*} (s : Finset ι) (f : ι → Para) (h : ∀ i∈s,(f i).Native) : Native (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact native_zero
  | insert i s hi ih => rw [sum_insert hi]; exact ad (h _ (by simp)) (ih fun j hj=> h j (by simp [hj]))
lemma rotated (h : A.Native) : Native (turn A) := ⟨h.1,by unfold turn physical; rw [star_neg, show star A.2=A.2 from h.2]⟩
lemma quad_m (h : A.Native) : quad A= (↑(A.fst.re^2 + ∑ i, (A.snd i).re^2 : ℝ):ℂ) := by
  unfold quad; push_cast; simp_rw [h.caste,h.tangible]
lemma quad_cast (h : A.Native) : ((quad A).re:ℂ)=quad A := by rw [h.quad_m]; simp only [Complex.ofReal_re]
lemma quad_ge (h : A.Native) : 0≤(quad A).re := by rw [h.quad_m,Complex.ofReal_re]; positivity
lemma magnitude (h : A.Native) : ‖quad A‖=(quad A).re := by rw [← h.quad_cast]; simp [h.quad_ge]
lemma first (h : A.Native) : (A.fst.re)^2 ≤ (quad A).re := by rw [h.quad_m,Complex.ofReal_re]; exact le_add_of_nonneg_right (sum_nonneg fun _ _=> sq_nonneg _)
lemma nodes (h : A.Native) (i) : (A.2 i).re^2 ≤ (quad A).re := by
  rw [h.quad_m,Complex.ofReal_re]; exact (single_le_sum (fun j _=> sq_nonneg (A.2 j|>.re)) (mem_univ i)).trans (le_add_of_nonneg_left (sq_nonneg _))
lemma conjugate (h : A.Native) : star (model A)=model (turn A) := by
  have hh : star (hiss A.2)=hiss A.2 := by unfold hiss; simp_rw [star_sum,star_smul,fun i => show star (A.2 i)=A.2 i from congr_fun h.2 i,wave_star,gamma_star]
  unfold model; rw [star_add,star_smul,star_one,h.1,star_smul,hh]; simp [turn,hiss]
lemma reciprocal (h : A.Native) : Native (reciprocalP A) := by
  unfold reciprocalP; rw [← h.quad_cast,← Complex.ofReal_inv]; exact h.rotated.realSc _
end Native
end Para
end YM.QCD.Flume
