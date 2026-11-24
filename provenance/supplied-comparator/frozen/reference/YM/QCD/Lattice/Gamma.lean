import YM.Space.Index
import YM.QCD.Group
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Euclidean Clifford convention -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Complex
open scoped Kronecker Matrix.Norms.Frobenius ComplexConjugate

abbrev Pinor := Fin 2 × Fin 2
abbrev Spike := Matrix Pinor Pinor ℂ
abbrev Pauli := Matrix (Fin 2) (Fin 2) ℂ

def sx : Pauli := !![0,1;1,0]
def sy : Pauli := !![0,-I;I,0]
def sz : Pauli := !![1,0;0,-1]

def gamma : Axis → Spike := ![sx ⊗ₖ (1:Pauli), sy ⊗ₖ sx, sy ⊗ₖ sy, sy ⊗ₖ sz]
def g5 := sz ⊗ₖ (1:Pauli)

lemma herm_x : star sx=sx := by ext i j; fin_cases i <;> fin_cases j <;> simp [sx]
lemma herm_y : star sy=sy := by ext i j; fin_cases i <;> fin_cases j <;> simp [sy]
lemma herm_z : star sz=sz := by ext i j; fin_cases i <;> fin_cases j <;> simp [sz]

section
local macro "pcheck" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [sx,sz,sy,Matrix.mul_apply,Fin.sum_univ_succ]))
lemma xx : sx*sx=1 := by pcheck
lemma yy : sy*sy=1 := by pcheck
lemma zz : sz*sz=1 := by pcheck
lemma xy : sx*sy=-(sy*sx) := by pcheck
lemma xz : sx*sz=-(sz*sx) := by pcheck
lemma yz : sy*sz=-(sz*sy) := by pcheck
end

lemma star_kr {i j : Type*} (A : Matrix i i ℂ) (B : Matrix j j ℂ) : star (A ⊗ₖ B)=star A ⊗ₖ star B :=
  Matrix.conjTranspose_kronecker ..
lemma kron_neg {i j : Type*} (A : Matrix i i ℂ) (B : Matrix j j ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨_,_⟩ ⟨_,_⟩; simp
lemma neg_kron {i j : Type*} (A : Matrix i i ℂ) (B : Matrix j j ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨_,_⟩ ⟨_,_⟩; simp

private lemma cases' (a : Axis) : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by fin_cases a <;> decide
private lemma g_0 : gamma 0 = sx ⊗ₖ (1:Pauli) := rfl
private lemma g_1 : gamma 1 = sy ⊗ₖ sx := rfl
private lemma g_2 : gamma 2 = sy ⊗ₖ sy := rfl
private lemma g_3 : gamma 3 = sy ⊗ₖ sz := rfl

@[simp] lemma gamma_star (a : Axis) : star (gamma a)=gamma a := by
  rcases cases' a with h|h|h|h <;>
    simp only [h,g_0,g_1,g_2,g_3,star_kr,herm_y,herm_x,herm_z,star_one]

@[simp] lemma g5_star : star g5=g5 := (star_kr ..).trans (by rw [herm_z,star_one]; rfl)

@[simp] lemma gamma_sq (a : Axis) : gamma a*gamma a=1 := by
  rcases cases' a with h|h|h|h <;>
    simp only [h,g_0,g_1,g_2,g_3,← Matrix.mul_kronecker_mul, xx,yy,zz,one_mul,Matrix.one_kronecker_one]
@[simp] lemma g5_sq : g5*g5=1 := by unfold g5; rw [← Matrix.mul_kronecker_mul,zz,one_mul,Matrix.one_kronecker_one]

lemma clifford {a b : Axis} (h : a ≠ b) : gamma a * gamma b = -(gamma b * gamma a) := by
  rcases cases' a with rfl|rfl|rfl|rfl <;> rcases cases' b with rfl|rfl|rfl|rfl <;>
    first | exact absurd rfl h | simp only [g_0,g_1,g_2,g_3, ← Matrix.mul_kronecker_mul, xy,xz,yz,kron_neg,neg_kron,one_mul,mul_one,neg_neg]

lemma five (a : Axis) : gamma a * g5 = -(g5 * gamma a) := by
  rcases cases' a with rfl|rfl|rfl|rfl <;>
    simp only [g_0,g_1,g_2,g_3,g5, ← Matrix.mul_kronecker_mul, xz,yz,kron_neg,one_mul,mul_one,neg_neg]

def lo (a : Axis) : Spike := (2:ℂ)⁻¹ • (1-gamma a)
def hi (a : Axis) : Spike := (2:ℂ)⁻¹ • (1+gamma a)

@[simp] lemma lo_star (a) : star (lo a)=lo a := by simp only [lo, star_smul, star_sub,star_one,gamma_star]; congr; norm_num
@[simp] lemma hi_star (a) : star (hi a)=hi a := by simp only [hi, star_smul, star_add,star_one,gamma_star]; congr; norm_num
lemma projectors (a) : lo a+hi a=1 := by
  rw [lo,hi, ← smul_add, show 1-gamma a+(1+gamma a)=(2:ℂ) • (1:Spike) by rw [two_smul]; abel, inv_smul_smul₀ (by norm_num)]
@[simp] lemma even_hi (a) : hi a * gamma a = hi a := by rw [hi,smul_mul_assoc, add_mul,gamma_sq,one_mul,add_comm]
@[simp] lemma gamma_hi (a) : gamma a * hi a = hi a := by simpa only [star_mul,gamma_star,hi_star] using congrArg star (even_hi a)
@[simp] lemma odd_lo (a) : lo a * gamma a = -lo a := by rw [lo,smul_mul_assoc,sub_mul,gamma_sq,one_mul,← neg_sub,smul_neg]
@[simp] lemma gamma_lo (a) : gamma a * lo a = -lo a := by simpa only [star_mul,gamma_star,lo_star,star_neg] using congrArg star (odd_lo a)
@[simp] lemma vanish (a) : lo a*hi a = 0 := by rw [hi, mul_smul_comm,mul_add,odd_lo,mul_one,add_neg_cancel,smul_zero]
@[simp] lemma vanish' (a) : hi a*lo a = 0 := by simpa only [star_mul,lo_star,hi_star,star_zero] using congrArg star (vanish a)
@[simp] lemma lo_sq (a) : lo a*lo a=lo a := by have h := congrArg (lo a * ·) (projectors a); simpa only [mul_add,vanish,add_zero,mul_one] using h
@[simp] lemma hi_sq (a) : hi a*hi a=hi a := by have h := congrArg (hi a * ·) (projectors a); simpa only [mul_add,vanish',zero_add,mul_one] using h

lemma swap_hi (a) : g5*hi a=lo a*g5 := by
  rw [lo,hi,mul_smul_comm,smul_mul_assoc,mul_add,sub_mul,mul_one,one_mul,five,sub_neg_eq_add]
lemma swap_lo (a) : g5*lo a=hi a*g5 := by simpa only [star_mul,g5_star,hi_star,lo_star] using (congrArg star (swap_hi a)).symm

lemma tangent (a b) (h : b≠a) : gamma b*lo a*gamma b=hi a := by
  rw [lo,hi,mul_smul_comm,smul_mul_assoc,mul_sub,mul_one,sub_mul, gamma_sq, clifford h,
    neg_mul,Matrix.mul_assoc, gamma_sq,mul_one,sub_neg_eq_add]
lemma tangent' (a b) (h : b≠a) : gamma b*hi a*gamma b=lo a := by
  rw [← tangent a b h, ← mul_assoc, ← mul_assoc,gamma_sq,one_mul,mul_assoc, gamma_sq,mul_one]

end YM.QCD.Lat
