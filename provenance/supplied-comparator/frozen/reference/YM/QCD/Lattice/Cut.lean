import YM.QCD.Matter
import YM.QCD.Grass.Fubini
import YM.QCD.Lattice.Magnet
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Coupled finite regulator

Bare Wilson action for gauge and antiperiodic fundamental Dirac Grassmann integral with common
bare mass-coordinate. Use continuous insertions; not declaring normalization valid without an
existence/lower-bound statement. Calculating on the unreduced field configurations, with tests
for gauge invariant insertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lat
open Grass Wilson Lattice Function Finset MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology

abbrev Modes (n : Side) (F : ℕ) := Row n × Flavor F
abbrev Fields (n : Side) (F : ℕ) := Grass.Dirac (Modes n F)
abbrev Insertion (n : Side) (F : ℕ) := C(Grid n, Fields n F)

def copies (F : ℕ) {i : Type*} (A : Matrix i i ℂ) := Matrix.blockDiagonal fun _ : Flavor F => A

section
variable {i : Type*} [Fintype i] [DecidableEq i]
@[simp] lemma copies_one (F : ℕ) : copies F (1:Cost.Mx i)=1 := Matrix.blockDiagonal_one
lemma copies_mul (F : ℕ) (A B : Cost.Mx i) : copies F (A*B)=copies F A*copies F B := Matrix.blockDiagonal_mul ..
lemma copies_star (F : ℕ) (A : Cost.Mx i) : copies F (star A)=star (copies F A) := (block_star ..).symm
lemma copies_unitary (F : ℕ) (U : Cost.Mx i) (h : U∈ unitary _) : copies F U∈unitary _ := by
  constructor
  · rw [← copies_star,← copies_mul,h.1,copies_one]
  rw [← copies_star,← copies_mul,h.2,copies_one]
lemma copies_det (F : ℕ) (A : Cost.Mx i) : (copies F A).det=A.det^F := by
  rw [copies,Matrix.det_blockDiagonal]; simp
end

variable {n : Side} {F : ℕ}

@[fun_prop] lemma continuous_shift (t : Site n) (a : Axis) : Continuous fun U : Grid n => shift t U a := by
  unfold shift thread; apply ride_c; intro x; fun_prop

@[fun_prop] lemma continuous_bareD (t : Site n) (m : ℝ) : Continuous fun U : Grid n => bareD t U m := by
  unfold bareD singleHop; fun_prop

@[fun_prop] lemma continuous_copies {i : Type*} [Fintype i] (F : ℕ) : Continuous fun A : Cost.Mx i => copies F A := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [copies, Matrix.blockDiagonal_apply]; split <;> fun_prop

/-- the regulators at explicit real scalar parameters. Stencil positive reflection plans at
all-link planes use this twist throughout. -/
structure Cut (n : Side) (F : ℕ) where
  β : ℝ
  t : Site n
  m : ℝ

namespace Cut
variable (C : Cut n F)

def ferm (U : Grid n) := copies F (bareD C.t U C.m)
def insertD : Insertion n F := ⟨fun U => gauss (C.ferm U), continuous_gauss.comp ((continuous_copies F).comp (continuous_bareD _ _))⟩
@[simp] lemma insertD_apply (U) : C.insertD U=gauss (C.ferm U) := rfl

def rate (x : Insertion n F) (U : Grid n) : ℂ := (bare C.β U : ℂ) * ber _ ((C.insertD*x) U)

@[fun_prop] lemma rate_cont (x : Insertion n F) : Continuous (C.rate x) := by unfold rate; fun_prop
lemma rate_pay (x : Insertion n F) : Integrable (C.rate x) (prior su n) :=
  (C.rate_cont x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Unnormalized regulator functional on all continuous Grassmann insertions -/
def raw : Insertion n F →ₗ[ℂ] ℂ where
  toFun x := ∫ U, C.rate x U ∂prior su n
  map_add' x y := by
    have h : C.rate (x+y) = C.rate x + C.rate y := funext fun i => by simp [rate,mul_add]
    rw [h]; exact integral_add (C.rate_pay _) (C.rate_pay _)
  map_smul' c x := by
    have h : C.rate (c • x) = c • C.rate x := funext fun i => by
      simp only [rate, ContinuousMap.mul_apply, ContinuousMap.smul_apply, mul_smul_comm, map_smul, Pi.smul_apply]
    rw [h]; exact integral_smul c (C.rate x)

def partitionR := (C.raw 1).re

def rateR (U : Grid n) := bare C.β U * (bareD C.t U C.m).det.re ^ F

lemma scaled_real (U) : (C.rateR U:ℂ)=C.rate 1 U := by simp only [rateR,rate,mul_one,insertD_apply,
  Complex.ofReal_mul,Complex.ofReal_pow,realD,det_amplitude,ferm,copies_det]

@[fun_prop] lemma real_cont : Continuous C.rateR := by unfold rateR; fun_prop
lemma real_pay : Integrable C.rateR (prior su n) :=
  C.real_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma located : C.partitionR=∫ U, C.rateR U ∂prior su n := by
  unfold partitionR
  change (∫ U, C.rate 1 U ∂prior su n).re = _
  simp_rw [← scaled_real, integral_complex_ofReal, Complex.ofReal_re]

lemma raw_one : C.raw 1=(C.partitionR:ℂ) := by
  change (∫ U, C.rate 1 U ∂prior su n) = _
  rw [located]; simp_rw [← scaled_real, integral_complex_ofReal]

/-- use only where `partitionR` has been proved nonzero. -/
def average : Insertion n F →ₗ[ℂ] ℂ := (C.partitionR:ℂ)⁻¹ • C.raw
lemma vacuum (h : 0<C.partitionR) : C.average 1=1 := by simp [average,raw_one,ne_of_gt h]
end Cut

-- gauge rotations
@[fun_prop] lemma gauge_c (k : Frame n) : Continuous (fun U : Grid n => Lattice.gauge k U) := by
  apply continuous_pi; intro i; unfold Lattice.gauge; fun_prop

def rotates (F : ℕ) (k : Frame n) := copies F (siteRot k)
lemma rotates_law (F : ℕ) (k : Frame n) : rotates F k∈unitary _ := copies_unitary _ _ (siteRot_u k)

/-- send ψ at x to k(x) ψ there. Bar transforms with the inverse. -/
def slots (F : ℕ) (k : Frame n) := adapter (rotates F k) (star (rotates F k)).transpose

lemma no_jac (F : ℕ) (k : Frame n) (x : Fields n F) : ber _ (slots F k x)=ber _ x := by
  rw [slots,volume_map,Matrix.det_transpose,← Matrix.det_mul,(rotates_law F k).2,Matrix.det_one,one_mul]

lemma site_op (k : Frame n) (C : Cut n F) (U) : C.ferm (gauge k U)=
    rotates F k*C.ferm U*star (rotates F k) := by rw [Cut.ferm,bareD_covariant]; unfold rotates; rw [copies_mul,copies_mul,copies_star]; rfl

lemma invariant_weight (k : Frame n) (C : Cut n F) (U : Grid n) :
    slots F k (C.insertD (Lattice.gauge k U)) = C.insertD U := by
  rw [slots,Cut.insertD_apply,gauss_map, Matrix.transpose_transpose,site_op,Cut.insertD_apply]; congr 1
  have h := (rotates_law F k).1
  rw [Matrix.mul_assoc (rotates F k*C.ferm U),h,Matrix.mul_one, ← Matrix.mul_assoc,h,Matrix.one_mul]

def transform (k : Frame n) (x : Insertion n F) : Insertion n F :=
  ⟨fun U => slots F k (x (gauge k U)), (slots F k).toLinearMap.continuous_of_finiteDimensional.comp
    (x.continuous.comp (gauge_c k))⟩

lemma transforms (k : Frame n) (C : Cut n F) (x : Insertion n F) (U) :
    C.rate (transform k x) U=C.rate x (gauge k U) := by
  rw [Cut.rate,Cut.rate,bare_gauge]
  rw [← no_jac F k ((C.insertD*x) (gauge k U))]
  simp only [ContinuousMap.mul_apply,map_mul,invariant_weight]; rfl

/-- local gauge rotation invariance at the finite regulator (whole group, including arbitrarily
rough transformations, any backgrounds in this geometry; no scalar positivity needed). -/
theorem invariant_raw (C : Cut n F) (k : Frame n) (x : Insertion n F) : C.raw (transform k x)=C.raw x := by
  change (∫ U, C.rate (transform k x) U ∂prior su n) = ∫ U, C.rate x U ∂prior su n
  simp_rw [transforms]
  have h := prior_gauge k
  nth_rw 2 [← h.map_eq]
  rw [integral_map h.aemeasurable (C.rate_cont _).aestronglyMeasurable]

def Invariant (x : Insertion n F) := ∀ k, transform k x=x
lemma invariant_mul (x y : Insertion n F) (hx : Invariant x) (hy : Invariant y) : Invariant (x*y) := by
  intro k; rw [show transform k (x*y)=transform k x * transform k y by
    ext1 i; exact map_mul (slots F k) _ _,hx,hy]
lemma invariant_one : Invariant (1:Insertion n F) := by intro k; ext1; exact map_one (slots F k)

end YM.QCD.Lat
