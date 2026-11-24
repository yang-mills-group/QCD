import YM.QCD.Lattice.Cut

/-!
# Massive QCD regulator

Same regulator (`su`, `Lat.bareD` incl the Wilson term with AP seams,
`Wilson.bare`) and Berezin order (`psi i * bar i`) as `YM.QCD`. Diagonal
**flavor-dependent** bare mass matrix. No assumption on signs of bare m.

Use `Insertion` (continuous on the full space of torus links with values in
the finite Grassmann algebra), without any parity or flavor restriction.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson Function MeasureTheory
open scoped Matrix.Norms.Frobenius Matrix BigOperators Topology

abbrev Density (n : Side) (F : ℕ) := Grid n → Fields n F

variable {n : Side} {F : ℕ}

/-- Joint integral; use only with integrable input. -/
def joint (f : Density n F) := ∫ U, ber (Modes n F) (f U) ∂prior su n

/-- Wilson regulator, t locates the negative seams as in the `Lat.Cut` convention. -/
structure Regulator (n : Side) (F : ℕ) where
  β : ℝ
  t : Site n
  m : Flavor F → ℝ

namespace Regulator
variable (R : Regulator n F)

def D (U : Grid n) : Matrix (Modes n F) (Modes n F) ℂ :=
  Matrix.blockDiagonal fun i => bareD R.t U (R.m i)

@[fun_prop]
theorem continuous_D : Continuous R.D := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  rcases i with ⟨u,i⟩; rcases j with ⟨v,j⟩
  simp only [D, Matrix.blockDiagonal_apply]; split <;> fun_prop

/-- Joint density, no normalization. -/
def density : Insertion n F :=
  ⟨fun U => (bare R.β U : ℂ) • gauss (R.D U), by fun_prop⟩

@[simp] lemma density_apply (U) : R.density U = (bare R.β U : ℂ) • gauss (R.D U) := rfl

lemma integrable (x : Insertion n F) : Integrable (fun U => ber _ ((R.density*x) U)) (prior su n) :=
  (continuous_ber.comp (R.density*x).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def raw : Insertion n F →ₗ[ℂ] ℂ where
  toFun x := joint ⇑(R.density * x)
  map_add' x y := by
    change joint ⇑(R.density * (x+y)) = _
    rw [mul_add]; simp only [joint, ContinuousMap.add_apply,map_add]
    exact integral_add (R.integrable x) (R.integrable y)
  map_smul' z x := by
    simp only [joint,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
      mul_smul_comm,map_smul,RingHom.id_apply, integral_smul]

def Z := R.raw 1

/-- Needs `Z≠0`; the target will require strict positivity. -/
def average : Insertion n F →ₗ[ℂ] ℂ := R.Z⁻¹ • R.raw

@[simp] theorem average_one (h : R.Z ≠ 0) : R.average 1 = 1 := by
  change R.Z⁻¹ * R.Z = 1
  exact inv_mul_cancel₀ h

/-- The integrated mass is real (but pointwise nonnegative gauge marginal
for a degenerate pair does not transfer by this calculation). -/
def gaugeRate (U : Grid n) : ℝ := bare R.β U * ∏ i, (bareD R.t U (R.m i)).det.re

@[simp] theorem gaugeRate_complex (U) : (R.gaugeRate U : ℂ) = ber _ (R.density U) := by
  simp only [density_apply,gaugeRate,D,map_smul,Complex.ofReal_mul,
    Complex.ofReal_prod,realD,det_amplitude,Matrix.det_blockDiagonal,smul_eq_mul]

@[fun_prop] lemma continuous_gaugeRate : Continuous R.gaugeRate := by unfold gaugeRate; fun_prop

lemma partition : R.Z = ((∫ U, R.gaugeRate U ∂prior su n : ℝ) : ℂ) := by
  change joint ⇑(R.density*1) = _
  rw [mul_one]; unfold joint; simp_rw [← gaugeRate_complex]; rw [integral_complex_ofReal]

lemma Z_real : R.Z = R.Z.re := by rw [R.partition, Complex.ofReal_re]

/-- Exact recovery of baseline regulator when the masses coincide. -/
def common (C : Cut n F) : Regulator n F := ⟨C.β,C.t,fun _ => C.m⟩

@[simp] theorem common_raw (C : Cut n F) (x) : (common C).raw x = C.raw x := by
  change (∫ U, ber _ (((common C).density*x) U) ∂prior su n) = ∫ U, C.rate x U ∂prior su n
  congr 1; funext U; rw [ContinuousMap.mul_apply,density_apply,smul_mul_assoc,map_smul]; rfl

end Regulator
end YM.Massive
