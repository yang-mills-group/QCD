import YM.QCD.Group

/-!
# Plane decomposition for su3, real Lie algebra in the defining representation
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD
namespace Roots

open scoped Topology Matrix.Norms.Frobenius BigOperators ComplexConjugate
open Complex

abbrev Root := Fin 3

def a : Root → Hue := ![0, 0, 1]
def b : Root → Hue := ![1, 2, 2]

theorem asc (p : Root) : a p < b p := by fin_cases p <;> decide

/-- Pure imaginary diagonal (use only at trace zero when claiming Lie). -/
def H (h : Hue → ℝ) : Mat := Matrix.diagonal fun i => (h i : ℂ) * I

/-- A real two-dimensional plane -/
def plane (p : Root) (z : ℂ) : Mat :=
  Matrix.single (a p) (b p) z - Matrix.single (b p) (a p) (conj z)

def coroot (p : Root) : Hue → ℝ := Pi.single (a p) 1 - Pi.single (b p) 1

def weights (X : Mat) : Hue → ℝ := fun i => (X i i).im

def br (A B : Mat) := A * B - B * A

@[simp] theorem brackets_neg (A B : Mat) : -br A B = br B A := neg_sub ..

lemma H_lie {h : Hue → ℝ} (hu : ∑ i, h i = 0) : H h ∈ su.lie := by
  apply (lie_iff _).mpr
  constructor
  · rw [Matrix.star_eq_conjTranspose]; ext i j
    by_cases h' : i = j
    · subst j; simp [H]
    simp [H,h',Ne.symm h']
  simp only [H, Matrix.trace_diagonal, ← Finset.sum_mul, ← ofReal_sum, hu]; simp

@[simp] lemma plane_zero (p : Root) : plane p 0 = 0 := by simp [plane]

lemma plane_add (p : Root) (z w : ℂ) : plane p (z+w) = plane p z + plane p w := by
  simp only [plane, map_add, Matrix.single_add]; abel

lemma plane_smul (p : Root) (z : ℂ) (s : ℝ) : plane p (s • z) = s • plane p z := by
  simp [plane, smul_sub, Matrix.smul_single, Complex.real_smul]

lemma plane_lie (p : Root) (z : ℂ) : plane p z ∈ su.lie := by
  apply (lie_iff _).mpr
  constructor
  · rw [plane, star_sub]; simp [Matrix.star_eq_conjTranspose]
  simp [plane, Matrix.trace_single_eq_of_ne _ _ _ (asc p).ne,
    Matrix.trace_single_eq_of_ne _ _ _ (asc p).ne']

lemma coroot_units (p : Root) : ∑ i, coroot p i = 0 := by simp [coroot,Finset.sum_sub_distrib,Pi.single_apply]

@[simp] lemma upper (p : Root) (z : ℂ) : plane p z (a p) (b p) = z := by
  simp [plane, Matrix.single, (asc p).ne, (asc p).ne']

lemma from_lie {X : Mat} (hX : X ∈ su.lie) (i j : Hue) : X j i = -conj (X i j) := by
  have hp := congrFun (congrFun ((lie_iff X).mp hX).1 j) i
  simpa [Matrix.star_eq_conjTranspose] using congrArg Neg.neg hp.symm

lemma entries_zero {X : Mat} (hX : X ∈ su.lie) (i : Hue) : (X i i).re = 0 := by
  have he := congrArg Complex.re (from_lie hX i i); simp at he; linarith

lemma units {X : Mat} (hX : X ∈ su.lie) : ∑ i, weights X i = 0 := by
  simpa [weights,Matrix.trace] using congrArg Complex.im ((lie_iff X).mp hX).2

lemma decompose {X : Mat} (hX : X ∈ su.lie) :
    X = H (weights X) + ∑ p, plane p (X (a p) (b p)) := by
  have hd (i : Hue) : (X i i) = (weights X i : ℂ) * I := by
    apply Complex.ext <;> simp [weights, entries_zero hX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, b, H, plane, Fin.sum_univ_three, Matrix.single] <;>
    first | apply hd | exact from_lie hX _ _

lemma action (h : Hue → ℝ) (X : Mat) (i j : Hue) : br (H h) X i j =
    I * ((h i - h j : ℝ) : ℂ) * X i j := by
  simp only [br, Matrix.sub_apply,H,Matrix.diagonal_mul,Matrix.mul_diagonal,ofReal_sub]; ring

lemma spin (h : Hue → ℝ) (p : Root) (z : ℂ) :
    br (H h) (plane p z) = plane p (I * ((h (a p) - h (b p) : ℝ) : ℂ) * z) := by
  ext i j
  rw [action]
  by_cases hu : a p = i ∧ b p = j
  · rcases hu with ⟨rfl',rfl''⟩
    subst i j; rw [upper, upper]
  by_cases hd : b p = i ∧ a p = j
  · rcases hd with ⟨rfl',rfl''⟩
    subst i j
    simp [plane, Matrix.single, (asc p).ne, (asc p).ne']; ring
  simp [plane, Matrix.single, hu, hd]

/-- Bracketing the angular and radial direction in a real root plane -/
lemma rotated (p : Root) (z : ℂ) : br (plane p (I*z)) (plane p z) =
    (-2 * normSq z : ℝ) • H (coroot p) := by
  let i := a p; let j := b p
  have h := (asc p).ne
  dsimp only [br, plane]
  simp only [sub_mul, mul_sub, Matrix.single_mul_single_of_ne _ _ _ _ h,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm, Matrix.single_mul_single_same]
  ext i j
  by_cases hi : i = a p
  · subst i; by_cases hj : a p = j
    · subst j; simp [Matrix.single,H,coroot,h,h.symm, Complex.real_smul, ← Complex.mul_conj]
      ring
    simp [Matrix.single,H,h.symm,hj]
  by_cases hi' : i = b p
  · subst i; by_cases hj : b p = j
    · subst j; simp [Matrix.single,H,coroot,h,h.symm, Complex.real_smul, ← Complex.mul_conj]
      ring
    simp [Matrix.single,H,h,hj]
  by_cases hij : i = j
  · subst j; simp [Matrix.single,H,coroot,Pi.single_apply,hi,Ne.symm hi,hi',Ne.symm hi']
  simp [Matrix.single,H,hij,Ne.symm hi,Ne.symm hi']

/-- Span of coroots (take those meeting the 2 coordinate). -/
lemma diagonals {h : Hue → ℝ} (hu : ∑ i, h i = 0) :
    H h = h 0 • H (coroot 1) + h 1 • H (coroot 2) := by
  rw [Fin.sum_univ_three] at hu
  have he : h 2 = -h 0 - h 1 := by linarith
  ext i j
  by_cases hj : i = j
  · subst j
    have hv : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    have hz : (2 : Hue) ≠ 0 := by decide
    have hy : (2 : Hue) ≠ 1 := by decide
    rcases hv with rfl | rfl | rfl <;>
      simp [H, coroot, a, b, he, show (![0,0,1] : Root → Hue) 2 = 1 from rfl,
        show (![1,2,2] : Root → Hue) 2 = 2 from rfl, Complex.real_smul, hz,hz.symm, hy, hy.symm] <;> ring
  simp [H, hj]

lemma twice (h : Hue → ℝ) (X : Mat) (i j : Hue) : br (H h) (br (H h) X) i j =
    (-((h i - h j)^2) : ℝ) • X i j := by
  simp only [action, Complex.real_smul, ofReal_neg, ofReal_pow, ofReal_sub]
  linear_combination (norm := ring) ((h i:ℂ) - ↑(h j)) ^ 2 * X i j * I_mul_I

end Roots
end YM.QCD
