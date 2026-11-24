import StressProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive
open scoped BigOperators

theorem constant_tensor_rotates (x : SectorCoefficients) (p : EuPin) :
    Physics.tensor constantSectorFields p (constantTensor x) := by
  classical
  intro a b
  change (if a = b then x else 0) =
    ∑ i : Axis, ∑ j : Axis, (↑(p.coord.val i a * p.coord.val j b) : ℂ) •
      (if i = j then x else 0)
  have ho := congrFun (congrFun (Ortho.transp p.coord) a) b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at ho
  have hs : (∑ i : Axis, ∑ j : Axis, (↑(p.coord.val i a * p.coord.val j b) : ℂ) •
      (if i = j then x else 0)) =
      (↑(∑ i : Axis, p.coord.val i a * p.coord.val i b) : ℂ) • x := by
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.ofReal_sum, Finset.sum_smul]
  rw [hs, ho]
  split_ifs <;> simp

theorem constant_tensor_candidate (x : SectorCoefficients) :
    Physics.Candidate constantSectorFields (constantTensor x) := by
  classical
  constructor
  · intro a b
    change (if a = b then x else 0) ∈ (⊤ : Submodule ℂ SectorCoefficients)
    trivial
  · intro a b; simp [constantTensor, eq_comm]
  · intro a b; rfl
  · intro a b; rfl
  · intro a b p; rfl
  · intro p _; exact constant_tensor_rotates x p
  · intro b
    change (∑ _a : Axis, (0 : SectorCoefficients)) = 0
    simp

def constant_separate_sectors : SeparateStressSectors constantSectorFields where
  sector i := constantTensor (sectorVector i)
  candidate i := constant_tensor_candidate _
  probe := constantProbe
  identity_zero i := by
    change sectorProbe i sectorUnit = 0
    exact (sector_controls i i).1
  detects i j := by
    change sectorProbe i (sectorVector j) = _
    exact (sector_controls i j).2

theorem stress_control_test : StressControlTest :=
  stress_exclusion constantSectorFields ⟨constant_separate_sectors⟩

end YMReview.QCD
#print axioms YMReview.QCD.constant_tensor_rotates
#print axioms YMReview.QCD.constant_tensor_candidate
#print axioms YMReview.QCD.stress_control_test
