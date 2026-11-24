import ContinuumSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter
open scoped Topology

def cutoffLog (C : Sequence) (i : ℕ) := Real.log ((C.S.spacing (C.N i))⁻¹)
def cutoffStiffness (C : Sequence) (a b : Axis) (T : QCD.su.Color) (i : ℕ) :=
  Stiffness.read ((C.A i).density (C.N i)) a b T

-- Standard SU(3), six-flavor coefficient in the convention
-- μ dg/dμ = -b₀ g³ + ... . The conversion β=6/g² is an explicitly named
-- benchmark convention, not an independently proved observable dictionary.
def canonicalB0 : ℝ := (11 - 2 * 6 / 3) / (16 * Real.pi^2)

def CouplingTest : Prop := ∀ (C : Sequence) (β ε : ℝ), C.Path β ε →
  ∀ (a b : Axis), a ≠ b → ∀ T : QCD.su.Color, ‖T‖ = 1 →
    Tendsto (fun i => cutoffStiffness C a b T i / cutoffLog C i) atTop (𝓝 betaSlope) ∧
    Tendsto (fun i => (cutoffStiffness C a b T i / 6) / cutoffLog C i)
      atTop (𝓝 (2 * canonicalB0))

end YMReview.QCD
