import FitStabilitySpec
import ContinuumSpec

/-! Stronger bounds using the actual symmetric axial readings and separated
positive reference masses. These concern renP, not a rescaling of the current. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive Filter
open scoped Topology BigOperators

def symmetricResidualWeight (i j k l : Copies) : ℝ :=
  (if k=i ∧ l=j then 1/2 else 0)+(if k=j ∧ l=i then 1/2 else 0)-
    fitWeight i k l-fitWeight j k l

def SharpNormalizationTest : Prop := ∀ (C : Sequence) (s : Signals),
  s.Read C → s.Masses → (∀ i j, s.axial i j=s.axial j i) →
  ∀ i j, i ≠ j → |s.axial i j/(s.bMass i+s.bMass j)-1| ≤ 12/1489

def SharpNormalizationAcceptance : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ β in atTop,
  ∃ w : Witness β ε, LiteralLimit w.sequence w.calibration w.fields w.moments ∧
    ∀ i j, i ≠ j → |w.signals.axial i j/(w.signals.bMass i+w.signals.bMass j)-1| ≤ 12/1489

end YMReview.QCD
