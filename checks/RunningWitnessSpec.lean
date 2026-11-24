import CouplingSpec
import FlavorSpec
import NormalizationBoundSpec

/-! Actual witnesses from the supplied six-flavor theorem, carrying the stronger
review consequences together. No two-loop or massless claim is added. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter
open scoped Topology

def RunningWitnessTest : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ β in atTop,
  ∃ w : Witness β ε,
    LiteralLimit w.sequence w.calibration w.fields w.moments ∧
    (∀ i j, i ≠ j →
      |w.signals.axial i j/(w.signals.bMass i+w.signals.bMass j)-1| ≤ 4/197 ∧
      |w.signals.polar i j/(w.signals.bMass i-w.signals.bMass j)-1| ≤ 3/98) ∧
    (∀ a b : Axis, a ≠ b → ∀ T : QCD.su.Color, ‖T‖=1 →
      Tendsto (fun i => cutoffStiffness w.sequence a b T i/cutoffLog w.sequence i)
        atTop (𝓝 (12*gBeta0 6)) ∧
      ∀ᶠ i in atTop, 0 < cutoffStiffness w.sequence a b T i)

end YMReview.QCD
