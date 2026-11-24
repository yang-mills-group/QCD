import FitStabilitySpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive

def QuantitativeNormalizationTest : Prop := ∀ (C : Sequence) (s : Signals),
  s.Read C → s.Masses → ∀ i j, i ≠ j →
    |s.axial i j / (s.bMass i + s.bMass j) - 1| ≤ 4/197 ∧
    |s.polar i j / (s.bMass i - s.bMass j) - 1| ≤ 3/98

end YMReview.QCD
