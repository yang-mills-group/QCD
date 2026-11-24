import MassFitSpec
import ContinuumSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Function
open scoped BigOperators

def CurrentWardTest : Prop := ∀ (F : Fields) (S : Fields.Kernel F)
    (s : Signals) (A : MassFields), Fields.Euclidean S → s.PCAC F A →
    ∀ (i j : Copies), i ≠ j → ∀ (n : ℕ) (x : Points n), x ∈ conf n →
    ∀ (v : Fin n → F.W) (k : Fin n),
      (∑ a : Axis, YM.Analysis.D (Points.direction k a)
        (fun y => S n y (update v k (A.axial F i j a))) x) =
        (s.axial i j : ℂ) * S n x (update v k (A.pseudo F i j)) ∧
      (∑ a : Axis, YM.Analysis.D (Points.direction k a)
        (fun y => S n y (update v k (A.polar F i j a))) x) =
        (s.polar i j : ℂ) * S n x (update v k (A.scalar F i j))

def NormalizationTest : Prop := ∀ (F : Fields) (s : Signals) (A : MassFields),
  s.Masses → s.PCAC F A → ∀ i j, i ≠ j →
    0 < s.axial i j / (s.bMass i + s.bMass j) ∧
    0 < s.polar i j / (s.bMass i - s.bMass j) ∧
    s.renP F A i j ≠ 0 ∧ s.renS F A i j ≠ 0 ∧
    (↑((s.bMass i + s.bMass j) / s.axial i j) : ℂ) • s.renP F A i j = A.pseudo F i j ∧
    (↑((s.bMass i - s.bMass j) / s.polar i j) : ℂ) • s.renS F A i j = A.scalar F i j

end YMReview.QCD
