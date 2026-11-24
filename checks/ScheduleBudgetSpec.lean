import FlavorSpec
import YM.VStages.Settlement

/-! The later, variable-stride scheduling interface has the same flavor margin.
This is a restriction on the stated estimates, not a no-go result for QCD. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.QCD.Acre.Stratum.MarchQ

def ActualScheduleTest : Prop :=
  (∀ F : ℕ, 0 < delta₀ F ↔ F ≤ 8) ∧
  (∀ {K : RG.KernelChoices} {h s : ℕ → ℕ} (P : Docket K h s)
    (F : ℕ) (gate : ChangeQ → ℕ), Earlier P F gate → F ≤ 8)

end YMReview.QCD
