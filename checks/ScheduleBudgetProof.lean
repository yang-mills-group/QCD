import ScheduleBudgetSpec
import FlavorProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.QCD.Acre.Stratum.MarchQ

theorem actual_schedule_margin (F : ℕ) : 0 < delta₀ F ↔ F ≤ 8 := by
  rw [delta₀,sub_pos]
  exact trajectory_budget_integer_range F

theorem earlier_requires_eight_or_fewer {K : RG.KernelChoices} {h s : ℕ → ℕ}
    (P : Docket K h s) (F : ℕ) (gate : ChangeQ → ℕ) (he : Earlier P F gate) : F ≤ 8 :=
  (actual_schedule_margin F).mp he.positive

theorem actual_schedule_test : ActualScheduleTest :=
  ⟨actual_schedule_margin,earlier_requires_eight_or_fewer⟩

end YMReview.QCD
#print axioms YMReview.QCD.actual_schedule_margin
#print axioms YMReview.QCD.earlier_requires_eight_or_fewer
#print axioms YMReview.QCD.actual_schedule_test
