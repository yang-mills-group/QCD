import FlavorSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM
open scoped InnerProductSpace

theorem matter_index_counts_flavors (f : ℕ) (X Y : QCD.su.Color) :
    -(QCD.generator f X * QCD.generator f Y).trace.re = 6 * f * ⟪X,Y⟫_ℝ :=
  QCD.index_Weyl f X Y

theorem trace_coefficient (f : ℕ) : QCD.bTrace f / 6 = oneLoopCoefficient f :=
  QCD.conventional f

theorem running_coefficient (f : ℕ) : QCD.Raft.betaQ f = 12 * gBeta0 f := by
  rw [QCD.Raft.qbeta]
  unfold gBeta0 oneLoopCoefficient
  ring

theorem flavor_screening_increment (f : ℕ) :
    QCD.Raft.betaQ (f+1) - QCD.Raft.betaQ f = -(1 / (2 * Real.pi^2)) := by
  rw [QCD.Raft.qbeta, QCD.Raft.qbeta]
  push_cast
  ring

theorem six_flavor_target_coefficient : Massive.betaSlope = 12 * gBeta0 6 := by
  unfold Massive.betaSlope Gauge.slopeConstant gBeta0 oneLoopCoefficient
  rw [QCD.Roots.casimir]
  ring

theorem asymptotic_freedom_integer_range (f : ℕ) :
    0 < QCD.Raft.betaQ f ↔ f ≤ 16 := QCD.Raft.ultraviolet f

theorem trajectory_budget_integer_range (f : ℕ) : trajectoryBudget f ↔ f ≤ 8 := by
  unfold trajectoryBudget
  have h0 : QCD.Raft.betaQ 0 = QCD.su.slopeConstant := by simp [QCD.Raft.betaQ]
  rw [← h0, QCD.Raft.qbeta, QCD.Raft.qbeta]
  have hp : 0 < 3 / (4 * Real.pi^2) := by positivity
  have he : (3 / (4 * Real.pi^2)) * (11 - 2 * (0:ℝ) / 3) / 2 <
      (3 / (4 * Real.pi^2)) * (11 - 2 * (f:ℝ) / 3) ↔ (f:ℝ) < 33/4 := by
    constructor <;> intro h
    · nlinarith
    · nlinarith
  simp only [Nat.cast_zero]
  rw [he]
  constructor
  · intro h
    by_contra! hf
    have h9 : (9:ℝ) ≤ f := by exact_mod_cast (show 9 ≤ f by omega)
    linarith
  · intro h
    have h8 : (f:ℝ) ≤ 8 := by exact_mod_cast h
    linarith

theorem flavor_test : FlavorTest :=
  ⟨trace_coefficient, running_coefficient, six_flavor_target_coefficient,
    asymptotic_freedom_integer_range, trajectory_budget_integer_range⟩

end YMReview.QCD
#print axioms YMReview.QCD.matter_index_counts_flavors
#print axioms YMReview.QCD.trace_coefficient
#print axioms YMReview.QCD.running_coefficient
#print axioms YMReview.QCD.flavor_screening_increment
#print axioms YMReview.QCD.six_flavor_target_coefficient
#print axioms YMReview.QCD.asymptotic_freedom_integer_range
#print axioms YMReview.QCD.trajectory_budget_integer_range
#print axioms YMReview.QCD.flavor_test
