import RunningWitnessSpec
import ContinuumProof
import CouplingProof
import FlavorProof
import NormalizationBoundProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter
open scoped Topology

theorem six_flavor_coefficient_positive : 0 < 12*gBeta0 6 := by
  unfold gBeta0 oneLoopCoefficient
  have hp := Real.pi_pos
  norm_num
  positivity

theorem cutoff_stiffness_positive {C : Sequence} {β ε : ℝ} (h : C.Path β ε)
    {a b : Axis} (hab : a ≠ b) {T : QCD.su.Color} (hT : ‖T‖=1) :
    ∀ᶠ i in atTop, 0 < cutoffStiffness C a b T i := by
  have hs := (coupling_test C β ε h a b hab T hT).1
  rw [six_flavor_target_coefficient] at hs
  have hh := hs.eventually (lt_mem_nhds six_flavor_coefficient_positive)
  filter_upwards [hh,(cutoff_log_diverges h).eventually_gt_atTop 0] with i hi hl
  exact (div_pos_iff_of_pos_right hl).mp hi

theorem running_witness_test : RunningWitnessTest := by
  intro ε hε
  filter_upwards [continuum_acceptance ε hε] with β hβ
  obtain ⟨w,hL⟩ := hβ
  refine ⟨w,hL,quantitative_normalization_test w.sequence w.signals w.massReading w.masses,?_⟩
  intro a b hab T hT
  refine ⟨?_,cutoff_stiffness_positive w.path hab hT⟩
  rw [← six_flavor_target_coefficient]
  exact (coupling_test w.sequence β ε w.path a b hab T hT).1

end YMReview.QCD
#print axioms YMReview.QCD.six_flavor_coefficient_positive
#print axioms YMReview.QCD.cutoff_stiffness_positive
#print axioms YMReview.QCD.running_witness_test
