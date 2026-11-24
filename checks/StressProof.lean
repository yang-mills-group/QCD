import StressSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive

theorem two_detected_candidates_exclude_stress {F : Fields}
    (U V : Momentum F) (hU : Physics.Candidate F U) (hV : Physics.Candidate F V)
    (p q : Momentum F →ₗ[ℂ] ℂ)
    (pI : p (Physics.identity F) = 0) (qI : q (Physics.identity F) = 0)
    (pU : p U = 1) (qU : q U = 0) (qV : q V = 1)
    (T : Momentum F) : ¬ Physics.Stress F T := by
  intro hT
  obtain ⟨a,b,ha⟩ := (hT.unique U).mp hU
  obtain ⟨c,d,hc⟩ := (hT.unique V).mp hV
  have hp : (1 : ℂ) = a * p T := by
    simpa only [map_add, map_smul, pI, smul_zero, add_zero, smul_eq_mul, mul_zero, pU]
      using congrArg p ha
  have hq : (0 : ℂ) = a * q T := by
    simpa only [map_add, map_smul, qI, smul_zero, add_zero, smul_eq_mul, mul_zero, qU]
      using congrArg q ha
  have hv : (1 : ℂ) = c * q T := by
    simpa only [map_add, map_smul, qI, smul_zero, add_zero, smul_eq_mul, mul_zero, qV]
      using congrArg q hc
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at hp
  have hqt : q T = 0 := (mul_eq_zero.mp hq.symm).resolve_left ha0
  simp [hqt] at hv

theorem stress_exclusion : StressExclusion := by
  rintro F ⟨s⟩ T
  apply two_detected_candidates_exclude_stress (s.sector 0) (s.sector 1)
    (s.candidate 0) (s.candidate 1) (s.probe 0) (s.probe 1)
    (s.identity_zero 0) (s.identity_zero 1)
  · simpa using s.detects 0 0
  · simpa using s.detects 1 0
  · simpa using s.detects 1 1

theorem sector_controls (i j : Fin 7) :
    sectorProbe i sectorUnit = 0 ∧
    sectorProbe i (sectorVector j) = if i = j then 1 else 0 := by
  classical
  simp [sectorProbe, sectorUnit, sectorVector, Pi.single_apply]

theorem sector_no_collapse (T : SectorCoefficients) :
    ¬ (∀ i : Fin 7, ∃ a b : ℂ, sectorVector i = a • T + b • sectorUnit) := by
  intro h
  obtain ⟨a,b,ha⟩ := h 0
  obtain ⟨c,d,hc⟩ := h 1
  have hp := congrFun ha 1
  have hq := congrFun ha 2
  have hv := congrFun hc 2
  norm_num [sectorVector, sectorUnit, Pi.single_apply, Fin.ext_iff] at hp hq hv
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at hp
  have hqt : T 2 = 0 := hq.resolve_left ha0
  simp [hqt] at hv

end YMReview.QCD
#print axioms YMReview.QCD.two_detected_candidates_exclude_stress
#print axioms YMReview.QCD.stress_exclusion
#print axioms YMReview.QCD.sector_controls
#print axioms YMReview.QCD.sector_no_collapse
