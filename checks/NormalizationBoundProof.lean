import NormalizationBoundSpec
import FitStabilityProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive

theorem axial_mass_residual {C : Sequence} {s : Signals} (hR : s.Read C)
    (hM : s.Masses) {i j : Copies} (hij : i ≠ j) :
    |s.axial i j - (s.bMass i+s.bMass j)| ≤ s.margin/25 := by
  have hm := (target_mass_margins hR hM).1
  have h := abs_add_three (s.axial i j-(s.rg i+s.rg j))
    (s.rg i-s.bMass i) (s.rg j-s.bMass j)
  have he : s.axial i j-(s.rg i+s.rg j)+(s.rg i-s.bMass i)+(s.rg j-s.bMass j) =
    s.axial i j-(s.bMass i+s.bMass j) := by ring
  rw [he,abs_sub_comm (s.rg i),abs_sub_comm (s.rg j)] at h
  linarith [hR.axialPaid i j hij,hm i,hm j]

theorem polar_mass_residual {C : Sequence} {s : Signals} (hR : s.Read C)
    (hM : s.Masses) {i j : Copies} (hij : i ≠ j) :
    |s.polar i j - (s.bMass i-s.bMass j)| ≤ 3*s.margin/100 := by
  have hm := (target_mass_margins hR hM).2 i j
  have h := abs_sub (s.polar i j-(s.rg i-s.rg j))
    ((s.bMass i-s.bMass j)-(s.rg i-s.rg j))
  have he : s.polar i j-(s.rg i-s.rg j)-((s.bMass i-s.bMass j)-(s.rg i-s.rg j)) =
    s.polar i j-(s.bMass i-s.bMass j) := by ring
  rw [he] at h
  linarith [hR.polarPaid i j hij]

theorem fitted_mass_sum_lower {C : Sequence} {s : Signals} (hR : s.Read C)
    (hM : s.Masses) (i j : Copies) :
    197*s.margin/100 ≤ s.bMass i+s.bMass j := by
  have hi := (abs_le.mp ((target_mass_margins hR hM).1 i)).1
  have hj := (abs_le.mp ((target_mass_margins hR hM).1 j)).1
  linarith [hR.signalPos i,hR.signalPos j]

theorem fitted_mass_difference_lower {C : Sequence} {s : Signals} (hR : s.Read C)
    (hM : s.Masses) {i j : Copies} (hij : i ≠ j) :
    49*s.margin/50 ≤ |s.bMass i-s.bMass j| := by
  have hm := (target_mass_margins hR hM).2 i j
  have h := abs_sub_abs_le_abs_sub (s.rg i-s.rg j) (s.bMass i-s.bMass j)
  rw [abs_sub_comm (s.rg i-s.rg j)] at h
  linarith [hR.separated i j hij]

theorem quantitative_normalization_test : QuantitativeNormalizationTest := by
  intro C s hR hM i j hij
  constructor
  · have hp : 0 < s.bMass i+s.bMass j := add_pos (hM.positive i) (hM.positive j)
    rw [div_sub_one hp.ne',abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    have he := axial_mass_residual hR hM hij
    have hl := fitted_mass_sum_lower hR hM i j
    linarith
  · have hn : s.bMass i-s.bMass j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hM.distinct he))
    rw [div_sub_one hn,abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hn)).mpr
    have he := polar_mass_residual hR hM hij
    have hl := fitted_mass_difference_lower hR hM hij
    linarith

end YMReview.QCD
#print axioms YMReview.QCD.axial_mass_residual
#print axioms YMReview.QCD.polar_mass_residual
#print axioms YMReview.QCD.fitted_mass_sum_lower
#print axioms YMReview.QCD.fitted_mass_difference_lower
#print axioms YMReview.QCD.quantitative_normalization_test
