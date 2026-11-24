import FitStabilitySpec
import MassFitProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace YMReview.QCD
open YM.Massive
open scoped BigOperators

theorem fit_error_formula (b : Copies → Copies → ℝ) (r : Copies → ℝ) (i : Copies) :
    closedFit b i - r i = ∑ k, ∑ l, fitWeight i k l * (b k l - (r k + r l)) := by
  fin_cases i <;>
    simp only [closedFit, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;>
    norm_num [fitWeight, Fin.ext_iff, Fin.succ] <;> ring

theorem weight_norm (i : Copies) : (∑ k, ∑ l, |fitWeight i k l|) = 3/2 := by
  fin_cases i <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;>
    norm_num [fitWeight, Fin.ext_iff, Fin.succ]

theorem difference_weight_norm (i j : Copies) (hij : i ≠ j) :
    (∑ k, ∑ l, |fitWeight i k l - fitWeight j k l|) = 2 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  all_goals norm_num [fitWeight, Fin.ext_iff, Fin.succ]

theorem weighted_error_bound (w b : Copies → Copies → ℝ) (r : Copies → ℝ)
    (δ : ℝ) (h : ∀ k l, k ≠ l → |b k l - (r k + r l)| ≤ δ)
    (hw : ∀ k, w k k = 0) :
    |∑ k, ∑ l, w k l * (b k l - (r k + r l))| ≤ (∑ k, ∑ l, |w k l|) * δ := by
  calc
    _ ≤ ∑ k, |∑ l, w k l * (b k l - (r k + r l))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |w k l * (b k l - (r k + r l))| :=
      Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |w k l| * δ := by
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      by_cases hkl : k = l
      · subst l; simp [hw]
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h k l hkl) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

theorem fit_stability : FitStability := by
  intro b r δ hδ h
  constructor
  · intro i
    rw [fit_error_formula]
    have hb := weighted_error_bound (fitWeight i) b r δ h (fun k => by simp [fitWeight])
    rw [weight_norm] at hb
    linarith
  · intro i j
    by_cases hij : i = j
    · subst j; simp; positivity
    have he : (closedFit b i - closedFit b j) - (r i - r j) =
        ∑ k, ∑ l, (fitWeight i k l - fitWeight j k l) * (b k l - (r k + r l)) := by
      rw [show (closedFit b i - closedFit b j) - (r i - r j) =
        (closedFit b i - r i) - (closedFit b j - r j) by ring,
        fit_error_formula, fit_error_formula]
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [he]
    have hb := weighted_error_bound (fun k l => fitWeight i k l - fitWeight j k l) b r δ h
      (fun k => by simp [fitWeight])
    rwa [difference_weight_norm i j hij] at hb

theorem target_fit_eq {s : Signals} (h : s.Masses) : s.bMass = closedFit s.axial := by
  by_contra hn
  have hs := (mass_fit_correct s.axial).2 s.bMass hn
  have hw := h.fitted (closedFit s.axial)
  linarith

theorem target_mass_margins {C : Sequence} {s : Signals} (hR : s.Read C) (hM : s.Masses) :
    (∀ i, |s.bMass i - s.rg i| ≤ 3 * s.margin / 200) ∧
    (∀ i j, |(s.bMass i - s.bMass j) - (s.rg i - s.rg j)| ≤ s.margin / 50) := by
  rw [target_fit_eq hM]
  have h := fit_stability s.axial s.rg (s.margin / 100) (by linarith [hR.room]) hR.axialPaid
  constructor
  · intro i; have hi := h.1 i; linarith
  · intro i j; have hi := h.2 i j; linarith

end YMReview.QCD
#print axioms YMReview.QCD.fit_error_formula
#print axioms YMReview.QCD.weight_norm
#print axioms YMReview.QCD.difference_weight_norm
#print axioms YMReview.QCD.weighted_error_bound
#print axioms YMReview.QCD.fit_stability
#print axioms YMReview.QCD.target_fit_eq
#print axioms YMReview.QCD.target_mass_margins
