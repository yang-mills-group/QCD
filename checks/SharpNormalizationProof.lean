import SharpNormalizationSpec
import FitStabilityProof
import ContinuumProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace YMReview.QCD
open YM.Massive Filter
open scoped Topology BigOperators

theorem sum_weight_norm (i j : Copies) (hij : i ≠ j) :
    (∑ k, ∑ l, |fitWeight i k l+fitWeight j k l|)=11/5 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals norm_num [fitWeight,Fin.ext_iff,Fin.succ]

theorem symmetric_residual_weight_norm (i j : Copies) (hij : i ≠ j) :
    (∑ k, ∑ l, |symmetricResidualWeight i j k l|)=12/5 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals norm_num [symmetricResidualWeight,fitWeight,Fin.ext_iff,Fin.succ]

theorem sum_fit_error_formula (b : Copies → Copies → ℝ) (r : Copies → ℝ) (i j : Copies) :
    (closedFit b i+closedFit b j)-(r i+r j)=
      ∑ k, ∑ l, (fitWeight i k l+fitWeight j k l)*(b k l-(r k+r l)) := by
  rw [show (closedFit b i+closedFit b j)-(r i+r j)=
    (closedFit b i-r i)+(closedFit b j-r j) by ring,fit_error_formula,fit_error_formula]
  simp only [add_mul,Finset.sum_add_distrib]

theorem symmetric_residual_formula (b : Copies → Copies → ℝ) (r : Copies → ℝ)
    (i j : Copies) (hsym : b i j=b j i) :
    b i j-(closedFit b i+closedFit b j)=
      ∑ k, ∑ l, symmetricResidualWeight i j k l*(b k l-(r k+r l)) := by
  have h := sum_fit_error_formula b r i j
  have he : (∑ k,∑ l,symmetricResidualWeight i j k l*(b k l-(r k+r l)))=
      (b i j-(r i+r j))/2+(b j i-(r j+r i))/2-
        (∑ k,∑ l,(fitWeight i k l+fitWeight j k l)*(b k l-(r k+r l))) := by
    simp [symmetricResidualWeight,sub_mul,add_mul,ite_mul,ite_and,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring
  rw [he,← h,← hsym]
  ring

theorem sum_fit_error_bound (b : Copies → Copies → ℝ) (r : Copies → ℝ) (δ : ℝ)
    (hb : ∀ k l,k ≠ l → |b k l-(r k+r l)| ≤ δ) (i j : Copies) (hij : i ≠ j) :
    |(closedFit b i+closedFit b j)-(r i+r j)| ≤ 11*δ/5 := by
  rw [sum_fit_error_formula]
  have h := weighted_error_bound (fun k l => fitWeight i k l+fitWeight j k l) b r δ hb
    (fun k => by simp [fitWeight])
  rw [sum_weight_norm i j hij] at h
  linarith

theorem symmetric_residual_bound (b : Copies → Copies → ℝ) (r : Copies → ℝ) (δ : ℝ)
    (hb : ∀ k l,k ≠ l → |b k l-(r k+r l)| ≤ δ) (i j : Copies)
    (hij : i ≠ j) (hsym : b i j=b j i) :
    |b i j-(closedFit b i+closedFit b j)| ≤ 12*δ/5 := by
  rw [symmetric_residual_formula b r i j hsym]
  have h := weighted_error_bound (symmetricResidualWeight i j) b r δ hb (fun k => by
    simp only [symmetricResidualWeight,fitWeight,ite_true,sub_zero]
    have hi : ¬(k=i ∧ k=j) := by rintro ⟨rfl,rfl⟩; exact hij rfl
    have hj : ¬(k=j ∧ k=i) := by rintro ⟨rfl,rfl⟩; exact hij rfl
    simp [hi,hj])
  rw [symmetric_residual_weight_norm i j hij] at h
  linarith

theorem separated_reference_sum {C : Sequence} {s : Signals} (hR : s.Read C)
    (i j : Copies) (hij : i ≠ j) : 3*s.margin ≤ s.rg i+s.rg j := by
  have h := hR.separated i j hij
  rcases le_total (s.rg i) (s.rg j) with he|he
  · rw [abs_of_nonpos (sub_nonpos.mpr he)] at h
    linarith [hR.signalPos i]
  · rw [abs_of_nonneg (sub_nonneg.mpr he)] at h
    linarith [hR.signalPos j]

theorem sharp_normalization_test : SharpNormalizationTest := by
  intro C s hR hM hsym i j hij
  have hsum := sum_fit_error_bound s.axial s.rg (s.margin/100) hR.axialPaid i j hij
  have hres := symmetric_residual_bound s.axial s.rg (s.margin/100) hR.axialPaid i j hij (hsym i j)
  rw [← target_fit_eq hM] at hsum hres
  have hl : 1489*s.margin/500 ≤ s.bMass i+s.bMass j := by
    have h := (abs_le.mp hsum).1
    linarith [separated_reference_sum hR i j hij]
  have hp : 0 < s.bMass i+s.bMass j := add_pos (hM.positive i) (hM.positive j)
  rw [div_sub_one hp.ne',abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem sharp_normalization_acceptance : SharpNormalizationAcceptance := by
  intro ε hε
  filter_upwards [continuum_acceptance ε hε] with β hβ
  obtain ⟨w,hL⟩ := hβ
  exact ⟨w,hL,sharp_normalization_test w.sequence w.signals w.massReading w.masses w.pcac.axialCross⟩

end YMReview.QCD
#print axioms YMReview.QCD.sum_weight_norm
#print axioms YMReview.QCD.symmetric_residual_weight_norm
#print axioms YMReview.QCD.sum_fit_error_formula
#print axioms YMReview.QCD.symmetric_residual_formula
#print axioms YMReview.QCD.sum_fit_error_bound
#print axioms YMReview.QCD.symmetric_residual_bound
#print axioms YMReview.QCD.separated_reference_sum
#print axioms YMReview.QCD.sharp_normalization_test
#print axioms YMReview.QCD.sharp_normalization_acceptance
