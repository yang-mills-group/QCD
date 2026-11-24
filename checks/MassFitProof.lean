import MassFitSpec

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
noncomputable section
namespace YMReview.QCD
open YM.Massive
open scoped BigOperators

theorem loss_gap (b : Copies → Copies → ℝ) (u : Copies → ℝ) :
    Signals.loss b u = Signals.loss b (closedFit b) +
      8 * (∑ i, (u i - closedFit b i)^2) + 2 * (∑ i, (u i - closedFit b i))^2 := by
  simp only [Signals.loss, closedFit, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [Fin.ext_iff]
  <;> ring

theorem mass_fit_correct : MassFitCorrect := by
  intro b
  constructor
  · intro u
    have hs : 0 ≤ ∑ i, (u i - closedFit b i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ht := sq_nonneg (∑ i, (u i - closedFit b i))
    linarith [loss_gap b u]
  · intro u hu
    have hi : ∃ i, u i ≠ closedFit b i := by
      by_contra hn
      push Not at hn
      exact hu (funext hn)
    obtain ⟨i, hi⟩ := hi
    have hp : 0 < (u i - closedFit b i)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hi)
    have hs : (u i - closedFit b i)^2 ≤ ∑ j, (u j - closedFit b j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j - closedFit b j)) (Finset.mem_univ i)
    have ht := sq_nonneg (∑ j, (u j - closedFit b j))
    linarith [loss_gap b u]

theorem six_pair_difference : SixPairDifference := by
  simp only [SixPairDifference, Signals.loss, closedFit, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [exampleB, referenceMass, Fin.ext_iff]

-- These synthetic readings meet the same pointwise accuracy scale, but this
-- does not assert that this array is realized by the constructed QCD theory.
theorem example_accuracy (i j : Copies) :
    |exampleB i j - (referenceMass i + referenceMass j)| ≤ (1:ℝ)/100 := by
  simp only [exampleB]
  split_ifs <;> ring_nf <;> norm_num

end YMReview.QCD
#print axioms YMReview.QCD.loss_gap
#print axioms YMReview.QCD.mass_fit_correct
#print axioms YMReview.QCD.six_pair_difference
#print axioms YMReview.QCD.example_accuracy
