import CurrentSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Function Filter
open scoped BigOperators Topology

theorem divergence_with_spectators {F : Fields} {S : Fields.Kernel F}
    (hE : Fields.Euclidean S) (J : Axis → F.W) (O : F.W) (c : ℂ)
    (hJ : Signals.divergence F J = c • O)
    (n : ℕ) (x : Points n) (hx : x ∈ conf n) (v : Fin n → F.W) (k : Fin n) :
    (∑ a : Axis, YM.Analysis.D (Points.direction k a)
      (fun y => S n y (update v k (J a))) x) = c * S n x (update v k O) := by
  classical
  calc
    _ = ∑ a : Axis, S n x (update v k (F.partialD a (J a))) := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [update_self, update_idem] using hE.derivatives n (update v k (J a)) k x hx a
    _ = S n x (update v k (Signals.divergence F J)) := by
      simp only [Signals.divergence, MultilinearMap.map_update_sum]
    _ = _ := by rw [hJ, MultilinearMap.map_update_smul]; rfl

theorem current_ward_test : CurrentWardTest := by
  intro F S s A hE hP i j hij n x hx v k
  exact ⟨divergence_with_spectators hE _ _ _ (hP.pairs i j hij).trueA n x hx v k,
    divergence_with_spectators hE _ _ _ (hP.pairs i j hij).trueV n x hx v k⟩

theorem normalization_test : NormalizationTest := by
  intro F s A hM hP i j hij
  have hsum : 0 < s.bMass i + s.bMass j := add_pos (hM.positive i) (hM.positive j)
  have hdiff : s.bMass i - s.bMass j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hM.distinct h))
  have ha := hM.signAxial i j hij
  have hv := hM.signPolar i j hij
  have hap : 0 < s.axial i j / (s.bMass i + s.bMass j) := div_pos ha hsum
  have hvp : 0 < s.polar i j / (s.bMass i - s.bMass j) := div_pos_iff.mpr (mul_pos_iff.mp hv)
  have hpolar : s.polar i j ≠ 0 := by intro hz; simp [hz] at hv
  have hpa : (↑(s.axial i j / (s.bMass i + s.bMass j)) : ℂ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hap)
  have hpv : (↑(s.polar i j / (s.bMass i - s.bMass j)) : ℂ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hvp)
  refine ⟨hap,hvp,?_,?_,?_,?_⟩
  · exact smul_ne_zero hpa (hP.pairs i j hij).pseudo
  · exact smul_ne_zero hpv (hP.pairs i j hij).scalar
  · unfold Signals.renP
    rw [smul_smul, ← Complex.ofReal_mul]
    have he : ((s.bMass i + s.bMass j) / s.axial i j) *
        (s.axial i j / (s.bMass i + s.bMass j)) = 1 := by
      field_simp
    rw [he, Complex.ofReal_one, one_smul]
  · unfold Signals.renS
    rw [smul_smul, ← Complex.ofReal_mul]
    have he : ((s.bMass i - s.bMass j) / s.polar i j) *
        (s.polar i j / (s.bMass i - s.bMass j)) = 1 := by
      field_simp
    rw [he, Complex.ofReal_one, one_smul]

-- A control for the stronger, unrescaled common-mass assertion. The previously
-- checked 1/100 accuracy condition alone cannot imply this assertion.
theorem small_errors_do_not_force_additive_masses :
    ¬ ∃ m : Copies → ℝ, ∀ i j, i ≠ j → exampleB i j = m i + m j := by
  rintro ⟨m,h⟩
  have h01 := h 0 1 (by decide)
  have h45 := h 4 5 (by decide)
  have h04 := h 0 4 (by decide)
  have h15 := h 1 5 (by decide)
  norm_num [exampleB, referenceMass, Fin.ext_iff] at h01 h45 h04 h15
  linarith

-- Uniform C0 control does not by itself control derivatives of currents.
def oscillatingResidual (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (((n : ℝ) + 1) * x) / ((n : ℝ) + 1)

theorem residual_uniform_small (n : ℕ) (x : ℝ) :
    |oscillatingResidual n x| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [oscillatingResidual, abs_div, abs_of_pos hn]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hn)

theorem residual_derivative_stays_one (n : ℕ) :
    HasDerivAt (oscillatingResidual n) 1 0 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul ((n : ℝ) + 1)).sin).div_const ((n : ℝ) + 1)
  simpa [oscillatingResidual, hn] using! h

theorem residual_bound_tends_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end YMReview.QCD
#print axioms YMReview.QCD.divergence_with_spectators
#print axioms YMReview.QCD.current_ward_test
#print axioms YMReview.QCD.normalization_test
#print axioms YMReview.QCD.small_errors_do_not_force_additive_masses
#print axioms YMReview.QCD.residual_uniform_small
#print axioms YMReview.QCD.residual_derivative_stays_one
#print axioms YMReview.QCD.residual_bound_tends_zero
