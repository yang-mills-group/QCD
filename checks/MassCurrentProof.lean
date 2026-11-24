import MassFitSpec
import YM.Massive.PCAC.Bare

/-! Normalization audit, November 23.
The finite contact identities use the actual Wilson regulator. The rescaling
and flavor tests isolate what separated divergence identities can determine;
they are not countermodels of the complete existence theorem. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive YM.QCD YM.QCD.Grass YM.QCD.Grass.Ward YM.QCD.Lat
open YM.Massive.PCAC YM.Lattice
open scoped BigOperators

-- No support restriction: the spectator may contain fields at the acted-on site.
theorem mark_contact {A : Type*} [Fintype A] (k : Bool)
    (T : Sour A) (hT : T.trace = 0) (d y : Dirac A) :
    ber A (applyMark k T d * y) = -ber A (d * applyMark k T y) := by
  have h := integrated k T (d * y)
  rw [LMark, map_add, hT, zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem finite_vector_contact {c : Side} {N : ℕ} (R : Regulator c N)
    (i j : Flavor N) (hij : i ≠ j) (u : Site c) (U : Grid c)
    (y : Dirac (Modes c N)) :
    ber _ ((R.density U *
      (((R.m i : ℂ) - (R.m j : ℂ)) • scalarProbe i j u 1 U +
        ∑ v : Site c, current R i j u v U)) * y) =
      -ber _ (R.density U *
        (applyMark false (localF u 1 i j) y - applyMark true (localF u 1 i j) y)) := by
  have hv := congrArg (fun f : Insertion c N => f U) (vectorWard R i j u)
  simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.sum_apply] at hv
  change applyMark false (localF u 1 i j) (R.density U) -
    applyMark true (localF u 1 i j) (R.density U) = R.density U *
      (((R.m i : ℂ) - (R.m j : ℂ)) • scalarProbe i j u 1 U +
        ∑ v : Site c, current R i j u v U) at hv
  rw [← hv]
  rw [sub_mul, map_sub, mul_sub, map_sub,
    mark_contact false _ (near_trace i j 1 u hij),
    mark_contact true _ (near_trace i j 1 u hij)]
  ring

-- The entire axial remainder is retained; no claim that it vanishes.
theorem finite_axial_contact {c : Side} {N : ℕ} (R : Regulator c N)
    (i j : Flavor N) (hij : i ≠ j) (u : Site c) (U : Grid c)
    (y : Dirac (Modes c N)) :
    ber _ ((R.density U *
      (((R.m i : ℂ) + (R.m j : ℂ)) • scalarProbe i j u g5 U +
        axial_rest R i j u g5 U)) * y) =
      -ber _ (R.density U *
        (applyMark false (localF u g5 i j) y + applyMark true (localF u g5 i j) y)) := by
  have ha := congrArg (fun f : Insertion c N => f U) (axialWard R i j u g5)
  change applyMark false (localF u g5 i j) (R.density U) +
    applyMark true (localF u g5 i j) (R.density U) = R.density U *
      (((R.m i : ℂ) + (R.m j : ℂ)) • scalarProbe i j u g5 U +
        axial_rest R i j u g5 U) at ha
  rw [← ha]
  rw [add_mul, map_add, mul_add, map_add,
    mark_contact false _ (near_trace i j g5 u hij),
    mark_contact true _ (near_trace i j g5 u hij)]
  ring

-- A homogeneous divergence equation survives simultaneous rescaling.
theorem simultaneous_current_density_rescaling (F : Massive.Fields)
    (J : Axis → F.W) (P : F.W) (b z : ℂ)
    (h : Signals.divergence F J = b • P) :
    Signals.divergence F (fun a => z • J a) = b • (z • P) := by
  simp only [Signals.divergence, map_smul, ← Finset.smul_sum] at *
  rw [h, smul_comm]

-- A specified nonzero contact response removes this freedom.
theorem nonzero_contact_fixes_scale (z response : ℂ) (hr : response ≠ 0)
    (h : z * response = response) : z = 1 := by
  exact (mul_right_cancel₀ hr) (h.trans (one_mul response).symm)

-- A common scalar factor cannot repair a failure of these pair relations.
theorem common_scalar_requires_cycle (v : Copies → Copies → ℝ)
    (m : Copies → ℝ) (Z : ℝ) (h : ∀ i j, i ≠ j → v i j = Z * (m i - m j))
    (i j k : Copies) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    v i j + v j k = v i k := by
  rw [h i j hij, h j k hjk, h i k hik]
  ring

def vectorExample (i j : Copies) : ℝ := referenceMass i - referenceMass j +
  (if i = 4 ∧ j = 5 then 1/1000 else 0) -
  (if i = 5 ∧ j = 4 then 1/1000 else 0)

theorem vector_example_antisymmetric (i j : Copies) :
    vectorExample i j = -vectorExample j i := by
  simp only [vectorExample, and_comm]
  ring

theorem vector_example_close (i j : Copies) :
    |vectorExample i j - (referenceMass i - referenceMass j)| ≤ (1 : ℝ)/100 := by
  unfold vectorExample
  split_ifs <;> ring_nf <;> norm_num

theorem vector_example_no_common_mass :
    ¬∃ (m : Copies → ℝ) (Z : ℝ),
      ∀ i j, i ≠ j → vectorExample i j = Z * (m i - m j) := by
  rintro ⟨m, Z, h⟩
  have hc := common_scalar_requires_cycle vectorExample m Z h 0 4 5
    (by decide) (by decide) (by decide)
  norm_num [vectorExample, referenceMass, Fin.ext_iff] at hc

theorem axial_example_no_common_mass :
    ¬∃ (m : Copies → ℝ) (Z : ℝ),
      ∀ i j, i ≠ j → exampleB i j = Z * (m i + m j) := by
  rintro ⟨m, Z, h⟩
  have hc : exampleB 0 1 + exampleB 4 5 = exampleB 0 4 + exampleB 1 5 := by
    rw [h 0 1 (by decide), h 4 5 (by decide), h 0 4 (by decide), h 1 5 (by decide)]
    ring
  norm_num [exampleB, referenceMass, Fin.ext_iff] at hc

end YMReview.QCD
#print axioms YMReview.QCD.mark_contact
#print axioms YMReview.QCD.finite_vector_contact
#print axioms YMReview.QCD.finite_axial_contact
#print axioms YMReview.QCD.simultaneous_current_density_rescaling
#print axioms YMReview.QCD.nonzero_contact_fixes_scale
#print axioms YMReview.QCD.common_scalar_requires_cycle
#print axioms YMReview.QCD.vector_example_antisymmetric
#print axioms YMReview.QCD.vector_example_close
#print axioms YMReview.QCD.vector_example_no_common_mass
#print axioms YMReview.QCD.axial_example_no_common_mass
