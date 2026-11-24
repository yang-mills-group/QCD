import ScreeningSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM Filter
open scoped Topology

theorem bounded_log_error_gives_coefficient {ι : Type*} {l : Filter ι}
    {r L : ι → ℝ} {c E : ℝ} (hL : Tendsto L l atTop)
    (he : ∀ᶠ i in l, |r i-c*L i| ≤ E) :
    Tendsto (fun i => r i/L i) l (𝓝 c) := by
  have herr : Tendsto (fun i => (r i-c*L i)/L i) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => E/L i) ?_ (tendsto_const_nhds.div_atTop hL)
    filter_upwards [he,hL.eventually_gt_atTop 0] with i hi hli
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hli]
    exact div_le_div_of_nonneg_right hi hli.le
  have hs := herr.add_const c
  simp only [zero_add] at hs
  apply hs.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with i hi
  field_simp
  ring

theorem fermion_screening_test : FermionScreeningTest := by
  intro C hC
  let P : QCD.Flume.Plan 2 := Classical.choice (QCD.Flume.passport (by decide))
  obtain ⟨E,hE⟩ := QCD.Pearl.wilson P C hC
  have hL : Tendsto (fun n:Lattice.Side => Real.log (n.val:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp QCD.Free.exhausting)
  have h := bounded_log_error_gives_coefficient hL hE
  have hc : QCD.Pearl.chargeF = 1/(2*Real.pi^2) := by
    unfold QCD.Pearl.chargeF
    ring
  rw [hc] at h
  exact h

theorem many_flavor_screening (f : ℕ)
    (C : QCD.su.Color) (hC : ‖C‖ = 1) :
    Tendsto (fun n : Lattice.Side => (f:ℝ)*fermionResponse C n / Real.log (n.val:ℝ))
      atTop (𝓝 ((f:ℝ)/(2*Real.pi^2))) := by
  have h := (fermion_screening_test C hC).const_mul (f:ℝ)
  simpa only [← mul_div_assoc,mul_one] using! h

theorem fermion_screening_nonvacuous : ∃ C : QCD.su.Color, ‖C‖ = 1 ∧
    Tendsto (fun n : Lattice.Side => fermionResponse C n / Real.log (n.val:ℝ))
      atTop (𝓝 (1/(2*Real.pi^2))) := by
  let X := QCD.Roots.eightColors (Sum.inl 0)
  have hX : X ≠ 0 := QCD.Roots.eightColors.ne_zero _
  let C := ‖X‖⁻¹ • X
  have hC : ‖C‖ = 1 := by
    simp [C,norm_smul,hX]
  exact ⟨C,hC,fermion_screening_test C hC⟩

end YMReview.QCD
#print axioms YMReview.QCD.bounded_log_error_gives_coefficient
#print axioms YMReview.QCD.fermion_screening_test
#print axioms YMReview.QCD.many_flavor_screening
#print axioms YMReview.QCD.fermion_screening_nonvacuous
