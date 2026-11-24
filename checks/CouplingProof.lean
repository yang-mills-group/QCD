import CouplingSpec
import YM.QCD.Casimir
import YM.Massive.Brush.Floors

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter Set
open scoped Topology

theorem canonical_coefficient : betaSlope / 6 = 2 * canonicalB0 := by
  unfold betaSlope Gauge.slopeConstant canonicalB0
  rw [QCD.Roots.casimir]
  ring

theorem cutoff_log_diverges {C : Sequence} {β ε : ℝ} (h : C.Path β ε) :
    Tendsto (cutoffLog C) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h.physical)

theorem cutoff_beta_slope {C : Sequence} {β ε : ℝ} (h : C.Path β ε) :
    Tendsto (fun i => (C.A i).β (C.N i) / cutoffLog C i) atTop (𝓝 betaSlope) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have hs := h.uv.tendsto_atTop (h.runs.2 (η/2) (half_pos hη))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hs
  refine ⟨N, fun i hi => ?_⟩
  have hb := hN i hi i le_rfl
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb (by linarith)

theorem bounded_read_preserves_slope {f g L : ℕ → ℝ} {ε c : ℝ}
    (hL : Tendsto L atTop atTop) (hg : Tendsto (fun i => g i / L i) atTop (𝓝 c))
    (hfg : ∀ᶠ i in atTop, |f i - g i| ≤ ε) :
    Tendsto (fun i => f i / L i) atTop (𝓝 c) := by
  have herror : Tendsto (fun i => (f i - g i) / L i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => ε / L i) ?_ (tendsto_const_nhds.div_atTop hL)
    filter_upwards [hfg, hL.eventually_gt_atTop 0] with i hi hLi
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLi]
    exact div_le_div_of_nonneg_right hi (le_of_lt hLi)
  have hsum := herror.add hg
  simpa only [sub_div, sub_add_cancel, zero_add] using hsum

theorem coupling_test : CouplingTest := by
  intro C β ε h a b hab T hT
  have hread := bounded_read_preserves_slope (cutoff_log_diverges h) (cutoff_beta_slope h)
    (Eventually.of_forall fun i => (h.compare (i:=i) (m:=C.N i) le_rfl).band a b hab T hT)
  refine ⟨hread, ?_⟩
  have hc := hread.div_const 6
  rw [canonical_coefficient] at hc
  convert hc using 1
  ext i
  dsimp [cutoffStiffness]
  ring

theorem regulator_body_is_wilson {n : Lattice.Side} {flavors : ℕ}
    (R : Regulator n flavors) (U : QCD.Lat.Grid n) :
    Stiffness.body R.density U = (Wilson.bare R.β U : ℂ) := by
  classical
  unfold Stiffness.body
  rw [Regulator.density_apply, map_smul]
  have hg : QCD.Grass.coef ∅ (QCD.Grass.gauss (R.D U)) = 1 :=
    QCD.Grass.Ward.Loft.body_exp (QCD.Grass.Ward.Loft.wage (QCD.Grass.form_two _) (by decide))
  rw [hg, smul_eq_mul, mul_one]

theorem terminal_body_is_wilson {C : Sequence} {β ε : ℝ} (h : C.Path β ε)
    (i : ℕ) (U : QCD.Lat.Grid (C.S.side (C.R i) (C.N i))) :
    Stiffness.body ((C.A i).density (C.N i)) U = (Wilson.bare ((C.A i).β (C.N i)) U : ℂ) := by
  rw [(h.normalized i).start]
  exact regulator_body_is_wilson _ _

theorem uv_jet_limit {F : Fields} {S : Fields.Kernel F} {B : Bases F}
    (h : B.Comparison S) (n : ℕ) (d : Fin n → ℕ) (u : (i : Fin n) → UV.Label (d i))
    (j : ℕ) (x : Points n) (hx : x ∈ conf n) :
    Tendsto (fun k => iteratedFDeriv ℝ j
      (fun z => S n (B.radius k • z) (fun i => B.choice k (u i))) x)
      atTop (𝓝 (iteratedFDeriv ℝ j (fun z => UV.Free.wick d z u) x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (h.linearJet n d u j (ε/2) (half_pos hε) {x} (isCompact_singleton)
      (singleton_subset_iff.mpr hx))
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hN k hk x (mem_singleton x)) (by linarith)

-- A basis-normalization control, not a countermodel of the full target.
theorem variable_basis_can_hide_amplitude (n : ℕ) :
    ((n : ℝ) + 1)^2 * (1 / ((n : ℝ) + 1))^2 = 1 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end YMReview.QCD
#print axioms YMReview.QCD.canonical_coefficient
#print axioms YMReview.QCD.cutoff_log_diverges
#print axioms YMReview.QCD.cutoff_beta_slope
#print axioms YMReview.QCD.bounded_read_preserves_slope
#print axioms YMReview.QCD.coupling_test
#print axioms YMReview.QCD.regulator_body_is_wilson
#print axioms YMReview.QCD.terminal_body_is_wilson
#print axioms YMReview.QCD.uv_jet_limit
#print axioms YMReview.QCD.variable_basis_can_hide_amplitude
