import ContinuumSpec
import YM.Plata.Massive

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter Set
open Fields.Limit
open scoped Topology

theorem correlator_limit_along_sites {C : Sequence} {P : Calibration C} {F : Fields}
    {S : Fields.Kernel F} (hS : Fields.Scaling S C P) (hE : Fields.Euclidean S)
    {n : ℕ} {x : Points n} (hx : x ∈ conf n)
    (sites : ℕ → Fin n → Lattice.Cover)
    (hsites : Tendsto (fun i => regulatorPositions C i (sites i)) atTop (𝓝 x))
    (d : Fin n → ℕ) (u : (j : Fin n) → UV.Label (d j)) (r : Fin n → Averaging) :
    Tendsto (fun i => evaluation C P d u r (sites i) i) atTop
      (𝓝 (S n x (fun j => F.quotient (r j) _ (u j)))) := by
  obtain ⟨K, hK, hxK, hKconf⟩ := exists_compact_subset (conf_open n) hx
  have hmem : ∀ᶠ i in atTop, regulatorPositions C i (sites i) ∈ K :=
    hsites (mem_interior_iff_mem_nhds.mp hxK)
  have hcont := (hE.smooth n (fun j => F.quotient (r j) _ (u j))).continuousOn
  have hlim := (hcont.continuousAt ((conf_open n).mem_nhds hx)).tendsto.comp hsites
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hc := (Metric.tendsto_atTop.mp hlim) (ε/2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hS.uniform n d u r K hK hKconf (ε/2) (half_pos hε)).and hmem)
  obtain ⟨M, hM⟩ := hc
  refine ⟨max N M, fun i hi => ?_⟩
  have hiN := hN i (le_trans (le_max_left _ _) hi)
  have hiM := hM i (le_trans (le_max_right _ _) hi)
  have hb := hiN.1 (sites i) hiN.2
  rw [dist_eq_norm] at hiM ⊢
  dsimp only [Function.comp_apply] at hiM
  calc
    ‖evaluation C P d u r (sites i) i - S n x (fun j => F.quotient (r j) _ (u j))‖ ≤
        ‖evaluation C P d u r (sites i) i - S n (regulatorPositions C i (sites i))
          (fun j => F.quotient (r j) _ (u j))‖ +
        ‖S n (regulatorPositions C i (sites i)) (fun j => F.quotient (r j) _ (u j)) -
          S n x (fun j => F.quotient (r j) _ (u j))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

theorem literal_limit {C : Sequence} {P : Calibration C} {F : Fields}
    {S : Fields.Kernel F} (hS : Fields.Scaling S C P) (hE : Fields.Euclidean S) :
    LiteralLimit C P F S := by
  intro n x hx
  obtain ⟨sites, hs⟩ := hS.coverage n x
  exact ⟨sites, hs, fun d u r => correlator_limit_along_sites hS hE hx sites hs d u r⟩

theorem continuum_acceptance : ContinuumAcceptance := by
  intro ε hε
  filter_upwards [YM.Massive.interacting_six ε hε] with β h
  obtain ⟨C,P,F,m,s,B,T,S,V,hβ,hG,hC,hP,hRead,hF,hS,hE,hPCAC,hM,hT,hWard,hB,hCompare,hW,hV⟩ := h
  exact ⟨⟨C,P,F,m,s,B,T,S,V,hβ,hG,hC,hP,hRead,hF,hS,hE,hPCAC,hM,hT,hWard,hB,hCompare,hW,hV⟩,
    literal_limit hS hE⟩

end YMReview.QCD
#print axioms YMReview.QCD.correlator_limit_along_sites
#print axioms YMReview.QCD.literal_limit
#print axioms YMReview.QCD.continuum_acceptance
