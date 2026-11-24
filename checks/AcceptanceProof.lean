import AcceptanceSpec
import YM.Plata.Massive

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive Filter
open scoped Topology

theorem selected_of_theory {β ε : ℝ} (h : TheoryAt β ε) : Selected β ε := by
  obtain ⟨C,P,F,m,s,B,T,S,V,hβ,hG,hC,hP,hRead,hF,hS,hE,hPCAC,hM,hT,hWard,hB,hCompare,hW,hV⟩ := h
  let w : Witness β ε := ⟨C,P,F,m,s,B,T,S,V,hβ,hG,hC,hP,hRead,hF,hS,hE,hPCAC,hM,hT,hWard,hB,hCompare,hW,hV⟩
  obtain ⟨R,hR⟩ := hV.success
  refine ⟨w,R,hR,hV.euclidean V.chosen,hV.ward V.chosen,hV.compare V.chosen,
    hM.positive,hM.distinct,?_,hT.nontrivial,?_⟩
  · intro i j hij
    exact (hPCAC.pairs i j hij).pseudo
  · intro i j hij hz
    have he : R.φ (m.pseudo F i j) = R.φ 0 := by simpa only [map_zero] using hz
    exact (hPCAC.pairs i j hij).pseudo (hR.faithful he)

theorem acceptance : Acceptance := by
  intro ε hε
  filter_upwards [YM.Massive.interacting_six ε hε] with β hβ
  exact selected_of_theory hβ

-- Nonzero denominators needed for the *defined* PCAC rescalings.
theorem mass_sum_ne_zero {s : Signals} (h : s.Masses) (i j : Copies) :
    s.bMass i + s.bMass j ≠ 0 := ne_of_gt (add_pos (h.positive i) (h.positive j))

theorem mass_difference_ne_zero {s : Signals} (h : s.Masses) (i j : Copies) (hij : i ≠ j) :
    s.bMass i - s.bMass j ≠ 0 := sub_ne_zero.mpr (fun he => hij (h.distinct he))

end YMReview.QCD
#print axioms YMReview.QCD.selected_of_theory
#print axioms YMReview.QCD.acceptance
#print axioms YMReview.QCD.mass_sum_ne_zero
#print axioms YMReview.QCD.mass_difference_ne_zero
