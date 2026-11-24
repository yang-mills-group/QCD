import AcceptanceSpec
import Mathlib.Tactic

/-! Literal convergence of the submitted, normalized Wilson correlators.
The path of lattice sites is shared by all choices of insertions at a given
configuration. No independent continuum construction is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive Filter Set
open scoped Topology

def LiteralLimit (C : Sequence) (P : Calibration C) (F : Fields)
    (S : Fields.Kernel F) : Prop :=
  ∀ (n : ℕ) (x : Points n), x ∈ conf n →
    ∃ sites : ℕ → Fin n → Lattice.Cover,
      Tendsto (fun i => Fields.Limit.regulatorPositions C i (sites i)) atTop (𝓝 x) ∧
      ∀ (d : Fin n → ℕ) (u : (j : Fin n) → UV.Label (d j)) (r : Fin n → Averaging),
        Tendsto (fun i => Fields.Limit.evaluation C P d u r (sites i) i)
          atTop (𝓝 (S n x (fun j => F.quotient (r j) _ (u j))))

def ContinuumAcceptance : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ β in atTop,
  ∃ w : Witness β ε, LiteralLimit w.sequence w.calibration w.fields w.moments

end YMReview.QCD
