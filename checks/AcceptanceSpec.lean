import YM.Massive.Target.Statement

/-! Readable, common-witness acceptance specification. All public target
clauses are retained. The selected reconstruction is explicitly attached to
the same fields, stresses, masses and family, not a separately chosen model.
-/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM.Massive
open Filter
open scoped Topology

structure Witness (β ε : ℝ) where
  sequence : Sequence
  calibration : Calibration sequence
  fields : Fields
  mesons : MassFields
  signals : Signals
  bases : Bases fields
  stress : Momentum fields
  moments : Fields.Kernel fields
  vacua : Vacua fields
  positiveCoupling : 0 < β
  geometry : Geometry
  path : sequence.Path β ε
  calibrated : calibration.System
  massReading : signals.Read sequence
  fieldSystem : fields.System calibration
  scaling : Fields.Scaling moments sequence calibration
  euclidean : Fields.Euclidean moments
  pcac : signals.PCAC fields mesons
  masses : signals.Masses
  stressTest : Physics.Stress fields stress
  ward : Physics.Ward stress moments
  content : bases.Content calibration stress
  comparison : bases.Comparison moments
  continuation : ∃ w : Continuation fields, w.Produces moments
  decomposition : vacua.Decomposes moments stress bases

def Selected (β ε : ℝ) : Prop := ∃ w : Witness β ε,
  ∃ R : Reconstruction w.fields,
    R.Theory (w.vacua.ensemble w.vacua.chosen) ∧
    Fields.Euclidean (w.vacua.ensemble w.vacua.chosen) ∧
    Physics.Ward w.stress (w.vacua.ensemble w.vacua.chosen) ∧
    w.bases.Comparison (w.vacua.ensemble w.vacua.chosen) ∧
    (∀ i, 0 < w.signals.bMass i) ∧ Function.Injective w.signals.bMass ∧
    (∀ i j, i ≠ j → w.mesons.pseudo w.fields i j ≠ 0) ∧
    (∀ z : ℂ, w.stress ≠ z • Physics.identity w.fields) ∧
    (∀ i j, i ≠ j → R.φ (w.mesons.pseudo w.fields i j) ≠ 0)

def Acceptance : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ β in atTop, Selected β ε

end YMReview.QCD
