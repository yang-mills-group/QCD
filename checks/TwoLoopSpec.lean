import FlavorSpec

/-! A leading logarithmic slope cannot identify a two-loop coefficient.
The parameter t is log(μ/Λ), so log t is the subleading log-log term. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Filter
open scoped Topology

def logCorrected (A k t : ℝ) : ℝ := A*t + k*Real.log t
def secondOrderRead (A : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := (w t - A*t) / Real.log t
/-- Coefficient of log t for Wilson convention w=6/g², if the two-loop flow holds. -/
def wilsonLogLog (f : ℝ) : ℝ := 6*gBeta1 f/gBeta0 f

def LeadingSlopeDoesNotFixTwoLoop : Prop := ∀ A k : ℝ,
  Tendsto (fun t => logCorrected A k t/t) atTop (𝓝 A) ∧
  Tendsto (secondOrderRead A (logCorrected A k)) atTop (𝓝 k)

def SecondOrderReadStable : Prop := ∀ (L w v : ℕ → ℝ) (A k E : ℝ),
  Tendsto L atTop atTop → (∀ᶠ i in atTop, |w i - v i| ≤ E) →
  Tendsto (fun i => (v i-A*L i)/Real.log (L i)) atTop (𝓝 k) →
  Tendsto (fun i => (w i-A*L i)/Real.log (L i)) atTop (𝓝 k)

def uvLogScale (C : YM.Massive.Sequence) (i : ℕ) : ℝ :=
  Real.log ((C.S.spacing (C.N i))⁻¹)

/-- An additional requirement, not a clause of the submitted Path. -/
def TwoLoopPath (C : YM.Massive.Sequence) : Prop :=
  Tendsto (fun i => ((C.A i).β (C.N i) - YM.Massive.betaSlope * uvLogScale C i) /
    Real.log (uvLogScale C i)) atTop (𝓝 (wilsonLogLog 6))

def TwoLoopStiffness (C : YM.Massive.Sequence) (a b : YM.Axis) (T : YM.QCD.su.Color) : Prop :=
  Tendsto (fun i => (YM.Massive.Stiffness.read ((C.A i).density (C.N i)) a b T -
    YM.Massive.betaSlope * uvLogScale C i) / Real.log (uvLogScale C i))
    atTop (𝓝 (wilsonLogLog 6))

def TwoLoopStiffnessBridge : Prop := ∀ (C : YM.Massive.Sequence) (β ε : ℝ),
  C.Path β ε → TwoLoopPath C → ∀ (a b : YM.Axis), a ≠ b →
  ∀ T : YM.QCD.su.Color, ‖T‖ = 1 → TwoLoopStiffness C a b T

end YMReview.QCD
