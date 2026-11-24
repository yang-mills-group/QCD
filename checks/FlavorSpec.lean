import YM.QCD.Matter
import YM.QCD.Raft.Roads
import YM.Massive.Target.Tower
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Flavor-dependent benchmarks. These definitions specify conventional perturbative
coefficients; they do not assert a Feynman-diagram calculation or a continuum beta function.
The proofs separately connect the first coefficient to the submitted trace and RG data. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM

/-- Coefficient in da/d(log μ) = -2 a² (B₀ + B₁ a + ...), a=g²/(16π²). -/
def oneLoopCoefficient (f : ℝ) : ℝ := 11 - 2 * f / 3
/-- Conventional massless SU(3), fundamental Dirac two-loop benchmark. -/
def twoLoopCoefficient (f : ℝ) : ℝ := 102 - 38 * f / 3
def gBeta0 (f : ℝ) : ℝ := oneLoopCoefficient f / (16 * Real.pi^2)
def gBeta1 (f : ℝ) : ℝ := twoLoopCoefficient f / (16 * Real.pi^2)^2

/-- This strict inequality is the actual hypothesis used by Stratum.Burg.perimeter. -/
def trajectoryBudget (f : ℕ) : Prop := QCD.su.slopeConstant / 2 < QCD.Raft.betaQ f

def FlavorTest : Prop :=
  (∀ f : ℕ, QCD.bTrace f / 6 = oneLoopCoefficient f) ∧
  (∀ f : ℕ, QCD.Raft.betaQ f = 12 * gBeta0 f) ∧
  Massive.betaSlope = 12 * gBeta0 6 ∧
  (∀ f : ℕ, 0 < QCD.Raft.betaQ f ↔ f ≤ 16) ∧
  (∀ f : ℕ, trajectoryBudget f ↔ f ≤ 8)

end YMReview.QCD
