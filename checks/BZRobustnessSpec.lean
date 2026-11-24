import BZHigherOrderSpec
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniform size and derivative control have different consequences for a fixed point.
These are conditional scalar tests, not supplied QCD remainder estimates. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open Set

def correctedBeta (f : ℝ) (R : ℝ → ℝ) (a : ℝ) : ℝ :=
  -2*a^2*correctedBracket f R a
def plateauRemainder (f h a : ℝ) : ℝ :=
  -twoLoopCoefficient f*max (-h) (min h (a-bzRoot f))

def BoundAloneNotUnique : Prop := ∀ (f δ : ℝ),
  0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  0 < δ → δ < oneLoopCoefficient f/2 →
  ∃ R : ℝ → ℝ, Continuous R ∧ (∀ a, |R a| ≤ δ) ∧
    ∃ a b : ℝ, a ∈ Ioo (bzRoot f/2) (3*bzRoot f/2) ∧
      b ∈ Ioo (bzRoot f/2) (3*bzRoot f/2) ∧ a ≠ b ∧
      correctedBracket f R a=0 ∧ correctedBracket f R b=0

def BZRobustnessTest : Prop := ∀ (f δ ρ : ℝ) (R R' : ℝ → ℝ),
  0 < oneLoopCoefficient f → twoLoopCoefficient f < 0 →
  0 ≤ δ → δ < oneLoopCoefficient f/2 → 0 ≤ ρ → ρ < -twoLoopCoefficient f →
  (∀ a ∈ Icc (bzRoot f/2) (3*bzRoot f/2), HasDerivAt R (R' a) a) →
  (∀ a ∈ Icc (bzRoot f/2) (3*bzRoot f/2), |R a| ≤ δ ∧ |R' a| ≤ ρ) →
  ∃ a ∈ Ioo (bzRoot f/2) (3*bzRoot f/2), correctedBeta f R a=0 ∧
    |a-bzRoot f| ≤ δ/(-twoLoopCoefficient f) ∧
    (∀ b ∈ Icc (bzRoot f/2) (3*bzRoot f/2), correctedBeta f R b=0 → b=a) ∧
    HasDerivAt (correctedBeta f R) (-2*a^2*(twoLoopCoefficient f+R' a)) a ∧
    0 < -2*a^2*(twoLoopCoefficient f+R' a)

/-- Concrete three-loop reference check, with the remainder hypotheses discharged. -/
def ThreeLoopRobustnessTest : Prop :=
  ∃ a ∈ Ioo (1/318:ℝ) (1/316), threeLoopBeta 16 a=0 ∧
    (∀ b ∈ Icc (bzRoot 16/2) (3*bzRoot 16/2), threeLoopBeta 16 b=0 → b=a) ∧
    HasDerivAt (threeLoopBeta 16)
      (-2*a^2*(twoLoopCoefficient 16+2*threeLoopCoefficient 16*a)) a ∧
    0 < -2*a^2*(twoLoopCoefficient 16+2*threeLoopCoefficient 16*a)

end YMReview.QCD
