import ContinuumSpec

/-! An independently stated exclusion test for the exact submitted Candidate
class. A physical free model must supply this interface; it is not assumed
to follow merely from calling some fields 'free'. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive

structure SeparateStressSectors (F : Fields) where
  sector : Fin 7 → Momentum F
  candidate : ∀ i, Physics.Candidate F (sector i)
  probe : Fin 7 → Momentum F →ₗ[ℂ] ℂ
  identity_zero : ∀ i, probe i (Physics.identity F) = 0
  detects : ∀ i j, probe i (sector j) = if i = j then 1 else 0

def StressExclusion : Prop := ∀ (F : Fields),
  Nonempty (SeparateStressSectors F) → ∀ T : Momentum F, ¬ Physics.Stress F T

-- Exact algebraic control: one identity direction plus seven sector directions.
-- This is a coefficient space, not a constructed free QCD field system.
abbrev SectorCoefficients := Fin 8 → ℂ
def sectorUnit : SectorCoefficients := Pi.single 0 1
def sectorVector (i : Fin 7) : SectorCoefficients := Pi.single i.succ 1
def sectorProbe (i : Fin 7) : SectorCoefficients →ₗ[ℂ] ℂ := LinearMap.proj i.succ

-- Explicit degenerate model for checking Candidate membership, rotations and
-- conservation. These constant fields are NOT the free gauge/Dirac theory.
def constantSectorFields : Fields where
  W := SectorCoefficients
  level _ := ⊤
  quotient _ _ := 0
  unit := sectorUnit
  adj _ := starLinearEquiv ℂ
  parity := LinearEquiv.refl ℂ _
  charge := LinearEquiv.refl ℂ _
  flavor := 1
  action := 1
  partialD _ := 0
  lie _ := 0

def constantTensor (x : SectorCoefficients) : Momentum constantSectorFields :=
  fun a b => if a = b then x else 0

def constantProbe (i : Fin 7) : Momentum constantSectorFields →ₗ[ℂ] ℂ where
  toFun T := T 0 0 i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def StressControlTest : Prop := ∀ T : Momentum constantSectorFields,
  ¬ Physics.Stress constantSectorFields T

end YMReview.QCD
