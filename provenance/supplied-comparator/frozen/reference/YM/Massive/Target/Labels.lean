import YM.Massive.Target.Covers
import YM.Massive.Finite.Core
import YM.Labels.Action
import YM.Maxwell.Wick
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Statement: all-horizon graded UV labels

`Label d`, d **twice** the inclusive engineering weight horizon, incl any spin count,
parity and flavor. Radial gauge, real Lie algebra Taylor variables, complex exterior
algebra of independent column and row jets (**derivative values** for spin slots).
In particular the action of constant color is simultaneous on the two factors, NOT taking
separately invariant gauge polynomials and spin polynomials.

Actions on polynomials in the two factors by substitution. Under (R,S) test the column labels
by S⁻¹ ψ(Rx), bars by bar(Rx) S. On spin µ derivatives of order |alpha|, the components of an
old derivative ∂µ transform with R_{νµ}. For adjunction the reflected polynomial applies an
**order reversal** on all spin letters, switches columns and bars with `-γ_axis`, and conjugates
coefficients (in the real Lie basis). Don't confuse complex or charge conjugation with this step.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice TensorProduct
open scoped Topology TensorProduct BigOperators Matrix.Norms.Frobenius Matrix

namespace UV

def order (v : Axis → ℕ) := ∑ a, v a

/-- Ambient derivatives through d. After taking engineering cap, some of these
variables never contribute. -/
abbrev Multi (d : ℕ) := {p : Axis → Fin (d+1) // order (fun a => (p a).val) ≤ d}

instance (d : ℕ) : Fintype (Multi d) := Fintype.ofFinite _
instance (d : ℕ) : Zero (Multi d) := ⟨⟨fun _ => 0, by simp [order]⟩⟩

variable {d : ℕ}

def power (p : Multi d) (a : Axis) : ℕ := (p.val a).val

def first (a : Axis) : Multi 8 := ⟨Pi.single a 1, by
  simp [order,Pi.single_apply, apply_ite Fin.val]⟩

abbrev SpinMode (d : ℕ) := (Multi d × Fiber) × Flavor 6
abbrev GPol := Labels.Pol su
abbrev SpinPol (d : ℕ) := Dirac (SpinMode d)

/-- Graded polynomial algebra (ambient, then take cap below). -/
abbrev Pol (d : ℕ) := GPol ⊗[ℂ] SpinPol d

abbrev Powers := (Labels.Key su →₀ ℕ) -- gauge monomial, suppress identity notation
abbrev PowerPair (d : ℕ) := Powers × Finset (Pairs (SpinMode d))

def spinWeight (p : Multi d) : ℕ := 3 + 2 * order (power p)
def letterWeight (i : Pairs (SpinMode d)) : ℕ := spinWeight (Sum.elim id id i).1.1

def weight (p : PowerPair d) := 2 * Labels.height p.1 + ∑ i ∈ p.2, letterWeight i

def gen (p : PowerPair d) : Pol d := MvPolynomial.monomial p.1 1 ⊗ₜ[ℂ] Grass.mono p.2

def cap (d : ℕ) : Submodule ℂ (Pol d) := Submodule.span ℂ (gen '' {p | weight p ≤ d})

def colorTable (u : su.El) : Matrix (SpinMode d) (SpinMode d) ℂ :=
  Matrix.of fun i j => if i.2=j.2 ∧ i.1.1=j.1.1 then touch (colour u) i.1.2 j.1.2 else 0

def colorAct (u : su.El) : Pol d →ₗ[ℂ] Pol d :=
  TensorProduct.map (Labels.changed fun _ => Labels.Taylor.paint u).toLinearMap
    (Grass.adapter (colorTable u) (star (colorTable u)).transpose).toLinearMap

def labels (d : ℕ) : Submodule ℂ (Pol d) := cap d ⊓ ⨅ u, LinearMap.ker (colorAct u - LinearMap.id)

abbrev Label (d : ℕ) := ↥(labels d)

theorem weightFinite (d : ℕ) : {p : PowerPair d | weight p ≤ d}.Finite := by
  apply ((Labels.cap_finite su d).prod (Set.finite_univ : (Set.univ (α:=Finset _)).Finite)).subset
  rintro p hp
  change weight p ≤ d at hp
  refine ⟨?_,Set.mem_univ _⟩
  change Labels.height p.1 ≤ d
  unfold weight at hp; omega

instance (d : ℕ) : FiniteDimensional ℂ (cap d) := Module.Finite.of_fg (Submodule.fg_span ((weightFinite d).image _))

instance (d : ℕ) : FiniteDimensional ℂ (Label d) := by
  refine FiniteDimensional.of_injective (V₂ := ↥(cap d)) (Submodule.inclusion (show labels d ≤ cap d from inf_le_left))
    ?_
  exact Submodule.inclusion_injective _

def unit (d : ℕ) : Pol d := tmul ℂ 1 1

/- symmetries of the polynomial system used in interpreting QCD ranks -/

def multiMove (p : EuPin) (i j : Multi d) : ℂ :=
  let x (a : Axis) : MvPolynomial Axis ℂ := ∑ b : Axis,
    MvPolynomial.C (p.coord.val b a : ℂ) * MvPolynomial.X b
  MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (power j)) (∏ a, (x a) ^ power i a)

def turned (p : EuPin) (S : Bundle) : Matrix (SpinMode d) (SpinMode d) ℂ :=
  Matrix.of fun i j => if i.2 = j.2 then multiMove p i.1.1 j.1.1 * S i.1.2 j.1.2 else 0

def pinAct (p : EuPin) : Pol d →ₗ[ℂ] Pol d :=
  TensorProduct.map (Labels.rotated p.coord).toLinearMap
    (Grass.adapter (turned p (wave p.matrix⁻¹.val)) (turned p (wave p.matrix.val.transpose))).toLinearMap

abbrev FlavorTorus := Flavor 6 → ↥(unitary ℂ)

def byFlavor {A : Type*} [DecidableEq A] (u : FlavorTorus) (f : A → Flavor 6) : Matrix A A ℂ :=
  Matrix.diagonal fun i => u (f i)

def flavorAct (u : FlavorTorus) : Pol d →ₗ[ℂ] Pol d :=
  TensorProduct.map LinearMap.id
    (Grass.adapter (byFlavor u fun i : SpinMode d => i.2) (byFlavor u⁻¹ fun i : SpinMode d => i.2)).toLinearMap

def parityAct : Pol d →ₗ[ℂ] Pol d := TensorProduct.map LinearMap.id grade.toLinearMap

section ChargeConjugation

/-- Lie automorphism in the given basis takes componentwise conjugate in color matrices. -/
def reflectColor : su.Color →ₗ[ℝ] su.Color := su.projectColor.comp <|
  (show QCD.Mat →ₗ[ℝ] QCD.Mat from
    { toFun := QCD.which true, map_add' := by intro a b; ext; simp [QCD.which]
      map_smul' := by intro a b; ext; simp [QCD.which] }).comp su.colorMat

def recolor {j : ℕ} : Labels.Taylor su j →ₗ[ℝ] Labels.Taylor su j where
  toFun A := ⟨fun i => reflectColor.toContinuousLinearMap.compContinuousMultilinearMap (A.val i), by
    refine ⟨fun i x s => ?_, fun z => ?_⟩
    · exact congrArg reflectColor (A.property.1 i x s)
    change ∑ i, z i • reflectColor (Labels.Taylor.value A i z) = _
    rw [← map_zero reflectColor, ← A.radial_value z, map_sum]; simp only [map_smul]⟩
  map_add' := by intro x y; apply Subtype.ext; funext i; ext1; exact map_add reflectColor _ _
  map_smul' := by intro c x; apply Subtype.ext; funext i; ext1; exact map_smul reflectColor _ _

def spinTable (S : Spike) : Matrix (SpinMode d) (SpinMode d) ℂ :=
  Matrix.of fun i j => if i.2=j.2 ∧ i.1.1=j.1.1 then wave S i.1.2 j.1.2 else 0

/-- `psi → C bar^t`, `bar → -psi^t C^{-1}`, C=gamma 0 gamma 2. -/
def chargeAct : Pol d →ₗ[ℂ] Pol d :=
  TensorProduct.map (Labels.changed (fun _ => recolor)).toLinearMap
    (changeVars (Matrix.fromBlocks 0 (spinTable chargeMatrix)
      (spinTable (-(chargeMatrix⁻¹).transpose)) 0)).toLinearMap
end ChargeConjugation

def conjGPol : GPol →ₛₗ[starRingEnd ℂ] GPol where
  toFun := Labels.conjPol
  map_add' _ _ := map_add (MvPolynomial.map (starRingEnd ℂ)) _ _
  map_smul' := by
    intro c x; apply Labels.eval_ext
    intro A; rw [Labels.conj_value,map_smul,map_smul,Labels.conj_value]; simp

def flipTable (a : Axis) (S : Spike) : Matrix (SpinMode d) (SpinMode d) ℂ :=
  Matrix.of fun i j => (-1 : ℂ) ^ power i.1.1 a * spinTable S i j

def adj (a : Axis) : Pol d →ₛₗ[starRingEnd ℂ] Pol d :=
  TensorProduct.map ((Labels.rotated (Signed.reflect a)).toLinearMap.comp conjGPol)
    ((changeVars (Matrix.fromBlocks 0 (flipTable a (-(gamma a).transpose))
      (flipTable a (-gamma a)) 0)).toLinearMap.comp dagger)

/- explicit systems of target observables -/

def bilinear (a b : Flavor 6) (M : Spike) (p q : Multi d) : Pol d := tmul ℂ 1
  (∑ i : Pinor, ∑ j : Pinor, ∑ k : Hue, M i j • (bar ((p,i,k),a) * psi ((q,j,k),b)))

def curvature (a b : Axis) (k : su.ColorIndex) : GPol :=
  ∑ i : Fin (Labels.dim su 0),
    MvPolynomial.C (σ:=Labels.Key su)
      ((Maxwell.takeCurl (Labels.axes su 0 i) a b fun _ => 0) k : ℂ) *
        MvPolynomial.X ⟨0,i⟩

def dotF (a b i j : Axis) : Pol d := tmul ℂ (∑ k, curvature a b k * curvature i j k) 1

/-- Maxwell stress reference. -/
def gaugeStress (a b : Axis) : Pol 8 :=
  (∑ k, dotF a k b k) - (if a=b then (1/4 : ℂ) • (∑ i : Axis, ∑ j : Axis, dotF i j i j) else 0)

def spinStressUnsymm (i : Flavor 6) (a b : Axis) :=
  bilinear i i (gamma a) 0 (first b) - bilinear i i (gamma a) (first b) 0

/-- Eq.(tFull) reference in orientation test. -/
def totalStress (a b : Axis) := gaugeStress a b +
  (1/4 : ℂ) • (∑ i : Flavor 6, (spinStressUnsymm i a b + spinStressUnsymm i b a))

/-- Explicit odd color singlet (the three distinct flavors 0,1,2). -/
def baryon (i j k : Pinor) : Pol 9 := tmul ℂ 1 (∑ σ : Equiv.Perm Hue, Equiv.Perm.sign σ •
  (psi ((0,i,σ 0),0) * psi ((0,j,σ 1),1) * psi ((0,k,σ 2),2)))

end UV
end YM.Massive
