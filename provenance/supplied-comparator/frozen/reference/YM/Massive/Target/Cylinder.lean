import YM.Massive.Target.Labels
import YM.Source.Local

/-!
# Anchored local lattice field algebra and its orientations

Positions on the cover to retain AP seams. `Stencil` here uses integer
spacing independent cylinders for the reference section (can depend on the
engineering horizon, not on the torus); their translates needn't inject
at the first few terms in a sequence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson TensorProduct Function UV
open scoped Topology TensorProduct BigOperators Matrix.Norms.Frobenius Matrix
variable {n : Side} {F : ℕ}

def conjugate (U : su.El) : su.El := by
  let A := QCD.which true (colour U)
  have hu : A ∈ unitary _ := by
    unfold A; constructor
    · rw [QCD.which_star, ← QCD.which_mul,show star (colour U) * colour U = 1 from su.mat_star_mul U,QCD.which_one]
    rw [QCD.which_star, ← QCD.which_mul,show colour U * star (colour U) = 1 from su.mat_mul_star U,QCD.which_one]
  refine ⟨⟨A,hu⟩,?_⟩
  change (A.det)=1
  change ((starRingEnd ℂ).mapMatrix (colour U)).det=1
  rw [← RingHom.map_det,show (colour U).det = 1 from QCD.det_su U,map_one]

@[simp] theorem colour_conjugate (U : su.El) : colour (conjugate U)=QCD.which true (su.mat U) := rfl

namespace Cylinder

abbrev Nearest (S : Finset Cover) (F : ℕ) := ((↥S × Fiber) × Flavor F)

abbrev Formula (S : Finset Cover) (F : ℕ) := Source.Formula su S ⊗[ℂ] Dirac (Nearest S F)

/-- Store spin representatives on the torus as in `[0,n)`; `t=0` is the seam. -/
def sheet (x : Site n) : Cover := fun i => (x i).val

def ap (n : Side) (x : Cover) : ℂ := ∏ i, (-1:ℂ) ^ (x i / (n.val:ℤ))

variable {S : Finset Cover}

def evaluate (U : CoverConfig su) (x : Formula S F) : Dirac (Nearest S F) :=
  TensorProduct.lid ℂ _ (TensorProduct.map (MvPolynomial.aeval (Source.entry U)).toLinearMap LinearMap.id x)

/-- Use lift `b`, not just its value modulo the period, in a physical placement. -/
def lower (b : Cover) : Matrix (Nearest S F) (Modes n F) ℂ := Matrix.of fun i j =>
  let y := i.1.1.val+b
  if ((wrap n y,i.1.2),i.2)=j then ap n y else 0

def places (b : Cover) (x : Formula S F) (U : Grid n) : Fields n F :=
  let M : Matrix (Nearest S F) (Modes n F) ℂ := lower b
  adapter M M (evaluate (expandAt (wrap n b) U) x)

namespace Action
abbrev FlavorTorusF (F : ℕ) := Flavor F → ↥(unitary ℂ)

def flavorF (u : FlavorTorusF F) (x : Density n F) : Density n F := fun U =>
  Grass.adapter (Matrix.diagonal fun i : Modes n F => (u i.2).val)
    (Matrix.diagonal fun i : Modes n F => star (u i.2).val) (x U)

abbrev flavor (u : UV.FlavorTorus) (x : Density n 6) : Density n 6 := flavorF u x

def moved (s : Signed) (M : Spike) : Matrix (Modes n F) (Modes n F) ℂ := Matrix.of fun i j =>
  let p := s.act (sheet i.1.1)
  if j.2=i.2 ∧ j.1.1=wrap n p then ap n p * wave M i.1.2 j.1.2 else 0

def pin (p : EuPin) (s : Signed) (x : Density n F) : Density n F := fun U =>
  Grass.adapter (moved s p.matrix⁻¹.val) (moved s p.matrix.val.transpose) (x (pull s 0 U))

def adj (a : Axis) (x : Density n F) : Density n F := fun U =>
  changeVars (Matrix.fromBlocks 0 (moved (Signed.mirror a) (-(gamma a).transpose))
                (moved (Signed.mirror a) (-gamma a)) 0)
    (dagger (x (pull (Signed.mirror a) 0 U)))

def charge (x : Density n F) : Density n F := fun U =>
  changeVars (Matrix.fromBlocks 0 (moved 1 chargeMatrix) (moved 1 (-(chargeMatrix⁻¹).transpose)) 0)
    (x (conjugate ∘ U))

def parity (x : Density n F) : Density n F := fun U => grade (x U)

end Action
end Cylinder
end YM.Massive
