import YM.QCD.Lattice.Gamma
import YM.Mink.Poincare
import YM.Mink.Boost

/-!
# Statement: coordinate group and spin conventions

Keep **both lifts**, also for discrete and improper Euclidean rotations.
A matrix presentation: intertwine the Dirac gammas and preserve the C form.
SO maps `Lorentz` in these statements are the actual proper orthochronous
Lorentz matrices; `Ortho` includes orientation reversing. Use time **last**
(`su` theory always four coordinate directions).
To specify content without assuming any Lie theory, the target includes,
inter alia, that there are lifts of every such element with doublet fibers
and lifts along the rotations/boosts used in the field covariance statements.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat Matrix Mink Function
open scoped Matrix Matrix.Norms.Frobenius BigOperators

def chargeMatrix : Spike := gamma 0 * gamma 2

/-- Positive-plane-reflection-square convention. Take S with S C Sᵀ = C. -/
def KeepsC (S : Spikeˣ) := S.val * chargeMatrix * S.val.transpose = chargeMatrix

lemma KeepsC.mul {S T : Spikeˣ} (h : KeepsC S) (H : KeepsC T) : KeepsC (S*T) := by
  change S.val*T.val * _ * (S.val*T.val).transpose = _
  rw [transpose_mul]
  unfold KeepsC at h H
  calc
    _ = S.val * (T.val * chargeMatrix * T.val.transpose) * S.val.transpose := by simp only [mul_assoc]
    _ = _ := by rw [H,h]

lemma KeepsC.inverse {S : Spikeˣ} (h : KeepsC S) : KeepsC S⁻¹ := by
  let A := S.val
  let B := S⁻¹.val
  have he : B*A=1 := S.inv_val
  change B*_ * B.transpose = _
  calc
    _ = B*(A*chargeMatrix*A.transpose)*B.transpose := by rw [show A*chargeMatrix*A.transpose=_ from h]
    _ = B*A*chargeMatrix*(B*A).transpose := by rw [transpose_mul]; simp only [mul_assoc]
    _ = _ := by rw [he]; simp

def slash (x : E4) : Spike := ∑ i, (x i : ℂ) • gamma i

/-- at Minkowski x take the gamma of (space x, -i time x), per Wick convention. -/
def wickSlash (x : E4) : Spike :=
  (∑ i : SpaceAxis, (x i.castSucc : ℂ) • gamma i.castSucc) +
    (-Complex.I * time x : ℂ) • gamma timeAxis

private def presentation {P : Type*} [Group P] (f : P → E4 → E4)
    (h : ∀ x, f 1 x = x) (H : ∀ s t x, f (s*t) x = f s (f t x)) (g : E4 → Spike) :
    Subgroup (P × Spikeˣ) where
  carrier := {p | KeepsC p.2 ∧ ∀ x, p.2.val * g x = g (f p.1 x) * p.2.val}
  one_mem' := by simp [KeepsC,h]
  mul_mem' := by
    rintro ⟨s,A⟩ ⟨t,B⟩ ⟨hA,W⟩ ⟨hB,V⟩
    refine ⟨hA.mul hB,fun x => ?_⟩
    change A.val*B.val*g x = g (f (s*t) x) * (A.val*B.val)
    rw [H]; change ∀ x, A.val*g x = _ at W; change ∀ x, B.val*g x = _ at V
    dsimp only at W V; rw [mul_assoc, V, ← mul_assoc, W,mul_assoc]
  inv_mem' := by
    rintro ⟨s,A⟩ ⟨hA,W⟩
    refine ⟨hA.inverse,fun x => ?_⟩
    change A⁻¹.val*g x=g (f s⁻¹ x) * A⁻¹.val
    specialize W (f s⁻¹ x); dsimp only at W
    rw [← H,mul_inv_cancel,h] at W
    calc
      _ = A⁻¹.val*(g x*A.val)*A⁻¹.val := by rw [mul_assoc, mul_assoc, show A.val*A⁻¹.val=1 from A.val_inv,mul_one]
      _ = _ := by rw [← W, ← mul_assoc, show A⁻¹.val*A.val=1 from A.inv_val,one_mul]

def euPinSubgroup := presentation (P:=Ortho) Ortho.move Ortho.move_one Ortho.move_mul slash

def minkSpinSubgroup := presentation (P:=Lorentz) (fun p => p.act) Lorentz.act_one
  Lorentz.act_mul wickSlash

abbrev EuPin := ↥euPinSubgroup
abbrev RealSpin := ↥minkSpinSubgroup

-- Make content checkable and invocable without unfolding through this module.
lemma euPin_iff (p : Ortho × Spikeˣ) : p ∈ euPinSubgroup ↔
    KeepsC p.2 ∧ ∀ x, p.2.val * slash x = slash (Ortho.move p.1 x) * p.2.val := Iff.rfl

lemma realSpin_iff (p : Lorentz × Spikeˣ) : p ∈ minkSpinSubgroup ↔
    KeepsC p.2 ∧ ∀ x, p.2.val * wickSlash x = wickSlash (p.1.act x) * p.2.val := Iff.rfl

namespace EuPin
def coord (p : EuPin) := p.val.1
def matrix (p : EuPin) := p.val.2

def IsRotation (p : EuPin) := Lorentz.properTurn p.coord

def Lifts (p : EuPin) (s : Signed) := p.coord = s.ortho

def Path (a : Ortho.Skew) (p : ℝ → EuPin) :=
  p 0=1 ∧ Continuous p ∧ ∀ r, (p r).coord = Ortho.oneParameter a r
end EuPin

namespace RealSpin
def coord (p : RealSpin) := p.val.1
def matrix (p : RealSpin) := p.val.2

def Path (a : SpaceAxis) (p : ℝ → RealSpin) :=
  p 0=1 ∧ Continuous p ∧ ∀ r, (p r).coord = (Ray.fromAxis a).boost r
end RealSpin

structure Geometry : Prop where
  euclidean : Surjective EuPin.coord
  realTime : Surjective RealSpin.coord
  euOpen : IsOpenMap EuPin.coord
  realOpen : IsOpenMap RealSpin.coord
  euBoth (p : EuPin) : ∃ q : EuPin, p.coord = q.coord ∧ q.matrix = -p.matrix
  minkBoth (p : RealSpin) : ∃ q : RealSpin, p.coord = q.coord ∧ q.matrix = -p.matrix
  euFiber (p q : EuPin) (h : p.coord=q.coord) : p=q ∨ p.matrix = -q.matrix
  minkFiber (p q : RealSpin) (h : p.coord=q.coord) : p=q ∨ p.matrix = -q.matrix
  unitary (p : EuPin) : p.matrix.val ∈ _root_.unitary _
  reflection (a : Axis) : ∃ p : EuPin, p.Lifts (Signed.mirror a) ∧
    p.matrix.val = (-Complex.I) • (gamma a * g5)
  path (a : Ortho.Skew) : ∃ p, EuPin.Path a p
  boost (a : SpaceAxis) : ∃ p, RealSpin.Path a p
  parityDouble (a b : Axis) (h : a ≠ b) (p) (hp : EuPin.Path (Ortho.plane a b) p) :
    (p (2*Real.pi)).coord = 1 ∧ (p (2*Real.pi)).matrix = -1
  spatial (p : EuPin) (h : Lorentz.spatialTurn p.coord) : ∃ q : RealSpin,
    q.coord = Lorentz.room p.coord h ∧ q.matrix=p.matrix

end YM.Massive
