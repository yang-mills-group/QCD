import ScreeningSpec

/-! Independent block-determinant check of flavor multiplicity for identical free
Wilson flavors. This benchmark does not satisfy the target's distinct-mass condition. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM Filter
open scoped Topology

def repeatedRectify {n : Lattice.Side} (F : ℕ) (C : QCD.su.Color)
    (M : QCD.Run.St n) (x : QCD.Rudder.Weath n) : ℝ :=
  -deriv (deriv (fun t:ℝ => Real.log ‖(Matrix.blockDiagonal
    (fun _ : Fin F => M (QCD.Rudder.bird C ∘ (t • x)))).det‖)) 0

def repeatedResponse (F : ℕ) (C : QCD.su.Color) (n : Lattice.Side) : ℝ :=
  let M : QCD.Run.St n := fun X => QCD.Lat.bareD 0 X 0
  (repeatedRectify F C M (QCD.Pearl.cosine (Lattice.step 0) 1) +
    repeatedRectify F C M (QCD.Pearl.sineP (Lattice.step 0) 1)) /
      ((n.val:ℝ)^4 * QCD.Pearl.beamH n^2)

def FlavorDeterminantTest : Prop := ∀ (F : ℕ) (C : QCD.su.Color), ‖C‖ = 1 →
  Tendsto (fun n : Lattice.Side => repeatedResponse F C n/Real.log (n.val:ℝ))
    atTop (𝓝 ((F:ℝ)/(2*Real.pi^2)))

end YMReview.QCD
