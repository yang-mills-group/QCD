import FlavorSpec
import YM.QCD.Pearl.Usage

/-! Read an actual submitted one-fermion determinant response, not just its named
coefficient. This is the frozen-background free Wilson calculation; it is not a
proof of the full interacting continuum beta function. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM Filter
open scoped Topology

def fermionResponse (C : QCD.su.Color) (n : Lattice.Side) : ℝ :=
  QCD.Pearl.priceR C (fun X : QCD.Lat.Grid n => QCD.Lat.bareD 0 X 0)

def FermionScreeningTest : Prop := ∀ (C : QCD.su.Color), ‖C‖ = 1 →
  Tendsto (fun n : Lattice.Side => fermionResponse C n / Real.log (n.val:ℝ))
    atTop (𝓝 (1/(2*Real.pi^2)))

end YMReview.QCD
