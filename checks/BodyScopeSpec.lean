import CouplingSpec

/-! Distinguish the target's scalar Grassmann body from the Berezin marginal.
This holds at the microscopic regulator; it does not describe all blocked scales. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive

def BodyScopeTest : Prop := ∀ (n : Lattice.Side) (F G : ℕ)
    (R : Regulator n F) (Q : Regulator n G), R.β=Q.β →
  (∀ U, Stiffness.body R.density U=Stiffness.body Q.density U) ∧
  (∀ a b T, Stiffness.read R.density a b T=Stiffness.read Q.density a b T) ∧
  (∀ U, QCD.Grass.ber (QCD.Lat.Modes n F) (R.density U)=
    (Wilson.bare R.β U : ℂ)*∏ i, (QCD.Lat.bareD R.t U (R.m i)).det)

end YMReview.QCD
