import BodyScopeSpec
import CouplingProof

set_option autoImplicit false
noncomputable section
namespace YMReview.QCD
open YM YM.Massive
open scoped BigOperators

theorem regulator_body_flavor_blind {n : Lattice.Side} {F G : ℕ}
    (R : Regulator n F) (Q : Regulator n G) (h : R.β=Q.β) (U : QCD.Lat.Grid n) :
    Stiffness.body R.density U=Stiffness.body Q.density U := by
  rw [regulator_body_is_wilson,regulator_body_is_wilson,h]

theorem regulator_stiffness_flavor_blind {n : Lattice.Side} {F G : ℕ}
    (R : Regulator n F) (Q : Regulator n G) (h : R.β=Q.β)
    (a b : Axis) (T : QCD.su.Color) :
    Stiffness.read R.density a b T=Stiffness.read Q.density a b T := by
  have he : Stiffness.action R.density=Stiffness.action Q.density := by
    ext U
    unfold Stiffness.action
    rw [regulator_body_flavor_blind R Q h U]
  simp only [Stiffness.read,he]

theorem regulator_marginal_keeps_flavors {n : Lattice.Side} {F : ℕ}
    (R : Regulator n F) (U : QCD.Lat.Grid n) :
    QCD.Grass.ber (QCD.Lat.Modes n F) (R.density U)=
      (Wilson.bare R.β U : ℂ)*∏ i, (QCD.Lat.bareD R.t U (R.m i)).det := by
  rw [← R.gaugeRate_complex U]
  simp only [Regulator.gaugeRate,Complex.ofReal_mul,Complex.ofReal_prod,QCD.Lat.realD]

theorem body_scope_test : BodyScopeTest := by
  intro n F G R Q h
  exact ⟨regulator_body_flavor_blind R Q h,regulator_stiffness_flavor_blind R Q h,
    regulator_marginal_keeps_flavors R⟩

end YMReview.QCD
#print axioms YMReview.QCD.regulator_body_flavor_blind
#print axioms YMReview.QCD.regulator_stiffness_flavor_blind
#print axioms YMReview.QCD.regulator_marginal_keeps_flavors
#print axioms YMReview.QCD.body_scope_test
