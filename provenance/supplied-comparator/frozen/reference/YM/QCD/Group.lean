import YM.Gauge.Casimir
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Gauge input for vectorlike QCD

Actual closed image in the defining representation. Check the Lie algebra in the convention of
`YM.Gauge`. The two color representations for one Dirac flavor are treated in `Matter`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD

open scoped Topology Matrix.Norms.Frobenius BigOperators
open Function Filter NormedSpace

/-- SU(3) in the defining complex representation; not a quotient. -/
def su : Gauge where
  n := 2
  imageGroup := {
    carrier := {X | X.val.det = 1}
    one_mem' := Matrix.det_one
    mul_mem' {X Y} hx hy := by
      change (X.val * Y.val).det = 1
      rw [Matrix.det_mul, hx, hy, mul_one]
    inv_mem' {X} hx := by
      change (star X.val).det = 1
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one] }
  closed_imageGroup := isClosed_eq (show Continuous fun X : GaugeU 2 => X.val.det from by fun_prop)
    continuous_const

abbrev Hue := Fin 3
abbrev Mat := Matrix Hue Hue ℂ

@[simp] theorem det_su (U : su.El) : (su.mat U).det = 1 := U.property

/-- Jacobi determinant variation at 1 (complex matrices along real parameter).
Proof patterned on pure-gauge real tables (`YM.ProofPorts...Score`). -/
lemma det_at_one {I : Type*} [Fintype I] [DecidableEq I] {A : ℝ → Matrix I I ℂ} {B : Matrix I I ℂ} {x : ℝ}
    (h : A x = 1) (he : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x) :
    HasDerivAt (fun t => (A t).det) B.trace x := by
  classical
  let f (σ : Equiv.Perm I) (t : ℝ) := Equiv.Perm.sign σ • ∏ i, A t (σ i) i
  have ht (σ : Equiv.Perm I) : HasDerivAt (f σ) (if σ = 1 then ∑ i, B i i else 0) x := by
    have hh := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => he (σ i) i)).const_smul
      (Equiv.Perm.sign σ)
    simp only [h] at hh
    unfold f
    split_ifs with hi
    · subst σ; simpa only [Pi.smul_def, Equiv.Perm.sign_one, one_smul, Matrix.one_apply,
        Equiv.Perm.coe_one, id_eq, ↓reduceIte, Finset.prod_const_one,
        ← Finset.prod_fn (s := Finset.univ)] using hh
    have hv (i : I) : (∏ j ∈ Finset.univ.erase i, (1 : Matrix I I ℂ) (σ j) j) = 0 := by
      obtain ⟨j,hj,hs⟩ : ∃ j, j ≠ i ∧ σ j ≠ j := by
        by_contra! hf
        apply hi; ext j
        by_cases hj : j = i
        · subst j; by_contra! hl; exact hl (σ.injective (hf (σ i) hl))
        exact hf j hj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) (by simp [hs])
    simpa only [hv, zero_smul, Finset.sum_const_zero, smul_zero, Pi.smul_def,
      Finset.prod_apply] using hh
  simp_rw [Matrix.det_apply]
  simpa [f, Matrix.trace] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)

lemma exp_tangent (X : Mat) :
    HasDerivAt (fun t : ℝ => (exp (t • X)).det) X.trace 0 := by
  haveI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℝ _
  refine det_at_one (by simp) (fun i j => ?_)
  have hh : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa using! hasDerivAt_exp_smul_const X (0:ℝ)
  let F : Mat →ₗ[ℝ] ℂ :=
    { toFun := fun Y => Y i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f := LinearMap.toContinuousLinearMap F
  exact f.hasFDerivAt.comp_hasDerivAt _ hh

lemma det_exp_of_trace {X : Mat} (h : X.trace = 0) (t : ℝ) :
    (exp (t • X)).det = 1 := by
  haveI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℝ _
  let F := fun u : ℝ => (exp (u • X)).det
  have hF (u v : ℝ) : F (u + v) = F u * F v := by
    have he : Commute (u • X) (v • X) := ((Commute.refl X).smul_left u).smul_right v
    rw [show F (u+v) = _ from congrArg Matrix.det (show exp ((u+v) • X) =
      exp (u • X) * exp (v • X) by
        rw [add_smul]; exact exp_add_of_commute he),
      Matrix.det_mul]
  have ha (u : ℝ) : HasDerivAt F 0 u := by
    have hp := (exp_tangent X).scomp_of_eq u ((hasDerivAt_id' u).sub_const u) (by simp)
    rw [h, smul_zero] at hp
    change HasDerivAt (fun w => F (w-u)) 0 u at hp
    have hx : (fun s => F (s-u) * F u) = F := funext fun s => by rw [← hF, sub_add_cancel]
    simpa only [hx, zero_mul] using hp.mul_const (F u)
  exact (is_const_of_deriv_eq_zero (fun u => (ha u).differentiableAt) (fun u => (ha u).deriv) t 0).trans
    (by simp [F])

lemma lie_iff (X : Mat) : X ∈ su.lie ↔ star X = - X ∧ X.trace = 0 := by
  haveI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℝ _
  constructor
  · intro h
    refine ⟨su.generates_skew h, ?_⟩
    apply (exp_tangent X).unique
    have hp : (fun t : ℝ => (exp (t • X)).det) = (fun _ => (1:ℂ)) := by
      funext t
      obtain ⟨u, hu⟩ := (Gauge.mem_lie su).mp h t
      exact (congrArg Matrix.det hu.symm).trans (det_su u)
    rw [hp]
    exact hasDerivAt_const ..
  rintro ⟨hx, ht⟩ t
  have hp : exp (t • X) ∈ unitary Mat := by
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star (t • X) = -(t • X)
    rw [star_smul, hx, star_trivial, smul_neg]
  exact ⟨⟨⟨_, hp⟩, det_exp_of_trace ht t⟩, rfl⟩

end YM.QCD
