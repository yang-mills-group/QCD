import YM.QCD.Casimir

/-!
# The all-left matter count and the local Lie-index checks

Cubic and linear traces. Ordinary spin with independent SU(3), no other gauged factors. We
report the conventional one-loop sign **test** using these actual trace normalizations; it is not
a calculation of a running coupling in the construction. Global anomaly theory on general
manifolds is not formalized here. The finite flat periodic *Dirac* regulator is meant to preserve
the gauge invariance exactly; the trace checks in this file alone do not establish that either.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD
open Complex Finset
open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius InnerProductSpace

/-- A flavor contributes a fundamental and an antifundamental all left-handed. -/
abbrev Flavor (F : ℕ) := Fin F
abbrev LeftSlots (F : ℕ) := Flavor F × Bool
abbrev SlotColors (F : ℕ) := Hue × LeftSlots F

def which : Bool → Mat → Mat
  | false, X => X
  | true, X => X.map conj

lemma which_mul (g : Bool) (U V : Mat) : which g (U*V) = which g U * which g V := by
  cases g
  · rfl
  exact Matrix.map_mul

lemma which_one (g : Bool) : which g 1 = 1 := by cases g <;> simp [which]

lemma which_star (g : Bool) (U : Mat) : star (which g U) = which g (star U) := by
  cases g
  · rfl
  ext; rfl

def action (F : ℕ) : su.El →* Matrix (SlotColors F) (SlotColors F) ℂ where
  toFun U := Matrix.blockDiagonal fun j => which j.2 (su.mat U)
  map_one' := by
    change Matrix.blockDiagonal (fun j : LeftSlots F => which j.2 1) = 1
    simp_rw [which_one]
    exact Matrix.blockDiagonal_one
  map_mul' U V := by
    rw [← Matrix.blockDiagonal_mul]
    congr 1; ext1 j
    exact which_mul j.2 (su.mat U) (su.mat V)

def generator (F : ℕ) (X : su.Color) := Matrix.blockDiagonal (fun j : LeftSlots F => which j.2 (su.colorMat X))

lemma block_star {i n : Type*} [DecidableEq i] (M : i → Matrix n n ℂ) :
    star (Matrix.blockDiagonal M) = Matrix.blockDiagonal fun j => star (M j) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases hv : b = d
  · subst d; simp [Matrix.star_eq_conjTranspose]
  simp [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_apply',hv,Ne.symm hv]

@[simp] theorem action_inv (F : ℕ) (U : su.El) : action F U⁻¹ = star (action F U) := by
  change Matrix.blockDiagonal (fun j : LeftSlots F => which j.2 _) =
    star (Matrix.blockDiagonal _)
  rw [block_star]; congr 1; ext1 j
  exact (which_star _ (su.mat U)).symm

lemma unitary_action (F : ℕ) (U : su.El) : action F U ∈ unitary _ :=
  ⟨by rw [← action_inv, ← map_mul, inv_mul_cancel, map_one],
    by rw [← action_inv, ← map_mul, mul_inv_cancel, map_one]⟩

/-- The Lie action is that of the displayed group representation. -/
theorem generator_tangent (F : ℕ) (X : su.Color) (i j : SlotColors F) :
    HasDerivAt (fun s : ℝ => action F (su.lieExp (s • X)) i j) (generator F X i j) 0 := by
  let f : ℝ → Mat := fun s => su.mat (su.lieExp (s • X))
  have he : HasDerivAt f (su.colorMat X) 0 := by
    dsimp only [f]
    simp_rw [Gauge.mat_lieExp, map_smul]
    simpa using! hasDerivAt_exp_smul_const (su.colorMat X) (0:ℝ)
  have he (i j : Hue) : HasDerivAt (fun s => f s i j) ((su.colorMat X) i j) 0 := by
    let L : Mat →ₗ[ℝ] ℂ :=
      { toFun := fun Y => Y i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt _ he
  simp only [action,MonoidHom.coe_mk,OneHom.coe_mk,generator,Matrix.blockDiagonal_apply]
  by_cases hv : i.2 = j.2
  · simp only [if_pos hv]
    cases i.2.2
    · exact he ..
    exact (he _ _).star
  simp only [if_neg hv]
  exact hasDerivAt_const ..

/-- Standard local anomaly test: trace(X {Y,Z}). -/
def cubic {n : Type*} [Fintype n] (X Y Z : Matrix n n ℂ) : ℂ := (X*Y*Z).trace + (X*Z*Y).trace

lemma bar_trace (U : Mat) : (which true U).trace = star (U.trace) := by simp [which,Matrix.trace]

lemma dual_sign (X Y Z : su.Color) :
    cubic (which true (su.colorMat X)) (which true (su.colorMat Y)) (which true (su.colorMat Z)) =
    -cubic (su.colorMat X) (su.colorMat Y) (su.colorMat Z) := by
  have e (x y z : su.Color) : star ((su.colorMat x*su.colorMat y*su.colorMat z).trace) =
      - (su.colorMat x*su.colorMat z*su.colorMat y).trace := by
    rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose]
    simp only [star_mul, Gauge.colorMat_skew]
    let A : Mat := su.colorMat x
    let B : Mat := su.colorMat y
    let C : Mat := su.colorMat z
    change ((-C)*((-B)*(-A))).trace = -(A*C*B).trace
    rw [show -C*(-B*-A) = -(C*B*A) by noncomm_ring,Matrix.trace_neg,
      Matrix.trace_mul_cycle]
  simp only [cubic, ← which_mul,bar_trace]
  change star (((su.colorMat X)*(su.colorMat Y)*(su.colorMat Z)).trace) +
    star (((su.colorMat X)*(su.colorMat Z)*(su.colorMat Y)).trace) = - _
  rw [e X Y Z,e X Z Y]; abel

lemma anomaly (F : ℕ) (X Y Z : su.Color) : cubic (generator F X) (generator F Y) (generator F Z) = 0 := by
  have h : _ = _ := dual_sign X Y Z
  simp only [cubic,generator,← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]
  rw [← sum_add_distrib,Fintype.sum_prod_type]; apply sum_eq_zero
  intro f _
  rw [Fintype.sum_bool]
  change cubic (which true _) (which true _) (which true _) + cubic (su.colorMat X) (su.colorMat Y) (su.colorMat Z) = _
  rw [h, neg_add_cancel]

theorem mixed (F : ℕ) (X : su.Color) : (generator F X).trace = 0 := by
  have he := ((lie_iff _).mp (su.colorMat_mem X)).2
  rw [generator,Matrix.trace_blockDiagonal]
  apply sum_eq_zero; rintro ⟨i, _|_⟩ _
  · exact he
  rw [bar_trace,he,star_zero]

theorem flavors (F : ℕ) : Fintype.card (LeftSlots F) = 2*F := by simp [mul_comm]

/-- Dynkin index of all Weyl slots in the baseline inner product. -/
def leftT (F : ℕ) : ℝ := 6*F

lemma index_Weyl (F : ℕ) (X Y : su.Color) :
    - (generator F X * generator F Y).trace.re = leftT F * ⟪X,Y⟫_ℝ := by
  have ht (s : Bool) (A B : Mat) : (which s A * which s B).trace.re = (A*B).trace.re := by
    cases s
    · rfl
    rw [← which_mul, bar_trace]; rfl
  simp only [generator, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal, re_sum, ht]
  have he := su.trace_color X Y
  let A : Mat := su.colorMat X
  let B : Mat := su.colorMat Y
  change -(∑ _ : LeftSlots F, (A*B).trace.re) = _
  change -(A*B).trace.re = (↑(2+1:ℕ):ℝ)*⟪X,Y⟫_ℝ at he
  rw [← sum_neg_distrib]; simp only [he, sum_const, card_univ, flavors, leftT]; simp; ring

/-- The sign criterion from Lie trace data, in the trace-normalization of YM.Gauge. -/
def bTrace (F : ℕ) : ℝ := (11 * su.casimir - 2 * leftT F) / 3

theorem conventional (F : ℕ) : bTrace F / 6 = 11 - 2 * F / 3 := by
  rw [bTrace,leftT,Roots.casimir]; ring

/-- Test only. -/
theorem strict_screen (F : ℕ) : 0 < bTrace F ↔ F ≤ 16 := by
  have h := conventional F
  constructor
  · intro hp
    by_contra! hF; have hq : 17 ≤ F := hF
    have he : (17:ℝ) ≤ F := by exact_mod_cast hq
    linarith
  intro hF
  have he : (F:ℝ) ≤ 16 := by exact_mod_cast hF
  linarith

theorem six_screen : bTrace 6 / 6 = 7 := by rw [conventional]; norm_num

end YM.QCD
