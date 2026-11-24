import YM.QCD.Grass.Gauss

/-!
# Dirac reflection operations

Anti-linear reversal with psi and bar interchanged. `tilt` uses a Hermitian
involutive R for gamma-axis and relabeling, and the extra minus sign
for the chosen Berezin/exponent convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Function Finset NormedSpace
open scoped Matrix BigOperators

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

lemma ext_reversing {F G : Alg A →ₛₗ[starRingEnd ℂ] Alg B} (hf : ∀ x y,F (x*y)=F y * F x)
    (hg : ∀ x y,G (x*y)=G y * G x) (h₁ : F 1=G 1) (h : ∀ i,F (atom i)=G (atom i)) : F=G := by
  ext1 x
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp [Algebra.algebraMap_eq_smul_one,h₁]
  | ι v => rw [line_atoms (A:=A)]; simp_rw [map_sum,map_smulₛₗ,h]
  | add x y hx hy => simp [hx,hy]
  | mul x y hx hy => simp [hf,hg,hx,hy]

def turn : Dirac A →ₛₗ[starRingEnd ℂ] Dirac A := (embed (Sum.swap (α:=A) (β:=A))).toLinearMap.comp dagger
@[fun_prop] lemma turn_cont : Continuous (fun x : Dirac A => turn x) := (continuous_embed _).comp continuous_dagger
@[simp] lemma turn_one : turn (1:Dirac A)=1 := by simp [turn,dagger_one]
lemma turn_mul (x y : Dirac A) : turn (x*y)=turn y*turn x := by simp [turn,dagger_mul]
@[simp] lemma turn_psi (i : A) : turn (psi i)=bar i := by rw [turn,LinearMap.comp_apply,psi,dagger_atom, AlgHom.toLinearMap_apply,embed_atom]; rfl
@[simp] lemma turn_bar (i : A) : turn (bar i)=psi i := by rw [turn,LinearMap.comp_apply,bar, dagger_atom, AlgHom.toLinearMap_apply,embed_atom]; rfl
@[simp] lemma turn_pair (i : A) : turn (pair i)=pair i := by simp [pair,turn_mul]
lemma turn_parity (x : Dirac A) : grade (turn x)=turn (grade x) := by simp only [turn,LinearMap.comp_apply,AlgHom.toLinearMap_apply,embed_grade,dagger_parity]
lemma turn_deg {n} {x : Dirac A} (h : x ∈ layer (Pairs A) n) : turn x ∈ layer _ n := embed_layer _ (dagger_degree h)
lemma turn_atom (i : Pairs A) : turn (atom i) = atom (Sum.swap i) := by cases i; exact turn_psi _; exact turn_bar _
@[simp] lemma turned (x : Dirac A) : turn (turn x)=x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp [Algebra.algebraMap_eq_smul_one,turn_one]
  | ι v => rw [line_atoms (A:=Pairs A)]; simp [turn_atom]
  | add x y hx hy => simp [hx,hy]
  | mul x y hx hy => simp [hx,hy,turn_mul]
lemma turn_exp (x : Dirac A) : turn (exp x)=exp (turn x) := by simp only [turn,LinearMap.comp_apply,dagger_exp,AlgHom.toLinearMap_apply,map_weight]

lemma turn_vol (s : Finset A) : turn (vol s)=vol s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [vol_step _ _ hi, turn_mul, ih, turn_pair]; exact (pair_grade i).central _
lemma turn_amp (x : Dirac A) : ber A (turn x)=star (ber A x) := by
  classical
  rw [← write x]; simp only [map_sum, star_sum]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i=univ
  · subst i
    have he : mono (univ : Finset (Pairs A)) ∈ layer (Pairs A) (Fintype.card (Pairs A)) := homogeneous _
    rw [top_is _ he]; simp [turn_vol]
  have hv : Fintype.card (Pairs A) ≠ i.card := fun h => hi (eq_univ_of_card i h.symm)
  rw [map_smulₛₗ,map_smul,map_smul,discarded (homogeneous _) hv, discarded (turn_deg (homogeneous _)) hv]; simp

lemma turn_form (M : Matrix A A ℂ) : turn (form M)=form (star M) := by
  unfold form
  simp only [map_sum, map_smulₛₗ, turn_mul, turn_psi, turn_bar,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
  rw [sum_comm]; rfl

lemma adapt_together (S T : Matrix A B ℂ) (V W : Matrix B C ℂ) (x : Dirac A) :
    adapter V W (adapter S T x)=adapter (S*V) (T*W) x := by
  unfold adapter; rw [← AlgHom.comp_apply,← change_mul]; simp [Matrix.fromBlocks_multiply]
@[simp] lemma adapt_one [DecidableEq A] (x : Dirac A) : adapter 1 1 x=x := by simp [adapter,Matrix.fromBlocks_one]

abbrev Twist (S : Matrix A B ℂ) := S.conjTranspose.transpose
lemma turns (S T : Matrix A B ℂ) (x : Dirac A) : turn (adapter S T x)=adapter (Twist T) (Twist S) (turn x) := by
  let F := (turn (A:=B)).comp (adapter S T).toLinearMap
  let G := (adapter (Twist T) (Twist S)).toLinearMap.comp (turn (A:=A))
  suffices F=G by change F x = G x; rw [this]
  apply ext_reversing (by intro x y; simp [F,map_mul,turn_mul]) (by intro x y; simp [G,map_mul,turn_mul]) (by simp [F,G])
  intro i; cases i with
  | inl i => change turn (adapter S T (psi i)) = adapter _ _ (turn (psi i)); simp [adapt_psi,adapt_bar]
  | inr i => change turn (adapter S T (bar i)) = adapter _ _ (turn (bar i)); simp [adapt_bar,adapt_psi]

def tilt (R : Matrix A A ℂ) : Dirac A →ₛₗ[starRingEnd ℂ] Dirac A :=
  (adapter (-R) (-R)ᵀ).toLinearMap.comp turn
lemma tilts (R : Matrix A A ℂ) (x) : tilt R x=adapter (-R) (-R)ᵀ (turn x) := rfl
@[fun_prop] lemma tilt_cont (R : Matrix A A ℂ) : Continuous (tilt R) :=
  (adapter _ _).toLinearMap.continuous_of_finiteDimensional.comp turn_cont
@[simp] lemma tilt_one (R : Matrix A A ℂ) : tilt R 1=1 := by simp [tilts]
lemma tilt_mul (R : Matrix A A ℂ) (x y : Dirac A) : tilt R (x*y)=tilt R y*tilt R x := by simp only [tilts,turn_mul,map_mul]
lemma tilt_exp (R : Matrix A A ℂ) (x) : tilt R (exp x)=exp (tilt R x) := by simp only [tilts,turn_exp,map_weight]
lemma tilt_grade (R : Matrix A A ℂ) (x) : grade (tilt R x)=tilt R (grade x) := by rw [tilts,tilts,adapter,changeVars,exterior_parity,turn_parity]
lemma tilt_form (R : Matrix A A ℂ) (M) : tilt R (form M)=form (R * (star M * R)) := by rw [tilts,turn_form,form_map,Matrix.transpose_transpose, mul_neg,neg_mul_neg]
lemma tilt_psi (R : Matrix A A ℂ) (i) : tilt R (psi i)=∑ j, (-R j i) • bar j := by simp [tilts,adapt_bar]
lemma tilt_bar (R : Matrix A A ℂ) (i) : tilt R (bar i)=∑ j, (-R i j) • psi j := by simp [tilts,adapt_psi]
lemma untilt [DecidableEq A] (R : Matrix A A ℂ) (h : star R=R) (hs : R*R=1) (x) : tilt R (tilt R x)=x := by
  rw [tilts,tilts,turns,turned,adapt_together]
  have hv : Twist (-R) = (-R)ᵀ := by unfold Twist; rw [← Matrix.star_eq_conjTranspose,star_neg,h]
  rw [show Twist (-R)ᵀ = (Twist (-R))ᵀ by rfl,hv,Matrix.transpose_transpose, ← Matrix.transpose_mul, neg_mul_neg,hs,Matrix.transpose_one]; simp
lemma tilt_amp [DecidableEq A] (R : Matrix A A ℂ) (h : R*R=1) (x) : ber A (tilt R x)=star (ber A x) := by
  rw [tilts,volume_map,Matrix.det_transpose,← Matrix.det_mul,neg_mul_neg,h,Matrix.det_one,one_mul,turn_amp]

lemma twist_turn (S : Matrix A B ℂ) : Twist (Twist S) = S := by ext; simp
lemma twist_mul (S : Matrix A B ℂ) (T : Matrix B C ℂ) : Twist (S*T)=Twist S*Twist T := by unfold Twist; rw [Matrix.conjTranspose_mul,Matrix.transpose_mul]

/-- Intertwine symmetry under transform for ψ,bar via S and complex conjugate S respectively. -/
lemma tilt_through (S V : Matrix A B ℂ) (R : Matrix A A ℂ) (H : Matrix B B ℂ)
    (hr : star R=R) (hh : star H=H) (e : R*V=S*H) (x : Dirac A) :
    tilt H (adapter S (Twist S) x)=adapter V (Twist V) (tilt R x) := by
  rw [tilts, tilts, turns, twist_turn,adapt_together,adapt_together]
  have hr' : Twist R=Rᵀ := by unfold Twist; rw [← Matrix.star_eq_conjTranspose,hr]
  have hh' : Twist H=Hᵀ := by unfold Twist; rw [← Matrix.star_eq_conjTranspose,hh]
  have he := congrArg Twist e
  rw [twist_mul, twist_mul,hr',hh'] at he
  simp only [Matrix.transpose_neg,Matrix.neg_mul, Matrix.mul_neg,e,he]
end YM.QCD.Grass
