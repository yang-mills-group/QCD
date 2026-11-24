import YM.QCD.Grass.Schur
import YM.QCD.Step.High
import YM.QCD.Grass.Time

/-! # Exact normalized Grass blocking at any stencil and arbitrary insertions -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Grass Lat Wilson Finset
open scoped Matrix Matrix.Norms.L2Operator Topology
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def joinD (b : ℝ) (Q : Matrix B A ℂ) (D : Matrix A A ℂ) := Matrix.fromBlocks
  (D+(b:ℂ) • (Qᴴ*Q)) ((-b:ℂ) • Qᴴ) ((-b:ℂ) • Q) ((b:ℂ) • 1)

/-- shearing the far variables, to produce kernel -/
def skin (Q : Matrix B A ℂ) : Dirac (A ⊕ B) →ₐ[ℂ] Dirac (A ⊕ B) := adapter (Matrix.fromBlocks 1 0 (-Q) 1)
  (Matrix.fromBlocks 1 0 (-Qᴴ)ᵀ 1)
lemma skin_act (Q : Matrix B A ℂ) (x : Grass.Dirac A) : skin Q (near A B x)=near A B x := by
  refine AlgHom.congr_fun (φ₁:=(skin Q).comp (near A B)) (ext_atoms fun i => ?_) x
  cases i with
  | inl i =>
    change adapter _ _ (pass _ (psi i)) = pass _ (psi i)
    rw [pass_psi,adapt_psi]; simp [Fintype.sum_sum_type, Matrix.one_apply,ite_smul]
  | inr i =>
    change adapter _ _ (pass _ (bar i)) = pass _ (bar i)
    rw [pass_bar,adapt_bar]; simp [Fintype.sum_sum_type, Matrix.one_apply,ite_smul]
lemma skin_volume (Q : Matrix B A ℂ) (x) : ber _ (skin Q x)=ber _ x := by
  rw [skin,volume_map,Matrix.det_fromBlocks_zero₁₂,Matrix.det_fromBlocks_zero₁₂]; simp
lemma generate (b : ℝ) (Q : Matrix B A ℂ) (D : Matrix A A ℂ) :
    gauss (joinD b Q D)=skin Q (near A B (gauss D)*far A B (gauss ((b:ℂ) • 1))) := by
  rw [← gauss_blocks,skin,gauss_map]; congr 1
  simp [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,joinD,add_comm]

def sheath (b : ℝ) (Q : Matrix B A ℂ) (x : Grass.Dirac A) :=
  (b:ℂ)⁻¹ ^ Fintype.card B • marginal A B (near A B x * gauss (joinD b Q 0))

lemma form_near_zero (x : Matrix A A ℂ) : near A B (gauss x)=gauss (Matrix.fromBlocks x 0 0 0) := by
  rw [gauss_blocks]; simp [gauss, Grass.form]
lemma clothe (b : ℝ) (Q : Matrix B A ℂ) (D : Matrix A A ℂ) (x) : sheath b Q (gauss D * x) =
    (b:ℂ)⁻¹ ^ Fintype.card B • marginal A B (gauss (joinD b Q D) * near A B x) := by
  rw [sheath,map_mul (near A B), mul_assoc, (gauss_plus _).central (near _ _ x), ← mul_assoc, form_near_zero,← gauss_add]
  simp [joinD,Matrix.fromBlocks_add]

lemma insulate {b : ℝ} (hb : b≠0) (Q : Matrix B A ℂ) (x) : ber _ (sheath b Q x)=ber _ x := by
  rw [sheath,map_smul,marginal_full,generate]
  have hu : (gauss 0 : Grass.Dirac A)=1 := by simp [gauss,Grass.form]
  rw [hu,map_one,one_mul, ← skin_act Q x,← map_mul,skin_volume,split,det_amplitude,Matrix.det_smul,Matrix.det_one,mul_one]
  rw [smul_eq_mul,mul_left_comm,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hb)),mul_one]

@[fun_prop] lemma sheath_cont {b : ℝ} : Continuous fun (x : Matrix B A ℂ × Grass.Dirac A) => sheath b x.1 x.2 := by
  have hn : Continuous (near A B) := (near A B).toLinearMap.continuous_of_finiteDimensional
  unfold sheath joinD; fun_prop

def disguise (U : Matrix A A ℂ) := adapter U (star U)ᵀ
abbrev whole (R : Matrix A A ℂ) (W : Matrix B B ℂ) := Matrix.fromBlocks R 0 0 W
lemma whole_star (R : Matrix A A ℂ) (W : Matrix B B ℂ) : star (whole R W)=whole (star R) (star W) := by
  simp only [whole, Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]
lemma whole_u (R : Matrix A A ℂ) (W : Matrix B B ℂ) (h : R∈unitary _) (H : W∈unitary _) : whole R W∈unitary _ := by
  constructor
  · rw [whole_star]; simp [whole,Matrix.fromBlocks_multiply,h.1,H.1,Matrix.fromBlocks_one]
  rw [whole_star]; simp [whole,Matrix.fromBlocks_multiply,h.2,H.2,Matrix.fromBlocks_one]
lemma rotate_join (R : Matrix A A ℂ) (W : Matrix B B ℂ) (h : R∈unitary _) (H : W∈unitary _) (D : Matrix A A ℂ) (Q : Matrix B A ℂ) (b : ℝ) :
    joinD b (W * Q*star R) (R*D*star R)=whole R W * joinD b Q D * star (whole R W) := by
  rw [whole_star]
  simp only [whole,joinD,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,
    Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose (star R),star_star,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,H.2, ← Matrix.star_eq_conjTranspose W]
  simp only [Matrix.mul_assoc] -- check
  rw [← Matrix.mul_assoc (star _) W, H.1,Matrix.one_mul]; simp
lemma disguise_mul (R S : Matrix A A ℂ) (x) : disguise R (disguise S x) = disguise (S*R) x := by
  unfold disguise; rw [adapt_together, star_mul, Matrix.transpose_mul]
lemma discard {R : Matrix A A ℂ} (h : R∈unitary _) (x) : disguise R (disguise (star R) x) = x := by rw [disguise_mul,h.1,disguise]; simp
lemma vanishV {R : Matrix A A ℂ} (h : R∈unitary _) (x) : ber _ (disguise R x)=ber _ x := by
  rw [disguise,volume_map,Matrix.det_transpose,← Matrix.det_mul,h.2,Matrix.det_one,one_mul]
lemma disguised {R : Matrix A A ℂ} (h : R∈unitary _) (M : Matrix A A ℂ) : disguise R (gauss (R*M*star R))=gauss M := by
  rw [disguise,gauss_map,Matrix.transpose_transpose,mul_assoc (R*M),h.1,mul_one, ← mul_assoc,h.1,one_mul]
lemma partitioned (U : Matrix A A ℂ) (W : Matrix B B ℂ) (x) : disguise (whole U W) (near A B x)=near A B (disguise U x) := by
  refine AlgHom.congr_fun (φ₁:=(disguise (whole U W)).comp (near A B)) (φ₂:=(near A B).comp (disguise U)) (ext_atoms fun i => ?_) x
  unfold disguise; cases i with
  | inl i => change adapter _ _ (pass _ (psi i))=pass _ (adapter _ _ (psi i)); rw [pass_psi,adapt_psi,adapt_psi]; simp [Fintype.sum_sum_type,whole]
  | inr i => change adapter _ _ (pass _ (bar i))=pass _ (adapter _ _ (bar i)); rw [pass_bar,adapt_bar,adapt_bar,whole_star]; simp [Fintype.sum_sum_type,whole]
lemma partitioned' (U : Matrix A A ℂ) (W : Matrix B B ℂ) (x) : disguise (whole U W) (far A B x)=far A B (disguise W x) := by
  refine AlgHom.congr_fun (φ₁:=(disguise (whole U W)).comp (far A B)) (φ₂:=(far A B).comp (disguise W)) (ext_atoms fun i => ?_) x
  unfold disguise; cases i with
  | inl i => change adapter _ _ (pass _ (psi i))=pass _ (adapter _ _ (psi i)); rw [pass_psi,adapt_psi,adapt_psi]; simp [Fintype.sum_sum_type,whole]
  | inr i => change adapter _ _ (pass _ (bar i))=pass _ (adapter _ _ (bar i)); rw [pass_bar,adapt_bar,adapt_bar,whole_star]; simp [Fintype.sum_sum_type,whole]
lemma rotated_marginal {R : Matrix A A ℂ} {W : Matrix B B ℂ} (h : R∈unitary _) (H : W∈unitary _) (x) :
    disguise W (marginal A B x)=marginal A B (disguise (whole R W) x) := by
  apply (perfect B).injective; apply LinearMap.ext; intro y
  rw [← discard H y,perfect_apply,perfect_apply,← map_mul,vanishV H,marginal_test,marginal_test,
    ← partitioned' R W (disguise (star W) y),← map_mul,vanishV (whole_u R W h H)]
lemma compat {R : Matrix A A ℂ} {W : Matrix B B ℂ} (h : R∈unitary _) (H : W∈unitary _) (b : ℝ) (Q : Matrix B A ℂ) (x) :
    disguise W (sheath b (W*Q*star R) x)=sheath b Q (disguise R x) := by
  have hh := rotate_join R W h H 0 Q b
  rw [Matrix.mul_zero, Matrix.zero_mul] at hh
  rw [sheath,map_smul, rotated_marginal h H, map_mul,partitioned,hh,disguised (whole_u R W h H)]
  rfl
end YM.QCD.Kit
