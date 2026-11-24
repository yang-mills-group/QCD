import YM.QCD.Grass.Super

/-! # Generator substitutions, top determinant and embeddings -/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass
open Function Module Finset
open scoped BigOperators Topology

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

abbrev exterior (f : Seed A →ₗ[ℂ] Seed B) := ExteriorAlgebra.map f

omit [Fintype A] [Fintype B] in
lemma exterior_layer (f : Seed A →ₗ[ℂ] Seed B) {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) :
    exterior f x ∈ layer B n := by
  have H := Submodule.mem_map_of_mem (f := (exterior f).toLinearMap) hx
  unfold layer ExteriorAlgebra.exteriorPower at *
  rw [Submodule.map_pow] at H
  apply SetLike.le_def.mp _ H
  refine pow_le_pow_left' ?_ n
  rintro y ⟨x, ⟨z,rfl⟩,rfl⟩
  exact ⟨f z, (ExteriorAlgebra.map_apply_ι f z).symm⟩

lemma exterior_parity (f : Seed A →ₗ[ℂ] Seed B) (x : Alg A) :
    grade (exterior f x) = exterior f (grade x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp
  | ι v => simp
  | add x y hx hy => simp [hx,hy]
  | mul x y hx hy => simp [hx,hy]

/-- top form in any order -/
private lemma crown :
    ∃ b : Basis (Fin (Fintype.card A)) ℂ (Seed A), mono univ = ExteriorAlgebra.ιMulti ℂ _ b := by
  obtain ⟨f,hf,h,e⟩ := expression (univ : Finset A)
  let g : Fin (Fintype.card A) ≃ A := Equiv.ofBijective f ⟨hf, fun i => (h i).mp (mem_univ i)⟩
  refine ⟨(thetaBasis A).reindex g.symm, ?_⟩
  rw [e,ExteriorAlgebra.ιMulti_apply]
  have hp : (fun i => ExteriorAlgebra.ι ℂ (((thetaBasis A).reindex g.symm) i)) = atom ∘ f := by
    ext1 i
    rw [Basis.reindex_apply]; rfl
  rw [hp]; rfl

lemma jacobian (f : Seed A →ₗ[ℂ] Seed A) :
    coef univ (exterior f (mono univ)) = LinearMap.det f := by
  classical
  obtain ⟨b,h⟩ := crown (A:=A)
  rw [h, ExteriorAlgebra.map_apply_ιMulti]
  let φ := (coef (univ : Finset A)).compAlternatingMap (ExteriorAlgebra.ιMulti ℂ (Fintype.card A))
  have hz : φ b = 1 := by change coef univ (ExteriorAlgebra.ιMulti ℂ _ (⇑b)) = _; rw [← h]; exact read _
  change φ (⇑f ∘ ⇑b) = _
  rw [AlternatingMap.eq_smul_basis_det b φ,hz,one_smul,Basis.det_comp, Basis.det_self,mul_one]

lemma coef_top_change (f : Seed A →ₗ[ℂ] Seed A) (x : Alg A) :
    coef univ (exterior f x) = LinearMap.det f * coef univ x := by
  classical
  conv_lhs => rw [← write x]; simp only [map_sum,map_smul]
  rw [sum_eq_single univ]
  · rw [jacobian,smul_eq_mul,mul_comm]
  · intro t _ ht
    rw [spectrum (exterior_layer f (homogeneous t)) _ (fun e => ht (eq_univ_of_card t e.symm)), smul_zero]
  simp

/-- Row convention. The image of generator `i` is `∑_j M i j atom j`. -/
def substitution (M : Matrix A B ℂ) : Seed A →ₗ[ℂ] Seed B :=
  (thetaBasis A).constr ℂ fun i => M i

def changeVars (M : Matrix A B ℂ) : Alg A →ₐ[ℂ] Alg B := exterior (substitution M)

lemma change_atom (M : Matrix A B ℂ) (i : A) : changeVars M (atom i) = ∑ j, M i j • atom j := by
  rw [changeVars,atom, ExteriorAlgebra.map_apply_ι]
  rw [substitution, Basis.constr_basis]
  exact line_atoms _

lemma changes [DecidableEq A] (M : Matrix A A ℂ) : LinearMap.det (substitution M) = M.det := by
  rw [← LinearMap.det_toMatrix (thetaBasis A)]
  have he : LinearMap.toMatrix (thetaBasis A) (thetaBasis A) (substitution M) = M.transpose := by
    ext i j; rw [LinearMap.toMatrix_apply]
    simp [thetaBasis, substitution]
  rw [he, Matrix.det_transpose]

lemma top_change [DecidableEq A] (M : Matrix A A ℂ) (x : Alg A) :
    coef univ (changeVars M x) = M.det * coef univ x := by rw [changeVars,coef_top_change,changes]

lemma change_mul (M : Matrix A B ℂ) (N : Matrix B C ℂ) :
    changeVars (M*N) = (changeVars N).comp (changeVars M) := by
  apply ext_atoms; intro i
  rw [change_atom,AlgHom.comp_apply,change_atom,map_sum]
  simp_rw [Matrix.mul_apply,sum_smul,map_smul,change_atom,smul_sum,mul_smul]; rw [sum_comm]

@[simp] lemma change_one [DecidableEq A] : changeVars (1:Matrix A A ℂ) = AlgHom.id ℂ _ := by
  apply ext_atoms; intro i; rw [change_atom]; simp [Matrix.one_apply,ite_smul]

lemma linear_power {n : ℕ} (f : Fin n → A) : (List.ofFn (atom ∘ f)).prod ∈ layer A n :=
  ExteriorAlgebra.ιMulti_range ℂ n ⟨thetaBasis A ∘ f, rfl⟩

/-- Move generators (permutations are frequent). -/
def rename (f : A → B) : Seed A →ₗ[ℂ] Seed B :=
  (thetaBasis A).constr ℂ fun i => thetaBasis B (f i)

def embed (f : A → B) : Alg A →ₐ[ℂ] Alg B := exterior (rename f)

@[simp] lemma embed_atom (f : A → B) (i : A) : embed f (atom i) = atom (f i) := by rw [embed,atom,ExteriorAlgebra.map_apply_ι,rename,Basis.constr_basis]; rfl
@[simp] lemma embed_id : embed (@id A) = AlgHom.id ℂ _ := ext_atoms (fun i => by simp)

lemma embed_comp (f : A → B) (g : B → C) (x : Alg A) : embed g (embed f x) = embed (g ∘ f) x :=
  AlgHom.congr_fun (φ₁ := (embed g).comp (embed f)) (ext_atoms fun i => by simp) x

/-- Any ordering of distinct generators for its subset differs only by sign. -/
lemma sign_product (l : List A) (h : l.Nodup) [DecidableEq A] :
    (l.map atom).prod = mono l.toFinset ∨ (l.map atom).prod = -mono l.toFinset := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨h,hl⟩ := List.nodup_cons.mp h
    have H : Disjoint {i} l.toFinset := by simp [h]
    have he := mono_mul_sign _ _ H
    simp_rw [mono_single i, Finset.disjUnion_eq_union, singleton_union] at he
    rcases ih hl with hx|hx <;> rcases he with he|he <;> simp [hx,he]

lemma embed_blade (f : A ↪ B) (s : Finset A) :
    embed f (mono s)=mono (s.map f) ∨ embed f (mono s)=- mono (s.map f) := by
  classical
  obtain ⟨w,hw,h,e⟩ := expression s
  let L := List.ofFn (f ∘ w)
  have hp : embed f (mono s)=(L.map atom).prod := by
    rw [e, map_list_prod]; simp [L, Function.comp_def]
  rw [hp]
  have ht : s.map f = L.toFinset := by ext i; simp [L,h]
  rw [ht]; exact sign_product _ (List.nodup_ofFn_ofInjective (f.injective.comp hw))

lemma norm_embed_le (f : A ↪ B) (x : Alg A) : ‖embed f x‖ ≤ ‖x‖ := by
  conv_lhs => rw [← write x, map_sum]
  refine (norm_sum_le _ _).trans ?_; rw [norm_def x]; apply sum_le_sum
  intro i _; rw [map_smul,norm_smul]; rcases embed_blade f i with h | h <;> rw [h] <;> simp

lemma embed_layer (f : A → B) {x : Alg A} {n : ℕ} (hx : x ∈ layer A n) : embed f x ∈ layer B n := exterior_layer _ hx

lemma continuous_embed (f : A → B) : Continuous (embed f) :=
  (embed f).toLinearMap.continuous_of_finiteDimensional

lemma embed_grade (f : A → B) (x : Alg A) : grade (embed f x) = embed f (grade x) := exterior_parity _ x

end YM.QCD.Grass
