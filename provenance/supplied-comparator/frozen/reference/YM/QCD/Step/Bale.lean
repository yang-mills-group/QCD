import YM.QCD.Step.Tour

/-! # gauge-covariant coarse Grassmann coordinate map, averaging all axis paths -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Lat Lattice Cost Wilson Function Finset WithLp
open scoped Matrix.Norms.L2Operator Matrix Topology InnerProductSpace
variable {c f : Side} (r : Ratio c f)

abbrev Rail (c f : Side) := Matrix (Row c) (Row f) ℂ

def mouth (i : Row c) : Row f := (r.embed i.1,i.2)
lemma mouth_inj : Injective (mouth r) := fun _ _ h => Prod.ext (r.embed_injective (congrArg Prod.fst h)) (congrArg (fun p : Row f => p.2) h)

def scoop : Rail c f := Matrix.of fun i j => if mouth r i=j then 1 else 0
lemma scoops : scoop r * (scoop r)ᴴ = 1 := by
  ext i j; by_cases hv : i=j
  · subst j; simp [Matrix.mul_apply,scoop]
  have he := (mouth_inj r).ne hv
  simp [Matrix.mul_apply,scoop,apply_ite,hv,he]
lemma shows {A : Type*} (D : Matrix (Row f) A ℂ) (i : Row c) j : (scoop r*D) i j=D (mouth r i) j := by simp [Matrix.mul_apply,scoop,ite_mul]
lemma shown {A : Type*} (D : Matrix A (Row c) ℂ) x y z (h : z=mouth r y) :
    (D*scoop r) x z=D x y := by subst z; simp [Matrix.mul_apply,scoop,mul_ite,(mouth_inj r).eq_iff]
lemma subslice (v : Vec (Row f)) i : lead (scoop r) v i=v (mouth r i) := by change ((scoop r)*ᵥ v.ofLp) i=_; simp [Matrix.mulVec,dotProduct,scoop,ite_mul]
lemma subsec (v : Vec (Row f)) i : fiber (lead (scoop r) v) i=fiber v (r.embed i) := by ext1 j; exact subslice ..
lemma oneNorm {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] : ‖(1:Mx A)‖=1 := by
  rw [Matrix.cstar_norm_def,map_one,norm_one]
lemma price_scoop : ‖scoop r‖=1 := by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self (scoop r)ᴴ
  rw [Matrix.conjTranspose_conjTranspose,scoops, oneNorm, Matrix.l2_opNorm_conjTranspose] at he
  nlinarith [norm_nonneg (scoop r)]

abbrev path (o : Lattice.Order) (j : Site r.count) := route 0 (lift j) o
/-- Per order, per final offset. -/
def stripe (t : Site f) (U : Grid f) (o : Lattice.Order) (j : Site r.count) :=
  scoop r * routeM t U (path r o j)

lemma strip_poly (t : Site f) (U : Grid f) (o) (j : Site r.count) : stripe r t U o j * (stripe r t U o j)ᴴ=1 := by
  rw [stripe,Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (scoop r) (routeM t U (path r o j)) (routeM t U (path r o j))ᴴ]
  rw [show routeM t U (path r o j)*(routeM t U (path r o j))ᴴ = _ from (circle t U (path r o j)).2,Matrix.mul_one,scoops]
lemma sparse (t : Site f) (U : Grid f) (o) (j : Site r.count) i y (h : r.assemble (i.1,j)≠ y.1) :
    stripe r t U o j i y=0 := by
  unfold stripe; rw [shows]; obtain ⟨e,D,hh,he,ht⟩ := travel_data t U (path r o j)
  rw [he,rr, if_neg]
  exact fun hr => h (by rw [← block_stop r i.1 j o,← hh]; exact hr)
lemma apart (t : Site f) (U : Grid f) (o p) (a b : Site r.count) (h : a ≠ b) : stripe r t U o a * (stripe r t U p b)ᴴ = 0 := by
  ext i j; rw [Matrix.mul_apply]; apply sum_eq_zero; intro y _
  by_cases he : r.assemble (i.1,a)=y.1
  · have ht : r.assemble (j.1,b)≠y.1 := fun ht => h (congrArg Prod.snd (r.assemble_bijective.1 (he.trans ht.symm)))
    rw [Matrix.conjTranspose_apply,sparse _ _ _ _ _ _ _ ht,star_zero,mul_zero]
  rw [sparse _ _ _ _ _ _ _ he,zero_mul]
lemma audits (t : Site f) (U : Grid f) (o) (j : Site r.count) (x) (p) :
    ‖fiber (lead (stripe r t U o j) x) p‖ = ‖fiber x (r.assemble (p,j))‖ := by
  unfold stripe; rw [lead_act,subsec]; obtain ⟨e,D,hh,he,ht⟩ := travel_data t U (path r o j)
  rw [he,lead_op, travel_vec,unitary_moves _ (ht _), hh]; rw [block_stop]
lemma concurs (t : Site f) (U : Grid f) (o : Lattice.Order) (x : Vec (Row f)) :
    ∑ j, ‖lead (stripe r t U o j) x‖^2=‖x‖^2 := by
  rw [norms x]
  simp_rw [fun j : Site r.count => norms (lead (stripe r t U o j) x),audits]
  rw [sum_comm, ← Fintype.sum_prod_type fun p : Site c × Site r.count => ‖fiber x (r.assemble p)‖^2]
  exact Equiv.sum_comp r.splitSites.symm (fun p => ‖fiber x p‖^2)

def slope (L : Side) := (Real.sqrt (L.val:ℝ))⁻¹
def scale (L : Side) := slope L/(L.val:ℝ)^2
lemma sidePrice (L : Side) : 0<(L.val:ℝ) := by exact_mod_cast L.property
lemma slope_pos (L : Side) : 0<slope L := inv_pos.mpr (Real.sqrt_pos.mpr (sidePrice _))
lemma scale_pos (L : Side) : 0<scale L := div_pos (slope_pos _) (pow_pos (sidePrice _) _)

def vane (t : Site f) (U : Grid f) (o : Lattice.Order) := (scale r.count:ℂ) • ∑ j, stripe r t U o j
abbrev votes := Fintype.card Lattice.Order
lemma poll_pos : 0<(votes:ℝ) := by exact_mod_cast Fintype.card_pos

def Q (t : Site f) (U : Grid f) := (votes:ℂ)⁻¹ • ∑ o, vane r t U o

lemma Gram (t : Site f) (U : Grid f) (o) : vane r t U o*(vane r t U o)ᴴ=((slope r.count)^2:ℝ) • (1:Mx (Row c)) := by -- no norm space real? matrix over complex
  unfold vane
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul]
  simp only [Matrix.conjTranspose_sum,Complex.star_def,Complex.conj_ofReal,Matrix.sum_mul,Matrix.mul_sum,smul_smul]
  have he (i : Site r.count) : ∑ j, stripe r t U o i * (stripe r t U o j)ᴴ=1 := by
    rw [sum_eq_single i (fun j _ h=> apart r t U o o i j h.symm) (by simp), strip_poly]
  rw [sum_comm]
  simp_rw [he]; rw [sum_const, card_univ,site_card, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hs : ((r.count.val:ℝ):ℂ)≠0 := by exact_mod_cast r.count.property.ne'
  simp only [scale,Nat.cast_pow, Complex.ofReal_div,Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [show (slope r.count:ℝ)^2 • (1:Mx (Row c)) = (↑(slope r.count^2):ℂ) • (1:Mx (Row c)) from by ext; simp] -- check
  congr 1; push_cast; field_simp
lemma vane_cost (t : Site f) (U : Grid f) (o) : ‖vane r t U o‖=slope r.count := by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self (vane r t U o)ᴴ
  rw [Matrix.conjTranspose_conjTranspose,Gram] at he
  rw [← sq_eq_sq₀ (by positivity) (slope_pos _).le];
  -- real smul norm use equality
  rw [show slope r.count^2 • (1:Mx (Row c)) = (↑(slope r.count^2):ℂ) • (1:Mx (Row c)) from by ext; simp, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), oneNorm, mul_one, Matrix.l2_opNorm_conjTranspose, ← sq] at he
  exact he.symm
lemma votes_cost (t : Site f) (U : Grid f) : ‖Q r t U‖ ≤ slope r.count := by
  rw [Q,norm_smul,norm_inv,Complex.norm_natCast]
  have he := norm_sum_le univ (vane r t U)
  simp_rw [vane_cost,sum_const,card_univ] at he
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ poll_pos.ne',one_mul]

@[fun_prop] lemma continuous_Q (t : Site f) : Continuous (Q r t) := by unfold Q vane stripe; fun_prop
end YM.QCD.Kit
