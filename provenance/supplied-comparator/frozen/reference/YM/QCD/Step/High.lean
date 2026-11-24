import YM.QCD.Step.Rooted

/-! # remaining kinetic high/low kernels in background, covariance -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kit
open Lat Lattice Cost Wilson Function Finset WithLp
open scoped Matrix.Norms.L2Operator Matrix Topology InnerProductSpace
variable {c f : Side} (r : Ratio c f) {b m : ℝ}

def InPlay (b m : ℝ) := 0 < b ∧ 0 < m + fraction b r.count
variable (hp : InPlay r b m)

lemma roots (F : Site f→Bundle) : scoop r*rides (Equiv.refl _) F=rides (Equiv.refl _) (fun i => F (r.embed i))*scoop r := by
  ext i j
  by_cases he : r.embed i.1=j.1
  · rw [shows, shown r (rides (Equiv.refl _) (fun i => F (r.embed i))) i (i.1,j.2) j (Prod.ext he.symm rfl)]
    simp [rides,mouth,he]
  rw [shows,rr,mouth,Equiv.refl_apply, if_neg (by exact he), Matrix.mul_apply]
  symm; apply sum_eq_zero; intro k _; unfold scoop; rw [rr];
  split
  next h =>
    rw [Matrix.of_apply,if_neg, mul_zero]
    exact fun e => he (congrArg r.embed h |>.trans (congrArg (·.1) e)) -- check
  simp

lemma gaugeQ (t : Site f) (U : Grid f) (k : Frame f) :
    Q r t (gauge k U)= siteRot (k ∘ r.embed)*Q r t U*star (siteRot k) := by
  have he : scoop r * siteRot k = siteRot (k∘r.embed)*scoop r := roots r _
  unfold Q vane stripe; simp_rw [gaugeM,Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_sum,Matrix.sum_mul]
  have h (X : Sheet f) : scoop r*(siteRot k*X*star (siteRot k))= siteRot (k ∘ r.embed)*(scoop r*X)*star (siteRot k) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,he,Matrix.mul_assoc (siteRot (k ∘ r.embed)) (scoop r) X]
  simp_rw [h]; simp only [Matrix.mul_smul,Matrix.mul_sum,Matrix.smul_mul,Matrix.sum_mul]
lemma gaugeH (t : Site f) (U : Grid f) (k : Frame f) : hefty r b t (gauge k U) m = siteRot k*hefty r b t U m*star (siteRot k) := by
  unfold hefty; rw [bareD_covariant,gaugeQ]
  simp only [mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul]; congr 2
  simp only [Matrix.conjTranspose_mul]
  let T := siteRot k
  let S := siteRot (k∘r.embed)
  let A := Q r t U
  change star (star T)*(Aᴴ * star S)*(S*A*star T) = T*(Aᴴ*A)*star T
  rw [star_star]; dsimp only [T,S]; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star _) (siteRot _), (siteRot_u _).1,Matrix.one_mul]

lemma spinQ (t : Site f) (U : Grid f) (X : Spike) : Q r t U*onSpin f X=onSpin c X*Q r t U := by
  have he : scoop r*onSpin f X=onSpin c X*scoop r := roots r _
  unfold Q vane stripe; simp only [Matrix.smul_mul, Matrix.mul_smul,Matrix.sum_mul,Matrix.mul_sum]
  have h (w) : scoop r*routeM t U w*onSpin f X = onSpin c X*(scoop r*routeM t U w) := by rw [Matrix.mul_assoc,(spinM ..).eq, ← Matrix.mul_assoc, he,Matrix.mul_assoc]
  simp_rw [h]
lemma chiQ (t : Site f) (U : Grid f) : Q r t U * chirality f=chirality c * Q r t U := spinQ ..
lemma chi_back (t : Site f) (U : Grid f) : (Q r t U)ᴴ * chirality c=chirality f*(Q r t U)ᴴ := by
  have he := congrArg (·ᴴ) (chiQ r t U); simpa only [Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose, chi_star] using he.symm
lemma gammaH (t : Site f) (U : Grid f) : star (hefty r b t U m)=chirality f * hefty r b t U m *chirality f := by
  unfold hefty; rw [star_add,gamma5,star_smul, Matrix.star_eq_conjTranspose ( (Q r t U)ᴴ * Q r t U), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [show star (b:ℂ)=(b:ℂ) by simp]
  simp only [mul_add,add_mul, Matrix.mul_smul,Matrix.smul_mul]; congr 2
  rw [← Matrix.mul_assoc (chirality f),← chi_back,Matrix.mul_assoc _ (Q r t U) (chirality f),chiQ,Matrix.mul_assoc,← Matrix.mul_assoc (chirality c), chi_sq, Matrix.one_mul]

include hp in
lemma invertH (t : Site f) (U : Grid f) : IsUnit (hefty r b t U m).det := (cushions r hp.1 t U m).unit hp.2
include hp in
lemma priceH (t : Site f) (U : Grid f) : ‖(hefty r b t U m)⁻¹‖ ≤ (m+fraction b r.count)⁻¹ := (cushions r hp.1 t U m).reciprocal hp.2
include hp in
lemma positiveH (t : Site f) (U : Grid f) : 0 < (hefty r b t U m).det.re := det_pos chi_sq (gammaH ..) hp.2 (cushions r hp.1 t U m)
include hp in
lemma chi_cov (t : Site f) (U : Grid f) : chirality f * (hefty r b t U m)⁻¹ = star (hefty r b t U m)⁻¹ * chirality f := by
  let J:=chirality f; let H := hefty r b t U m
  have hj : J*J=1 := chi_sq
  have he := invertH r hp t U
  have hy : (star H)*(star (H⁻¹))=1 := by rw [← star_mul,Matrix.nonsing_inv_mul _ he,star_one]
  change J*H⁻¹=star (H⁻¹)*J
  have hh : (star (H⁻¹))*(star H)=1 := mul_eq_one_comm.mp hy
  calc
    J*H⁻¹= (star (H⁻¹)*star H)*J*H⁻¹ := by rw [hh,one_mul]
    _ = _ := by rw [mul_assoc (star (H⁻¹)),show star H=_ from gammaH r t U,mul_assoc (J*H) J J,hj,mul_one,mul_assoc,mul_assoc,Matrix.mul_nonsing_inv _ he,mul_one]

def target (b m : ℝ) (t : Site f) (U : Grid f) := (b:ℂ) • (1:Sheet c) - (b:ℂ)^2 • (Q r t U*(hefty r b t U m)⁻¹*(Q r t U)ᴴ)
include hp
lemma symH (t : Site f) (U : Grid f) (k : Frame f) : (hefty r b t (gauge k U) m)⁻¹ = siteRot k*(hefty r b t U m)⁻¹*star (siteRot k) := by
  rw [gaugeH]; apply Matrix.inv_eq_right_inv
  let R:=siteRot k; let A:= hefty r b t U m
  change R*A*star R*(R*A⁻¹*star R)=1
  rw [← mul_assoc,← mul_assoc _ R A⁻¹, mul_assoc _ (star R) R,(siteRot_u k).1,mul_one, mul_assoc R A A⁻¹,Matrix.mul_nonsing_inv _ (invertH r hp ..),mul_one]
  exact (siteRot_u k).2

lemma gaugeTarget (t : Site f) (U : Grid f) (k : Frame f) : target r b m t (gauge k U) = siteRot (k∘r.embed)*target r b m t U*star (siteRot (k∘r.embed)) := by
  unfold target; rw [gaugeQ,symH _ hp]; simp only [mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul, mul_one,(siteRot_u _).2, Matrix.conjTranspose_mul]
  congr 2
  let R:=siteRot k; let L:=siteRot (k∘r.embed); let Z:=Q r t U; let A:=(hefty r b t U m)⁻¹
  change L*Z*star R*(R*A*star R)*(star (star R)*(Zᴴ*star L))=_
  rw [star_star]; dsimp only [R,L,A,Z]
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star _) (siteRot k), (siteRot_u k).1,Matrix.one_mul, ← Matrix.mul_assoc (star _) (siteRot k), (siteRot_u k).1,Matrix.one_mul]

lemma chirally (t : Site f) (U : Grid f) : star (target r b m t U)=chirality c * target r b m t U *chirality c := by
  unfold target
  simp only [star_sub,star_smul, star_one,Complex.star_def,Complex.conj_ofReal,map_pow,mul_sub,sub_mul,Matrix.mul_smul, Matrix.smul_mul,mul_one,chi_sq]
  congr 2
  let Z:=Q r t U; let A:=(hefty r b t U m)⁻¹
  change (Z*A*Zᴴ)ᴴ = chirality c*(Z*A*Zᴴ)*chirality c
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have ht : Aᴴ= chirality f*A*chirality f := by rw [chi_cov r hp,Matrix.mul_assoc, chi_sq,Matrix.mul_one]; rfl
  dsimp only [Z]; rw [ht]; simp only [Matrix.mul_assoc]; rw [chi_back,← Matrix.mul_assoc (chirality c),← chiQ,Matrix.mul_assoc]

lemma target_bound (t : Site f) (U : Grid f) : ‖target r b m t U‖ ≤ b + b^2*(slope r.count*(m+fraction b r.count)⁻¹*slope r.count) := by
  have hb := hp.1
  unfold target; apply (norm_sub_le ..).trans
  rw [norm_smul,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hb.le,oneNorm,mul_one]
  refine add_le_add_right (mul_le_mul_of_nonneg_left ((Matrix.l2_opNorm_mul (Q r t U * (hefty r b t U m)⁻¹) (Q r t U)ᴴ).trans ?_) (sq_nonneg b)) _
  rw [Matrix.l2_opNorm_conjTranspose]
  exact mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (votes_cost ..) (priceH _ hp ..) (norm_nonneg _) (slope_pos _).le)) (votes_cost ..) (norm_nonneg _) (mul_nonneg (slope_pos _).le (inv_pos.mpr hp.2).le)
end YM.QCD.Kit
