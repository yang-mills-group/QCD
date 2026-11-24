import YM.QCD.Free.Symbol
import YM.CellFourier.Mesh

/-! # exact matching of free symbol to torus regulator, antiperiodic all four axes -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Free
open Lattice Lat Finset Function
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker
variable {n : Side}

/-- physical momenta on unit four torus, real -/
def fixed (p : Cover) : Freq := fun a => (2*(p a:ℝ)-1)*Real.pi
def spacer (n : Side) := (n.val:ℝ)⁻¹
lemma fine (n) : 0<spacer n := inv_pos.mpr (Bloch.side_pos _)

def menu (p : Site n) : Freq := spacer n • fixed (lift p)
lemma carded (p : Site n) : Boxed (menu p) := by
  intro a
  rw [abs_le]
  have he := lift_centers p a
  have ht : -(n.val:ℤ) ≤ 2*lift p a-1 := by omega
  have hu : 2*lift p a-1 ≤ n.val := by omega
  have he : -(n.val:ℝ) ≤ 2*(lift p a:ℝ)-1 := by exact_mod_cast ht
  have hf : 2*(lift p a:ℝ)-1 ≤ (n.val:ℝ) := by exact_mod_cast hu
  change _ ≤ spacer n * _ ∧ spacer n * _ ≤ _
  rw [spacer,mul_comm ((n.val : ℝ)⁻¹), ← div_eq_mul_inv, le_div_iff₀ (Bloch.side_pos _),div_le_iff₀ (Bloch.side_pos _)]
  dsimp only [fixed]; constructor
  · nlinarith [Real.pi_pos]
  nlinarith [Real.pi_pos]
lemma fixed_lower (p : Cover) (i : Axis) : Real.pi ≤ |fixed p i| := by
  rw [fixed,abs_mul,abs_of_pos Real.pi_pos]
  apply le_mul_of_one_le_left Real.pi_pos.le
  have hp : (p i:ℤ) ≤ 0 ∨ 1 ≤ p i := by omega
  rcases hp with hp|hp
  · have he : (p i:ℝ) ≤ 0 := by exact_mod_cast hp
    exact (show (1:ℝ)≤ -(2*↑(p i)-1) by linarith).trans (neg_le_abs _)
  have he : (1:ℝ) ≤ p i := by exact_mod_cast hp
  exact (show (1:ℝ)≤ 2*↑(p i)-1 by linarith).trans (le_abs_self _)
lemma away (p : Site n) {m : ℝ} (hm : 0 ≤ m) : 2*spacer n ≤ Real.sqrt (square (menu p) m) := by
  have he : spacer n * Real.pi ≤ |menu p 0| := by
    change _ ≤ |spacer n*fixed (lift p) 0|; rw [abs_mul,abs_of_pos (fine _)]; exact mul_le_mul_of_nonneg_left (fixed_lower ..) (fine _).le
  have ht : (spacer n * Real.pi)^2 ≤ lensq (menu p) := (pow_le_pow_left₀ (mul_nonneg (fine _).le Real.pi_pos.le) he 2).trans (by
    rw [sq_abs]; exact single_le_sum (f:=fun a=> ((menu p) a)^2) (fun i _ => sq_nonneg _) (mem_univ (0:Axis)))
  have hf := le_add_of_nonneg_left (a:=4/Real.pi^2 * lensq (menu p)) (sq_nonneg m)
  have hu := ((mul_le_mul_of_nonneg_left ht (show 0≤4/Real.pi^2 by positivity)).trans hf).trans (wilsonLower' _ (carded p) hm)
  rw [← sq_le_sq₀ (mul_nonneg (by norm_num) (fine _).le) (Real.sqrt_nonneg _),Real.sq_sqrt (sq_pos ..)]
  convert hu using 1; field_simp
  ring
lemma menu_pos (p : Site n) {m : ℝ} (hm : 0 ≤ m) : 0 < square (menu p) m := Real.sqrt_pos.mp ((mul_pos (by norm_num) (fine n)).trans_le (away p hm))

/-- twist scalar, choose minus-half-mode shift to handle tie convention. -/
def wind (x : Site n) := cis (-Real.pi * (∑ a, ((x a).val:ℝ))/n.val)
lemma valuated (x : Per n) : (x+1).val=(x.val+1)%n.val := by
  have e : (((x.val+1:ℕ):ℕ):Per n)=x+1 := by simp
  rw [← e,ZMod.val_natCast]
lemma wind_step (x : Site n) (i : Axis) :
    seam 0 x i * wind (x+step i)=wind x*cis (-Real.pi/n.val) := by
  have h (y : Site n) : (∑ a, ((y a : Per n).val:ℝ))= (∑ a∈(univ.erase i), ((y a).val:ℝ))+((y i).val:ℝ) := (sum_erase_add univ _ (mem_univ _)).symm -- check parentheses
  have ht : (∑ a∈(univ.erase i), ((((x+step i : Site n) a).val):ℝ)) = ∑ a∈(univ.erase i), ((x a).val:ℝ) := sum_congr rfl fun j hj => by simp [(mem_erase.mp hj).1]
  unfold seam wind
  simp only [Pi.zero_apply]; rw [← cis_add]; rw [show ∑ a, ((((x+step i : Site n) a).val):ℝ) = _ from h (x+step i), ht, h x, Pi.add_apply,step_apply,if_pos rfl];
  split
  next he =>
    have hv := valuated (x i)
    rw [he,ZMod.val_zero] at hv
    have hw : (x i).val+1=n.val := by
      have hh := ZMod.val_lt (x i)
      by_contra! hh'
      rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hh : ((x i).val:ℝ)+1=n.val := by exact_mod_cast hw
    rw [he,ZMod.val_zero,Nat.cast_zero,add_zero]
    have hp : cis (-Real.pi) = -1 := by simp only [cis_trig, Real.cos_neg,Real.sin_neg, Real.cos_pi,Real.sin_pi]; simp
    rw [← hp,← cis_add]; congr 1
    have hs : (n.val:ℝ)≠0 := (Bloch.side_pos _).ne'
    field_simp; nlinarith
  next he =>
    have hv : (x i).val+1<n.val := by
      have ht := ZMod.val_lt (x i)
      by_contra! hh
      have hw : (x i).val+1=n.val := by omega
      apply he
      have h := congrArg ((↑) : ℕ→Per n) hw
      simpa using h
    rw [one_mul]; congr 1
    rw [valuated,Nat.mod_eq_of_lt hv]; push_cast; ring

/-- Counting unitary matrix from antiperiodic modes. -/
def scarf (p x : Site n) : ℂ := (n.val:ℂ)⁻¹ ^ 2 * wind x*Bloch.cell p x

def plain (n : Side) : Matrix (Site n) (Site n) ℂ := Matrix.of (fun i j => scarf j i)
lemma plain_u (n : Side) : plain n ∈ unitary _ := by
  have hh : star (plain n) * plain n=1 := by
    ext i j
    rw [Matrix.mul_apply];
    have h (x : Site n) : star (plain n) i x * plain n x j = (n.val:ℂ)⁻¹ ^4 * (Bloch.cell j x*(Bloch.cell i x)⁻¹) := by
      have ht : star (wind x)*wind x=1 := by rw [wind,star_cis,← cis_add]; simp [cis]
      change star (scarf i x)*scarf j x=_
      simp only [scarf,star_mul,star_pow]
      rw [show star ((n.val:ℂ)⁻¹)=_ from map_inv₀ (starRingEnd ℂ) (n.val:ℂ),map_natCast, show star (Bloch.cell i x)=_ from Bloch.cell_bar ..]; grind
    simp_rw [h]; rw [← mul_sum,Bloch.orthogonal]
    by_cases hv : i=j
    · subst j; simp
    simp [hv,Ne.symm hv]
  exact ⟨hh,mul_eq_one_comm.mp hh⟩
  -- fix

def leaf (n : Side) : Sheet n := plain n ⊗ₖ (1:Bundle)
lemma leaf_u (n : Side) : leaf n∈unitary _ := by
  constructor
  · rw [leaf, star_kr, star_one,← Matrix.mul_kronecker_mul,(plain_u n).1, one_mul]; exact Matrix.one_kronecker_one
  rw [leaf, star_kr, star_one,← Matrix.mul_kronecker_mul,(plain_u n).2, one_mul]; exact Matrix.one_kronecker_one

lemma onestep (x p : Site n) (i) : seam 0 x i * scarf p (x+step i)=scarf p x*cis (menu p i) := by
  have he : cis (-Real.pi / n.val)*Bloch.cell p (step i)=cis (menu p i) := by
    rw [Bloch.cell_step]; unfold cis; rw [← Complex.exp_add]; congr 1
    dsimp only [Bloch.mon,menu,Pi.smul_apply,smul_eq_mul,spacer,Laurent.reciprocal,fixed]
    push_cast; ring
  rw [scarf, Bloch.cell_add,← he]
  calc
    _ = ((n.val:ℂ)⁻¹^2*(seam 0 x i * wind (x+step i))*Bloch.cell p x)*Bloch.cell p (step i) := by ring
    _ = _ := by rw [wind_step]; unfold scarf; ring
end YM.QCD.Free
