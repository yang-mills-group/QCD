import YM.QCD.Roots

/-! # Nonabelian real simplicity for the actual QCD input -/

set_option autoImplicit false
noncomputable section
namespace YM.QCD
namespace Roots
open Finset Complex

/-- Its three positive-plane speeds have distinct nonzero squares. -/
private def regular : Hue → ℝ := ![1, 2, -3]
private def r (p : Root) := regular (a p) - regular (b p)

private theorem trace_free : ∑ i, regular i = 0 := by
  norm_num [Fin.sum_univ_succ, regular]
private theorem nonzero (p : Root) : r p ≠ 0 := by
  fin_cases p <;> norm_num [r, regular, a, b, show (![1, 2, -3] : Hue → ℝ) 2 = -3 from rfl]
private theorem distinct (p q : Root) (h : p ≠ q) : r p ^ 2 ≠ r q ^ 2 := by
  fin_cases p <;> fin_cases q <;> norm_num [r, regular, a, b, show (![1, 2, -3] : Hue → ℝ) 2 = -3 from rfl] at *

variable (J : Submodule ℝ Mat)
def Closes := ∀ (X : Mat), X ∈ su.lie → ∀ (Y : Mat), Y ∈ J → br X Y ∈ J

private lemma isolate (hc : Closes J) (hl : J ≤ su.lie) {p : Root} {X : Mat}
    (hx : X ∈ J) (hz : X (a p) (b p) ≠ 0) : ∃ z, z ≠ 0 ∧ plane p z ∈ J := by
  have h0 := H_lie trace_free
  -- progressively annihilate other root planes in real coordinates
  have kill (s : Finset Root) : p ∉ s →
      ∃ A ∈ J, A (a p) (b p) ≠ 0 ∧ ∀ q ∈ s, A (a q) (b q) = 0 := by
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨X,hx,hz,by simp⟩
    | @insert k s hk ih =>
      intro he
      have ht : p ≠ k := fun h => he (by simp [h])
      have hp : p ∉ s := fun h => he (mem_insert_of_mem h)
      obtain ⟨B,hB,hb,Hb⟩ := ih hp
      let C := br (H regular) (br (H regular) B) + (r k)^2 • B
      have readout (q : Root) : C (a q) (b q) = ((r k)^2-(r q)^2) • B (a q) (b q) := by
        simp [C, twice, sub_smul, r]; abel
      refine ⟨C,J.add_mem (hc _ h0 _ (hc _ h0 _ hB)) (J.smul_mem _ hB),?_,?_⟩
      · rw [readout]; exact smul_ne_zero (sub_ne_zero.mpr (distinct p k ht).symm) hb
      intro q hq; rw [readout]; rcases Finset.mem_insert.mp hq with hq | hq
      · rw [hq]; simp
      simp [Hb _ hq]
  obtain ⟨Y,hy,hv,hP⟩ := kill (univ.erase p) (notMem_erase _ _)
  let Z := br (H regular) Y
  have hZ : Z ∈ J := hc _ h0 _ hy
  have hz0 : weights Z = 0 := funext fun i => by simp [Z, action, weights]
  have hz' (q : Root) (hq : q ≠ p) : Z (a q) (b q) = 0 := by
    unfold Z; rw [action, hP q (mem_erase.mpr ⟨hq, mem_univ _⟩), mul_zero]
  have he := decompose (hl hZ)
  rw [sum_eq_single p (fun q _ hu => by rw [hz' q hu, plane_zero]) (by simp), hz0] at he
  refine ⟨Z (a p) (b p), ?_, ?_⟩
  · unfold Z; rw [action]; exact mul_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (nonzero p))) hv
  · rw [show H 0 = 0 by simp [H], zero_add] at he
    rwa [← he]

private lemma diagonal_arbitrary_plane (hc : Closes J) {p : Root} {h : Hue → ℝ}
    (hh : H h ∈ J) (hδ : h (a p) - h (b p) ≠ 0) (z : ℂ) : plane p z ∈ J := by
  let t := I * ((h (a p) - h (b p) : ℝ) : ℂ)
  have ht : t ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hδ)
  have he : br (plane p (z/t)) (H h) ∈ J := hc _ (plane_lie _ _) _ hh
  rw [← brackets_neg, J.neg_mem_iff, spin, (show t * (z / t) = z by field_simp)] at he
  exact he

private lemma to_diagonal (hc : Closes J) {p : Root} {z : ℂ} (hz : z ≠ 0) (hj : plane p z ∈ J) :
    H (coroot p) ∈ J := by
  have hp := hc _ (plane_lie p (I*z)) _ hj
  rw [rotated] at hp
  exact (J.smul_mem_iff (show (-2 * normSq z : ℝ) ≠ 0 from
    mul_ne_zero (by norm_num) (ne_of_gt (normSq_pos.mpr hz)))).mp hp

private lemma from_plane (hl : J ≤ su.lie) (hc : Closes J) (p : Root) (z : ℂ)
    (hz : z ≠ 0) (h : plane p z ∈ J) : J = su.lie := by
  have hd := to_diagonal J hc hz h
  have ha (q : Root) (w : ℂ) : plane q w ∈ J := by
    apply diagonal_arbitrary_plane J hc hd
    clear * - p q
    fin_cases p <;> fin_cases q <;>
      norm_num [a,b,coroot,Pi.single_apply, Fin.ext_iff]
  have hb (q) : H (coroot q) ∈ J := to_diagonal J hc one_ne_zero (ha q 1)
  refine le_antisymm hl ?_
  intro X hX
  rw [decompose hX, diagonals (units hX)]
  exact J.add_mem (J.add_mem (J.smul_mem _ (hb 1)) (J.smul_mem _ (hb 2))) (J.sum_mem fun i _ => ha _ _)

lemma ideals (hl : J ≤ su.lie) (hc : Closes J) : J = ⊥ ∨ J = su.lie := by
  rcases eq_or_ne J ⊥ with h | h; · exact Or.inl h
  right
  obtain ⟨X,hX,hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  by_cases hz : ∀ p, X (a p) (b p) = 0
  · let h := weights X
    have he : X = H h := by simpa only [hz, plane_zero, sum_const_zero, add_zero] using decompose (hl hX)
    have hp : ∃ q, h (a q)-h (b q) ≠ 0 := by
      by_contra! hh
      have h₁ := sub_eq_zero.mp (hh 0)
      have h₂ := sub_eq_zero.mp (hh 1)
      change h 0 = h 1 at h₁
      change h 0 = h 2 at h₂
      have hh : ∑ i, h i = 0 := units (hl hX)
      rw [Fin.sum_univ_three, ← h₁, ← h₂] at hh
      have h0 : h 0 = 0 := by linarith
      have hv : h = 0 := funext fun i => by
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
        rcases hi with rfl | rfl | rfl
        · exact h0
        · exact h₁.symm.trans h0
        exact h₂.symm.trans h0
      apply hx; rw [he, hv]; simp [H]
    obtain ⟨p,hp⟩ := hp
    exact from_plane J hl hc p 1 one_ne_zero (diagonal_arbitrary_plane J hc (he ▸ hX) hp _)
  push Not at hz; obtain ⟨p,hp⟩ := hz
  obtain ⟨z,hz,hv⟩ := isolate J hc hl hX hp
  exact from_plane J hl hc _ _ hz hv

end Roots
open Roots

/-- real nonabelian simplicity in this convention -/
theorem simple : su.Simple := by
  refine ⟨⟨plane 0 (Complex.I*1),plane_lie _ _,plane 0 1,plane_lie _ _,?_⟩,
    fun J h hh => Roots.ideals J h hh⟩
  change br _ _ ≠ 0
  rw [rotated]
  apply smul_ne_zero (by norm_num)
  intro he
  have hz := congrFun (congrFun he 0) 0
  simp [H, coroot, a, b] at hz

end YM.QCD
