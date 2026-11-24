import YM.QCD.Step.High
import YM.Lattice.Support

/-!
# range and link dependence. These are distinct properties.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Kit
open Lat Lattice Wilson Finset Function
open scoped Matrix Matrix.Norms.L2Operator Topology
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
variable {c f : Side}

def view (x : Site f) (p : ℕ) : Set (Site f) := {y| separation x y ≤ p}
structure Reads (x : A→Site f) (y : B→Site f) (p : ℕ) (D : Grid f→ Matrix A B ℂ) : Prop where
  absent (i j) : ¬ y j ∈ view (x i) p → ∀ U, D U i j=0
  sees (i j) : LocalOn (view (x i) p) (fun (U : Grid f) => D U i j)

namespace Reads
variable {x : A→Site f} {y : B→Site f} {z : C→Site f} {p q : ℕ} {D E : Grid f→ Matrix A B ℂ}
lemma dilate (h : Reads x y p D) (hv : p ≤ q) : Reads x y q D := by
  have he (i : Site f) : view i p ⊆ view i q := fun _ hu => le_trans hu hv
  exact ⟨fun i j hj => h.absent i j (mt (fun e => he _ e) hj),fun i j U V H => h.sees i j U V (agrees_mono H (he _))⟩
lemma plus (h : Reads x y p D) (k : Reads x y p E) : Reads x y p (fun U => D U+E U) :=
  ⟨fun i j hj U => by rw [Matrix.add_apply,h.absent i j hj,hk i j hj,add_zero], fun i j U V H => congrArg₂ (·+·) (h.sees i j U V H) (k.sees i j U V H)⟩
 where hk := k.absent
lemma minus (h : Reads x y p D) (k : Reads x y p E) : Reads x y p (fun U => D U-E U) :=
  ⟨fun i j hj U => by rw [Matrix.sub_apply,h.absent i j hj,k.absent i j hj,sub_zero], fun i j U V H => congrArg₂ (·-·) (h.sees i j U V H) (k.sees i j U V H)⟩
lemma coin (h : Reads x y p D) (w : ℂ) : Reads x y p (fun U => w • D U) :=
  ⟨fun i j hj U => by rw [Matrix.smul_apply,h.absent i j hj,smul_zero], fun i j U V H => congrArg (w • ·) (h.sees i j U V H)⟩
lemma single : Reads x x p (fun _ => (1:Matrix A A ℂ)) := by
  refine ⟨fun i j hj U => ?_, fun i j U V H => rfl⟩
  by_cases he : i=j
  · subst j; exact (hj (by simp [view])).elim
  simp [Matrix.one_apply,he]
lemma empty : Reads x y p (fun _ => (0:Matrix A B ℂ)) := ⟨fun i j _ _ => rfl, fun i j U V H=>rfl⟩
lemma collect {i : Type*} [Fintype i] {D : Grid f → i → Matrix A B ℂ} (h : ∀ j, Reads x y p (D · j)) : Reads x y p (fun U => ∑ j, D U j) := by
  refine ⟨fun a b hb U => ?_, fun a b U V H => ?_⟩
  · simp only [Matrix.sum_apply,(fun j => (h j).absent a b hb U),sum_const_zero]
  change (∑ j, D U j) a b = (∑ j,D V j) a b
  simp only [Matrix.sum_apply]; exact sum_congr rfl fun i _ => (h i).sees a b U V H
lemma across {W : Grid f→Matrix B C ℂ} (hD : Reads x y p D) (hW : Reads y z q W) : Reads x z (p+q) (fun i => D i * W i) := by
  have hu {i j : Site f} (h : j∈view i p) : view j q ⊆ view i (p+q) := fun k hk => (separation_triangle i j k).trans (Nat.add_le_add h hk)
  refine ⟨fun a b hb U => ?_,fun a b U V H => ?_⟩
  · rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _
    by_cases hv : y k∈view (x a) p
    · rw [hW.absent k b (fun hh=> hb (hu hv hh)),mul_zero]
    rw [hD.absent a k hv,zero_mul]
  change (D U * W U) a b = (D V * W V) a b
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply sum_congr rfl; intro k _
  by_cases hv : y k∈view (x a) p
  · rw [(show D U a k=D V a k from ((hD.dilate (show p≤p+q by omega)).sees a k U V H)), (show W U k b=W V k b from hW.sees k b U V (agrees_mono H (hu hv)))]
  rw [hD.absent a k hv,hD.absent a k hv, zero_mul,zero_mul]
lemma turn (h : Reads x y p D) : Reads y x (p+p) (fun U => (D U)ᴴ) := by
  have he i j (hp : y i∉ view (x j) p) U : (D U)ᴴ i j=0 := by rw [Matrix.conjTranspose_apply,h.absent j i hp U,star_zero]
  constructor
  · intro i j hv; apply he; intro hp; apply hv
    change separation _ _ ≤ _; rw [separation_comm]; exact le_trans hp (by omega)
  intro i j U V H
  change (D U)ᴴ i j = (D V)ᴴ i j
  by_cases hv : y i ∉ view (x j) p
  · rw [he i j hv,he i j hv]
  have hk : separation (y i) (x j) ≤ p := by rw [separation_comm]; exact not_not.mp hv
  exact congrArg star (h.sees j i U V (agrees_mono H (fun w hw => (separation_triangle (y i) (x j) w).trans (Nat.add_le_add hk hw))))
lemma power {M : Grid f→Matrix A A ℂ} (h : Reads x x p M) (n : ℕ) : Reads x x (p*n) (fun U => M U^n) := by
  induction n with
  | zero => simp only [pow_zero]; exact single
  | succ n ih => simp_rw [pow_succ,Nat.mul_succ]; exact ih.across h
end Reads

def eye : Row f→Site f := (·.1)
lemma shifting (t : Site f) (a) : Reads eye eye 1 (fun U => shift t U a) := by
  have ht (p : Row f) : p.1 + step a∈view (eye p) 1 := by
    unfold view eye separation
    simp only [Set.mem_setOf_eq, show p.1-(p.1+step a)=-(step a) by abel]
    rw [pdist_neg]; exact pdist_step a
  constructor
  · intro i j h U
    rw [shift,rr,if_neg (show forward a i.1 ≠ j.1 from fun e => h ((show i.1+step a=eye j from e) ▸ ht i))]
  intro i j U V H
  have he : U (i.1,a)=V (i.1,a) := H (i.1,a) (by simp [eye,view]) (ht i)
  change shift _ U _ i j = shift _ V _ i j; simp only [shift, rr, thread, he]
lemma here (t : Site f) (a) : Reads eye eye 2 (fun U => leg t U a) := by
  unfold leg; split
  · exact (shifting t _).turn
  exact (shifting t _).dilate (by decide)
lemma membership (t : Site f) (w : Walk) : Reads eye eye (2*w.length) (fun U => routeM t U w) := by
  induction w with
  | nil => exact Reads.single
  | cons a w ih =>
    rw [List.length_cons, show 2*(w.length+1)=2+2*w.length by omega]; exact (here t a).across ih
lemma pupil (X : Spike) : Reads (f:=f) eye eye 0 (fun _ => onSpin f X) := by
  refine ⟨fun i j h _ => ?_,fun _ _ _ _ _ => rfl⟩
  rw [onSpin, rr, Equiv.refl_apply, if_neg]
  exact fun he => h (by simp [eye, ← he,view])
lemma readD (t : Site f) (m : ℝ) : Reads eye eye 2 (fun U => bareD t U m) := by
  unfold bareD; refine (Reads.single.coin _).plus (Reads.collect fun j => Reads.single.minus ?_)
  refine Reads.plus ((pupil (lo _)).across ((shifting t j).dilate (show 1≤2 by decide))) ((pupil (hi _)).across (shifting t j).turn)
variable (r : Ratio c f)

def perch := r.embed ∘ eye
lemma scooping : Reads (perch r) eye 0 (fun _ => scoop r) := by
  refine ⟨fun i j h _ => ?_,fun _ _ _ _ _ => rfl⟩
  apply if_neg; intro he; exact h (by simp [← he,eye,mouth,perch,view])
def reachQ (L : Side) := 2*reach L
lemma readQ (t : Site f) : Reads (perch r) eye (reachQ r.count) (fun U => Q r t U) := by
  unfold Q vane stripe; refine Reads.coin (Reads.collect fun o => Reads.coin (Reads.collect fun j => ?_) _) _
  apply Reads.dilate ((scooping r).across (membership t _))
  rw [zero_add,reachQ]; gcongr; exact Kit.covers r.count o j

def hike (L : Side) := reachQ L+reachQ L+reachQ L
lemma hikes (L : Side) : 2≤hike L := by unfold hike reachQ reach; have h : 0<L.val := L.property; exact (le_trans (by omega : 2 ≤ 2*(4*L.val)) (by omega))
lemma readH (b : ℝ) (t : Site f) (m : ℝ) : Reads eye eye (hike r.count) (hefty r b t · m) :=
  ((readD t m).dilate (hikes _)).plus (((readQ r t).turn.across (readQ r t)).coin _)
end YM.QCD.Kit
