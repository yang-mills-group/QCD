import YM.QCD.Flume.Song
import YM.Next.FREE_KERNELS.PatchMean

/-! # blocking col on actual patches. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ}

lemma unroll (t : Site f) (w : Walk) (p : Site f) : peel (routeM (0: Site f) 1 w)=lined fun i=> mode (tuning i) (stop 0 w) • (1:Bundle) := by
  induction w with
  | nil => simp only [routeM,List.map_nil,List.prod_nil,peel_one,stop,mode_zero,one_smul]; exact ridden.symm
  | cons a w ih=>
    rw [show routeM (0: Site f) 1 (a::w)=leg 0 1 a*routeM 0 1 w from rfl,peel_mul,ih]
    have hu (a:Axis) (i : Site f): mode (tuning i) (step a)=cis (menu i a):=by rw [Exterior.factor,mul_comm]; rfl
    have hb (a:Axis) (i : Site f): mode (tuning i) (-step a)=star (cis (menu i a)):=by rw [← hu]; have he:=mode_adjoint (tuning i) (step a); rw [show star (tuning i)=tuning i from (keyboard _).1] at he; exact he.symm
    rw [show peel (leg (0:Site f) 1 a)= lined (fun i=> mode (tuning i) a.vec • (1:Bundle)) from by
      rcases a with ⟨a,_|_⟩
      · rw [leg,if_neg (by simp),peel_shift]; simp only [Step.vec,Bool.false_eq_true,↓reduceIte,hu]
      rw [leg,if_pos rfl,peel_back]; simp only [Step.vec, if_true,hb]]
    rw [lined_law]; congr 1; funext i
    simp only [Pi.mul_apply,Matrix.smul_mul,one_mul,smul_smul,stop,zero_add]
    congr 1
    rw [← mode_shift]; congr 1; exact (cover_along a.vec 0 w|>.symm).trans (by rw [add_zero]) --

lemma bare_leaf (x i : Site n) (a b : Fiber) : leaf n (x,a) (i,b)=scarf i x*(1:Bundle) a b:=rfl
lemma slide_kit (r : Ratio c f) (ho : Odd r.count.val) (o : Lattice.Order) (x : Cover) (p : Site c) (l : Site r.count) (y : Site c) (a b : Fiber) :
    ((scoop r*routeM (0:Site f) 1 (route 0 x o))*leaf f) (y,a) (twins r p l,b)=
      ((r.count.val:ℂ)⁻¹^2*mode (aliasAt (tuning p) l) x)*leaf c (y,a) (p,b):=by
  rw [Matrix.mul_assoc,shows]; let i:=twins r p l
  have he : routeM (0:Site f) 1 (route 0 x o)*leaf f=leaf f*lined (fun i => mode (tuning i) x • (1:Bundle)) := by
    conv_lhs => arg 1; rw [peel_out (routeM (0:Site f) 1 (route 0 x o)),unroll 0 _ (twins r p l),route_end]
    rw [mul_assoc _ (star _) (leaf f),(leaf_u f).1,mul_one]
  rw [he]; unfold mouth; rw [Free.face, welcome r ho,full_tune r ho,Matrix.smul_apply,bare_leaf]; ring

-- take Q normalization matching covariance recursion on counting-measure spin
abbrev sliceL (P : Flight j k) (h : f.val=c.val*P.L.val) : Ratio c f := ⟨P.L,h⟩
def lineF (P : Flight j k) (h : f.val=c.val*P.L.val) (t : Site f) (U : Grid f) (o : Lattice.Order) : Rail c f :=
  ∑ a : P.patch.Points, (P.patch.weight a:ℂ) • (scoop (sliceL P h)*routeM t U (route 0 a.val o))
def massL (L : Side) : ℝ := slope L*(L.val:ℝ)^2
def tied (P : Flight j k) (h : f.val=c.val*P.L.val) (t : Site f) (U : Grid f) : Rail c f :=
    (massL P.L:ℂ) • ((votes:ℂ)⁻¹ • ∑ o,lineF P h t U o)
lemma tight (P : Flight j k) (h : f.val=c.val*P.L.val) (p : Site c) (l : Site P.L) (x : Site c) (a b : Fiber) :
    (tied P h 0 1 * leaf f) (x,a) (twins (sliceL P h) p l,b)=((slope P.L:ℂ)*book P (tuning p) l)*leaf c (x,a) (p,b):=by
  let r := sliceL P h
  have he (o : Lattice.Order) : (lineF P h 0 1 o*leaf f) (x,a) (twins (sliceL P h) p l,b) = ((P.L.val:ℂ)⁻¹^2*book P (tuning p) l)*leaf c (x,a) (p,b):=by
    unfold lineF book; simp only [Matrix.sum_mul,Matrix.smul_mul,Matrix.sum_apply,Matrix.smul_apply]
    rw [← pays_roll, Finset.mul_sum, Finset.sum_mul]; apply sum_congr rfl; intro v _; rw [slide_kit (sliceL P h) P.odd]; ring
  unfold tied; simp only [Matrix.smul_mul,Matrix.sum_mul,Matrix.smul_apply, Matrix.sum_apply,he,sum_const, card_univ,nsmul_eq_mul,smul_eq_mul]
  unfold massL; push_cast; field_simp [show ((votes:ℕ):ℂ)≠0 from by exact_mod_cast (Fintype.card_pos (α:=Lattice.Order)).ne', side_ne P.L]

/-- Covariance already before flat evaluation. -/
lemma gauges (P : Flight j k) (h : f.val=c.val*P.L.val) (t : Site f) (U : Grid f) (s : Frame f):
    tied P h t (gauge s U) = siteRot (s ∘ (sliceL P h).embed)*tied P h t U*star (siteRot s):=by
  let r:=sliceL P h
  have hr : scoop r*siteRot s=siteRot (s ∘ r.embed)*scoop r:= roots ..
  unfold tied lineF; simp only [Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,gaugeM]
  simp only [← Matrix.mul_assoc]; dsimp only [r] at hr; simp_rw [hr]
end YM.QCD.Flume
