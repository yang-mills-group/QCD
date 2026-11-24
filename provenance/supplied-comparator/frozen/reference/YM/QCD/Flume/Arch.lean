import YM.QCD.Flume.Reed
import YM.Next.FREE_KERNELS.Sprout

/-! # scaled forward response at arbitrary alias, root filled BEFORE width estimate -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators Matrix
variable {ι : Type*} {j k : ℕ}

def book (P : Flight j k) (p : Momentum) (l : Site P.L) := massFilter P.patch (aliasAt p l)
abbrev host (c : Bool) (P : Flight j k) (p : Momentum) := view c (Dir P.land p)
def fairly (c : Bool) (P : Flight j k) (p : Momentum) := (1:Bundle)+ ∑ l∈Finset.univ.erase (0:Site P.L), book P p l^2 • view c (day P l p)
/-- forward, L scaled out before installation cost -/
def shout (c : Bool) : Thread j k Fiber Fiber:=fun P p l => if l=0 then
    (book P p 0)⁻¹ • (1-fairly c P p*host c P p)
  else book P p l • (view c (day P l p)*host c P p)
lemma priority (P : Flight j k) (p : Momentum) : book P p 0=massFilter P.patch (P.toe p):=rfl
lemma host_qual (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) (he : p≠0) :
    host false P p=(model (full P.land p))⁻¹ := by rw [host,view_false,recover _ _ (teen _ hp he), live_inv (full_inv hp he)]

lemma firstDay (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) (he : p≠0) :
    model (full P.land p)=book P p 0^2 • view false (day P 0 p)+fairly false P p:=by
  unfold Flight.land; rw [unfold_full]; simp only [model_add,model_solo,one_smul]
  have hh (l : Site P.L) : view false (day P l p)=(P.L.val:ℂ)⁻¹ • model (full P.wing (aliasAt p l)):=day_qual P l p hp (.inr he)
  unfold jump spool fairly
  have hx : model ((P.L.val:ℂ)⁻¹ • (∑ l, book P p l^2 • full P.wing (aliasAt p l)))=∑ l, book P p l^2 • view false (day P l p) := by
    rw [model_smul]
    change _ • Para.signal (∑ l:Site P.L, _)=_
    simp only [map_sum,map_smul,smul_sum]; apply sum_congr rfl; intro i _; rw [hh,smul_comm]; rfl
  change 1+ model ((P.L.val:ℂ)⁻¹ • (∑ l, book P p l^2 • full P.wing (aliasAt p l)))=_
  rw [hx,← add_sum_erase _ (fun l=>book P p l^2 • view false (day P l p)) (mem_univ (0:Site P.L)),add_left_comm]

lemma book_hits (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) : book P p 0≠0:=mass_filter_live P hp
lemma shout_eq (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) (he : p≠0) (l : Site P.L) :
    shout false P p l = book P p l • (view false (day P l p)*host false P p):=by
  unfold shout; split_ifs with h; swap; · rfl
  subst l
  have hm : model (full P.land p)*host false P p=1 := by rw [host_qual P p hp he,Matrix.mul_nonsing_inv _ (funds (full_inv hp he))]
  rw [firstDay P p hp he,add_mul] at hm
  rw [← (eq_sub_iff_add_eq.mpr hm : _ = (1:Bundle)- _),Matrix.smul_mul,smul_smul,pow_two, ← mul_assoc,inv_mul_cancel₀ (book_hits P _ hp),one_mul]
lemma shout_match (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) (he : p≠0) (l : Site P.L):
    shout false P p l=book P p l • (((P.L.val:ℂ)⁻¹ • model (full P.wing (aliasAt p l))) * model (Dir P.land p)):=by rw [shout_eq P _ hp he l,view_false,day_qual P l p hp (Or.inr he)]; rfl
lemma book_real (P : Flight j k) (p : Momentum) (hp : physical p) (l : Site P.L) : star (book P p l)=book P p l := by unfold book massFilter; rw [star_pow,Train.area_conj,show star (aliasAt p l)=aliasAt p l from alias_real hp l]; exact P.massFilter_even (aliasAt p l)
lemma low_book (P : Flight j k) (p : Momentum) (l : Site P.L) : book P (-p) (-l)=book P p l:= by rw [book,alias_reverse p P.odd,P.massFilter_even]; rfl

lemma shuffleH (c : Bool) (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) : host (!c) P (-p)=shade (host c P p):=by rw [host,evenD _ _ hp, polarized c _ (native_dir _ _ hp.1)]
lemma shuffleF (c : Bool) (P : Flight j k) (p : Momentum) (hp : p∈realCube zone): fairly (!c) P (-p)=shade (fairly c P p):=by
  unfold fairly; rw [shade_add,shade_nil]; congr 1
  have hh (s : Finset (Site P.L)) (f : Site P.L → Bundle): shade (∑ i∈s,f i)=∑ i∈s,shade (f i):=by ext a b; simp [shade,Matrix.sum_apply]
  rw [hh]
  refine Eq.symm (Finset.sum_equiv (Equiv.neg (Site P.L)) (fun x=> by simp) (fun i _=>?_))
  simp only [Equiv.neg_apply]; rw [day_reverse _ _ _ hp,polarized _ _ (day_native _ _ _ hp.1),shade_weight,star_pow,book_real P p hp.1,low_book]
lemma shuff (c : Bool) (P : Flight j k) (p : Momentum) (hp : p∈realCube zone) (l:Site P.L) : shade (shout c P p l)=shout (!c) P (-p) (-l):=by
  by_cases h:l=0
  · subst l
    simp only [shout,neg_zero,↓reduceIte]
    have hx := low_book P p 0; rw [neg_zero] at hx
    rw [shade_weight,star_inv₀, book_real _ _ hp.1,hx,shade_sub,shade_nil, shade_mul,shuffleF _ _ _ hp,shuffleH _ _ _ hp]
  simp only [shout,h,neg_ne_zero.mpr h,↓reduceIte]
  rw [shade_weight,book_real P _ hp.1,shade_mul,shuffleH _ _ _ hp,day_reverse _ _ _ hp,polarized _ _ (day_native _ _ _ hp.1),low_book]
lemma shiftsD (P : Flight j k) (p : Momentum) (l : Site P.L) (hp : p∈realCube zone) (x : Cover) (hx : p+Laurent.reciprocal x ∈ realCube zone) :
    shout false P (p+Laurent.reciprocal x) l=shout false P p (l+wrap P.L x):=by
  by_cases h:x=0; · rw [h,show Laurent.reciprocal (0:Cover)=0 by ext; simp [Laurent.reciprocal],add_zero,map_zero,add_zero]
  obtain ⟨hy,hz⟩:=overlap_regular h hp hx
  rw [shout_match _ _ hx hz, shout_match _ _ hp hy]; unfold book
  obtain ⟨y,hq⟩:=alias_exchange p l x
  rw [hq,periodic_full,period_dir P.land x hp hx,massFilter,Train.area_period]; rfl
lemma shifts (c : Bool) (P : Flight j k) (p : Momentum) (l : Site P.L) (hp : p∈realCube zone) (x : Cover) (hx : p+Laurent.reciprocal x ∈ realCube zone) :
    shout c P (p+Laurent.reciprocal x) l=shout c P p (l+wrap P.L x):=by
  cases c; · exact shiftsD P p l hp x hx
  have h (q : Momentum) (l : Site P.L) (hh : q∈realCube zone) : shout true P q l=shade (shout false P (-q) (-l)):=by simpa only [Bool.not_false,neg_neg] using (shuff false P _ (realCube_neg hh) (-l)).symm
  rw [h _ _ hx,h _ _ hp]; congr 1
  rw [neg_moves,shiftsD P (-p) (-l) (realCube_neg hp) (-x) (by rw [← neg_moves]; exact realCube_neg hx)]; simp [add_comm]

lemma bill_host (hk : 4≤k) (c : Bool) (F : ι→Flight j k) : Pay (fun _ : ι=>1) fun i p=> host c (F i) p:= coil (Dir_budget (by omega) fun i=> (F i).land) c
lemma fair_paid (hj : 4 ≤ j) (c : Bool) (F : ι→Flight j k) : Pay (fun _ : ι=>1) fun i p => fairly c (F i) p:=by
  unfold fairly; refine (Pay.const _).add ?_
  refine ⟨fun _=>zero_le_one,fun a b=>?_⟩; simp only [Matrix.sum_apply]
  let L:=fun i=> (F i).L
  let s:=fun i:ι=> Finset.univ.erase (0:Site (L i))
  let I:= Σ i,{l // l∈s i}
  let A (i:I):=F i.1; let l (i:I):=i.2.val
  have hl (i:I):l i≠0:= (Finset.mem_erase.mp i.2.property).1
  obtain ⟨C,hc,h⟩:=decay_cost
  have he i: ∑ l∈s i,decay 2 l≤C*1:=by rw [mul_one]; exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _=> (decay_pos ..).le)).trans (h _)
  apply Moderate.sum_family s (fun _=>decay 2) ⟨C,hc,he⟩
  apply (((coil (counter hj A l hl) c).scale ((Flight.bills A l).pow 2)).tap a b).raise_price
  intro i
  change (decay j _)^2 * _ ≤ _
  rw [pow_two]
  exact ((mul_le_of_le_one_right (mul_nonneg (decay_pos ..).le (decay_pos ..).le) (inv_le_one_of_one_le₀ (grade_ge _))).trans (mul_le_of_le_one_right (decay_pos ..).le (decay_le_one ..))).trans (decay_anti _ (by omega))
lemma shout_bill (hj : 4 ≤ j) (hk : 4 ≤ k) (c : Bool) (F : ι→Flight j k) (l : ∀ i, Site (F i).L) : Pay (fun i=> decay j (l i)) fun i p=> shout c (F i) p (l i):=by
  apply Pay.branches (fun i=>l i=0) (fun _=> (decay_pos ..).le)
  · have hB : Moderate (fun _ : ι=>1) fun i p=>book (F i) p 0:=by simpa only [book,decay_zero] using Flight.bills F fun _=> 0
    have hh: Pay (fun _ : ι=>1) fun i p => fairly c (F i) p*host c (F i) p:= by simpa only [mul_one] using (fair_paid hj c F).times (bill_host hk c F)
    have hx := (Pay.const 1|>.sub hh).scale (hB.inv (Flight.bills_firm F) fun _=>one_pos)
    have hl (i:{i//l i=0}):l i.val=0:=i.property
    simpa only [shout,hl,decay_zero,if_true,inv_one,mul_one] using hx.reindex (fun i:{i//l i=0}=> i.val)
  let I:={i//¬ l i=0}; let A (i:I):=F i; let L (i:I):=l i.val
  have hx:= (coil (counter hj A L fun i=> i.property) c|>.times (bill_host hk c A)).scale (Flight.bills A L)
  have ht : Pay (fun i=> decay j (L i)) fun i p=> book (A i) p (L i) • (view c (day (A i) (L i) p)*host c (A i) p) := by
    apply hx.raise; intro i; change decay j _*((grade _)⁻¹*1)≤_; rw [mul_one]; exact mul_le_of_le_one_right (decay_pos ..).le (inv_le_one_of_one_le₀ (grade_ge _))
  have hu (i:I):¬l i.val=0:=i.property
  simpa only [shout,hu,if_false] using ht

/-- Split the entries into two real-coefficient channels -/
def yip (c : Bool) : Thread j k Fiber Fiber:=fun P p l=> if c then
    (2*Complex.I)⁻¹ • (shout false P p l-shout true P p l)
    else (2:ℂ)⁻¹ • (shout false P p l+shout true P p l)
lemma reunited (P : Flight j k) (p : Momentum) (l) : shout false P p l=yip false P p l+Complex.I • yip true P p l:=by
  ext a b; simp [yip]; field_simp; ring_nf; rw [Complex.I_sq]; ring
lemma supplied (c : Bool) (hj : 4≤j) (hk : 4≤k) : Secured (yip (j:=j) (k:=k) c):= by
  constructor
  · have hx c := shout_bill hj hk c (fun i: Σ P:Flight j k,Site P.L=>i.1) fun i=>i.2
    cases c
    · simpa only [yip,Bool.false_eq_true,↓reduceIte,one_mul] using (((hx false).add (hx true)).scale (Moderate.const (2:ℂ)⁻¹))
    simpa only [yip,if_true,one_mul] using (((hx false).sub (hx true)).scale (Moderate.const (2*Complex.I)⁻¹))
  · intro P p hp x hx l; cases c <;> simp only [yip,Bool.false_eq_true,↓reduceIte,shifts _ _ _ _ hp _ hx]
  intro P p hp l; cases c <;> simp only [yip,Bool.false_eq_true,↓reduceIte,shade_weight,shade_add,shade_sub,shuff _ P _ hp,Bool.not_false,Bool.not_true]
  · rw [add_comm]; simp
  rw [sub_eq_neg_add]; -- finish
  simp [sub_eq_add_neg,mul_comm]
end YM.QCD.Flume
