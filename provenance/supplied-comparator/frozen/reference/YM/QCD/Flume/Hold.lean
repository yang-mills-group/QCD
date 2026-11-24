import YM.QCD.Flume.Tiny
import YM.Next.FREE_KERNELS.Reserve

/-! # Propagation of counting-measure scale factors for the Dirac RG step -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free
open scoped Topology BigOperators
variable {ι E : Type*} {j : ℕ}

lemma smooth_even (v : Train j) (p : Momentum) : v.smooth (-p)=v.smooth p := v.smooth_signed p ⟨1,fun _=>true⟩
lemma smooth_cast (v : Train j) (p : Momentum) (hp : physical p) : ((v.smooth p).re:ℂ)=v.smooth p := by
  have he := v.smooth_conj p
  rw [show star p=p from hp,smooth_even] at he
  exact Complex.ext rfl (Eq.symm (Complex.conj_eq_iff_im.mp he))
section
variable [AddCommGroup E] [Module ℂ E]
def spool (L : Side) (G : Momentum → ℂ) (D : Momentum → E) (p : Momentum) : E := (L.val:ℂ)⁻¹ • ∑ i : Site L, G (aliasAt p i)^2 • D (aliasAt p i)
def jump (P : RG.Patch) := spool (E:=E) P.L (massFilter P)
def carry (v : Train j) := spool (E:=E) v.mass v.smooth

lemma splice (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J)
    (f : Momentum → E) (p : Momentum) : carry (.hop P h h' v) f p = jump P (carry v f) p := by
  let L:=P.L; let w:=Train.hop P h h' v; let e:=radices P.odd_side v.mass_odd
  have he (r : Site v.mass) (q : Momentum) : w.smooth (aliasAt q r)=massFilter P q*v.smooth (aliasAt q r):=by unfold w; rw [Train.bind,alias_scale,Train.area_period]; rfl
  let W:=fun b : Site (L*v.mass) => w.smooth (aliasAt p b)^2 • f (aliasAt p b)
  let A:=fun l : Site L=> massFilter P (aliasAt p l)^2
  let B:=fun (l : Site L) (r : Site v.mass)=>v.smooth (aliasAt (aliasAt p l) r)^2 • f (aliasAt (aliasAt p l) r)
  have H (l r): W (e (l,r))=A l • B l r := by
    unfold W A B; rw [show aliasAt p (e (l,r))=_ from (alias_refine P.odd_side v.mass_odd p l r).symm,he,mul_pow,mul_smul]
  have hw : ∑ i, W i = ∑ l, A l • ∑ r,B l r := by rw [← e.sum_comp W,Fintype.sum_prod_type]; simp_rw [H,smul_sum]; rfl
  change ((L*v.mass).val:ℂ)⁻¹ • (∑ i, W i)=(L.val:ℂ)⁻¹ • ∑ l,A l • ((v.mass.val:ℂ)⁻¹ • ∑ r,B l r)
  rw [hw, mul_side_complex,mul_inv,mul_smul]
  congr 1; rw [smul_sum]; apply sum_congr rfl; intro _ _; rw [smul_comm]
lemma jump_add (P : RG.Patch) (f g : Momentum → E) (p : Momentum) : jump P (fun p=>f p + g p) p=jump P f p+jump P g p:= by simp [jump,spool,smul_add,sum_add_distrib]
lemma zero_jump (P : RG.Patch) (p : Momentum) : jump P (fun _=> (0:E)) p=0 := by simp [jump,spool]
lemma carry_top (j) (D : Momentum→E) (p : Momentum) : carry (.top j) D p=D p:=by
  unfold carry spool; simp only [Train.mass,Train.smooth_top,one_pow,one_smul]
  letI : Subsingleton (Site 1):=inferInstanceAs (Subsingleton (Axis → ZMod 1))
  rw [sum_eq_single (0:Site 1) (fun i _ h=> False.elim (h (Subsingleton.elim ..))) (by simp)]
  simp [aliasAt]
lemma periodic_spool (L : Side) (g : Momentum→ℂ) (f : Momentum→E) (hg : Stable g) (hf : ∀ p x,f (p+Laurent.reciprocal x)=f p) (p : Momentum) (x : Cover) : spool L g f (p+Laurent.reciprocal x)=spool L g f p := by
  unfold spool; congr 1
  let e:=Equiv.addRight (wrap L x)
  let A i:=g (aliasAt p i)^2 • f (aliasAt p (i:Site L))
  rw [← Equiv.sum_comp e A]
  refine sum_congr rfl fun i _=> ?_
  obtain ⟨y,H⟩:=alias_exchange p i x
  rw [H,hg,hf]; rfl
end

def stripsum (l : List (Train j)) (p : Momentum) : ℂ := (l.map fun v => carry v (fun _ => (1:ℂ)) p).sum
def spr (v : Train j) := stripsum v.nozzle
lemma sprayed (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J) (p : Momentum) : spr (.hop P h h' v) p=1+jump P (spr v) p:= by
  have he (l : List (Train P.J)) : stripsum (l.map (Train.hop P h h')) p=jump P (stripsum l) p := by
    induction l with
    | nil=> simp [stripsum,jump,spool]
    | cons b l ih=>
      rw [show stripsum (b :: l)=fun q => carry b (fun _=> (1:ℂ)) q+stripsum l q from by funext q; simp [stripsum],jump_add,← ih]
      simp only [stripsum,List.map_cons,List.sum_cons,splice]
  simp only [spr, Train.nozzle]
  change carry _ _ p+stripsum _ p=_
  rw [carry_top]; exact congr_arg (1+·) (he v.nozzle)
lemma coins (v : Train j) (p : Momentum) (hp : physical p) : ((carry v (fun _=> (1:ℂ)) p).re:ℂ)=carry v (fun _=>1) p ∧ 0 ≤ (carry v (fun _=> (1:ℂ)) p).re := by
  have he : carry v (fun _=> (1:ℂ)) p=(↑((v.mass.val:ℝ)⁻¹ * ∑ i: Site v.mass,(v.smooth (aliasAt p i)).re^2):ℂ) := by
    simp only [carry,spool,smul_eq_mul,mul_one]; push_cast
    simp_rw [fun i => smooth_cast v _ (alias_real hp i)]
  rw [he]; simp only [Complex.ofReal_re]; exact ⟨trivial,by positivity⟩
lemma bids (l : List (Train j)) (p : Momentum) (hp : physical p) : ((stripsum l p).re:ℂ)=stripsum l p ∧ 0 ≤ (stripsum l p).re := by
  induction l with
  | nil=> simp [stripsum]
  | cons b l ih=>
    change ((carry b _ p + stripsum l p).re:ℂ)=_+_ ∧ 0 ≤ (carry b _ p + stripsum l p).re
    simp only [Complex.add_re, Complex.ofReal_add]; rw [(coins b p hp).1,ih.1]; exact ⟨rfl,add_nonneg (coins b p hp).2 ih.2⟩
lemma whole_bid (P : RG.Patch) {h : j≤P.J} {h' : P.J≤j+1} (v : Train P.J) (p : Momentum) (hp : physical p) : 1 ≤ (spr (.hop P h h' v) p).re := by
  unfold spr Train.nozzle; change 1 ≤ (carry _ _ p + stripsum _ p).re
  rw [carry_top,Complex.add_re]; exact le_add_of_nonneg_right (bids _ p hp).2
lemma spr_stable (v : Train j) : Stable (spr v) := by
  have h (l : List (Train j)): Stable (stripsum l):= by
    induction l with
    | nil=> intro p x; simp [stripsum]
    | cons b l ih=> intro p x; exact congr_arg₂ (·+·) (periodic_spool _ b.smooth (fun _=> (1:ℂ)) b.smooth_period (fun _ _=> rfl) p x) (ih p x)
  exact h _

lemma carry_money (hj : 2≤j) (v : ι→Train j) : Moderate (fun i => ((v i).mass.val:ℝ)⁻¹) fun i=> carry (v i) (fun _=> (1:ℂ)):= by
  unfold carry spool; simp only [smul_eq_mul,mul_one]
  let L:=fun i=> (v i).mass
  have hm : ∃ B:ℝ,0<B ∧ ∀ i:ι,∑ l:Site (L i), decay 2 l ≤ B*1:=by obtain ⟨C,hc,h⟩:=decay_cost; exact ⟨C,hc,fun i=>by rw [mul_one]; exact h _⟩
  let F (i:ι) (l:Site (L i)) (p:Momentum):= (v i).smooth (aliasAt p l)^2
  have ht : Moderate (fun _:ι=>1) fun i p=>∑ l,F i l p:=by
    apply Moderate.sum_family _ _ hm
    let π:=fun x: Σ i,{l:Site (L i) // l ∈ (Finset.univ:Finset _)}=> x.1
    refine ((Train.smooth_cost (v∘π) fun x=>x.2.val).pow 2).raise_price fun i=>?_
    let u:=i.2.val
    change decay j u^2 ≤ _; rw [pow_two]; exact (mul_le_of_le_one_left (decay_pos ..).le (decay_le_one ..)).trans (decay_anti _ hj)
  have hs : Moderate (fun i=> ((L i).val:ℝ)⁻¹) fun i _=> ((L i).val:ℂ)⁻¹ := Moderate.bounded_const _ 1 one_pos fun _=> by simp
  simpa only [mul_one] using hs.mul ht

def fare (l : List (Train j)) := (l.map fun i => (i.mass.val:ℝ)⁻¹).sum
lemma fare_safe (v : Train j) : fare v.nozzle ≤ 2:= by
  induction v with
  | top _ => simp [fare,Train.nozzle]
  | @hop j P h h' v ih =>
    have hh (l : List (Train P.J)) : fare (l.map (Train.hop P h h'))=(P.L.val:ℝ)⁻¹ * fare l:=by
      induction l with
      | nil => simp [fare]
      | cons b l ih' => change ((P.L*b.mass).val:ℝ)⁻¹+fare _= (P.L.val:ℝ)⁻¹ * ((b.mass.val:ℝ)⁻¹+fare l); rw [ih',mul_side_real,mul_inv,mul_add]
    rw [Train.nozzle]; change (((1:Side).val:ℝ))⁻¹+fare _ ≤ 2
    rw [hh]; have he : (3:ℝ)≤ P.L.val := by exact_mod_cast P.coarse
    have hu := mul_le_mul_of_nonneg_left ih (show 0 ≤ (P.L.val:ℝ)⁻¹ by positivity)
    norm_num; have ht : (P.L.val:ℝ)⁻¹*2 ≤1:=by rw [inv_mul_eq_div,div_le_one (by positivity)]; linarith
    linarith
lemma spr_money (hj : 2≤j) (v : ι→Train j) : Moderate (fun _ : ι=>1) fun i=> spr (v i):= by
  obtain ⟨η,C,he,hc,h⟩:=carry_money hj (fun i=>i)
  refine ⟨η,C*2,he,by positivity,fun i=>?_⟩
  have hm (l : List (Train j)) : SafeCube η (C*fare l) (stripsum l):=by
    induction l with
    | nil=> simp [fare]; exact ⟨fun _ _=> differentiableAt_const _,fun _ _=> (norm_zero).le⟩
    | cons b l ih=>
      refine ⟨fun p hp=> ?_, fun p hp=> ?_⟩
      · change DifferentiableAt ℂ (fun p=> carry _ _ p+stripsum l p) p
        exact ((h b).hol p hp).add (ih.hol p hp)
      change ‖carry _ _ p + stripsum l p‖ ≤ C*((b.mass.val:ℝ)⁻¹+fare l)
      rw [mul_add]; exact (norm_add_le ..).trans (add_le_add ((h b).bound p hp) (ih.bound p hp))
  exact (hm (v i).nozzle).mono le_rfl ((mul_le_mul_of_nonneg_left (fare_safe (v i)) hc.le).trans (mul_one _).ge)
end YM.QCD.Flume
