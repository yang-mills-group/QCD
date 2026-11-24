import YM.QCD.Flume.Hold

/-!
# uniform high-alias budgets with the coarse pole removed
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}

def tall (p : Momentum) (v : Train j) (l : Site v.mass):ℂ:= v.smooth (aliasAt p l)^2
def rest (v : Train j) (p : Momentum) := solo (spr v p) + ∑ i∈Finset.univ.erase (0:Site v.mass), tall p v i • reciprocalP (tiny p i)
def full (v : Train j) (p : Momentum) := solo (spr v p)+carry v (fun x=> reciprocalP (kernel x)) p
lemma periodic_full (v : Train j) (p x) : full v (p+Laurent.reciprocal x)=full v p:= by
  unfold full carry; rw [spr_stable,periodic_spool _ _ _ v.smooth_period (fun p x=> by rw [period_k])]
lemma jump_solo (P : RG.Patch) (f : Momentum → ℂ) (p : Momentum) :
    jump P (fun p=>solo (f p)) p=solo (jump P f p) := by
  unfold jump spool; simp only [solo]
  ext <;> simp [Prod.fst_sum,Prod.snd_sum]
lemma unfold_full (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J) (p : Momentum) :
    full (.hop P h h' v) p=solo 1+jump P (full v) p := by
  unfold full; rw [sprayed,splice,jump_add,jump_solo]
  change solo (1+ _)+_= _; unfold solo; rw [← add_assoc]; congr 1; ext <;> simp

abbrev key (v : Train j) (p : Momentum):ℂ:=tall p v 0
abbrev peg (v : Train j) (p : Momentum):Para:=tiny p (0:Site v.mass)
abbrev chipper (v : Train j) (p : Momentum) := quad (peg v p)
def nume (v : Train j) (p : Momentum) := key v p • turn (peg v p)+ chipper v p • rest v p
def den (v : Train j) (p : Momentum) := key v p^2+2*key v p*beam (turn (peg v p)) (rest v p)+chipper v p*quad (rest v p)
def Dir (v : Train j) (p : Momentum) := (den v p)⁻¹ • turn (nume v p)

lemma separate (v : Train j) (p : Momentum):full v p=key v p • reciprocalP (peg v p)+rest v p:=by
  unfold full carry spool rest; rw [smul_sum]
  have hx (i : Site v.mass) : (v.mass.val:ℂ)⁻¹ • (tall p v i • reciprocalP (kernel (aliasAt p i)))=tall p v i • reciprocalP (tiny p i):=by rw [reciprocal_scaled, smul_comm]
  change solo _+(∑ i, (v.mass.val:ℂ)⁻¹ • (tall p v i • _))= _
  simp_rw [hx]; rw [← add_sum_erase _ (fun i=> tall p v i • _) (mem_univ (0:Site v.mass))]; rw [add_left_comm]
lemma clarify (v : Train j) (p : Momentum) (he : chipper v p≠0) :
    full v p=(chipper v p)⁻¹ • nume v p := by rw [separate, nume,smul_add,smul_comm (chipper v p)⁻¹ (key v p),smul_smul (chipper v p)⁻¹ (chipper v p),inv_mul_cancel₀ he,one_smul]; rfl
lemma form_den (v : Train j) (p : Momentum) : quad (nume v p)=chipper v p*den v p:= by
  rw [nume,quad_add,quad_smul,quad_smul,beam_smul]; simp only [quad_turn]
  unfold chipper den; ring
lemma form_dir (v : Train j) (p : Momentum) : quad (Dir v p)=chipper v p*(den v p)⁻¹:= by
  rw [Dir, quad_smul, quad_turn, form_den]; by_cases h:den v p=0
  · rw [h]; simp
  field_simp
lemma recover (v : Train j) (p : Momentum) (he : chipper v p ≠ 0) : Dir v p=reciprocalP (full v p):=by
  rw [Dir,clarify _ _ he,reciprocalP,quad_smul,form_den]
  have ht (a : ℂ) (x : Para) : turn (a • x : Para)=a • turn x := by ext <;> simp [turn]
  rw [ht,smul_smul]; congr 1; by_cases h : den v p=0
  · rw [h]; simp
  field_simp

lemma tall_silver (p : Momentum) (v : Train j) (l : Site v.mass) (hp : physical p) : ((tall p v l).re:ℂ)=tall p v l ∧ 0 ≤ (tall p v l).re:= by
  have h : tall p v l=(↑(((v.smooth (aliasAt p l)).re)^2):ℂ) := by push_cast; rw [smooth_cast v _ (alias_real hp _)]; rfl
  rw [h]; simp only [Complex.ofReal_re]; exact ⟨trivial,sq_nonneg _⟩
lemma native_rest (v : Train j) (p : Momentum) (hp : physical p) : Native (rest v p) := by
  have hm : ((spr v p).re:ℂ)=spr v p := (bids _ p hp).1
  unfold rest; apply Native.ad (by rw [← hm]; exact Native.scalar _)
  apply Native.recur; intro i _; rw [← (tall_silver p v i hp).1]; exact (genuine p hp i).reciprocal.realSc _
lemma real_num (v : Train j) (p : Momentum) (hp : physical p) : Native (nume v p):= by
  unfold nume; refine Native.ad ?_ ?_
  · rw [← show ((key v p).re:ℂ)=key v p from (tall_silver _ v _ hp).1]; exact ((genuine p hp (0 : Site v.mass)).rotated).realSc _ -- syntax
  rw [← show ((chipper v p).re:ℂ)=chipper v p from (genuine p hp (0:Site v.mass)).quad_cast]; exact (native_rest v p hp).realSc _
lemma real_den (v : Train j) (p : Momentum) (hp : physical p) : ((den v p).re:ℂ)=den v p:= by
  have H:= genuine p hp (0:Site v.mass)
  have hx := native_rest v p hp
  unfold den
  have he : ((key v p).re:ℂ)=key v p := (tall_silver _ _ _ hp).1
  rw [← he,← native_additive _ _ H.rotated hx,← show ((chipper v p).re:ℂ)=chipper v p from H.quad_cast, ← hx.quad_cast]
  norm_cast --
lemma nonneg_spin (A : Para) (h : Native A) (hg : 0≤A.1.re): 0 ≤ (reciprocalP A).fst.re:= by
  unfold reciprocalP; rw [← h.quad_cast,← Complex.ofReal_inv,Prod.smul_fst,smul_eq_mul]
  simp only [turn,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (inv_nonneg.mpr h.quad_ge) hg
lemma respect (v : Train j) (p : Momentum) (hp : physical p) : (spr v p).re ≤ (rest v p).fst.re:= by
  unfold rest; simp only [Prod.fst_add, Prod.fst_sum,solo, Complex.add_re, Complex.re_sum]
  apply le_add_of_nonneg_right; apply sum_nonneg; intro i _
  obtain ⟨hc,hh⟩:= tall_silver p v i hp; rw [← hc]; simp only [Prod.smul_fst,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg hh (nonneg_spin _ (genuine _ hp i) (real_tiny _ hp i))

lemma key_upper (v : ι→ Train j) : Moderate (fun _ : ι=>1) fun i=>key (v i):= by
  have hh := Train.smooth_cost v (fun i=>0); simpa only [tall,key,one_pow,decay_zero] using! hh.pow 2
lemma key_lower : ∃ c:ℝ,0<c∧∀ (v : Train j) p,p∈realCube zone → c ≤ (key v p).re := by
  obtain ⟨c,hc,h⟩ := Train.smooth_lower j
  refine ⟨c^2,pow_pos hc _,fun v p hp=>?_⟩
  have he := h v p hp
  obtain ⟨hm,hb⟩:= tall_silver p v 0 hp.1
  calc
    _ ≤ ‖key v p‖ := by unfold key tall; rw [norm_pow,alias_zero_eq]; exact pow_le_pow_left₀ hc.le he 2
    _ = _ := by unfold key; rw [← hm]; simp [hb]

lemma remainder (hj : 2≤j) (v : ι → Train j) : Scale (fun _ : ι=>1) fun i=> rest (v i):=by
  unfold rest; apply Scale.ad (Scale.solo_w (spr_money hj v))
  let L:=fun i=> (v i).mass
  let s:=fun i:ι => Finset.univ.erase (0:Site (L i))
  have hm : ∃ B:ℝ,0<B ∧ ∀ i, ∑ l∈s i, decay 2 l ≤ B*1:= by
    obtain ⟨C,hc,h⟩:=decay_cost; refine ⟨C,hc,fun i=>?_⟩; rw [mul_one]; exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (s i)) fun l _ _ => (decay_pos ..).le).trans (h _)
  let π:= fun x: Σ i,{k // k∈s i}=>x.1
  let L' := L ∘ π
  let F (x : ι) (l:Site (L x)) (p: Momentum):= tall p (v x) l • reciprocalP (tiny p l)
  apply Scale.gather s (fun _ => decay 2) hm F
  let u:=fun x: Σ i,{k // k∈s i}=>x.2.val
  have hx (i): Odd (L' i).val:= (v (π i)).mass_odd
  have ht (i): u i ≠ 0:= (Finset.mem_erase.mp i.2.property).1
  have hh := (tiny_price L' hx u).reciprocal (tiny_firm _ hx _ ht) (fun i=> grade_pos _)
  refine (hh.weight ((Train.smooth_cost (v ∘ π) u).pow 2)).raise fun i=> ?_
  change decay j (u i)^2*(grade (u i))⁻¹ ≤ _
  rw [pow_two]
  refine (mul_le_of_le_one_right ?_ (inv_le_one_of_one_le₀ (grade_ge _))).trans ((mul_le_of_le_one_left (decay_pos ..).le (decay_le_one ..)).trans (decay_anti _ hj)); exact mul_nonneg (decay_pos ..).le (decay_pos ..).le
lemma pegs (v : ι → Train j) : Scale (fun _ : ι=>1) fun i=> peg (v i):=by
  have hh := tiny_price (fun i=> (v i).mass) (fun i=> (v i).mass_odd) fun i=>0
  simpa [grade,pdist] using! hh
lemma n_house (hj : 2≤j) (v : ι → Train j) : Scale (fun _ : ι=>1) fun i=> nume (v i):= by
  unfold nume
  have hA := pegs v; have hb := remainder hj v
  apply Scale.ad
  · simpa only [Pi.mul_def,one_mul] using hA.turnback.weight (key_upper v)
  simpa only [Pi.mul_def,one_pow,one_mul] using hb.weight hA.squares
lemma d_house (hj : 2≤j) (v : ι → Train j) : Moderate (fun _ : ι=>1) fun i => den (v i):= by
  unfold den; have he := key_upper v; have hu := pegs v; have hX := remainder hj v
  apply Moderate.add
  · apply Moderate.add; · simpa only [one_pow] using he.pow 2
    simpa only [Pi.mul_apply,one_mul] using (((Moderate.const (2:ℂ)).mul he).mul (hu.turnback.illuminates hX))
  simpa only [one_pow,one_mul] using (hu.squares.mul hX.squares)
end YM.QCD.Flume
