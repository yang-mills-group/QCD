import YM.QCD.Flume.Pole

/-! # Uniform regularity of the free trajectory and real-momentum tests -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}

lemma pen (v : Train j): peg v 0 = 0 := by simp [peg,tiny,alias_zero_eq,narrow]
lemma den_origin (v : Train j): den v 0 = 1:= by simp [den,pen,key,tall,alias_zero_eq,narrow,chipper,beam,turn]
@[simp] lemma Dir_nil (v : Train j): Dir v 0=0:=by simp [Dir,nume,pen,chipper,turn]
lemma high_nil (j : ℕ) : Finset.univ.erase (0:Site (Train.top j).mass) = ∅:=by
  letI : Subsingleton (Site 1):=inferInstanceAs (Subsingleton (Axis → ZMod 1))
  ext i; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false]; exact fun h=>h (Subsingleton.elim (α:=Site 1) ..)
lemma seat (j : ℕ) p : rest (.top j) p=0:=by simp [rest,high_nil,spr,Train.nozzle,stripsum,solo]
lemma seat_den (j : ℕ) p : den (.top j) p=1:=by simp [den,key,tall,seat,beam]
lemma Dir_top (j : ℕ) p : Dir (.top j) p=kernel p := by rw [Dir,seat_den]; simp [nume,seat,key,tall,peg,tiny,Train.mass]; change kernel (aliasAt p (0: Site 1))=_; rw [alias_zero_eq]; simp [narrow]

lemma num_gain (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J) (p : Momentum) (hp : physical p) :
    let V:=Train.hop P h h' v
    (chipper V p).re ≤ (nume V p).fst.re := by
  intro V; have he : 1≤(rest V p).fst.re:= (whole_bid P v p hp).trans (respect V p hp)
  have hu : 0≤(key V p).re := (tall_silver _ V _ hp).2
  have hi := genuine p hp (0:Site V.mass)
  have hπ : 0≤(chipper V p).re := hi.quad_ge
  have hz := real_tiny p hp (0:Site V.mass)
  have heq : ((key V p).re:ℂ)=key V p := (tall_silver _ V _ hp).1
  change (chipper V p).re ≤ (nume V p).fst.re
  unfold nume; rw [← heq, ← show ((chipper V p).re:ℂ)=chipper V p from hi.quad_cast]
  simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,Complex.add_re, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,turn]
  exact (le_mul_of_one_le_right hπ he).trans (le_add_of_nonneg_left (mul_nonneg hu hz))
lemma den_gain (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J) (p : Momentum) (hp : p∈realCube zone) :
    let V:= Train.hop P h h' v; (chipper V p).re ≤ (den V p).re := by
  intro V; by_cases he:p=0
  · subst p; simp only [chipper,pen,quad_zero,den_origin,Complex.zero_re,Complex.one_re]; norm_num
  have hh := (num_gain _ h h' v p hp.1)
  change (chipper V p).re ≤ _ at hh
  have hx : 0 < (chipper V p).re:= lt_of_lt_of_le (mul_pos (pow_pos meter.low_pos _) (lengthSq_pos he)) (charge_below p hp)
  have hu := (pow_le_pow_left₀ hx.le hh 2).trans ((real_num V p hp.1).first)
  rw [form_den] at hu
  rw [pow_two, ← show ((chipper V p).re:ℂ)=chipper V p from (genuine _ hp.1 (0:Site V.mass)).quad_cast] at hu
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hu
  exact le_of_mul_le_mul_left hu hx
lemma sparkling (v : Train j) (p : Momentum) (hp : p∈realCube zone) : 0 < (den v p).re:=by
  rcases v with j|⟨P,h,h',v⟩
  · rw [seat_den]; exact one_pos
  by_cases he:p=0
  · rw [he,den_origin]; exact one_pos
  exact ((mul_pos (pow_pos meter.low_pos _) (lengthSq_pos he)).trans_le (charge_below p hp)).trans_le (den_gain _ h h' v _ hp)
lemma shining (v : Train j) (p : Momentum) (hp : p∈realCube zone) : den v p ≠ 0:=fun h=> by simpa [h,Complex.zero_re] using sparkling v p hp

lemma near_peg (v : Train j) (p : Momentum) (hp : p∈realCube zone) : (meter.low*‖p‖)^2 ≤ (chipper v p).re:=by
  apply le_trans _ (charge_below p hp)
  have hx : ‖p‖^2 ≤ lengthSq p := by
    obtain ⟨i,h⟩ : ∃ i, ‖p‖=‖p i‖ := by
      rw [← coe_nnnorm]; change ∃ i, ↑(univ.sup fun i=>‖p i‖₊)=(‖p i‖:ℝ)
      obtain ⟨i,_,he⟩:=Finset.exists_mem_eq_sup univ univ_nonempty fun i=> ‖p i‖₊; exact ⟨i,by rw [he]; rfl⟩
    rw [h]; exact single_le_sum (fun j _=> sq_nonneg ‖p j‖) (mem_univ i)
  rw [mul_pow]; exact mul_le_mul_of_nonneg_left hx (sq_nonneg _)

lemma stable_den (hj : 2≤j) : ∃ η c : ℝ,0<η ∧ η≤zone ∧ 0<c ∧ ∀ (v : Train j) p,p∈realCube η → c ≤ (den v p).re := by
  obtain ⟨η,C,he,hc,h⟩:=d_house hj (fun i : Train j=>i)
  let θ:= min (η/4) zone
  have hθ:0<θ:= lt_min (by positivity) zone_pos
  have hu : θ≤zone:= min_le_right ..
  let t:=η/2; have ht:0<t:=by dsimp[t]; linarith
  let R:= (C+1)/t; have hr:0<R:=by dsimp[R]; positivity
  let b:= min (t/2) ((2*R)⁻¹); have hb : 0<b:= lt_min (by positivity) (by positivity)
  have hi : 0 < (meter.low * b)^2 := pow_pos (mul_pos meter.low_pos hb) _
  refine ⟨θ,min (1/2) ((meter.low*b)^2),hθ,hu,lt_min (by norm_num : (0:ℝ)<1/2) hi,fun v p hx=>?_⟩
  by_cases hl : ‖p‖≤ b
  · have h0:=cube_zero θ hθ
    have hT : ball (0: Momentum) t ⊆ cube η := (Metric.ball_subset_ball (show t ≤ η-θ from by have hh : θ≤η/4:=min_le_left ..; unfold t; linarith)).trans (ball_inside_cube h0)
    have hg : p∈ ball (0: Momentum) t:=by rw [Metric.mem_ball,dist_zero_right]; have he : b≤t/2:=min_le_left ..; linarith
    have hz (p) (hy:p∈ball (0:Momentum) t) : dist (den v p) (den v 0)≤ C+1:=by
      rw [dist_eq_norm]
      refine (norm_sub_le ..).trans (add_le_add ?_ ?_); · simpa using (h v).bound p (hT hy)
      rw [den_origin,norm_one]
    have hj := Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun p hy=> ((h v).hol p (hT hy)).differentiableWithinAt) (fun x hv=> Metric.mem_closedBall.mpr (hz _ hv)) hg
    change dist (den v p) (den v 0) ≤ R*dist p (0:Momentum) at hj
    rw [den_origin, dist_zero_right,dist_eq_norm] at hj
    have H := (Complex.abs_re_le_norm _).trans hj
    rw [Complex.sub_re,Complex.one_re] at H
    have hy : R*‖p‖ ≤ 1/2:= (mul_le_mul_of_nonneg_left (hl.trans (min_le_right ..)) hr.le).trans (le_of_eq (by field_simp))
    exact (min_le_left ..).trans (by linarith [(abs_le.mp (H.trans hy)).1])
  rcases v with _|⟨P,hz,h',v⟩
  · rw [seat_den]; exact (min_le_left ..).trans (by norm_num)
  have hx := realCube_mono hu hx
  exact (min_le_right ..).trans (((pow_le_pow_left₀ (mul_pos meter.low_pos hb).le (mul_le_mul_of_nonneg_left (le_of_not_ge hl) meter.low_pos.le) _).trans (near_peg _ _ hx)).trans (den_gain _ hz h' v p hx))
lemma Dir_budget (hj : 2≤j) (v : ι→Train j) : Scale (fun _ : ι=>1) fun i=> Dir (v i) := by
  have hu : Firm (fun _ : ι=>1) fun i=>den (v i):= by
    obtain ⟨η,c,hp,-,hc,h⟩:=stable_den hj; exact ⟨η,c,hp,hc,fun i p hx=> (mul_one _).trans_le ((h _ p hx).trans (Complex.re_le_norm _))⟩
  have he := (n_house hj v).turnback.weight ((d_house hj v).inv hu fun _=>one_pos)
  change Scale _ fun i p=> _
  simpa only [inv_one,mul_one,Pi.mul_def,Dir] using! he

lemma size_q (hj : 2≤j): ∃ η c : ℝ,0<η ∧ η≤zone ∧ 0<c ∧ ∀ (v : Train j) p,p∈realCube η →
    c*lengthSq p ≤ (quad (Dir v p)).re ∧ c*lengthSq p ≤ (Dir v p).1.re:= by
  obtain ⟨η,C,hp,hc,H⟩:=d_house hj (fun i : Train j=>i)
  let b:=meter.low^2
  have hb : 0<b:=pow_pos meter.low_pos _
  let θ:= min η zone; have hθ : 0<θ:= lt_min hp zone_pos
  refine ⟨θ,min (b/C) (b/2),hθ,min_le_right ..,lt_min (div_pos hb hc) (by positivity),fun v p hx=>?_⟩
  have he := (H v).bound p (mem_cube_real (realCube_mono (show θ≤η from min_le_left ..) hx) hp)
  have h : (den v p).re≤C := (Complex.re_le_norm _).trans (by simpa only [mul_one] using he)
  have hZ : p∈realCube zone := realCube_mono (min_le_right ..) hx
  have hs : 0 < (den v p).re:= sparkling v p hZ
  have ha := real_den v p hx.1
  have hL : 0 ≤ lengthSq p:= sum_nonneg fun _ _=> sq_nonneg _
  have hk := charge_below (L:=v.mass) p hZ
  have hm : min (b/C) (b/2)*lengthSq p ≤ (chipper v p).re/(den v p).re := by
    refine (mul_le_mul_of_nonneg_right (min_le_left ..) hL).trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hc hs]; rw [mul_comm _ C]
    exact mul_le_mul_of_nonneg_right hk hc.le |>.trans' (mul_le_mul_of_nonneg_left h (mul_nonneg hb.le hL)) |>.trans (le_of_eq (by ring)) -- adjust
  constructor
  · rw [form_dir,← ha, ← Complex.ofReal_inv,Complex.mul_re]; simpa only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,div_eq_mul_inv] using hm
  rcases v with _|⟨P,hz,h',v⟩
  · rw [Dir_top]
    have he := (divisor_real_bounds 1 hZ).1
    rw [← chip_gap,Complex.mul_re] at he
    simp only [Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at he
    exact (mul_le_mul_of_nonneg_right (min_le_right ..) hL).trans (by dsimp[b]; linarith)
  have hf := num_gain _ hz h' v p hx.1
  rw [Dir, ← ha,← Complex.ofReal_inv,Prod.smul_fst,smul_eq_mul,Complex.mul_re]; simp only [turn,Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero, inv_mul_eq_div]
  exact hm.trans (div_le_div_of_nonneg_right hf hs.le)
end YM.QCD.Flume
