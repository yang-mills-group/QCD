import YM.Massive.Target.Labels

/-!
# Statement: comparison system fixed independently of the limit

Free linear equations for the generators (Maxwell reuse, and massless
column and row slash equations), imposed even inside the polynomials.
Then project the entire invariant space. This specifies the meaning of
"rank W_D^0"; not an assumption identifying ranks, relations or fields.

Reference correlations: the Wick system on the full graded label space,
on separated points only. For readability specified with the off-shell labels;
require in the final statement a measurement through these formulas that factors
precisely through the free linear equations (`projection`), and that these
formulas actually detect that rank. So e.g. it wouldn't suffice to set some
of the Wick comparisons to zero or restrict the type of labels to a subspace
chosen by the limiting theory.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free
open QCD QCD.Lat QCD.Grass TensorProduct Lattice Function
open scoped Topology TensorProduct BigOperators Matrix.Norms.Frobenius Matrix

variable {d n : ℕ}

def AtNext (a : Axis) (p q : Multi d) := power q = update (power p) a (power p a + 1)

open scoped Classical in
def slashCol (i : SpinMode d) : Seed (Pairs (SpinMode d)) :=
  ∑ a : Axis, ∑ s : Pinor, ∑ q : Multi d,
    if AtNext a i.1.1 q then
      gamma a i.1.2.1 s • thetaBasis _ (Sum.inl ((q,s,i.1.2.2),i.2)) else 0

open scoped Classical in
def slashBar (i : SpinMode d) : Seed (Pairs (SpinMode d)) :=
  ∑ a : Axis, ∑ s : Pinor, ∑ q : Multi d,
    if AtNext a i.1.1 q then
      gamma a s i.1.2.1 • thetaBasis _ (Sum.inr ((q,s,i.1.2.2),i.2)) else 0

def slashEq (d : ℕ) := Submodule.span ℂ
  (Set.range (@slashCol d) ∪ Set.range (@slashBar d))

def reduceEq : Pol d →ₗ[ℂ] Maxwell.WickPol su ⊗[ℂ]
    ExteriorAlgebra ℂ (Seed (Pairs (SpinMode d)) ⧸ (slashEq d)) :=
  TensorProduct.map Maxwell.reduceEq.toLinearMap (ExteriorAlgebra.map (slashEq d).mkQ).toLinearMap

def observable : Label d →ₗ[ℂ] Maxwell.WickPol su ⊗[ℂ]
    ExteriorAlgebra ℂ (Seed (Pairs (SpinMode d)) ⧸ (slashEq d)) := reduceEq.comp (labels d).subtype

def freeLabels (d : ℕ) := LinearMap.range (@observable d)

abbrev Symbol (d : ℕ) := ↥(freeLabels d)

def projection : Label d →ₗ[ℂ] Symbol d := observable.rangeRestrict

theorem onto : Surjective (@projection d) := LinearMap.surjective_rangeRestrict _
instance (d : ℕ) : FiniteDimensional ℂ (Symbol d) := FiniteDimensional.of_surjective (V := Label d) projection onto

/-- dirac(s,t,x) unbarred s at x, barred t at 0. -/
def dirac (s t : Pinor) (x : E4) : ℂ :=
  - ∑ a : Axis, gamma a s t * ((YM.Analysis.D (basis a) Maxwell.Green x : ℝ) : ℂ)

def steps (p : Multi d) := (List.finRange 4).flatMap fun a => List.replicate (power p a) a

def derivatives (l : List Axis) (f : E4 → ℂ) : E4 → ℂ := l.foldr (fun a u => YM.Analysis.D (basis a) u) f

def leg {d e : ℕ} (v : SpinMode d) (q : SpinMode e) (x y : E4) : ℂ :=
  if v.1.2.2=q.1.2.2 ∧ v.2=q.2 then
    (-1:ℂ) ^ (steps q.1.1).length *
      derivatives (steps v.1.1 ++ steps q.1.1) (dirac v.1.2.1 q.1.2.1) (x-y) else 0

abbrev Occ (u : Fin n → ℕ) := (i : Fin n) × Pairs (SpinMode (u i))

def pair {u : Fin n → ℕ} (x : Points n) (i j : Occ u) : ℂ := if i.1 = j.1 then 0 else
  Sum.elim (fun v => Sum.elim (fun _ => 0) (fun q => leg v q (x i.1) (x j.1)) j.2)
    (fun v => Sum.elim (fun q => -leg q v (x j.1) (x i.1)) (fun _ => 0) j.2) i.2

/-- Recurrence pairing first letter with each later one, alternating.
Fuel only for recursion; never called with fuel less than the number of letters. -/
def pf {T : Type} (C : T → T → ℂ) : ℕ → List T → ℂ
 | _, [] => 1
 | 0, _::_ => 0
 | t+1, p::l => ∑ i : Fin l.length, (-1 : ℂ)^i.val * C p (l.get i) * pf C t (l.eraseIdx i)

def atomList {T : Type*} [Fintype T] (s : Finset T) : List T := List.ofFn (Grass.expression s).choose

def basisU (d : ℕ) : Module.Basis (PowerPair d) ℂ (Pol d) :=
  (MvPolynomial.basisMonomials (Labels.Key su) ℂ).tensorProduct (Grass.blades (Pairs (SpinMode d)))

def monomialValue {u : Fin n → ℕ} (x : Points n) (p : (i : Fin n) → PowerPair (u i)) : ℂ :=
  let l := (List.finRange n).flatMap fun i => (atomList (p i).2).map (fun a => (⟨i,a⟩ : Occ u))
  Maxwell.Wick.moment su x (fun i => Maxwell.reduceEq (MvPolynomial.monomial (p i).1 1)) * pf (pair x) l.length l

def moment (u : Fin n → ℕ) (x : Points n) : MultilinearMap ℂ (fun i => Pol (u i)) ℂ :=
  Multilabel.ofBasis (fun i => basisU (u i)) (monomialValue x)

def wick (u : Fin n → ℕ) (x : Points n) : MultilinearMap ℂ (fun i => Label (u i)) ℂ :=
  (moment u x).compLinearMap fun i => (labels (u i)).subtype

end YM.Massive.UV.Free
