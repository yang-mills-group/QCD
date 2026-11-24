import YM.Massive.Target.Physics
import YM.Fields.System
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Statement: mixture, positive metric and real time requirements

The point kernels include all products off collisions. Require a vacuum
choice in a decomposition of *that* scaling limit. Include proper
Spin covariance and spectrum, and the realization of actual joint tempered
continuation from those kernels. No Euclidean contact prescription is used.

Not claiming an assumption like `EveryPhase.extension` or just the
analytic continuation; require the Lorentzian theory with Wightman fields.

Vacuum selection variant: decomposition with full support probability measure,
continuous separated expectations across phases, residual flavor action on that
family, and selected (also a.e.-available) Wightman realization with no further
loss of fields in the family. This specifies physical vacuum existence as in the
statement, not asking for conclusions like matching every decomposition to a
particular ground character algebra, vacuum uniqueness across decompositions,
or being able to achieve the selected correlations at a bare torus by changing BCs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive

open Function Set Filter MeasureTheory
open QCD Lattice UV
open Spectral Mink Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff ENNReal

variable {F : Massive.Fields}

structure Continuation (F : Massive.Fields) where
  W (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => F.W) (Distn (Points n))
  hol (n : ℕ) : Times n → SpacePoints n → MultilinearMap ℂ (fun _ : Fin n => F.W) ℂ

namespace Continuation
variable (C : Continuation F) (S : Fields.Kernel F)

/-- holomorphic in the complex ordered times, point restriction to Euclidean
arguments, joint tempered when approaching the boundary of zero heights. -/
structure Produces : Prop where
  together (n) (v) : ContinuousOn (fun p : Times n × SpacePoints n => C.hol n p.1 p.2 v)
      (Boundary.strict n ×ˢ univ)
  analytic (n v x) : DifferentiableOn ℂ (fun z => C.hol n z x v) (Boundary.strict n)
  euclidean n v x (y : Heights n) (h : y ∈ east n) : C.hol n (fun i => ↑(y i)*Complex.I) x v =
    S n (Boundary.place x y) v
  integrable n (y : Heights n) (h : y ∈ east n) (f : Joint n) v :
    Integrable (fun x : Points n => C.hol n (Boundary.shift x y) (Boundary.trace x) v * f x)
  tempered n (f : Joint n) v : Tendsto
    (fun y : Heights n => ∫ x, C.hol n (Boundary.shift x y) (Boundary.trace x) v * f x)
    (𝓝[east n] 0) (𝓝 (C.W n v f))
end Continuation

structure Reconstruction (F : Massive.Fields) where
  reading : Continuation F
  spin : RealSpin →* (F.W ≃ₗ[ℂ] F.W)
  space : Hilbert
  translation : Orbit space E4
  spectrum : PVM space E4
  U : RealSpin →* (space ≃ₗᵢ[ℂ] space)
  D : Submodule ℂ space
  Ω : D
  φ : F.W →ₗ[ℂ] Test4 →ₗ[ℂ] (D →ₗ[ℂ] D)

namespace Reconstruction
variable (R : Reconstruction F) (S : Fields.Kernel F)

def vector (R : Reconstruction F) : List (F.W × Test4) → R.D
  | [] => R.Ω
  | v::l => R.φ v.1 v.2 (R.vector l)

def T (g : RealSpin) (p : E4) (v : R.space) : R.space := R.translation.translation p (R.U g v)

def direction (a : Axis) (f : Test4) : Test4 := LineDeriv.lineDerivOpCLM ℂ Test4 (basis a) f

structure Theory : Prop where
  finiteOrder d p x (h : x ∈ F.level d) : R.spin p x ∈ F.level d
  fundamental x : Continuous fun p => R.spin p x
  representation (u v : RealSpin) (x : F.W) : R.spin (u*v) x=R.spin u (R.spin v x)
  spatial (p : EuPin) (h : Lorentz.spatialTurn p.coord) (q : RealSpin)
      (t : q.coord = Lorentz.room p.coord h) (e : q.matrix=p.matrix) : R.spin q = F.action p
  boost i (p) (h : RealSpin.Path i p) v : HasDerivAt (fun t => R.spin (p t) v)
      ((-Complex.I) • F.lie (Ortho.plane timeAxis i.castSucc) v) 0
  conjugate q (v : F.W) : R.spin q (F.adj timeAxis v)= F.adj timeAxis (R.spin q v)
  parity q v : R.spin q (F.parity v) = F.parity (R.spin q v)
  graded q (h : q.coord=1) (hq : q.matrix= -1) : R.spin q = F.parity
  unit : ‖R.Ω.val‖ = 1
  separable : TopologicalSpace.SeparableSpace R.space
  dense : Dense (R.D : Set R.space)
  cyclic : R.D = Submodule.span ℂ (Set.range fun x : List (F.W × Test4) => (R.vector x).val)
  continuousOrbit (x : R.space) : Continuous (fun p : RealSpin × E4 => R.T p.1 p.2 x)
  action (u v : RealSpin) (p q : E4) (x : R.space) : R.T u p (R.T v q x) = R.T (u*v) (u.coord.act q + p) x
  ground u p : R.T u p R.Ω = R.Ω.val
  stays p b (x : R.D) : R.T p b x.val ∈ R.D
  covariance p b v f (x : R.D) : R.T p b (R.φ v f x).val =
    (R.φ (R.spin p v) (Joint.push ⟨p.coord,b⟩ f) (⟨R.T p b x.val,stays p b x⟩ : R.D)).val
  spectrum : R.translation.Spectrum R.spectrum
  forward : R.spectrum.region coneᶜ = 0
  unique v : (∀ p, R.translation.translation p v = v) → ∃ c : ℂ, v = c • R.Ω.val
  opens : R.reading.Produces S
  vacuum (n : ℕ) (u f) : inner ℂ R.Ω.val (R.vector (List.ofFn fun i => (u i,f i))).val =
      R.reading.W n u (Joint.materialize n f)
  tempered v (x : R.D) : Continuous (fun f => (R.φ v f x).val)
  star v f (x y : R.D) : inner ℂ (R.φ v f x).val y.val = inner ℂ x.val (R.φ (F.adj timeAxis v)
      (Probe.bar f) y).val
  faithful : Injective R.φ
  commute v u p q (h : F.homogeneous p v) (g : F.homogeneous q u) f j
      (hf : Boundary.Fields.causal f j) (x : R.D) :
    R.φ v f (R.φ u j x) = (if p && q then (-1:ℂ) else 1) • R.φ u j (R.φ v f x)
  derivative v f i : R.φ (F.partialD i v) f =
    (-(if i=timeAxis then Complex.I else 1)) • R.φ v (direction i f)
  scalarUnit (f : Test4) : R.φ F.unit f = (∫ y, f y) • LinearMap.id

end Reconstruction

structure Vacua (F : Massive.Fields) where
  X : Type
  [ab : MetricSpace X]
  [m : MeasurableSpace X]
  [borel : BorelSpace X]
  [compact : CompactSpace X]
  μ : Measure X
  flavor : FlavorTorus →* Equiv.Perm X
  ensemble : X → Fields.Kernel F
  chosen : X
attribute [instance] Vacua.ab Vacua.m Vacua.borel Vacua.compact

namespace Vacua

variable (P : Vacua F)

structure Decomposes (S : Fields.Kernel F) (T : Momentum F) (X : Bases F) : Prop where
  accessible : IsProbabilityMeasure P.μ
  support : ∀ U : Set P.X, IsOpen U → U.Nonempty → 0 < P.μ U
  euclidean x : Fields.Euclidean (P.ensemble x)
  continuous n (x : Points n) (h : x ∈ conf n) v : Continuous (fun p => P.ensemble p n x v)
  preserves n (x : Points n) (h : x ∈ conf n) v : S n x v = ∫ p, P.ensemble p n x v ∂P.μ
  readable n (x : Points n) (h : x ∈ conf n) v : Integrable (fun p => P.ensemble p n x v) P.μ
  compare p : X.Comparison (P.ensemble p)
  ward p : Physics.Ward T (P.ensemble p)
  acts : Continuous (fun p : FlavorTorus × P.X => P.flavor p.1 p.2)
  transport p : MeasurePreserving (P.flavor p) P.μ P.μ
  related n (x : Points n) (h : x ∈ conf n) v p u : P.ensemble (P.flavor p u) n x (F.flavor p ∘ v) =
    P.ensemble u n x v
  typical : ∀ᵐ p ∂P.μ, ∃ R : Reconstruction F, R.Theory (P.ensemble p)
  success : ∃ R : Reconstruction F, R.Theory (P.ensemble P.chosen)
end Vacua
end YM.Massive
