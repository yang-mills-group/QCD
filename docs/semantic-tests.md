# Four correspondence checks for the massive-QCD target

Later on November 18, the [flavor and running extension](flavor-running-tests.md) strengthened the density-rescaling bounds used in the current identities, supplied actual common witnesses for those bounds and the slope, and added two-loop/Banks–Zaks reference tests. The counts and statuses below describe this earlier four-area suite.

Review date: 18 November 2026. This extends the [initial assessment](assessment.md). The received submission and its frozen target have not been edited.

## Result and scope

The additions develop all four requested areas in Lean. They contain **33 new audited theorems** and seven separate Comparator targets. The checks establish several concrete consequences of the target, a conditional free-sector exclusion theorem, an explicit degenerate-model rejection, and controls showing why some stronger conclusions need more input.

**The full physical correspondence audit remains incomplete.** In particular, the free gauge-plus-six-Dirac field system has not been independently constructed and connected to the exclusion interface. Conventional current/mass matching and an independently specified physical running-coupling observable also remain open. Successful compilation of the tests must not be reported as completion of those missing constructions.

| Requested area | Established by the new Lean development | Remaining physical obligation |
|---|---|---|
| 1. Literal lattice-to-continuum limit | Actual normalized correlators converge along any approximating site path; a path exists and serves all insertions at a fixed configuration | No extra obligation for this separated-point assertion; distributional limits and a direct cutoff realization of each selected phase are outside this result |
| 2. Exclude the free theory | The exact `Physics.Candidate`/`Stress.unique` conditions exclude two independently detectable conserved sectors; an explicit constant-sector model is rejected | Construct the genuine free gauge/Dirac fields and verify their candidate tensors and separating probes in this interface |
| 3. Mass/current identification | Unrescaled axial/vector identities with arbitrary spectators; positive invertible rescalings; exact all-pairs fit stability and its application to target masses | Identify a conventional renormalization prescription and prove the required finite-cutoff Wilson-current residual estimates |
| 4. Coupling/UV matching | Actual cutoff stiffness has the declared logarithmic slope; coefficient arithmetic matches a stated conventional normalization; all comparison jets converge | Independently derive the perturbative coefficient and connect the coupling and comparison frames to fixed physical observables |

The compilation and Comparator receipts are linked in the [evidence index](evidence.md). There are no proof holes or additional axioms in the solution modules. Intentional holes exist only in the separately checked challenge. The run reuses the previously authenticated submission libraries and the accepted macOS environment; it is not a second clean Linux build.

**Verification completed:** all 14 modules compiled, with 37 permitted-axiom reports (33 new declarations and four repeated mass-fit declarations). All seven challenge targets then passed Comparator, Nanoda, and Lean's default kernel. The review build completed 16,265 jobs, mostly replayed dependencies; review modules were built fresh. All 7,600 staged source files, review inputs, and tools were unchanged across the run. The six recorded tool hashes also match the previous accepted review run. See the [compilation receipt](../evidence/semantic-checks/compilation/results.json) and [two-kernel receipt](../evidence/semantic-checks/comparator/result.json).

## 1. Literal convergence of normalized lattice correlators

Files: [ContinuumSpec](../checks/ContinuumSpec.lean), [ContinuumProof](../checks/ContinuumProof.lean).

`correlator_limit_along_sites` proves the following. Fix the actual sequence `C`, calibration `P`, fields `F`, and kernel `S`, with `Fields.Scaling S C P` and `Fields.Euclidean S`. For a separated configuration `x` and **any** site sequence whose physical positions tend to `x`,

$$
\operatorname{evaluation}_{C,P}(u,r,x_i;i)
\longrightarrow S_n(x)(F.\operatorname{quotient}(r_j)u_j).
$$

The left side is the supplied `Fields.Limit.evaluation`: the normalized finite Wilson/Grassmann expectation of the product of the actual calibrated physical insertions. It is not an independently chosen approximating function.

The proof chooses a compact neighborhood of `x` inside the separated-configuration set. A convergent site sequence eventually lies in this neighborhood. The target's uniform estimate controls the difference from `S` at the moving positions, and the target's smoothness supplies continuity of `S` at the limiting position. A triangle inequality then gives the literal limit. This resolves the concern that the conditional compact-set estimate might never be evaluated at any lattice configurations.

`literal_limit` obtains the site path from the target's coverage clause **before** choosing the labels, horizons, or averaging prescriptions. Thus the same path serves all those insertion choices at that configuration. `continuum_acceptance` derives the result from `YM.Massive.interacting_six`, retaining every original `TheoryAt` clause in the same `Witness`.

This is a consequence theorem, not an independent construction of `S`. It concerns separated point configurations. It does not exchange a continuum limit with integration, prove convergence across collisions, or establish convergence of lattice derivatives. Also, the kernel directly approached here is the original kernel in `TheoryAt`; the vacuum-decomposition clauses do not automatically give the same cutoff realization for each selected phase.

## 2. Stress uniqueness and free-sector exclusion

Files: [StressSpec](../checks/StressSpec.lean), [StressProof](../checks/StressProof.lean), [StressControlProof](../checks/StressControlProof.lean).

The exclusion proof uses the **actual** submitted `Physics.Candidate` predicate and the `unique` field of `Physics.Stress`. It does not replace them by a dimension claim with a similar name.

Suppose `U,V` are candidates and linear probes `p,q` satisfy

$$
p(I)=q(I)=0,\quad p(U)=1,\quad q(U)=0,\quad q(V)=1.
$$

If a stress `T` satisfied the target, both candidates would have the form

$$
U=aT+bI,\qquad V=cT+dI.
$$

Applying `p` gives `a ≠ 0`. Applying `q` to the first equation gives `q(T)=0`, while applying it to the second gives `1=0`. `two_detected_candidates_exclude_stress` proves this contradiction. The argument needs neither a presumed particle interpretation nor a nonzero connected correlation of composite fields.

`SeparateStressSectors` records seven candidate tensors and seven probes distinguishing them modulo the identity. `stress_exclusion` proves that any realization of this interface is rejected by the full stress predicate. Only two sectors are needed for the contradiction.

There are two controls. First, `sector_controls` and `sector_no_collapse` verify the exact coefficient algebra of one identity direction and seven separate sector directions. Second, `constantSectorFields` supplies a complete explicit `Fields` value with eight constant scalar components, trivial symmetry actions, and zero derivatives. Its diagonal tensors satisfy every `Candidate` clause. `constant_tensor_rotates` checks full orthogonal tensor covariance from orthogonality, and `constant_tensor_candidate` checks filtration, symmetry, parity, charge, flavor, orientation, and conservation. `stress_control_test` rejects this model using the independently established uniqueness obstruction.

**This constant-field control is not a free QCD model.** It is not claimed to satisfy the target's other field, scaling, or reconstruction clauses. Its purpose is to exercise the exact candidate interface and uniqueness test with actual data. The seven-sector coefficient space is likewise not a QFT construction.

The full free-theory benchmark remains conditional: one must construct the free gauge and six free Dirac sectors, place their separately conserved stress tensors in this precise filtration and symmetry class, and supply probes that survive the relevant quotient. The submitted free-label quotient and its finite rank results cannot be silently substituted for that construction; preservation of conservation and the field interpretation are part of what must be checked.

## 3. Current identities, mass fitting, and residual controls

Files: [CurrentSpec](../checks/CurrentSpec.lean), [CurrentProof](../checks/CurrentProof.lean), [FitStabilitySpec](../checks/FitStabilitySpec.lean), [FitStabilityProof](../checks/FitStabilityProof.lean).

### Actual unrescaled identities with spectators

`divergence_with_spectators` combines the Euclidean derivative clause with multilinearity. If `div J = c O` as fields, then for every separated configuration, every insertion slot, and arbitrary spectator fields,

$$
\sum_a \partial_{x_k^a}S_n(x;v[k\mapsto J_a])
=c\,S_n(x;v[k\mapsto O]).
$$

`current_ward_test` applies this to both the axial and vector currents using the target's **unrescaled** `trueA` and `trueV` relations. It therefore checks actual correlation identities rather than merely unfolding the definitions of `renP` and `renS`.

`normalization_test` proves that both pairwise normalization factors are strictly positive, that the rescaled pseudoscalar and scalar fields remain nonzero, and that the reciprocal rescalings recover the original fields exactly. The proof uses the actual mass-sign conditions and nonzero fields. It supplies a valid finite conversion within the submitted scheme; it does not identify that conversion with a separately specified conventional scheme.

### Stability of the actual all-pairs fit

The previous review checked the sharp stability coefficients in exact rational Python calculations. The new `fit_stability` proves the bounds universally in Lean. For arbitrary real readings, including asymmetric readings and arbitrary diagonal entries, if

$$
|b_{kl}-(r_k+r_l)|\le\delta\quad(k\ne l),\qquad \delta\ge0,
$$

then the all-pairs least-squares solution satisfies

$$
|m_i-r_i|\le\tfrac32\delta,\qquad
|(m_i-m_j)-(r_i-r_j)|\le2\delta.
$$

The proof independently expands each mass into reading coefficients. An incident ordered pair has coefficient `1/10`, another off-diagonal pair has coefficient `−1/40`, and a diagonal entry has coefficient zero. Their absolute row sum is `3/2`; a difference row has absolute sum `2`. The general estimate then follows from the triangle inequality. The explicit finite coefficient calculations use kernel-checked arithmetic tactics.

`target_fit_eq` connects the submitted fitted mass vector to the independently derived closed formula using the existing unique-minimum theorem. `target_mass_margins` applies the new bounds to the **actual** `Signals.Read` accuracy:

$$
|m_i-r_i|\le3\,\mathrm{margin}/200,\qquad
|(m_i-m_j)-(r_i-r_j)|\le\mathrm{margin}/50.
$$

### What does not follow from these checks

`small_errors_do_not_force_additive_masses` proves that the earlier synthetic, small-error reading array admits no single mass vector reproducing every off-diagonal reading as an exact sum. This is not a counterexample to the full target; it shows that its accuracy inequality alone cannot supply exact unrescaled common-mass identities.

The residual control is also exact. For

$$
f_n(x)=\frac{\sin((n+1)x)}{n+1},
$$

Lean proves the uniform bound `|f_n(x)| ≤ 1/(n+1)`, convergence of that bound to zero, and `f_n′(0)=1` for every `n`. Consequently, convergence of the correlators in check 1 does not, by itself, justify passing lattice-current derivatives to the limit. A bound controlling the relevant finite differences or compensated Wilson residual is still needed. These scalar functions are a control for that inference, not a claimed QCD countermodel.

## 4. Actual stiffness, coefficient normalization, and UV comparison

Files: [CouplingSpec](../checks/CouplingSpec.lean), [CouplingProof](../checks/CouplingProof.lean).

Write `L_i = log(1/a_i)` for the cutoff scale and `r_i` for the target's actual stiffness reading of the terminal density. `cutoff_log_diverges` proves `L_i → ∞`. `cutoff_beta_slope` transfers the target's block-history slope to the actual cutoff stages `N_i`, using their strict increase. The window gives `|r_i−β_i| ≤ ε`, and `bounded_read_preserves_slope` proves that the bounded error disappears after division by `L_i`. Thus `coupling_test` proves

$$
\frac{r_i}{\log(1/a_i)}\longrightarrow\mathrm{betaSlope}.
$$

This is a conclusion about the specified density observable, not just a check that a constant has been defined with the desired value.

The development also checks the normalization arithmetic. Using the submitted theorem that the color metric gives `su.casimir = 18`, it proves

$$
\mathrm{betaSlope}/6=2b_0,\qquad b_0=\frac{11-2\cdot6/3}{16\pi^2}
=\frac7{16\pi^2}.
$$

Here `b₀` is defined in the convention `μ dg/dμ = −b₀g³ + …`, and the factor six is the explicitly stated comparison convention `β=6/g²`. The PDG gives the equivalent one-loop coefficient in its `α_s` convention and the Wilson bare-coupling normalization. The conversion between conventions is algebraic. [PDG QCD, §9.1.1](https://pdgweb.lbl.gov/2024/reviews/rpp2024-rev-qcd.pdf), [PDG lattice QCD, §17.1.1](https://pdg.lbl.gov/2013/reviews/rpp2012-rev-lattice-qcd.pdf).

This is **not an independent loop calculation**, nor a proof that the blocked stiffness prescription is a particular conventional renormalized coupling. `CouplingTest` makes the division by six explicit; it does not hide it in a claim of physical identification.

A further exact check makes the observable distinction concrete. `regulator_body_is_wilson` proves, for every finite regulator and every gauge field,

$$
\operatorname{coef}_{\varnothing}(\rho_R(U))=\operatorname{Wilson.bare}(\beta_R,U).
$$

The Grassmann Gaussian has constant coefficient one, so this body does not depend on the bare quark masses. `terminal_body_is_wilson` transports the identity to the actual terminal density using `Run.Actual.start`. Berezin integration, by contrast, gives the determinant-weighted gauge marginal already defined in `Regulator.gaugeRate`. No equality of the two prescriptions is asserted, and the result does not remove fermion effects from blocked densities.

`uv_jet_limit` turns every compact-uniform comparison-jet clause into literal convergence at any separated point and any derivative order. It uses the same `Bases.choice` fields as the target. The elementary control `variable_basis_can_hide_amplitude` proves that a varying field normalization can exactly cancel a varying two-point amplitude. It does not show that this maneuver satisfies the full target: its purpose is to prevent treating arbitrary moving-frame comparison as an automatic identification of fixed calibrated observables.

## Updated judgment

The concrete lattice-limit concern is resolved for separated point insertions. The mass fit now has a universal Lean stability proof, the current identities have been checked with all spectators, and the stiffness slope has been connected to its actual density reading. These strengthen the interpretation of several existing clauses.

The strongest proposed conclusions in areas 2–4 remain unproved in this review. Their missing ingredients have not been added as axioms or concealed in unconditional theorem names. In particular, `StressExclusion` is explicitly conditional on `SeparateStressSectors`; the scalar residual and moving-basis controls are explicitly limited examples; and conventional coupling normalization remains a named benchmark.

The justified statement is still a checked substantial six-flavor formal construction with additional verified consequences. These results do not yet establish that every aspect of the conventional QCD identification has been independently validated, and they do not establish mass gap, confinement, or arbitrary prescribed quark masses.
