# Flavor dependence, two-loop running, and Banks–Zaks tests

**Review phase complete:** see the [final results and checks summary](results-summary.md). Deriving the physical two-loop coefficient from the constructed theory is deferred to later work; the completed reference tests below do not supply that derivation.

18 November 2026. This extends the [earlier assessment](assessment.md) and [four correspondence tests](semantic-tests.md). It distinguishes consequences of the received source from independent perturbative benchmarks.

**The source has meaningful one-loop flavor dependence. This review has not established its physical two-loop beta function or a Banks–Zaks quantum field theory.** The final existence theorem remains a six-flavor, positive-mass statement. A planning inequality in the construction also prevents directly extending that particular estimate to the integer Banks–Zaks benchmark range.

The first new suite contains **71 new audited Lean declarations**, with 11 previously checked declarations repeated as dependencies. Its 22 modules and twelve challenge targets passed fresh compilation, Comparator, Nanoda, and Lean; an unchanged control and nine deliberate mutations behaved as expected. The [Comparator receipt](../evidence/flavor-checks/comparator/result.json) records 193.57 seconds and unchanged inputs.

A second suite adds **39 new declarations** about differential sensitivity, global reference-flow dynamics below the fixed point, scheme transformations, and an actual six-flavor witness. Its combined fresh compilation passed 147 declaration audits across 46 modules. The density-reading and scheduling controls add seven declarations; the remainder-robustness suite adds another ten. A last nine-declaration extension sharpens the actual density-normalization bound using symmetry and mass separation. The added kernel and mutation checks have separate receipts. All runs reuse the authenticated submission build on the accepted macOS setup; they are not another clean submission build or a Linux isolation run.

## What flavor dependence is actually present

The submission's `YM.QCD.Matter` proves the trace identity for its actual fundamental/antifundamental Weyl slots. Its index is `leftT F = 6 F` in its chosen metric, and

$$
\frac{\operatorname{bTrace}(N_f)}6=11-\frac{2N_f}3.
$$

`YM.QCD.Raft.Roads` contains the corresponding running-coordinate coefficient

$$
\operatorname{betaQ}(N_f)=\frac{3}{4\pi^2}\left(11-\frac{2N_f}3\right).
$$

[FlavorProof](../checks/FlavorProof.lean) connects these actual definitions to independently named conventional coefficients, verifies the decrement of $1/(2\pi^2)$ per added flavor, and proves positivity exactly for integer $N_f\leq16$. The six-flavor coefficient in the frozen target is exactly `betaQ 6` in value, or $21/(4\pi^2)$.

This is more than a stand-alone trace formula. The submission's `Pearl.wilson` bounds a normalized second derivative of the real logarithm of the free Wilson determinant by its logarithmic leading term, with a bounded remainder. [ScreeningProof](../checks/ScreeningProof.lean) extracts the literal large-box limit

$$
\frac{\text{fermionResponse}(C,n)}{\log n}
\longrightarrow \frac1{2\pi^2},\qquad \|C\|=1.
$$

The auxiliary plan is constructed from the source's existence lemma; it is not left as an uninstantiated assumption. A separate theorem supplies an actual unit color direction, so this universal response test is nonvacuous.

[FlavorDeterminantProof](../checks/FlavorDeterminantProof.lean) checks the full block determinant for $N_f$ identical free Wilson flavors. It proves that its logarithmic response is exactly $N_f$ times the single-flavor response, including the zero-flavor case and the increment from one additional flavor. This checks determinant multiplicity, not just multiplication of a named coefficient. The identical-flavor benchmark is auxiliary: it does not satisfy the final target's distinct-mass condition.

[BodyScopeProof](../checks/BodyScopeProof.lean) makes a further distinction explicit. At the microscopic regulator, two models with the same bare gauge parameter have exactly the same scalar Grassmann body and the same `Stiffness.read`, even if their flavor counts, bare masses, and seam positions differ. Berezin integration instead retains the full product of Wilson determinants. This is the expected bare-action distinction, not evidence that the theory omits fermions. It explains why the cutoff body reading alone is not an independent measurement of the interacting physical beta function. The theorem is restricted to the microscopic regulator; it does not assert flavor blindness of all blocked densities.

These are frozen-background, free-fermion determinant calculations and algebraic links to the running-coordinate coefficient. They do not independently identify a renormalized physical coupling in the interacting continuum theory. The source itself marks the determinant calculation's one-loop scope; [authenticated excerpts](../evidence/flavor-checks/source-scope.json) preserve that qualification.

## Why the leading slope does not establish two loops

Use the convention

$$
a=\frac{g^2}{16\pi^2},\qquad
\frac{da}{d\log\mu}=-2a^2(B_0+B_1a+\cdots),
\quad B_0=11-\frac{2N_f}{3},\quad B_1=102-\frac{38N_f}{3}.
$$

These benchmark coefficients agree with the primary calculation in [Larin and Vermaseren, equations (1) and (10)](https://arxiv.org/pdf/hep-ph/9302208). Their derivative is with respect to $\log\mu^2$; our convention explains the factor two. The coefficients are supplied as reference formulas in this review, not derived from Feynman diagrams in Lean.

The submitted `Sequence.Slope` fixes a ratio to a leading logarithm. With $t=\log(\mu/\Lambda)$, [TwoLoopProof](../checks/TwoLoopProof.lean) proves for **every real $k$** that

$$
w_k(t)=A t+k\log t,\qquad
\frac{w_k(t)}t\longrightarrow A,
\qquad
\frac{w_k(t)-At}{\log t}\longrightarrow k.
$$

For $A>0$, these curves are eventually positive. Different $k$'s give incompatible second limits despite the same first limit. This is a formal demonstration of insufficiency of a leading-slope condition. It is **not** a construction of alternative models satisfying every clause of the QCD target.

Writing $b_0=B_0/(16\pi^2)$, $b_1=B_1/(16\pi^2)^2$, the convention $w=6/g^2$ gives

$$
\frac{dw}{dt}=12b_0+\frac{72b_1}{w},
\qquad
k=\frac{6b_1}{b_0}.
$$

[RunningConventionProof](../checks/RunningConventionProof.lean) verifies the chain rules from the specified two-loop equation for $g$ to those for $a$ and $w$. For six flavors, the expected log-log coefficient is $39/(28\pi^2)$. The review proves this value and a next-order flow detector; it does not prove that the submitted trajectory has this coefficient.

There is now a concrete missing proposition, `TwoLoopPath`, in [TwoLoopSpec](../checks/TwoLoopSpec.lean): subtract the target's leading term from its cutoff coupling and divide by the logarithm of the cutoff log scale. Require convergence to $39/(28\pi^2)$. The new theorem `two_loop_stiffness_bridge` proves that **if** this additional proposition holds, the target's bounded stiffness error transfers the same second-order limit to the actual cutoff stiffness reading. Thus bounded observable errors would not obstruct this test; the missing input is the second-order running theorem, followed by the physical coupling identification.

The second-order ratio is necessary evidence, but still does not determine a differential beta function. [DifferentialRunningProof](../checks/DifferentialRunningProof.lean) proves that

$$
w(t)=At+k\log t+e\sin t
$$

has the same first and second asymptotic coefficients. For $A>0$, $k\geq0$, and $0<e<A$, its derivative is positive for every $t>0$, yet has no finite limit: subsequences retain the distinct values $A+e$ and $A-e$. Thus even monotonicity and both coefficient limits are insufficient without derivative or finite-scale control. This is again a scalar control, not a countermodel to the complete QCD target. It applies in particular to the positive six-flavor log-log benchmark.

The bounded source audit also inspected the accumulated running estimates. `Reference/Scaling.toll` controls a deviation from one-loop running by $m(D+2)+N_fW'$ on a fixed-stride run; its `within` lemma extracts slope accuracy. The later `VStages/Settlement.Track.checks` and `flight_meter` similarly control cumulative errors relative to the leading scale. These bounds, as inspected, do not exhibit an extracted coefficient multiplying the required log-log term. The authenticated excerpts record their exact quantifiers; this is a bounded audit, not an assertion that every consequence of the entire source has been classified.

The variable-stride estimate is particularly explicit. With $t_i=\log\operatorname{den}(i)$, `Track.checks` bounds

$$
|v_i-(x+\operatorname{betaQ}(N_f)t_i)|
\leq \operatorname{net}(i)+(3+N_f)i+1+2N_f A.
$$

Here `net` sums the gauge-step allowances, while the determinant contributions telescope through `Survey.account` and `Survey.sum_toll` in `VStages/Revolves.lean`. The proof makes the displayed error negligible relative to $t_i$. A two-loop extraction instead needs its behavior relative to $\log t_i$, together with derivative or finite-scale control for the physical coupling. The inspected estimate does not supply that stronger comparison. It therefore supports the leading flavor coefficient without deciding whether the actual subleading term is zero or nonzero.

The exact density and blocking equations contain interactions beyond this leading description. **Not extracting a two-loop coefficient is not evidence that the actual two-loop effect vanishes.**

A text search of all 7,594 authenticated `YM` modules found no explicit Banks–Zaks/two-loop-labelled result. Its one match is an unrelated variable sequence `second loopBound`. This search is only an inspection aid. The precise reason not to claim two-loop verification is the unproved `TwoLoopPath`/coupling bridge, not the absence of a keyword.

## Banks–Zaks: what the tests prove

[BanksZaksProof](../checks/BanksZaksProof.lean) classifies the specified two-loop polynomial. With $B_0>0$, a positive nonzero zero exists exactly for integer

$$
9\leq N_f\leq16,\qquad a_\ast=-\frac{B_0}{B_1}.
$$

It proves uniqueness among positive zeros, the beta-function signs on either side, a positive derivative at the zero, and $a_\ast\to0$ as the real flavor parameter approaches $33/2$. The latter is a formal continuous-parameter limit, not a family of theories with fractional numbers of quarks. The physical setting of the original proposal is massless vector-like gauge theory; see [Banks and Zaks (1982)](https://doi.org/10.1016/0550-3213(82)90035-9).

The later tests close the global-existence hypothesis of the initial reference-flow test. [BZExistenceProof](../checks/BZExistenceProof.lean) constructs a global solution for **every** initial value $0<a(0)<a_\ast$. It remains in that interval, tends to $a_\ast$ in the IR, and tends to zero in the UV. The construction inverts the strictly increasing, surjective map $X\mapsto X+c\log X$ on positive $X$, where $c=-B_1/B_0>0$. It does not assume a global solution or import a numerical integration.

[BZInvariantProof](../checks/BZInvariantProof.lean) proves uniqueness within this interval and the exact finite-scale identity

$$
H(a(t))-H(a(s))=2B_0(t-s),\qquad
H(a)=a^{-1}-c+c\log(a^{-1}-c).
$$

[BZAsymptoticProof](../checks/BZAsymptoticProof.lean) then **derives** the leading and log-log coefficients from the ODE, rather than inserting them into an ansatz. For $w=6/(16\pi^2a)$,

$$
\frac{w(t)}t\to12b_0,\qquad
\frac{w(t)-12b_0t}{\log t}\to\frac{6b_1}{b_0}.
$$

[BZCriticalProof](../checks/BZCriticalProof.lean) also proves the logarithmic IR approach rate and the limit of its derivative:

$$
\frac{\log(a_\ast-a(t))}{t}\longrightarrow\lambda,
\qquad
\frac{d}{dt}\log(a_\ast-a(t))\longrightarrow\lambda,
\quad t\to-\infty,
\qquad \lambda=-2B_1a_\ast^2>0.
$$

At sixteen flavors this reference exponent is $1/453$, illustrating the slow approach in logarithmic scale. All of these are theorems about the specified two-loop scalar equation. They neither construct a massless QFT nor supply its nonperturbative beta function.

| Flavors | $B_0$ | $B_1$ | Two-loop $a_\ast$ | Illustrative $\alpha_\ast=4\pi a_\ast$ |
|---:|---:|---:|---:|---:|
| 6 | 7 | 26 | No positive zero | — |
| 9 | 5 | −12 | 5/12 | 5.2360 |
| 12 | 3 | −50 | 3/50 | 0.7540 |
| 15 | 1 | −88 | 1/88 | 0.1428 |
| 16 | 1/3 | −302/3 | 1/302 | 0.04161 |

The rational statements are proved in Lean or follow from its specified polynomial; the decimal column is illustrative floating-point evaluation. The [reference table](../evidence/flavor-checks/flavor-benchmarks.json) records all integer flavor counts from zero through seventeen. A positive zero at large coupling is not evidence of a controlled perturbative fixed point. The table's integer range must not be reported as a proven nonperturbative conformal window.

## A restriction in the current construction

The source's `Stratum.Burg.perimeter` uses

$$
\frac{\operatorname{su.slopeConstant}}2 < \operatorname{betaQ}(N_f).
$$

Lean proves that this is equivalent to $N_f\leq8$ for natural flavor counts. `Page.Steppes.canopyR` also has an explicit $N_f\leq8$ assumption. More directly, the later variable-stride scheduling interface `MarchQ.Earlier` in `YM/VStages/Settlement.lean` requires $0<\delta_0(N_f)$, with $\delta_0=\operatorname{betaQ}-\operatorname{su.slopeConstant}/2$. [ScheduleBudgetProof](../checks/ScheduleBudgetProof.lean) proves that **any instance** of that interface has at most eight flavors. Its `Track.slope_all` is used when assembling `Sequence.Path` in `YM/Parishes/Caves.lean`. Consequently **none** of the integer two-loop Banks–Zaks cases satisfies that trajectory-budget inequality.

A [declaration-graph diagnostic](../evidence/flavor-checks/dependency-paths/result.json) locates this interface inside the accepted theorem's dependencies: `interacting_six → Mako.meru → JuneP.Saga → roamΘ → Earlier`. It also finds the later `Track.slope_all`, `Track.perimeter`, `Track.Survey.sum_toll`, `Raft.calibrated`, and `Pearl.docket`. The simpler `Pearl.wilson` corollary used by our free-response test is not itself in that restricted closure; the general endpoint calculation is. The inspection follows constants in declaration types and values, so it is a compiler-environment diagnostic, not a proof that every assumption is mathematically indispensable.

This is a limitation of the displayed planning estimate. It is not a no-go theorem for other constructions, a contradiction in the six-flavor result, or a claim that every source lemma needs $N_f\leq8$. Extending the result to the Banks–Zaks regime needs a different estimate and a flavor-parameterized, massless target; changing `6` to `16` is not justified by the generic one-loop formula.

Positive masses also matter. The target requires six positive distinct scheme masses, while the fixed-point benchmark keeps its flavors massless. The [PDG QCD review, §9.1.1](https://pdgweb.lbl.gov/2024/reviews/rpp2024-rev-qcd.pdf) distinguishes active light flavors and heavy-flavor threshold matching. This review has not proved a decoupling theorem or massless limit for the submitted construction. Its fixed ultraviolet flavor coefficient is not a demonstration of scale-dependent flavor thresholds.

## Higher-order sensitivity

[BZHigherOrderProof](../checks/BZHigherOrderProof.lean) proves a conditional persistence test. If a continuous correction $R(a)$ to $B_0+B_1a$ is bounded by $\delta<B_0/2$ throughout $[a_\ast/2,3a_\ast/2]$, a corrected zero exists in that interval and

$$
|a-a_\ast|\leq\frac{\delta}{-B_1}.
$$

The hypothesis is a genuine required bound. It is not supplied for all higher-order or nonperturbative effects in the QCD construction.

[BZRobustnessProof](../checks/BZRobustnessProof.lean) shows exactly why this bound alone does not give uniqueness. For every admissible positive $\delta$, it constructs a continuous correction bounded globally by $\delta$ whose corrected bracket vanishes throughout a small interval around $a_\ast$. The theorem explicitly supplies two different zeros in the permitted neighborhood. Small amplitude does not mean small derivative.

The companion positive theorem adds an actual derivative hypothesis: $R$ is differentiable throughout the interval, with $|R'(a)|\leq\rho<-B_1$. It proves a unique corrected zero there, the same displacement bound, and

$$
\beta'_{\rm corrected}(a)=-2a^2(B_1+R'(a))>0.
$$

This establishes the corrected zero's positive slope, not a new global QFT flow theorem. Its amplitude and derivative bounds remain missing inputs for the physical QCD remainder. A mutation weakening the derivative allowance from $\rho<-B_1$ to $\rho<-2B_1$ is rejected by the proof.

[BZHigherOrderProof](../checks/BZHigherOrderProof.lean) also checks the specified three-loop MS-bar polynomial, using the coefficient in [Larin and Vermaseren, equation (10)](https://arxiv.org/pdf/hep-ph/9302208). At sixteen flavors, a zero lies strictly between $1/318$ and $1/316$, compared with the two-loop value $1/302$. At six flavors, it has no positive zero for $a\leq1$, but it does have a zero between one and two. That last case is a useful control against treating every truncated-polynomial zero as a convincing physical fixed point: its coupling is already extremely strong. No three-loop coefficient is extracted from the submitted theory.

The reference values show how strongly the truncation can matter:

| Flavors | Two-loop $\alpha_\ast$ | Three-loop MS-bar $\alpha_\ast$ | Shift in the positive root |
|---:|---:|---:|---:|
| 6 | No positive zero | 12.7258 | New strong-coupling zero |
| 9 | 5.2360 | 1.0280 | −80.37% |
| 12 | 0.7540 | 0.4349 | −42.32% |
| 15 | 0.1428 | 0.1234 | −13.60% |
| 16 | 0.04161 | 0.03973 | −4.51% |

These decimals are illustrative. The packaged reference table brackets the three-loop zeros by exact-rational Python bisection; those additional numerical brackets are separate from the Lean proofs at six and sixteen flavors. The smaller shift at sixteen flavors makes it a better perturbative benchmark than the lower-flavor examples. Agreement of two truncations still supplies no bound on all omitted terms and no proof of a QFT fixed point.

The sixteen-flavor case also passes a stronger Lean test. For the specified three-loop correction $R(a)=B_2(16)a^2$, `sixteen_three_loop_remainder_bounds` proves throughout $[a_\ast/2,3a_\ast/2]$ that

$$
|R(a)|\leq1/25< B_0(16)/2,\qquad |R'(a)|\leq15<-B_1(16).
$$

`three_loop_robustness_test` discharges the robustness theorem's hypotheses with these constants. It proves a zero in $(1/318,1/316)$, uniqueness throughout the larger interval around the two-loop root, and the exact derivative formula with positive beta slope. Reversing that final sign is rejected by a specification mutation. This tests a concrete polynomial correction rather than leaving its bounds as hypotheses; the uncomputed higher-order and nonperturbative remainder of physical QCD is still outside the result.

## Coupling-scheme sensitivity

[RunningSchemeProof](../checks/RunningSchemeProof.lean) checks the polynomial chain rule through fourth order for $a'=a+s a^2+t a^3$. Matching the transformed beta polynomial through that order is equivalent to

$$
B'_0=B_0,\qquad B'_1=B_1,\qquad
B'_2=B_2-sB_1+(t-s^2)B_0.
$$

This is a symbolic theorem for arbitrary real coefficients, including a converse: the matched jet forces those values. The linear term of the change is exactly $a$, and $s,t$ are constants; scale- or mass-dependent transformations are outside the test. It is a finite polynomial-jet test, not proof that the submitted stiffness coordinate and a conventional physical coupling are related by such a change. The three-loop comparison above is explicitly MS-bar; its numerical zero is not scheme-independent evidence by itself.

## Improved density-normalization check

[NormalizationBoundProof](../checks/NormalizationBoundProof.lean) strengthens the earlier positivity/invertibility check. It uses the actual `Signals.Read` tolerances and the proved all-pairs fit stability, without a perturbative model, to obtain

$$
\left|\frac{s_{ij}^{A}}{m_i+m_j}-1\right|\leq\frac4{197},\qquad
\left|\frac{s_{ij}^{V}}{m_i-m_j}-1\right|\leq\frac3{98}.
$$

These are approximately 2.031% and 3.062%. The denominators are controlled by the same positive separation margin used in the target. These are the factors multiplying the pseudoscalar and scalar fields in `Signals.renP` and `renS`; they do not rescale the axial and vector currents themselves. The allowed density rescalings therefore cannot be arbitrary. This still does not establish the conventional Wilson-current/renormalized-operator dictionary or equality to independently prescribed physical quark masses.

The later [SharpNormalizationProof](../checks/SharpNormalizationProof.lean) uses two further facts already required of the actual witness: symmetric axial readings and positive separated reference masses. It proves the exact coefficient-norm bounds $11/5$ for the fitted pair sum and $12/5$ for the symmetric axial residual. Distinct positive reference masses have sum at least three times the margin. Consequently the fitted sum is at least $1489\,\mathrm{margin}/500$, giving the stronger bound

$$
\left|\frac{s_{ij}^{A}}{m_i+m_j}-1\right|\leq\frac{12}{1489}\simeq0.008059.
$$

Thus the actual pseudoscalar rescaling is within **0.806%** of one. The theorem `sharp_normalization_acceptance` supplies a common witness retaining the original target and literal lattice limit with this bound. It does not claim the displayed ratio bound is optimal; the earlier weaker bounds remain valid and their original receipts are preserved.

[RunningWitnessProof](../checks/RunningWitnessProof.lean) removes a possible vacuity concern about these conditional bounds. For every positive tolerance and all sufficiently large reference parameters, the submitted existence theorem supplies **one witness** retaining all original target clauses, the literal lattice-correlator limit, both improved normalization bounds, the six-flavor stiffness slope, and eventual positivity of that stiffness. This derives consequences of the accepted theorem; it is not an independent construction, and it adds no two-loop claim.

## Evidence and judgment

The exact inventories are [flavor_suite.py](../scripts/flavor_suite.py), [sensitivity_suite.py](../scripts/sensitivity_suite.py), [body_suite.py](../scripts/body_suite.py), [robustness_suite.py](../scripts/robustness_suite.py), and [normalization_suite.py](../scripts/normalization_suite.py). Their twelve, eight, two, three, and two challenge propositions are separate from their solutions. Solutions import proofs and never import the intentional challenge holes. Fresh compilation, Comparator, and deliberate specification mutations have separate receipts under `evidence/{flavor,sensitivity,body,robustness,normalization}-checks/`. The development adds 136 distinct declarations, for 177 distinct audited review declarations in total; repeated dependency audits are not counted as new results.

**All five new suites passed:** 27 challenge targets were accepted by Comparator, Nanoda, and Lean, and all 26 specification controls behaved as expected (five unchanged passes, twenty-one intended rejections). Source and tool hashes remained unchanged within every recorded run.

The [target index](../evidence/flavor-checks/target-index.json) links every challenge to its specification and proof and states its scope. Of the 27 targets, seven are submitted-source results, three are local or conditional source checks, thirteen concern specified perturbative references, and four are general scalar controls. The conditional source checks include the open `TwoLoopPath` premise; their two normalization counterparts have hypotheses instantiated by the separate actual-witness results. These classifications explain the tests' roles and are not additional formal theorems.

The mutation runner preserves the authenticated submission and mutates only disposable review copies. It requires the unchanged control to pass and each mutant to fail in the expected proof module with a compiler diagnostic, excluding missing-import, resource-limit, and infrastructure failures. These controls test the sensitivity of the current proofs. A rejection is not a proof that the changed proposition is false; in particular, failure after tightening a bound does not establish optimality of the original bound.

The evidence now supports a more specific assessment: the source's one-loop flavor effect has a real determinant calculation behind it, and its fixed six-flavor slope has the expected conventional coefficient after the stated normalization. Its current target does not, through that slope clause, establish the two-loop coefficient. Banks–Zaks is a useful benchmark and exposes a concrete limitation of the current trajectory estimate; it is not part of the verified existence claim. The next decisive extension is a physical coupling prescription with proved second-order running **and** derivative or finite-scale control, followed by massless/flavor-uniform control and a bounded higher-order remainder. The new reference-flow tests make those requested conclusions precise; they do not substitute for proving them for the submitted construction.
