# What the new running-coupling tests establish

18 November 2026. Read the [full report](flavor-running-tests.md) for the Lean statements, assumptions, source locations and receipts.

The [final QCD results and checks summary](results-summary.md) closes this review phase. Derivation of the physical two-loop coefficient from the construction is deferred to later work. The reference results and open obligations recorded here are unchanged.

## Answers to the three questions

| Question | Answer from this review |
|---|---|
| Does the beta coefficient depend on the number of quark flavors? | **Yes at one loop.** The source's trace calculation and running-coordinate formula have the expected linear flavor dependence. A separate test extracts a nonzero free Wilson-determinant screening limit and verifies multiplicity using the full repeated-flavor block determinant. |
| Do we see a verified two-loop effect in the constructed QCD theory? | **Not yet.** We have not extracted its physical two-loop coefficient. Its leading-slope clause does not determine the next term. The new two-loop coefficients and flow are specified perturbative benchmarks, not an extraction from that theory. |
| Does the submission establish a Banks–Zaks fixed point? | **No such result is established here.** Its existence target has six positive distinct scheme masses. We prove global Banks–Zaks reference flows below the fixed point and higher-order sensitivity results, but no massless QFT or nonperturbative conformal window. |

In the convention

$$
a=g^2/(16\pi^2),\qquad \frac{da}{d\log\mu}=-2a^2(B_0+B_1a+\cdots),
$$

the reference coefficients are

$$
B_0=11-\frac23N_f,\qquad B_1=102-\frac{38}{3}N_f.
$$

The convention and coefficients follow [Larin and Vermaseren, equations (1) and (10)](https://arxiv.org/pdf/hep-ph/9302208), with the factor two converting their derivative in log scale squared. Lean checks their algebraic consequences here; it does not reproduce the two-loop diagram calculation.

At six flavors, the reference coefficients are 7 and 26, so the two-loop polynomial has no positive nonzero zero. At sixteen flavors they are 1/3 and −302/3, giving

$$
a_\ast=1/302,\qquad \alpha_\ast=4\pi a_\ast=2\pi/151\simeq0.04161.
$$

The integer positive-zero range is 9–16. This is a property of the polynomial, not a proved physical conformal window. The source's active scheduling interface requires at most eight flavors. At sixteen flavors its one-loop coefficient is only 1/33 of the pure-gauge coefficient; the current estimate requires it to exceed one half. Widening a planning band might fix that arithmetic inequality, but would require redoing the estimates and would not itself construct a massless theory.

## What was added

The development adds **136 distinct audited Lean declarations**, bringing the review total to **177**. All 27 new challenge targets passed Comparator and both kernels. All 26 specification controls behaved as expected, including twenty-one intended rejections. Declaration counts include helper lemmas and must not be read as 177 independent QCD constructions.

The substantial additions are:

- Actual one-loop flavor and determinant-response checks, including nonvacuity and flavor multiplicity.
- Counterexamples showing that the leading slope does not fix the log-log coefficient, and that even both asymptotic coefficients plus monotonicity do not fix a differential beta function.
- Global existence for every positive initial value below the reference Banks–Zaks root, uniqueness, an exact finite-scale identity, and derived UV and IR asymptotics.
- Scheme-transformation algebra through three-loop order, exact three-loop root brackets, and higher-order remainder controls. A small amplitude bound alone can permit many zeros; a derivative bound supplies uniqueness and a positive slope.
- Quantitative bounds on the pseudoscalar/scalar rescalings in the actual current identities, carried by one witness from the accepted six-flavor theorem. Symmetry and mass separation sharpen the pseudoscalar factor to within 0.806% of one.
- A microscopic scope check: the scalar Grassmann body reading ignores flavor and mass changes at fixed bare gauge parameter, whereas the Berezin marginal retains the determinants.

The accepted macOS setup still lacks Linux process isolation. The new runs reuse authenticated submission libraries and build fresh review modules. Their receipts, mutation diagnostics, exact inventories and physical limitations are preserved in the repository.

## Deferred physical running work

First identify a physical running coupling and prove how it relates to the submitted coordinate. Then establish next-order running with derivative or finite-scale control. For a differentiable Wilson-convention coupling $w=6/g^2$, one useful reference diagnostic is

$$
w(t)\,[w'(t)-12b_0]\longrightarrow72b_1,
\quad b_i=B_i/(16\pi^2)^{i+1}.
$$

This remains a requested result for the actual construction, not a theorem supplied here. The six-flavor log-log coefficient would be $39/(28\pi^2)$; merely imposing the leading slope cannot establish it.

A Banks–Zaks QFT claim additionally needs a massless, flavor-parameterized construction and controlled higher-order effects. The new robustness theorem states useful size and derivative bounds explicitly. No such physical remainder estimate, massless limit, or full free gauge/Dirac comparison model has been proved by this review.
