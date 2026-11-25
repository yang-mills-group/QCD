# Massive QCD: one-page results summary

25 November 2026 | Summary of results and checks

**Results.** The submitted proof constructs a continuum field system for four-dimensional SU(3) quantum chromodynamics (QCD) with six massive quark flavors. It is written in Lean, a computer proof assistant, and passed verification of its precise mathematical statement. It builds on the framework used in OpenAI's November 4 (Nov4) pure Yang-Mills submission, which treats gauge fields without quarks. The QCD construction supplies continuum correlations, six positive distinct fitted mass parameters, identities for currents and the stress tensor, and a reconstruction of real-time quantum fields, all within one construction.

Our additional checks establish explicit lattice-to-continuum correlation limits at distinct points, confirm that the properties hold for the same constructed objects, and bound normalization changes. They also confirm the expected one-loop dependence on the number of quark flavors in the source calculations. We found that the formal mass-fitting rule and the rule described in the separate informal review can differ on synthetic data; this does not establish a discrepancy in the constructed theory.

**Checks supplied by OpenAI and rerun here.**

- Check source files against recorded hashes, prepare fixed dependency versions, and build the complete proof.
- Use Comparator to check the theorem statement and its definitions against a preserved reference, and check that the reference has not changed.
- Check the allowed axioms and verify the proof with two proof checkers: Nanoda and Lean's kernel.

**Additional checks developed for this review.**

- **Lean proofs:** lattice correlation limits, properties of one common construction and its selected vacuum, current identities, normalization bounds, and a conditional test of the stress-tensor criterion.
- **Mass-fit algebra:** the exact solution and its stability, comparison with the informal prescription, and 44 exact-arithmetic diagnostics.
- **Lattice and flavor checks:** 41 numerical checks of the Wilson quark operator; Lean checks of one-loop flavor dependence and a fermion-determinant calculation in a fixed background.
- **Failure detection:** deliberately altered inputs, statements, definitions, axioms and coefficients, together with checks of the stored evidence.

All completed checks passed within their stated scopes. Numerical tests are separate from formal proofs; proofs that use the submitted theorem are not a second construction of QCD.

**Scope and open questions.** Full identification with the conventional physical operators, currents, masses and coupling remains open, as does comparison with a complete free gauge-and-quark model. Arbitrary prescribed quark masses, particle masses, a mass gap and confinement are not established. **Derivation of the physical two-loop coefficient is deferred.** The run used macOS without Linux process isolation. These formal checks do not verify every step of the separate informal argument.

The [initial draft assessment](assessment.md) places this summary first, followed by the detailed results and checks. A [initial draft PDF](qcd-verification-assessment.pdf) is also available.
