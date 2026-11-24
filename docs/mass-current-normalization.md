# Mass and current normalization: supplementary check

23 November 2026

**The lattice normalization checks pass. Identification of the constructed continuum currents and fitted masses with a conventional QCD normalization remains unverified.** The source contains more than a fitted PCAC identity: it specifies a common calibration of the lattice insertions and proves divergence identities before the final density rescalings. What we have not established is that these calibrated continuum currents have the prescribed flavor action on other fields, including the contact terms in Ward identities.

This supplement adds ten Lean declarations and three compilation controls. It does not add a new Comparator/Nanoda run or rerun the full submission build. The earlier assessment and its counts describe the earlier review; the cumulative count of audited review declarations is now 187.

## What the source fixes

The starting operators are local bilinears: axial current $\bar\psi_i\gamma_\mu\gamma_5\psi_j$, vector current $\bar\psi_i\gamma_\mu\psi_j$, pseudoscalar $\bar\psi_i\gamma_5\psi_j$, and scalar $\bar\psi_i\psi_j$. Their coefficients are specified by `Calibration.SectionLaws.mesons`, not chosen by fitting a mass. The insertions used in the limit also include `Calibration.mix`, blocking and averaging. Currents use labels of horizon 6 and direction-dependent averaging; the scalar and pseudoscalar use horizon 8 and isotropic averaging. These numbers are the source's weighted label horizons, not their usual engineering dimensions.

The common calibration matches Taylor coefficients of the ratio of marked to unmarked blocked densities, using gauge and Grassmann test profiles near the trivial gauge field, at reference level zero. Thus the construction **does impose a normalization scheme**. It is not permissible to rescale the whole construction arbitrarily while assuming its calibration still holds. The question is whether this specified scheme gives conventionally normalized flavor currents, and how its masses convert to a stated quark-mass scheme.

See `Target/Calibration.lean:59–106,143–211` and `Target/Physics.lean:37–56`; authenticated excerpts are in the [source audit](../evidence/mass-current-checks/source-audit.json). Source paths in this report are relative to `proof/YM/Massive/` unless another prefix is given.

## What the mass fit and rescalings establish

Write the unrescaled continuum identities as

$$\partial\!\cdot A_{ij}=b_{ij}P_{ij},\qquad
\partial\!\cdot V_{ij}=c_{ij}S_{ij}.$$

The source proves these identities in the common field space. In `proof/YM/Affina/Pearls.lean:38–62`, `backs` supplies the unrescaled identities and `destiny` turns them into the final PCAC fields. The preceding `Honors` statement also bounds the coefficients against the blocked mass readings (`proof/YM/Plateau/Tow.lean:50–61`). This is substantive content; the unrescaled identities are not obtained by defining the fitted masses.

The six masses $m_i$ minimize the all-pairs loss $\sum_{i\ne j}(b_{ij}-m_i-m_j)^2$. The source then defines

$$P^R_{ij}=\frac{b_{ij}}{m_i+m_j}P_{ij},\qquad
S^R_{ij}=\frac{c_{ij}}{m_i-m_j}S_{ij}.$$

Consequently the equations with coefficients $m_i+m_j$ and $m_i-m_j$ follow algebraically once the unrescaled identities and nonzero denominators are established. Our earlier checks bound the factors' deviations from one by $12/1489$ (about 0.806%) and $3/98$ (about 3.061%), respectively. These bounds concern **density rescalings relative to the source calibration**. They are not bounds on the difference between the calibrated currents and a conventional current, or between these masses and, for example, an MS-bar mass.

## New checks

The [Lean proofs](../checks/MassCurrentProof.lean) establish the following. The finite contact proofs reuse the submitted finite Ward algebra; they do not assume the final existence theorem or supply an independent construction of the regulator.

1. **Finite-lattice contact identities.** For the actual Wilson regulator, arbitrary gauge links, unequal flavor labels and an arbitrary Grassmann spectator, the vector Ward identity includes the variation of that spectator at the acted-on site. No separation-of-support assumption is made. The axial version retains the full `axial_rest` term. These statements hold after Berezin integration at fixed gauge field; no continuum or gauge-integration limit is used. They extend the separated-support check in `PCAC.clears`/`PCAC.rigid` by retaining the contact response.

2. **What fixes the overall normalization.** Simultaneously multiplying a current and its density by the same constant preserves their divergence equation. A specified, nonzero contact response removes that freedom: preserving the response requires the constant to be one. These are algebraic statements explaining the diagnostic. They do not assert that the full calibrated construction admits such a rescaling.

3. **Compatibility across flavor pairs.** If a single scalar normalization factor and six masses account for the raw vector readings, then $c_{ij}+c_{jk}=c_{ik}$. A common pseudoscalar factor likewise requires $b_{ij}+b_{kl}=b_{ik}+b_{jl}$ for the indicated off-diagonal pairs. The new proofs give small synthetic perturbations that violate these conditions, despite the appropriate exchange symmetry and closeness to mass sums or differences. For the vector example, masses $1,\ldots,6$ receive an antisymmetric $1/1000$ perturbation only in the $(4,5)$ channel; its cycle error is $1/1000$. The axial example uses the earlier symmetric perturbation of that channel.

These examples show that small pairwise errors do not guarantee an exact common factor. **They are not readings extracted from the constructed theory and are not counterexamples to its full target.** A mass-dependent renormalization scheme can have more general conversion factors; the common-factor tests apply only when that stronger normalization is claimed. The source explicitly permits the displayed pair-dependent density factors.

The ten declarations compile with only `propext`, `Classical.choice` and `Quot.sound`. An unchanged control also compiles; changing the vector contact sign or deleting the axial remainder makes the corresponding proof fail. These are checks of statement sensitivity, not additional physical countermodels. See the [compilation receipt](../evidence/mass-current-checks/compilation/results.json) and [control receipt](../evidence/mass-current-checks/mutations/results.json).

## The remaining continuum check

The finite Wilson action supplies a link current with a definite flavor-generator normalization. The local gamma-matrix bilinear used for the continuum vector field is a different lattice operator. Their continuum identification requires a matching argument. For the axial current, the Wilson term breaks chiral symmetry: the required argument must handle its allowed mixing with the pseudoscalar and current divergence, including mass subtraction, and control the remaining contribution. Simply demanding that the unsubtracted Wilson term vanish would be the wrong test. The distinction between local and conserved currents and their normalization is described by [Aoki, Bär and Sharpe, §§II–III](https://arxiv.org/pdf/0905.0804).

The source does keep Wilson and blocking corrections: `PCAC.axialWard` retains the axial remainder, `PCAC.charge` retains the blocking contact correction, and `PCAC.Brave.one_step` bounds a projected correction. The final proof establishes continuum divergence identities. This audit has **not** converted those results into a continuum Ward identity with the prescribed action on an internal insertion. We should therefore describe the open issue as an unverified comparison of normalizations, not as an established omission or failure of the submitted proof.

A useful next target is an integrated flavor Ward identity for these same continuum currents, with a specified internal bilinear and separated external insertions. Its contact term must reproduce the known variation of that bilinear. An axial identity with an internal axial current relates its normalization to the vector current; such a condition is used in [Della Morte et al., §2, especially equation (2.3)](https://arxiv.org/pdf/hep-lat/0505026). Once the current normalization is fixed, the density and mass conversion can be compared with a named scheme. The previously proved separated-point limits do not by themselves justify the integrations through a contact point.

This is the concrete unresolved task. The finite normalization check is now formalized; carrying it through calibration, blocking and the continuum limit remains to be done.

## Reproduction

Using the authenticated, previously built staged submission and Lean 4.32.0:

```sh
python3 -B scripts/build_checks.py --suite mass-current \
  --built-source /absolute/qcd-run/project --lean-bin /absolute/lean/bin \
  --work work/new-mass-current
python3 -B scripts/test_mass_current_mutations.py \
  --built-source /absolute/qcd-run/project --lean-bin /absolute/lean/bin \
  --baseline work/new-mass-current --work work/new-mass-current-controls
python3 -B scripts/verify_evidence.py
```
