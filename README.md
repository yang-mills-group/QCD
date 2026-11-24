# QCD — Results and verification

## [Read the draft assessment (PDF)](docs/assessment-1.pdf)

**Private draft for discussion, 24 November 2026.** The assessment is on page 1; page 2 explains the operator normalization, mass fit, and coupling prescription. [LaTeX source](docs/assessment-1.tex).

This repository collects QCD submissions and the group's checks and assessments. The first submission is OpenAI's massive-QCD construction, labeled **10 November 2026**. It extends the framework used in the November 4 pure Yang–Mills submission to SU(3) with six fundamental Dirac flavors, using Wilson fermions and including their determinants in the gauge-field weight. Its final theorem is separate from the pure Yang–Mills existence and matching theorems.

The submitted result gives continuum correlations, six positive distinct scheme masses, current and stress-tensor identities, and a Wightman reconstruction. Its potential significance is an existence construction with dynamical massive quarks. Identifying the constructed fields, masses, and coupling with conventionally normalized QCD quantities remains part of the review.

## Results and assessments

| Submission date | Original submission | Assessment |
|---|---|---|
| 10 November 2026 | [OpenAI-QCD-20261110](https://github.com/yang-mills-group/OpenAI-QCD-20261110) | [Draft assessment and renormalization appendix](docs/assessment-1.pdf) |

The submission date is provisional and may be corrected before public release. The assessment concerns the package preserved at [archive commit `53f81ca`](https://github.com/yang-mills-group/OpenAI-QCD-20261110/tree/53f81cafe5cb9cd18cd0d5b49b8364cce50a0fe7).

All 7,594 proof modules compiled, and the supplied Comparator checks passed. Our additional checks include 37 targets accepted by both kernels, finite Wilson-operator diagnostics, exact mass-fit calculations, and flavor-dependence checks. Ten later Lean checks address mass/current normalization and Wilson contact identities; these have not had a Comparator run. The recorded runs used macOS without the supplied Linux isolation.

The main open questions concern flavor-current normalization and contact terms, the physical interpretation of the fitted masses and coupling, and comparison with free gauge and fermion fields using the same operator identifications. The formal mass fit differs in general from the informal prescription, although disagreement on the actual construction has not been shown. No mass gap, confinement result, or particle spectrum is established by this assessment.

## Documents and verification records

[docs/](docs/README.md) contains the current assessment, detailed reports, and their sources. The [verification guide](VERIFICATION.md) describes the added Lean checks, diagnostics, and recorded results. [Evidence](docs/evidence.md) and [reproduction instructions](docs/reproduce.md) are included in this repository, along with the preserved source archive and original notices. The [original proof repository](https://github.com/yang-mills-group/OpenAI-QCD-20261110) also provides the received package. All of these materials are readable by members of `yang-mills-group`.

## Making a submission

Send proposed submissions and feedback to [yangmills4d@gmail.com](mailto:yangmills4d@gmail.com). Include the authors, claimed results, a fixed revision of the materials, and reproduction instructions for formal checks. The group's [submission requirements](https://github.com/yang-mills-group/.github-private/blob/main/profile/README.md#making-a-submission) apply. Inclusion does not constitute endorsement, and the group does not promise to post or review submissions.
