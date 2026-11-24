# QCD verification record and reproduction

Verification evidence and independent review of the received `massive-qcd-lean` package, organized like [OpenAI-Nov4-verification](https://github.com/yang-mills-group/submissions/tree/main/reviews/openai-20261104).

**The supplied theorem passed Comparator, Nanoda, and Lean on macOS.** The completed run verified `YM.Massive.interacting_six : YM.Massive.Goal`, after authenticating the source and independently building/exporting the frozen reference. Linux Landlock/systemd isolation was absent, as explicitly accepted for this run.

Read the [current assessment](docs/assessment-1.pdf) for results, completed checks, the mass-prescription discrepancy and unfinished physical checks ([Overleaf source](docs/assessment-1.tex)). The [detailed assessment PDF](docs/qcd-verification-assessment.pdf) has a results-and-checks summary followed by the full review. The same report is available [as Markdown](docs/assessment.md), with a separate [results summary](docs/results-summary.md) and [running-coupling answers](docs/running-summary.md). **This review phase is complete; deriving the physical two-loop coefficient from the construction is deferred to later work.** This is a verification review, not an OpenAI endorsement or a claim of a QCD mass-gap or confinement theorem. The submission is labeled 10 November 2026 provisionally; its creation/release date has not been established from the package.

The [November 18 correspondence tests](docs/semantic-tests.md) add 33 Lean theorems covering literal lattice limits, stress exclusion, current/mass checks, and stiffness/UV comparison. The separated-point limit is established. The full free-QCD comparison model and conventional current/coupling identifications remain open; the new formal checks must not be read as completion of those physical obligations.

The [flavor and running extension](docs/flavor-running-tests.md) finds real one-loop flavor dependence in the source, but does not verify its physical two-loop beta function. It strengthens actual PCAC density-normalization bounds and checks the active scheduling restriction to at most eight flavors. Through that extension, the independent review added 177 audited declarations, 37 Comparator challenge targets and 125 mathematical diagnostics and controls. These were developed beyond the received acceptance workflow; the totals include helper lemmas and auxiliary reference calculations.

The [November 23 mass/current audit](docs/mass-current-normalization.md) adds ten Lean declarations and three compilation controls: finite Wilson contact identities, normalization sensitivity and flavor-pair compatibility. All pass, bringing the cumulative totals to 187 audited declarations and 128 diagnostics/controls; the Comparator target count stays 37. Matching the calibrated continuum currents to conventional flavor-current normalization remains open. These new checks used Lean, without a new Comparator/Nanoda run.

| Evidence | Result | Record |
|---|---|---|
| 222 frozen inputs and 7,597 submission inputs | Authenticated | [Final input check](evidence/supplied-target/final-input-check.log) |
| Independently built reference export | Supplied expected SHA-256 matched, before and after adding solution | [Reference receipt](evidence/supplied-target/reference-export.json), [staged receipt](evidence/supplied-target/staged-reference-export.json) |
| Full submitted target | Comparator + both kernels passed; 16,250 build jobs | [Log](evidence/supplied-target/comparator.log), [status](evidence/supplied-target/status.json) |
| Initial eight review theorems | Compiled; permitted standard axioms only | [Receipt](evidence/independent-checks/results.json) |
| Exact mass-fit calculations | 44 checks passed | [Receipt](evidence/independent-checks/mass-fit.json) |
| Input-authenticator mutations | 9 checks passed | [Receipt](evidence/independent-checks/input-guard.json) |
| Comparator controls | 5 checks passed | [Receipt](evidence/independent-checks/comparator-controls/results.json) |
| Finite Wilson operator diagnostics | 41 checks passed | [Receipt](evidence/independent-checks/wilson.json) |
| Initial three review targets | Comparator + both kernels passed | [Receipt](evidence/independent-checks/review-comparator/result.json) |
| November 18 correspondence development | 14 modules compiled; 33 new theorem audits plus 4 repeated mass-fit audits | [Receipt](evidence/semantic-checks/compilation/results.json), [scope](docs/semantic-tests.md) |
| Seven November 18 challenge targets | Comparator + both kernels passed; inputs unchanged | [Receipt](evidence/semantic-checks/comparator/result.json), [log](evidence/semantic-checks/comparator/comparator.log) |
| Flavor and higher-order tests | 22 modules; 71 new declarations; twelve targets passed Comparator and both kernels | [Compilation](evidence/flavor-checks/compilation/results.json), [Comparator](evidence/flavor-checks/comparator/result.json) |
| Complete reference dynamics and actual witness | 46 modules; 39 additional declarations; eight targets passed Comparator and both kernels | [Compilation](evidence/sensitivity-checks/compilation/results.json), [Comparator](evidence/sensitivity-checks/comparator/result.json) |
| Density-reading and active schedule scope | 10 modules; seven additional declarations; two challenge targets | [Compilation](evidence/body-checks/compilation/results.json), [Comparator](evidence/body-checks/comparator/result.json) |
| Higher-order robustness | Eight modules; ten additional declarations; three targets passed Comparator and both kernels | [Compilation](evidence/robustness-checks/compilation/results.json), [Comparator](evidence/robustness-checks/comparator/result.json) |
| Stronger actual density normalization | Nine modules; nine new declarations; two targets passed Comparator and both kernels; renP bound 12/1489 | [Compilation](evidence/normalization-checks/compilation/results.json), [Comparator](evidence/normalization-checks/comparator/result.json) |
| November 23 mass/current normalization | Ten new Lean declarations; unchanged control accepted; wrong contact sign and omitted axial remainder rejected | [Compilation](evidence/mass-current-checks/compilation/results.json), [Controls](evidence/mass-current-checks/mutations/results.json), [Assessment](docs/mass-current-normalization.md) |
| New specification mutations | Five unchanged controls and twenty-one deliberate changes | [Flavor](evidence/flavor-checks/mutations/results.json), [Sensitivity](evidence/sensitivity-checks/mutations/results.json), [Scope](evidence/body-checks/mutations/results.json), [Robustness](evidence/robustness-checks/mutations/results.json), [Normalization](evidence/normalization-checks/mutations/results.json) |

The source archive, manifests, tool provenance and full logs are included; build products are excluded. The archive is a new container preserving the received source bytes, not the original download archive. See [reproduction instructions](docs/reproduce.md), [submission identity](provenance/submission.json), and [evidence index](docs/evidence.md), and [definition map](docs/source-map.md).

The new tests found a **mass-prescription difference**: the formal target uses all 30 ordered off-diagonal readings in a least-squares fit; the informal review describes an inversion from six selected unordered pairs. A proved synthetic example distinguishes these prescriptions. This is a scope/alignment finding, not a contradiction in the submitted theorem.

Original submission notices are retained separately. The repository's Apache-2.0 license covers the review additions as described in [NOTICE](NOTICE).

[Group import and link-migration record](provenance/group-import.json).
