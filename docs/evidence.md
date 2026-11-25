# Evidence index

| Location | Meaning |
|---|---|
| `provenance/submission.json` | Received snapshot identity, archive hash, reported submission date and creation-date limits |
| `provenance/massive-qcd-lean-source.tar.gz` | Complete received source bytes in a newly made archival container |
| `provenance/supplied-comparator/` | Supplied verifier, manifests, frozen target/configuration and reference definitions |
| `evidence/supplied-target/status.json` | Completed full-run state and UTC times |
| `evidence/supplied-target/comparator.{json,log}` | Full submitted-target result and build/kernel log |
| `evidence/supplied-target/reference-export.json` | Independently built frozen challenge export |
| `evidence/supplied-target/staged-reference-export.json` | Same export after adding submitted source |
| `evidence/supplied-target/*source-hashes.json` | Before/after staging source inventories |
| `evidence/supplied-target/tool-*.json` | Binary hashes and tool source provenance |
| `evidence/supplied-target/nanoda-carrier.json` | Authenticated macOS Nanoda carrier archive |
| `evidence/supplied-target/controls/` | Three preflight controls written during the verification run |
| `evidence/supplied-target/original-run-mac.py` | Exact executed orchestration script, with historical paths |
| `evidence/independent-checks/results.json` | Initial four Lean modules, eight theorem axiom audits |
| `evidence/independent-checks/{mass-fit,input-guard,wilson}.json` | Exact arithmetic, input mutations, finite numerical diagnostics |
| `evidence/independent-checks/comparator-controls/` | Five fresh controls, including hidden definition substitution and proof holes |
| `evidence/independent-checks/review-comparator/` | Fresh three-target Comparator overlay, both kernels |
| `evidence/semantic-checks/compilation/` | November 18 fresh compilation: 14 modules, 33 new theorem audits plus 4 repeated mass-fit audits |
| `evidence/semantic-checks/comparator/` | Seven November 18 targets passed Comparator, Nanoda, and Lean; staged source, review inputs and tools unchanged |
| `evidence/semantic-checks/coverage.json` | Explicit distinction between completed formal checks and open physical correspondence obligations |
| `comparator/semantic/` | Seven independent challenge statements for the November 18 development |
| `docs/semantic-tests.md` | Detailed statements, proof methods, controls, and remaining obligations in all four requested areas |
| `evidence/flavor-checks/compilation/` | 22 modules; 82 audits including 71 new declarations |
| `evidence/flavor-checks/comparator/` | Twelve flavor, two-loop, Banks–Zaks, higher-order and normalization targets |
| `evidence/flavor-checks/{source-scope,flavor-benchmarks}.json` | Authenticated source excerpts and exact-rational perturbative reference values |
| `evidence/sensitivity-checks/compilation/` | 46 modules; 147 audits including 39 new declarations |
| `evidence/sensitivity-checks/comparator/` | Eight targets: differential control, global initial-value problem, finite-scale identity, uniqueness, UV expansion, IR exponent, scheme transformation, actual common witness |
| `evidence/body-checks/compilation/` | Ten modules; 24 audits including seven new declarations |
| `evidence/body-checks/comparator/` | Microscopic body/marginal distinction and active schedule restriction |
| `evidence/robustness-checks/` | Eight modules; ten new declarations; three Comparator targets; size-only counterexample and derivative-controlled uniqueness/slope theorem |
| `evidence/normalization-checks/` | Nine modules; nine new declarations; two targets for the symmetry/separation bound and actual common witness |
| `evidence/{flavor,sensitivity,body,robustness,normalization}-checks/mutations/` | Twenty-six fresh-compilation controls: five positive, twenty-one negative; source hashes and replacements recorded |
| `evidence/flavor-checks/dependency-paths/` | Authenticated read-only Lean-environment inspection: paths from the accepted theorem to the active schedule and general determinant screening; not a new theorem |
| `evidence/flavor-checks/coverage.json` | Completed formal scope and explicitly open two-loop/QFT correspondence obligations |
| `evidence/flavor-checks/target-index.json` | Every new challenge linked to its specification, proof, classification and scope; thirteen are perturbative-reference targets |
| `comparator/{flavor,sensitivity,body,robustness,normalization}/` | Separate review challenges, solutions and permitted-axiom configurations |
| `docs/flavor-running-tests.md` | Detailed flavor, beta-function, fixed-point and normalization assessment |
| `docs/results-summary.md` | One-page summary of accepted results, checks and remaining obligations; physical two-loop derivation deferred |
| `docs/assessment.md`, `docs/qcd-verification-assessment.{tex,pdf}` | Consolidated assessment: one-page summary followed by detailed findings, test inventory and limits |
| `scripts/render_assessment.py` | Reproduce the paginated report with installed Pandoc, pdfLaTeX and Poppler; no Lean tests rerun |
| `evidence/source-relation/nov4-overlap.json` | Pinned QCD/Nov4 source comparison: 3,667 shared module paths, 3,018 byte-identical modules in the QCD source import closure; no claim of historical lineage or declaration-level dependency |
| `docs/assessment-document-checks.json` | Document hashes, compilation checks, one-page summary boundary and visual inspection of all nine pages |
| `checks/` | Independent specifications and proofs |
| `comparator/` | Review challenge, solution and Comparator configuration |
| `docs/informal-part-VI-review-r02.pdf` | Earlier analytic review, with its distinct scope and unresolved estimates |

Controls and review additions are not attributed to the supplied package. Numerical tests are not formal proofs. Review compilation reuses authenticated source build products; the supplied-target receipt is the clean submission build record. The log's build-job total includes dependencies and is not a count of mathematical theorems.

`provenance/review-files.sha256` pins the committed review scripts, checks, configurations and evidence. It is a consistency manifest, not an independently signed attestation. `scripts/verify_evidence.py` checks the complete packaged-file inventory, hashes, receipt relationships, and agreement between structured axiom reports and actual compiler messages. Thirteen disposable regression controls in `scripts/test_evidence_checker.py` check acceptance of matching records and rejection of changed, omitted, duplicated, or unsafe records, and prevent resource failures from counting as expected mutation rejections. These packaging controls are separate from the 125 mathematical diagnostic/specification controls reported above.

The November 18 inventory check also corrected a packaging omission: an unanchored `work/` ignore rule on the case-insensitive Mac excluded five copied frozen reference files under `YM/Work/` from Git. The original archive and local verifier already contained these bytes. The ignore rule is now limited to the repository's root work directory, and all five files are included and checked against the authenticated archive. This correction changes neither the submission nor any recorded theorem verdict.
