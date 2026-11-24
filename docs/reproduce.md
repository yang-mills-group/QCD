# Reproducing the review

Run from the repository root. Python 3.9+ standard library suffices for the Python diagnostics. Lean checks need the pinned toolchain and submission libraries. These instructions distinguish the completed run from the additional replay helper: only the receipts document actual executions.

## Authenticate and extract

```sh
python3 scripts/verify_evidence.py
python3 -B scripts/test_evidence_checker.py -v
mkdir -p work/source
tar -xzf provenance/massive-qcd-lean-source.tar.gz -C work/source
python3 -I -B work/source/massive-qcd-lean/comparator/check-inputs
```

The archive digest is pinned in `provenance/submission.json`. The supplied checker authenticates source manifests, file inventories and content. The archive contains the package's source and original notices; it does not contain tool binaries, dependency caches or compiled `.olean` files. The package therefore still requires its pinned external toolchain and dependencies to build.

## Lightweight independent checks

```sh
python3 scripts/test_mass_fit.py --output work/mass-fit.json
python3 scripts/test_input_guard.py --output work/input-guard.json
python3 scripts/test_wilson.py --source work/source/massive-qcd-lean/proof --output work/wilson.json
```

The input mutation suite extracts its own isolated archive copy and removes only that temporary copy. It never mutates the received package or the completed build. The exact rational and numerical Wilson scripts model the definitions independently; they are not an extraction of Lean execution.

## Complete supplied verification on Linux

Use the package's original `comparator/setup-linux` and `comparator/verify`. They require an unprivileged supported Linux environment with a systemd user session, Landlock ABI 5+, the listed prerequisites, at least 64 GiB RAM, and about 200 GiB initial free space. Inspect each script's `--help` before allocating the run. This repository contains **no completed Linux receipt**.

```sh
work/source/massive-qcd-lean/comparator/setup-linux /absolute/new/qcd-tools
work/source/massive-qcd-lean/comparator/verify /absolute/qcd-tools /absolute/new/qcd-run
```

Tool installation and dependency acquisition require network access. These commands are from the archived supplied workflow, not a cloud-cost or machine recommendation.

## Replay on the recorded Mac

The original executed runner is retained verbatim at `evidence/supplied-target/original-run-mac.py`, including its historical local paths. It assumed initial reference preparation and dependency acquisition had already happened.

`scripts/run_supplied_mac.py` is a parameterized replay helper that adds those preparation stages, accepts explicit paths, checks the Lean commit and exact recorded tool-binary hashes, and requires a fresh run directory. Its syntax/help were checked; it has **not** been run through a second seven-hour submission build. The original completed run remains the evidence for full submission acceptance.

The tools directory must have `lean` pointing to the Lean 4.32 installation and `bin/{comparator,lean4export,nanoda_bin,landrun-mac}`. Binary hashes and source revisions are in `evidence/supplied-target/{tool-hashes,tool-provenance,nanoda-carrier}.json`. This helper intentionally requires the recorded Apple Silicon binaries; it is not a cross-platform installer. Use the original Linux workflow for Linux tools.

```sh
python3 scripts/run_supplied_mac.py --package /absolute/massive-qcd-lean --tools /absolute/qcd-tools --run /absolute/new/qcd-run
```

The macOS shim supplies no Landlock/systemd isolation. Do not describe this replay as having the Linux workflow's containment properties. The helper preserves input/definition/axiom/two-kernel checks and the expected challenge-export digest.

## Compile the independent Lean checks

Use a completed authenticated project, such as the original run's `project` directory, plus the pinned Lean binary directory. Every recorded staged source hash is checked before compilation. A new output directory prevents reuse of review `.olean` artifacts.

```sh
python3 scripts/build_checks.py --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --work work/new-checks
python3 scripts/test_comparator.py --lean-bin /absolute/lean-4.32/bin --tools-bin /absolute/qcd-tools/bin --work work/new-controls
python3 scripts/run_review_comparator.py --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --tools-bin /absolute/qcd-tools/bin --work work/new-review-comparator
```

The review Comparator builds fresh review modules while reusing the authenticated submission build and pinned dependency libraries. It checks three targets, permits only `propext`, `Classical.choice`, and `Quot.sound`, and requires both kernel-success markers. Its challenge alone intentionally contains `sorry`; it is never imported by the solution. The input and tools are hashed before and after. Temporary output records use machine-specific absolute paths for auditability.

No suite here establishes every physical correspondence or informal analytic estimate. Consult the scope attached to each receipt and the assessment.

## November 18 correspondence checks

The `semantic` suite builds 14 modules in a new directory and checks an explicit inventory of 37 axiom reports: 33 new theorems and four repeated mass-fit theorems. It authenticates the staged source before compilation and rechecks source, review inputs, and compiler hashes afterward. The independent seven-target challenge is in `comparator/semantic/`; the solution never imports that challenge.

```sh
python3 -B scripts/build_checks.py --suite semantic --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --work work/new-semantic-checks
python3 -B scripts/run_review_comparator.py --suite semantic --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --tools-bin /absolute/qcd-tools/bin --work work/new-semantic-comparator
```

The original suite remains the default when `--suite` is omitted. Neither suite claims a clean rebuild of all submission libraries. `scripts/semantic_suite.py` lists the exact modules, audited declarations, and seven Comparator targets. Read [the correspondence report](semantic-tests.md) before interpreting a green result: in particular the free-sector exclusion is conditional, its explicit constant-field control is not a free QCD model, and the current/coupling dictionary remains incomplete.

## Flavor, higher-order running and scope checks

Five further suites use the same authenticated build, permitted axioms, fresh-review directories, and macOS limitations. Each suite's inventory is explicit in `scripts/{flavor,sensitivity,body,robustness,normalization}_suite.py`.

| Suite | Modules | Declaration audits in that compilation | New distinct declarations | Comparator targets |
|---|---:|---:|---:|---:|
| `flavor` | 22 | 82 | 71 | 12 |
| `sensitivity` | 46 | 147 | 39 | 8 |
| `body` | 10 | 24 | 7 | 2 |
| `robustness` | 8 | 42 | 10 | 3 |
| `normalization` | 9 | 23 | 9 | 2 |

The overlap is deliberate: the combined sensitivity run repeats the earlier correspondence and flavor declarations. Across all suites, including the original acceptance module, there are 177 distinct audited review declarations. These counts are not counts of independently constructed QFTs.

Run the following with `SUITE` set in turn to `flavor`, `sensitivity`, `body`, `robustness`, and `normalization`. Every invocation needs a new work directory. The mutation runner requires the accepted compilation directory, including its `.olean` files and receipt, as its baseline.

```sh
SUITE=flavor
python3 -B scripts/build_checks.py --suite "$SUITE" --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --work "work/new-$SUITE-checks"
python3 -B scripts/run_review_comparator.py --suite "$SUITE" --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --tools-bin /absolute/qcd-tools/bin --work "work/new-$SUITE-comparator"
python3 -B "scripts/test_${SUITE}_mutations.py" --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --baseline "work/new-$SUITE-checks" --work "work/new-$SUITE-mutations"
```

The mutation controls compile disposable review copies. They do not mutate the submission, and they are not additional Comparator runs. There are twenty-six controls: five unchanged controls and twenty-one intended rejections. A failure at the expected proof module with an actual compiler diagnostic is required; a missing import, inaccessible file, resource exhaustion, or other listed infrastructure error does not count.

The source inspection and exact-rational reference table can be regenerated separately:

```sh
python3 -B scripts/record_flavor_scope.py --built-source /absolute/qcd-run/project --output work/new-flavor-scope
```

The reference beta coefficients are specified conventional perturbative formulas. Their arithmetic and consequences are checked here; they are not extracted coefficients of the constructed continuum theory. Read [the running report](flavor-running-tests.md) for this distinction, the finite-scale and differential controls, and the open physical correspondence obligations.


## Inspect actual declaration dependencies

```sh
python3 -B scripts/record_dependency_paths.py --built-source /absolute/qcd-run/project --lean-bin /absolute/lean-4.32/bin --work work/new-dependency-paths
```

This runs `audit/DependencyPaths.lean` against the authenticated compiled source environment. It traverses constants in declaration types and values, restricted to `YM` names, and retains paths from `YM.Massive.interacting_six` to selected declarations. It is a diagnostic rather than a new formal theorem; a path does not establish indispensability, and absence from the restricted traversal does not establish mathematical independence.

## Render the summary and detailed assessment

The canonical text is [assessment.md](assessment.md). Its opening summary is also saved separately in [results-summary.md](results-summary.md). The PDF places that summary on page 1 and begins the detailed assessment on page 2. The complete generated LaTeX source is included beside the PDF.

With Pandoc, pdfLaTeX and Poppler already installed, run:

```sh
python3 -B scripts/render_assessment.py --evidence-commit "$(git rev-parse HEAD)"
```

The commit fixes the linked supporting reports and verification receipts; it is not a claim that this document revision existed at that snapshot. The renderer checks the summary boundary, compiles twice and rejects layout/character warnings. Render and inspect the pages after any content change. The included [document check record](assessment-document-checks.json) records inspection of all eight final pages. Rendering does not rerun Lean, Comparator or the physics checks; PDF metadata can vary between builds.
