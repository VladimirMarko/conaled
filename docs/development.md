# Development and verification

Use this guide when changing the toolchain, choosing acceptance checks, or
working on verification tooling. For library entry points, see the
[README](../README.md). Run commands below from the repository root.

## Development environment

Install Nix with `nix-command` and `flakes` enabled, and install direnv with
its [shell hook](https://direnv.net/docs/hook.html) enabled. From the repository
root, run `direnv allow`. The checked-in `.envrc` loads the flake shell whenever
you enter the directory. Without shell integration, use `nix develop`.

`flake.nix` declares the supporting tools, and `flake.lock` pins their Nixpkgs
revision. The shell provides elan, Python, Git, curl, direnv, and ripgrep.
Elan selects and downloads Lean (including Lake) from `lean-toolchain` on first
use; Lake resolves library revisions from `lake-manifest.json`. Initial setup
and cache downloads require network access.

For agent commands without an interactive shell, use `direnv exec . <command>`
after allowing the directory, or `nix develop --command <command>`.
Add additional project tools to the shell's `packages` list. Tools from the
existing Nixpkgs input share its lock; update that pin intentionally with
`nix flake update nixpkgs`. Check in `flake.nix` and `flake.lock` together.
Validate tooling changes with `nix flake check` and, for example,
`nix develop --command lean --version`.

## Build and audit

Lean is pinned in [lean-toolchain](../lean-toolchain), the Mathlib requirement in
[lakefile.toml](../lakefile.toml), and resolved dependency revisions in
[lake-manifest.json](../lake-manifest.json). Inside the development shell:

```sh
lake exe cache get
./check.sh
```

The first command obtains the pinned dependencies and their compiled cache.
`./check.sh` is the routine acceptance command. It checks the source policy and
public-entrypoint coverage, builds every integrated module with stock Lake's
incremental dependency tracking, then executes `ProofAudit.lean`. The exhaustive
audit runs on every invocation, including when compilation is entirely cached.
Import discovery uses the pinned Lean header parser; the source-policy guard
uses Lean's lexer, literal and comment parsers. The preflight also rejects
imports after initial module documentation before compiling project modules.
Compilation remains the authority for complete syntax, including local syntax
extensions. Python retains scheduling, coverage graph checks and candidate
receipts, but does not parse Lean source. See the
[native-source implementation record](research/native-verification-source.md).

Project compilation and audit execution use `-EhasSorry` to reject emitted
admission diagnostics early. Lake receives this diagnostic policy through
`weakLeanArgs`, which does not invalidate existing compilation traces. Ordinary
linter warnings remain nonfatal. Source code can suppress a diagnostic, and
cached artifacts need not have been compiled with this flag; the exhaustive
transitive axiom audit remains the acceptance rule in both cases.

Successful builds remain in Lake's normal output directories for later reuse.
Lake owns incremental scheduling; this wrapper adds no persistent cache. Before
and after the incremental build, an output-integrity guard compares project
artifacts with the output hashes in their saved Lake traces. Missing or
inconsistent evidence causes invalidation before the build; a mismatch after
the build fails verification before the audit. Guarded builds disable Lake
artifact-cache restoration/writes and rehash inputs, while reusing existing
dependency build outputs. The guard uses the pinned Lake hash implementation.

For acceptance of a committed candidate, use the persistent isolated workspace:

```sh
python3 scripts/check-candidate.py HEAD
python3 scripts/check-candidate.py HEAD --verify
```

The command resolves the revision once and keeps the caller's branch, index and
edits intact. It owns one detached worktree under the repository's common Git
directory, at `conaled/acceptance`, and retains that worktree's private Lake
outputs across commits. An exclusive lock serializes its users. The candidate's
tracked `.envrc` selects the development environment; the caller must already
have the pinned dependency cache in `.lake/packages`. Only that dependency cache
is shared. Keep it stable during checks, as with other isolated worktrees.
The command prints the workspace and resolved candidate for the review record.

`--verify` checks the existing candidate without switching commits. `--clean`
forwards a clean Lake rebuild that retains reusable outputs. `--fresh`
(and optional `--jobs N`) forwards the independent reference mode described below.
The wrapper delegates validation and receipt handling to the candidate's
`check.sh`; it adds no artifact cache or provenance guarantee. Direct invocation
of `./check.sh --candidate HEAD` and `./check.sh --verify-candidate HEAD` remains
available in an independently managed, clean isolated checkout.

The managed worktree is reserved for this command. Edits, an unowned existing
path, or an interrupted run cause refusal rather than automatic cleanup. On
interruption, inspect `conaled/acceptance-running.json` in the common Git
directory, stop any surviving verifier/compiler processes, and preserve useful
logs or edits. Once no process can write there, remove the marker and rerun
validation. Follow the integrity incident runbook if artifact state is suspect.
Read the last operational observation without starting a check:

```sh
python3 scripts/check-candidate.py --status
```

The JSON reports the candidate, phase, elapsed seconds and outcome. The workspace
lock distinguishes an active process from an abandoned observation. Outcomes
include `not-started`, `running`, `passed`, `failed`, `interrupted` and `unknown`.
Missing or malformed records and unresolved crashes report uncertainty. A live
observation may change immediately after it is read. `passed` describes the last
reported command result; use `--verify` to check the acceptance receipt.

On SIGINT or SIGTERM, the wrapper asks its verifier process group to stop, then
escalates to SIGKILL after two seconds. It removes a check's success receipt and
retains the interruption marker for inspection. SIGKILL cannot run cleanup; the
child retains the workspace lock until it exits. Processes that deliberately
leave the owned process group are outside this cleanup contract. Confirm that
all owned processes have stopped before resolving an interruption marker.

To retire the workspace, first resolve any interrupted run and preserve edits,
then use `git worktree remove` on the printed path and remove
`conaled/acceptance-owner.json`. Its next invocation creates a new cold workspace.

The underlying `./check.sh --candidate` command requires a clean Git checkout, including the index and
nonignored untracked files, and requires all integrated Lean sources to be
tracked. Dependency checkouts must be clean and match the Git revisions in
`lake-manifest.json`. It checks these conditions before compilation and again
after the audit, then atomically writes `.lake/verification.json` with the
resolved commit, dependency revisions, compiler version, mode, and completion
time. The record distinguishes `incremental`, `clean` and `fresh` modes. Combine
`--candidate HEAD` with the selected build mode when rebuilding is needed.

`--verify-candidate` checks that the success record still matches the current
candidate, dependencies, and compiler without compiling or rerunning the audit.
Use it immediately before accepting the recorded candidate. It uses the mode
in the record; omit `--clean`, `--fresh` and `--jobs`. Starting any new validation removes
the previous record, and only successful candidate validation writes a new one.
Ordinary `./check.sh` remains available for uncommitted development work and
does not produce a candidate success record. Other required tests and reviews
need their own evidence; this record covers only this verification command.

This is bookkeeping for trusted local checkouts, not a certificate of artifact
integrity or an immutable input snapshot. Before/after checks cannot detect
changes made and restored during the run, ignored external inputs, or hostile
Git metadata. Keep the isolated checkout stable throughout validation and
acceptance. Candidate records currently support Git-pinned Lake dependencies.

For focused development, use `lake build Applications.Interaction.Measurement`
(or another module target). A bare `lake build` builds the configured library
and audit, but does not replace `./check.sh`'s source-policy and coverage checks.

Choose validation by the effective inputs that changed:

| Change | Acceptance |
|---|---|
| Library definitions or proofs | Guarded incremental build and exhaustive audit. |
| Audit implementation only | Guarded incremental build and exhaustive audit, plus audit rejection and exhaustive-root regression suites. Record that compiler, dependency, scheduling and integrity inputs are unchanged. |
| Diagnostic severity only, using trace-independent Lake arguments | Guarded incremental build and exhaustive audit, plus real compiler tests for the diagnostic and warm-reuse tests. Record that artifact semantics and all other verification inputs are unchanged. |
| Compiler, other Lake configuration or dependency pins | Clean Lake rebuild and exhaustive audit; validate any affected adapters. |
| Retained-build lifecycle only, with compiler commands, dependency scheduling, source-policy and integrity checks unchanged | Clean Lake acceptance followed by incremental reuse, plus public-command regressions covering clean, incremental and reference modes. |
| Scheduler, source-policy or output-integrity implementation; uncertain compilation boundary; suspected stale artifacts | Independent `--fresh` reference check and applicable public-command regressions. |

`--clean` removes only this checkout's `.lake/build` after source, coverage,
configuration and version preflight, then runs the guarded Lake build and audit.
It disables artifact-cache restoration and writes, so prior project outputs
cannot satisfy the build. Lake produces normal outputs and traces for subsequent
incremental reuse. Dependency caches and other `.lake` state remain in place.
Symlinked `.lake` or `.lake/build` roots are refused. Keep the checkout exclusively
owned while cleaning or building. A failed build can leave partial compilation
outputs for recovery, but never a successful candidate receipt.

The independent `--fresh` path keeps its existing meaning: direct Lean compilation
in an empty temporary output directory, followed by the exhaustive audit. It
bypasses Lake's project build decisions and does not create Lake traces. Copying
its outputs into Lake's cache would not establish valid reuse. Use `--clean`
when a rebuild should warm the incremental cache.

For auxiliary tooling changes, identify the effective verification inputs: if
compiler, dependency, scheduling, source-policy, integrity and audit inputs are
unchanged, test the changed executable behavior on real fixtures without a
full-library cold rebuild. Record that input comparison with the evidence. If
the boundary is uncertain, use fresh validation. This applies to orchestration
wrappers and their documentation; it does not exempt edits to the verifier they
invoke. The [fresh verification workflow](../.github/workflows/fresh-verification.yml)
also runs weekly on the default branch and supports manual dispatch once pushed
to GitHub with Actions enabled. Fresh mode recompiles every project module into
a private temporary directory, audits those outputs, and removes the directory.
It reuses external dependency caches but neither reuses project artifacts nor
populates Lake's incremental cache. Use `--fresh --jobs 1` for serial compilation,
or `--fresh --jobs N` to set a memory-appropriate limit (default: up to four).

All modes discard caller `LEAN_PATH` and verify the compiler version against
`lean-toolchain`. Incremental and clean modes use Lake's configured import paths and
compiler. Fresh mode uses only its new project outputs and dependency paths resolved by Lake;
it also supports `LEAN=/absolute/path/to/lean`. `--jobs` and `LEAN` overrides are
rejected outside fresh mode rather than silently ignored. Clean and incremental
builds use Lake's scheduler; `--clean` and `--fresh` are mutually exclusive.

Keep sources, dependencies, and configuration stable during a check. Use an
isolated checkout when other agents may edit them, and do not share writable
project build directories across active checkouts. Routine acceptance trusts
Lake's input tracking and local artifacts; it is not a certificate against
artifact tampering or undeclared external inputs. Periodic fresh builds provide
an independent check of project cache state. Future verified reuse is tracked
in [#222](https://github.com/VladimirMarko/conaled/issues/222).

The local output-integrity guard is a temporary mitigation for mixed project
artifacts, not the verified-reuse contract in #222. Agreement with a trace does
not prove that artifacts were compiled from the claimed inputs. Lake's hashes
are noncryptographic; this is not authentication against hostile substitution.
The guard does not prevent changes between checking and consumption or establish
external dependency-cache integrity. Direct `lake build` invocations and editor
consumers bypass it. Keep the stable-checkout discipline, exhaustive audit, and
periodic fresh verification; see the
[mitigation scope and limitations](research/lake-output-cache-mismatch.md#local-mitigation).

The guard supports the repository's standard TOML build layout and pinned trace
schema. Custom project build/source directories, a `lakefile.lean`, or explicitly
enabling the project's artifact cache are rejected. Unknown trace evidence
triggers rebuilding; if a new build still produces unsupported evidence,
verification fails. Toolchain or layout changes must update and test the adapter.

For guard diagnostics, automatic recovery, and failures requiring investigation,
follow the [Lake integrity incident runbook](agents/lake-integrity-incidents.md).
While the temporary tracker is open, record unexpected incidents in [#272](https://github.com/VladimirMarko/conaled/issues/272);
normal cold-build invalidations need no report. The tracker defines how to alert
the owner when an already investigated failure recurs, including sub-agent relay.

All modes cover root Lean modules and `SquareKit/`, `Applications/`, and
`Examples/`; archived sources and isolated `experiments/` require their own
validation. Generated `.olean`, `.ilean`, `.lake`, and cache files are not source
artifacts. The command reports build, audit, and total elapsed times.

Run `python3 scripts/test-proof-audit.py` in the development shell to check
that the audit rejects private forbidden dependencies, admissions, and unsafe
source declarations. Its temporary fixtures also check that an unused external
axiom does not cause a false rejection. It compiles the real audit against a
small fixture entrypoint without using project build artifacts. The following suites need only the
development shell and cached dependencies:

```sh
python3 scripts/test-check.py
python3 scripts/test-check-candidate.py
python3 scripts/test-proof-audit-roots.py
python3 scripts/test-warning-summary.py
```

The first exercises incremental reuse and invalidation, clean-build retention, repeated auditing, fresh
compilation, concurrency, ordering, stale artifacts, coverage, and failure exits
through `check.sh`. The candidate-workspace suite checks retained compilation,
exact receipts, real signal interruption, process-group cleanup, status observations,
refusal and failure recovery through the public CLI. The roots
suite compares the audit's
exact root set with an independent exhaustive environment scan, including
private, generated, and current-module declarations. For diagnostics,
`set_option trace.ProofAudit.roots true in #audit_project_axioms` prints the
logical roots. The normal audit uses project module metadata to avoid scanning
unrelated dependency declarations, and Lean's cached transitive axiom summaries.
Formal refinement proofs for these checks are tracked separately in
[#43](https://github.com/VladimirMarko/conaled/issues/43).

### Warning summaries

Summarize a saved Lean or Lake build log, optionally comparing another log:

```sh
python3 scripts/summarize-warnings.py build.log
python3 scripts/summarize-warnings.py build.log --baseline earlier.log
```

The JSON groups warning occurrences by module and category, retaining unrecognized
messages as `other` and unlocated warnings under `<unknown>`. Comparisons report
count changes, not newly identified diagnostics. Compare logs with equivalent
coverage and output format: replayed cached warnings and repeated build attempts
can change counts without changing source warnings. This command is offline and
does not affect acceptance.

The process fixtures and structured status observations are reusable boundaries
for the [native tooling work](https://github.com/VladimirMarko/conaled/issues/591).
A verified controller still needs adapter tests: proofs about observations and
actions do not establish that an operating-system adapter implements them.
These helpers add no scheduler or artifact-evidence cache. Composition of verified
per-artifact audit evidence remains owned by
[#43](https://github.com/VladimirMarko/conaled/issues/43) and
[#222](https://github.com/VladimirMarko/conaled/issues/222).

### Audit performance

The audit reports milliseconds spent on inventory acquisition, root enumeration
and ownership, declaration sorting/counting, axiom collection, and summary
construction. `total` covers those phases. It excludes import/startup time,
elaboration of the audit implementation, delivery of queued diagnostic messages,
and any subsequent forbidden-axiom attribution on failure. The outer
`Proof audit: ...s` measurement covers the whole Lean subprocess.

Module membership uses a name set and per-module counters use an index, so
ownership and bookkeeping do not scan the module array for every declaration.
The audit still submits every logical root to Lean's public axiom collector.
The root regression suite compares both exact roots and per-module counts with
an independent exhaustive environment scan, including a scaled fixture.

Compare two audit implementations against the same existing project artifacts:

```sh
git show BASE_COMMIT:ProofAudit.lean > /tmp/ProofAudit-baseline.lean
python3 scripts/benchmark-proof-audit.py \
  --baseline /tmp/ProofAudit-baseline.lean \
  --repetitions 3 --output /tmp/audit-comparison.json
```

Run in the development shell after building the project. Keep the checkout and
dependency caches stable and serialize this benchmark with other heavy work.
The command compiles neither project imports nor a new artifact cache. It copies
both audit sources into temporary directories, alternates their execution order,
retains raw logs, compares complete semantic reports, and checks project artifact,
inventory and configuration fingerprints before and after. Each repetition also
measures an import-only process for the audit's current four imports. That probe
is a separate workload, not an exact subtraction of import cost from another run.
Phase timings are retained when the supplied implementation reports them.
The default refuses an import closure that does not cover the inventoried modules.
For a deliberately partial cached workload, pass `--allow-partial`; the console
and JSON identify incomplete coverage and the JSON lists missing modules. Such
results must be reported as partial-workload measurements.

These measurements do not establish artifact provenance or candidate acceptance.
Dependency-cache stability and absence of transient edits remain assumptions.
Use the normal acceptance checks for the candidate being delivered. Compositional
reuse of audit evidence is part of the
[verification plan](research/verification-architecture-plan.md#compositional-audit-evidence)
and [#591](https://github.com/VladimirMarko/conaled/issues/591).

The original dependency-free foundation remains available:

```sh
./check-foundation.sh
```

It checks the six original root modules using Lean alone. That smaller command
does not validate the rest of the monorepo.

## Proof audit details

The full check ends with a transitive axiom audit of integrated local kernel
declarations, including private definitions and generated proof auxiliaries.
Coverage, candidate checks and audit ownership share the filesystem inventory in
`scripts/project_sources.py`, including newly added root modules. Standalone audit
commands run from the project root and require Python to obtain that inventory;
an inventory failure stops the audit. `ProofAudit` itself is infrastructure.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Admissions, application-specific axioms, and native-evaluation axiom shortcuts
are rejected. See [ProofAudit.lean](../ProofAudit.lean) for the precise treatment
of logical declarations and compiler-generated runtime declarations.

The verification driver itself has no connected formal interaction semantics yet.
The [verification architecture plan](research/verification-architecture-plan.md)
describes the proposed use of library contracts, fallible external observations,
and an explicit bootstrap path.
