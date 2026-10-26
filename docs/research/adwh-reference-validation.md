# ADWH checkpoint 233 reference validation

Reference validation for [#150](https://github.com/VladimirMarko/conaled/issues/150),
part of [#149](https://github.com/VladimirMarko/conaled/issues/149), on 2026-10-26.
The source is the immutable [checkpoint 233 archive](../history/algorithm-design-haskell/README.md).
This checks the existing mathematical library without importing it into the
production library or changing its statements.

## Reproduction boundary

The repository archive and manifest were checked against their recorded SHA-256
values, then all 10,463 extracted files were checked against the member manifest.
A separate disposable copy of `project/adwh-lean/` supplied the build sources.
Before compilation, the supplied gate's `source_gate` and `control_gate`
reproduced its recorded 1,240 source entries and five verification-control
entries exactly. The source gate checks forbidden constructs and requires every
main-library source to be reachable from `ADWH.lean`.

The build used Lean 4.35.0, revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, selected through the repository's
pinned direnv environment. Each module was compiled once in dependency order,
with at most four concurrent processes, each using one Lean worker:

```text
<elan which lean> -j1 -DautoImplicit=false -DwarningAsError=true \
  -o <fresh-objects>/<module-path>.olean <module-path>.lean
```

The working directory was the disposable library root. `LEAN_PATH` was replaced
with the initially empty `fresh-objects` directory. No supplied `.olean` files
existed in the restored library, and no project or Mathlib build cache was on
that path. Lean's installed standard-library objects remained dependencies.
This establishes fresh ADWH elaboration; it does not rebuild the Lean compiler
or its standard library.

The unchanged supplied `scripts/Audit.lean` was then run with the same options
and fresh import path. Its module-origin filter selects all `ADWH` declarations
in the environment, including private and generated declarations, and checks
transitive axiom dependencies with `Lean.collectAxioms`. Only `propext`,
`Quot.sound` and `Classical.choice` are allowed. The driver also checks the audit
summary, unique declaration names and every reported axiom list. The supplied
`validate_coverage` function reconciles the preserved coverage references against
this invocation's audit records. Optional `ADWHMathlib` references are excluded
explicitly; no stale optional audit is used.

## Results

**The full reference build, exhaustive audit and coverage-reference validation
passed.**

| Check | Result |
| --- | --- |
| Fresh main-library compilation | 1,240 modules, including `ADWH.lean` |
| Transitive axiom audit | 83,281 declarations; 51,041 theorem declarations including generated proofs |
| Coverage references | 17,846 of 17,846 resolve to audited theorems; none missing, wrong-kind or optional-skipped |
| Source/control consistency | All 1,240 source and five control fingerprints unchanged |
| Archive preservation | Archive, manifest and all 10,463 pristine restored members verified again after completion |
| Fresh build elapsed | 1,260.788 seconds |
| Audit elapsed | 203.027 seconds |
| Gate elapsed | 1,474.477 seconds |

Gate timing includes source/control checks, compilation, audit, coverage and
final source/control comparison. It excludes archive extraction and later
receipt packaging. Other reconstruction builds ran concurrently, so these
measurements are validation observations, not performance benchmarks.
No proof, source statement or verification control was modified.

## Evidence and limits

The [machine-readable receipt](adwh-reference-validation.json) records counts,
timing scope, compiler identity and hashes of the detailed evidence. Full logs,
per-module commands, the validation driver, restored sources and fresh objects
are retained locally at:

```text
/home/vlad/.local/state/conaled-supervision/2026-10-26/149/150/
```

`validate.py` orchestrates the supplied gate functions and direct compiler
commands. It was launched from the conaled worktree with
`direnv exec . python3 <state-directory>/validate.py`; `commands.jsonl` records
every module's exact command, working directory, import path, exit code and
elapsed time. `proof-audit.jsonl` and `coverage-validation.json` retain detailed
results. These local logs are supplemental evidence; the repository archive
and receipt are the durable source and compact result. The [reference-specific driver](adwh-reference-validation.py) restores and
verifies the repository archive itself, then repeats the same build and audit.
Run it from the repository root with a new, nonexistent destination:

```sh
direnv exec . python3 docs/research/adwh-reference-validation.py /tmp/adwh-validation-new
```

The tracked driver adds archive restoration to the local run's build driver;
it does not change the supplied gate or Lean sources. It checks `STOP` and
`USAGE-UNKNOWN` files in the destination's parent between build completions.
Revalidation requires no Downloads artifact or supplied project objects.

The production conaled audit uses its own module ownership rules and enumerates
module metadata plus current-module declarations. It separates compiler-created
unsafe runtime declarations from logical roots and rejects source-authored
unsafe declarations. The supplied audit instead scans the full environment
and checks every declaration owned by `ADWH`; its Python source guard rejects
unsafe syntax. Both use the same foundational-axiom whitelist. This reference
run does not alter conaled's ownership rules, public entrypoint or build targets.
Every reconstructed slice still requires conaled's build, audit, statement
review and connected examples.

Coverage-reference validation establishes that selected references resolve to
audited theorems. It does not establish complete textbook coverage or Haskell
operational equivalence. The parallel [coverage inventory work](https://github.com/VladimirMarko/conaled/issues/156)
found that 266 of 1,239 correspondence records contain a `source_sha256` that
differs from the preserved source bytes; 973 match, and the aggregate has no
correspondence record. This run independently confirmed those counts against
the extracted archive. All actual source hashes still match the preserved
inventory and supplied gate. Stale correspondence hashes cannot certify current
source-to-textbook coverage. Historical metadata was preserved unchanged;
reconstruction must review the affected correspondence. Optional Mathlib material and kernel experiments were
not built. The stock `cqueens 16 = 14772512` proof remains unfinished, and
Chapter 6's accepted groups-three research qualification remains unchanged.
