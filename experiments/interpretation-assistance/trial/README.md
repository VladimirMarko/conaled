# Frozen two-arm author trial (#462)

The direct author made 3 Lean invocations; the assisted author made 13.
Independent statement review finds both final H1/H2 submissions meet the frozen
contracts. Independent replay matched all 16 exact recorded outcomes, including the one
expected failure, and audited all 15 passing snapshots. Reports and commands
are retained in `replay/`.
This is one author per arm on two tasks. It supplies no productivity ranking.

| Measure | Direct | Assisted |
|---|---|---|
| H1 full-submission first attempt | Passed | Passed |
| H2 full-submission first attempt | Failed; second passed | Passed |
| All actual Lean invocations | 3 | 13 |
| CLI invocations of Lean | 0 | 11 |
| Full-submission checks | 3 | 2 |
| Generated applications used in final proofs | 0 | 3 |

The direct failure was a rewrite attempted before exposing `finalExec`. Its
original source and compiler error are retained. The assisted author used the
extension package and two resource transport applications. It supplied the
extension proof and additive laws manually, and proved the compiler connection,
resource formulas, selected-witness properties and negative controls itself.
Image construction used native declarations. Both arms had native helpers.
No diagnostic-driven author repair occurred in the assisted arm: its checks
all succeeded. Development tests exercise the failure statuses separately.

## Evidence layout

- `setup/`: prospective prompts, obligations, registry changes, readiness,
  budget states and every counted round's source, log and receipt. Raw command
  paths name the original experiment directories.
- `authors/`: coordinator-frozen results and SHA manifests, including support
  files, generated CLI requests/results and the failed direct attempt.
- `author-output/`: original output tree, retained separately from its freeze.
- `handoff-sources/`: all tracked files of each isolated source environment,
  without Git metadata, dependencies or build artifacts.
- `prototype/`: exact prototype source and documentation at `3b5c9002`, including
  its prospective freeze. The old launch blockers and pre-trial statements are
  historical records, superseded by `setup/` readiness and launch evidence.
- `private-preparation/`: reference preparation, failed attempts, negative
  controls and unchanged-template applicability checks. Released only after
  both authors finished. Historical pending statuses are resolved by later
  independent reviews in the same archive.
- `development.tar.gz`: all retained development attempts/tests 1–9, focused
  and full-check logs, preparation and review handoff. Dependency provisioning
  artifacts are omitted. This is preparation cost, not author work saved.
- `origins.json` maps copied files to their original locations; `sha256.json`
  binds the archived bytes. The final report and portable replay instructions
  are written after the trial and are not prospective evidence.

The generic resource schema and implementation preceded private applicability
checks and author dispatch. The implementer had seen task descriptions, not
private proof solutions. This was a held-out application exercise, not blind
problem discovery. The original launch manifest records 45 minutes and 30
actual checks per arm, sequential dispatch, no exclusions, and cooperative
access restrictions. Exact underlying model/effort metadata was unavailable;
no token or runtime comparison is inferred from coordinator timestamps.

The prototype correction before launch is retained in Git: `e8704a20` failed
readiness finding `462-SPEC-1`; `3b5c9002` distinguishes checker infrastructure
failure from rejected evidence. No author source or frozen tool was repaired
after submission.

## Reproduction

Verify archive bytes from the repository root:

```sh
python3 - <<'PY'
import hashlib, json, pathlib
p = pathlib.Path('experiments/interpretation-assistance/trial')
for name, digest in json.loads((p / 'sha256.json').read_text()).items():
    assert hashlib.sha256((p / name).read_bytes()).hexdigest() == digest, name
print('Archive hashes match')
PY
```

For a source check, copy `handoff-sources/direct` or `handoff-sources/assisted`
to a new directory, initialize Git there, run `direnv allow`, and enter its
pinned shell. Provision the pinned Lake packages using the repository README;
use private project outputs. Build `TaskSetup462`, `Examples.DiagonalCoverage`
and `Examples.ConstructionTransport` (also `SquareKit.InterpretationDiagnostics`
for assisted). Copy the chosen `setup/control/ARM/round-NNN/source.lean` to
`Examples/ReplayRound.lean` and run:

```sh
direnv exec . lake env lean -o .lake/build/lib/lean/Examples/ReplayRound.olean Examples/ReplayRound.lean
```

Direct round 002 must fail; every other recorded round must pass. Comparing only
final submissions would omit this negative evidence. For an axiom audit use the
reviewer's retained `TrialAudit.lean` helper and a driver importing
`Examples.ReplayRound` and `TrialAudit`, followed by
`set_option trace.ProofAudit.roots true in #audit_project_axioms`.
Compile the helper to `.lake/build/lib/lean/TrialAudit.olean` first. The helper's
adaptation from the frozen repository audit is recorded in `replay/`.
This checks all eligible local/generated roots and their dependencies.
The original replay script and receipts preserve exact commands and exits;
its absolute paths must be relocated for a different machine.

To repeat development cases separately, extract `development.tar.gz` for the
original receipts and run the frozen `scripts/test-interpretation-assist.py`
with a new `--out` directory in a checkout of `3b5c9002`. Repeating checks does
not repeat the author experiment or add retrospective rounds to its counts.
