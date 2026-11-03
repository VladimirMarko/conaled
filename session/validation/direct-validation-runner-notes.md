# Direct validation runner: implementation handoff

Recorded 2026-11-03. This is an assigned implementation within the parent's
existing toolchain review loop. The current user exception in
`session/requirements/REQUEST-direct-toolchain-041.md` permits direct Lean/Lake
launching; every other project acceptance requirement remains in force.

## Scope and starting state

The new files are `run-direct-validation.py`, `test-direct-validation.py`, and
this handoff note, all under `session/validation`. None existed at the initial
inspection. No historical evidence or wrapper was edited. The author made no
formal branch commit and changed no repository file, dependency, environment
limit, profile, or tracker.

The following checkouts had empty index/working-tree/untracked status before
this implementation:

- `conaled`: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- `import-correction-r3`: `901f734161920a76f3b399a575805b9a1d31e971`.
- `signed-potential`: `d24c443ba22019613b1ce646d6eed7279c791ad6`.

The parent owns the stable artifact snapshot and independent Standards/Spec
review for these files together with the direct profile/launcher helpers.
This handoff does not constitute either review or acceptance.

## Public interface

Invoke the runner directly with Python; it invokes the environment launcher
itself. Use a new run ID for every attempted invocation that produces evidence.

```sh
python3 session/validation/run-direct-validation.py full import-901-direct-fresh-r1 --fresh
python3 session/validation/run-direct-validation.py focus signed-d24-direct-r1
python3 session/validation/run-direct-validation.py verify import-901-review-r1 --full-record import-901-direct-fresh-r1
```

The examples are commands to run only when dependencies are fully prepared,
the helpers are frozen/reviewed, and no conflicting writer is active. None of
these three build/verification commands was executed by this implementer.

The full mode fixes the exact prerequisite candidate and runs stock
`./check.sh --candidate HEAD`; `--fresh` adds the stock `--fresh --jobs 1` flags.
The first full check after this tooling recovery must use that fresh mode,
as README requires after tooling changes. Focus fixes the corrected signed-potential
candidate and the eleven previously assigned modules. Verify runs unchanged
`./check.sh --verify-candidate HEAD` only after checking the named successful
full-run evidence, its log digest, its saved stock verification record, the
live record, and current input identity. A fresh full record is bound to the
actual fresh command and stock record mode; incremental evidence is bound to
its incremental command and mode. Verify always omits `--fresh` and `--jobs`,
using the mode of its saved successful full record as the stock verifier requires.

Each run writes `RUN_ID.json` and `RUN_ID.log` beside the runner; successful
full validation also preserves `RUN_ID.verification.json`. Existing paths,
including symlinks, are refused. New record/log creation is exclusive; record
updates are atomic. Historical interrupted records remain untouched and cannot
qualify as successful evidence.

Full and verify share `active-validation/full-build.lock`; focus uses
`active-validation/focused-build.lock`. Both acquisitions are nonblocking:
when a slot is occupied, the invocation refuses before launching a command.
This preserves the one-full-plus-one-focused ceiling without an unbounded
queued process. The old focus wrapper's blocking wait is not retained.

Snapshots record the exact clean project HEAD/tree, source hashes, exact clean
dependency HEADs/trees, the pinned manifest, the complete deterministic launcher
description, and the controller source hashes. Full/verify hash all tracked
project files. Focus hashes the targets and recursive local imports together
with the five existing toolchain/Lake/flake control files. Queued, start, and
final snapshots must agree. The exact candidates use ordinary header import
declarations; this helper is not a general Lean parser.

The runner supervises its own child process group. SIGINT/SIGTERM cancellation
attempts to stop only that group and records an actually observed terminal
result where available. A hard interruption or workspace loss can still leave
a `queued`/`running` record, which must remain terminal-unknown evidence.

The record always contains `acceptance: false`. A passing focus is development
evidence only. A successful full gate still requires the existing independent
reviews and final stock verification immediately before acceptance. A saved
verification record is copied only after an actual zero command exit and
unchanged inputs; its presence alone is insufficient.

## Validation performed

Following the repository implementation/TDD references, tests exercise the
public runner CLI in temporary workspace fixtures. The agreed boundary is
refusal of conflicting or insufficient evidence; these tests never provide a
mock Lean/Lake command or synthesize passing formal evidence.

Three individual red-to-green cycles were observed:

1. Refuse an existing evidence filename without overwriting its contents.
2. Refuse an interrupted full-run record as support for verification.
3. Refuse a second full invocation while the full-validation lock is held.

Final command: `python3 session/validation/test-direct-validation.py` — exit 0,
three tests passed. The runner's public `--help` command also exited 0. Both
Python source files parsed successfully with `ast.parse`. Temporary fixture
directories were removed by the tests.

This implementer ran no Lean/Lake compiler, cache preparation, focused build,
full audit, or candidate verification. Actual successful terminal recording
must come from the coordinator's genuine jobs. Before/after hashing does not
prove the absence of transient edits and does not make shared writable
dependency outputs safe; the established frozen-input discipline remains.

Initial r1 implementation hashes, retained as history before the fresh-mode correction:

| File | SHA-256 |
| --- | --- |
| `run-direct-validation.py` | `9b8410607494646072488743126fc0c6f7dcc94e500213b395b2b8486446bca6` |
| `test-direct-validation.py` | `0d8e9660f47fbdedf2fd0e739fef1b76e6884b604e7a15d07a2db6d2814ea52b` |
