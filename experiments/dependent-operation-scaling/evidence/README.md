# Frozen author-trial evidence

This directory preserves the #358 experiment at frozen candidate
`2838b20125fc4253f55eb1feb45f069f604175df`. The [research report](../../../docs/research/dependent-operation-scaling.md)
explains scope, measurements and conclusions. The unchanged [protocol](../protocol.md)
and [task](../task.md) were independently reviewed before exposure.

- `native/` and `shared/` preserve exact author attempts, failed checks,
  diagnostics, activity records and timing. They are experimental evidence,
  not integrated library modules. Do not repair failed historical submissions.
- `native-public-manifest.json` and `shared-public-manifest.json` identify the
  exported source and public instructions. Source files come from the frozen
  Git candidate. Pinned dependency copies and project output caches are not
  stored here; preparation records identify their revisions and hashes.
- `setup/` preserves export, freeze, input verification, smoke, dispatch,
  coordinator replay and axiom-check evidence. Coordinator attempts are separate
  from measured author attempts. Absolute paths in original receipts describe
  the execution environment; they are not required durable locations.
- `review/` contains the pre-exposure approvals and independent statement
  assessment. Final ticket and integration review are separate acceptance gates.
- `run_attempt.py` is the reviewed timing/lock wrapper around the unchanged
  checker at `experiments/dependent-author-trial/check_attempt.py` in the frozen
  candidate. `test_runner.py` and `runner-unit-results.json` exercise status,
  exit propagation, lock contention and duplicate protection with a stub.
  `runner_smoke.py` connects it to the real checker; real receipts are in setup.

| Stage | Native exact snapshot | Shared exact snapshot |
|---|---|---|
| A | `native/Attempt02.lean` | `shared/Attempt03.lean` |
| B | `native/Attempt03.lean` | `shared/Attempt04.lean` |
| C | `native/Attempt07.lean` | `shared/Attempt06.lean` |
| Repair | `native/Attempt08.lean` | `shared/Attempt07.lean` |

The trial agents were fresh, with no conversation fork or task exposure.
Model and reasoning configuration were unavailable. They had identical task
outcomes but different prepared support. Staggered starts, initial timestamp
estimation, cumulative tasks and coupled dimensions limit timing comparisons.
Stage active time includes reading, editing, checking and reporting; recorded
lock waits are excluded. Reported child peak RSS is a Linux high-water measure,
not aggregate concurrent memory. Setup and coordinator work are not author time.

Preservation compares selected results. The tail in this experiment is the
chosen last member reconstructed from the selected runtime value, not an
arbitrary incoming witness. Author compilers use typed source syntax and two
executable passes; the prepared library separately checks typed target lowering.
