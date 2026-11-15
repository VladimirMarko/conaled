# Import footprint prerequisite: fourth direct-provider correction

Status: independent provider/preservation checks passed. Focused round r1 was
interrupted without a terminal result; its cause is unknown. Its unchanged raw
evidence is preserved, ownership is released, and root may run the stock full
check of frozen candidate 901f734. No focused success, compiler failure,
full-gate, audit or acceptance claim is inferred.
This continues existing local 10018 under requirements/import-footprint.md v1.
Root owns the frozen candidate, commits, whole-project gate and reviews.

## Observed failure and minimal correction

The unchanged full check of candidate 324962e733886e66d6cd92af6cb68627ed4c8f1d
reported IMPORT-VAL-004 in Examples/IndefiniteService.lean: unknown constant
Nat.size_pow in the existing unbounded-Nat-size example, followed by its
unsolved contradiction goal. The observation is preserved in
session/validation/import-footprint-324962e-observed-errors.json. The active
full 324 checkout/process was neither edited nor canceled by this worker.

Root prepared clean committed candidate
901f734161920a76f3b399a575805b9a1d31e971 on pfds/import-footprint-r3 in the
separate import-correction-r3 checkout. Its sole change relative to 324962e is
one new line in Examples/IndefiniteService.lean:

```lean
import Mathlib.Data.Nat.Size
```

The pinned provider was independently inspected. In namespace Nat,
Mathlib/Data/Nat/Size.lean:94 declares:

```lean
theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1
```

That is exactly the existing proof's rewrite. Applying the alleged bound to
2^bound and rewriting leaves bound+1 ≤ bound, which the existing omega step
contradicts. The example distinguishes a fixed number of state fields from a
uniform representation-size bound. Its statement, chosen witness and proof
body are unchanged. No extra theorem, test, proof adjustment or broader
requirements change is introduced.

## Independent source preservation

The checkout was clean at verification and its working source exactly matched
the committed candidate. Independent byte comparison removes import lines
only, preserving all remaining bytes and newline structure.

- From 324962e to 901f734, only Examples/IndefiniteService.lean changed; every
  non-import byte is identical.
- From fixed 10018 base 70a1477d822efd4fdcec2007280f650bb4695eda to 901f734,
  exactly six files changed: Applications/FRP/Demand.lean, Equivalence.lean,
  Finite.lean, Spec.lean, Examples/FRP.lean and Examples/IndefiniteService.lean.
  Every non-import byte in all six files is identical. No other path changed.
- Therefore the source declarations, proof scripts, checked cases, toolchain,
  dependency pins, build/audit code, guards and policy are retained. This is a
  source-byte claim, not a claim that elaborated kernel artifacts are identical.

Evidence is preserved in:

- active-validation/import-footprint-r3-source-comparison.json
- active-validation/import-footprint-r3-fixed-base-comparison.json

The Mathlib checkout is clean and matches manifest revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The directly inspected provider SHA-256 is
`ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b`.
The corrected example source SHA-256 is
`0daaf049128e56210c605cc5b2d5cf8b155aad1727eac6bad189615fc75fa7fd`; its shared non-import SHA-256 is
`1a5ce27ad026bb55452a3106e8783ce94ff7f95a06a5a2bbe4971dd9ff52a652`.

## Intended unchanged target coverage

The focused target recompiles the existing Examples.IndefiniteService cases:
single/two-delay finite traces and stream behavior; resource/work/arena bounds;
parallel and pure service composition; compiled-delay source connection;
finite-wait productivity; the redundant-complement representation's step,
output and retained-size transport; and unbounded Nat-size/history witnesses.
None of those cases was replaced or weakened. The direct import repairs the
last Nat-size witness's missing theorem scope.

## Focused validation setup

Target Examples.IndefiniteService was launched in import-correction-r3 with
its private project build directory. External packages use the established pinned
shared package symlink. The new private checkout started without project build
outputs; ordinary dependency compilation is allowed. No outputs were copied
from the running full 324 checkout.

The usual pinned offline Nix command, LEAN_NUM_THREADS=1 and shared focused
lock were used. The wrapper recorded the committed HEAD and hashes of 60
local source/config/provider inputs before queueing and at lock acquisition.
It was configured to repeat those hashes at completion and reject changed
inputs; that final automatic recording did not occur. Default proof limits and compiler
settings are retained. The source candidate remains immutable.

Evidence: active-validation/import-footprint-r3-focused-r1.{json,log}.
Session 54270 acquired the focused lock at 2026-11-02T22:02:16.541145+00:00.
Report/session writes were held during checkpoints 021 and 022 and resumed
only after root released each barrier; compiler/evidence writes stayed in active-validation.

The log also retains inherited module-system warnings and the nonfatal unused
`mul_left_comm` simp-argument warning in Applications/Timing/Digital.lean:186.
That dependency compiled; no warning was suppressed or proof script changed.

## Observed interruption and handoff

The source stayed frozen throughout the attempted check. The log records
successful dependency compilation through Applications.FRP.Temporal (523s),
with last progress line `[3177/3191]`; that is a dependency milestone, not a
completed target or a passing whole build. The log contains no compiler-error
line and no Examples.IndefiniteService completion.

An earlier root-agent attempt to poll session 54270 returned Unknown process
id while this owning agent could still poll it and observe its active compiler.
That earlier event did not show an interruption; it was consistent with a
routing limitation.
The later observations are different:

- By 2026-11-02T22:42:42.565045+00:00, this owning agent's own write_stdin call
  returned `Unknown process id 54270`. The original automatic JSON still had
  queued/started/start hashes and no terminal fields.
- At 2026-11-02T22:42:50.529359+00:00, a read-only exact-checkout process scan
  found no process, and known process/group IDs 597206, 597211 and 610050 no
  longer existed. Root had independently observed absence of the owned
  compiler processes. No cancellation or restart was issued by this worker.
- After those observations, the candidate remained clean at 901f734. All 60
  current source/config/provider hashes equalled both before/start records.
  This is a post-interruption integrity check; it does not create a missing
  successful terminal validation record.

The interruption has no known cause or recovered compiler exit code. Both
raw active-validation files remain unchanged. Byte-for-byte copies and the
independent source comparisons are now preserved in session/validation:

- import-footprint-r3-focused-r1.json
- import-footprint-r3-focused-r1.log
- import-footprint-r3-source-comparison.json
- import-footprint-r3-fixed-base-comparison.json

The separate observation/release record is
session/validation/import-footprint-r3-focused-interruption-r1.json. It records
`status = interrupted_without_terminal_record`,
`root_may_start_full_candidate = true` and `ownership_released = true`.
The raw JSON SHA-256 is
`d7b41244ca43e0af0ab96a088fb97bd8b4c19eeea223a0f87187637b59bde711`;
the raw log SHA-256 is
`98160ffe3934190bf4bb539f4fc8c3a2b1749276b2eaf9721a74922c85ca7eec`.

The focused round will not be restarted. Root's stock full check of frozen
901f734 will exercise the corrected example and its whole compiler closure.
The candidate still requires that complete check, exhaustive audit, matching
success record/final verification and both independent review axes. No
memory, speed or full-project resource improvement is inferred from this
interrupted round or from the import change.
