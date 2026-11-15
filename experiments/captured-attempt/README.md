# Captured attempt

An isolated [#194](https://github.com/VladimirMarko/conaled/issues/194) adapter experiment. The [assessment](../../docs/research/captured-attempt-adapter.md) separates the checked conditional claims from the OS premises and runtime evidence. The original `measurement-attempt` pilot is unchanged.

From the repository root in the pinned environment, with the integrated modules built:

```sh
direnv exec . lake build Applications.Interaction.CapturedAttempt Examples.CapturedAttempt
taskset -c 0 direnv exec . python3 experiments/captured-attempt/test.py \
  --results-dir /absolute/fresh/private/results
```

The test directory must be absent. The harness retains source identities, environment metadata, per-case supervisor observations, raw adapter output, provisional evidence, sealed bytes and markers. `--only success mixed publication-after-write` selects the initial smoke. Without `--only`, all public cases run sequentially. These commands do not replace the repository's guarded fresh candidate build and proof audit.

The direct command is:

```sh
direnv exec . lake env lean --run experiments/captured-attempt/Main.lean \
  WORK CASE FAULT /absolute/path/to/fixture.py
```

`WORK` contains `live/A`, `live/B`, and empty `sealed/` and `barrier/` directories. Sealed inputs, channel files, attempt marker and evidence must be absent. The harness normally prepares this state. The target is Linux and the adjacent trusted Python fixture, which creates no descendants. Other actors may change only live inputs as specified by the writer protocol. Private-path ownership excludes concurrent publishers, symlink attacks and changes to sealed input. Preflight preserves existing resources; it is not a reservation protocol for competing callers.

The adapter reads each input up to 4097 bytes and refuses inputs larger than 4096. It records read bytes, writes private sealed files, and uses the checked capture state to authorize one child only after both seal receipts. The child redirects its own output to owned regular files, reports the exact bytes it consumed and their sum on stdout, and writes `fixture-complete` on stderr. The adapter checks that response against its captured bytes. Both channels are read up to 65537 bytes, with 65536 as the acceptance cap; prefixes survive errors. This experiment does not implement pipe draining or arbitrary-program capture. Startup diagnostics before the trusted child's redirection are not part of its accepted output protocol.

## Concurrent source capture

For `mixed` and `live-input-bug`, the supervisor starts a separate writer. It announces `writer-ready`, then waits for `a-read`. The adapter reads and seals `A0\n`, releases that barrier, and waits for `writer-done`. The writer closes an A update to `A1\n`, then closes a B update to `B1\n`, records its observed stable states, and announces completion. The adapter then reads and seals B.

The collected pair is A0/B1. It never coexisted in the fixture's live tree. The intended child consumes the sealed pair; `live-input-bug` deliberately passes the changed live paths and must be rejected despite exit zero. The model permits arbitrary input values and read histories; these small ASCII inputs are executable specializations, not a definition of external state.

## Cases and faults

Cases are `success`, `mixed`, `live-input-bug`, `nonzero`, `signal`, `timeout`, `boundary`, `missing-output`, `stdout-overflow`, `stderr-overflow`, and `invalid-output`. The signal case records the runtime's raw nonzero result without guessing its encoding. `boundary` may observe either normal completion or timeout; the assertions accept either consistent outcome.

Faults are `none`, `read-a-denied`, `read-b-error-after-prefix`, `seal-b-error-after-prefix`, `spawn-before-call`, `poll-error`, `completion-unknown`, `cleanup-unknown`, `cleanup-failed`, `publication-before-write`, `publication-after-write`, and `receipt-truncated`. Requested faults and actually applied injections are distinct fields. Prefix faults perform the prefix operation before raising. Cleanup injections mask the reported result after actual cleanup; they do not deliberately leak a process. A polling exception can cause cleanup before the child writes its marker, so that case permits zero or one marker. Absence of a marker does not prove no process was spawned.

Real missing and oversized input arrangements and an existing-evidence refusal are also tested. Permission denial is injected rather than inferred from chmod behavior under privileged execution.

## Publication and unknown results

The disk payload is provisional: publication unknown and success false. A successful write/close supplies a separate returned acknowledgment; it does not establish atomic replacement, fsync, durability or remote receipt. `publication-after-write` performs that write, then raises before acknowledgment. The returned selection stays unknown and refuses another launch, while the supervisor independently observes the file and one attempt marker. `publication-before-write` leaves no file in that controlled case; arbitrary write errors may leave partial or complete effects.

`receipt-truncated` withholds a complete stdout receipt after internal confirmation. The supervisor reports delivery unknown and does not recover success from the provisional disk record. A zero CLI code alone is insufficient evidence. Normally zero means the selected result was accepted, one means a completed conservative failure, and two means invalid arguments or preexisting resources. Missing or malformed receipts remain unknown to a caller.

The model's `advance`, `authorizeCaptured`, and observation projection execute in the adapter. Detailed bytes, raw process values and diagnostic events remain in the receipt alongside that projection. The component observation trace derives its smaller Measurement correspondence. The separate `Joint` protocol model adds capture/child identity, ordering, one physical spawn witness and exact publication payload to a same-prefix refinement theorem. It requires normalized events and local external witnesses; no verified decoder from this receipt to those witnessed events is claimed. IO truthfulness and the exact JSON encoding remain runtime premises. The isolated `Main.lean` is typechecked and tested, but is outside the integrated proof audit.

## Resource and trust limits

Process observation uses at most 100 `tryWait` calls with 10ms sleeps, then one SIGTERM request and at most 100 cleanup polls. A termination request is not a reap observation. Timeout remains timeout after successful cleanup. Barrier observation uses at most 500 polls. The supervisor limits each case to 30 seconds, bounds retained stdout and stderr to 1 MiB each, and kills/reaps its owned processes on failure. These are finite policies and externally enforced tests, not unconditional syscall or scheduler deadlines.

The installed runtime's Linux implementation was inspected locally: a returned raw zero follows waitpid's normal-exit branch with exit byte zero. Nonzero values retain their raw representation and project to unknown. Filesystem visibility, read semantics, private ownership, honest child consumption reports, wait/reap semantics and the runtime executing these calls remain named assumptions. No performance, crash-recovery or arbitrary-process refinement is claimed.
