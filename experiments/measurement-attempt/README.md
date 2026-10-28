# One measurement attempt

Experimental Lean adapter for [#216](https://github.com/VladimirMarko/conaled/issues/216).
The [pilot report](../../docs/research/measurement-attempt-pilot.md) states the
mathematical connection, primitive trust contract, and migration assessment.
This directory is outside the integrated proof audit. The command imports the
proved `Interaction.Measurement` controller and uses `begin`, `record`, and
`successful` for its launch authorization and final decision.

From the repository root, with dependencies available:

```sh
nix develop --command lake build Applications.Interaction.Measurement
nix develop --command python3 experiments/measurement-attempt/test.py
```

The public command takes six arguments:

```sh
nix develop --command lake env lean --run experiments/measurement-attempt/Main.lean \
  WORK LIVE_INPUT EVIDENCE MODE FAULT /absolute/path/to/child.py
```

`WORK` must be a private writable directory. `LIVE_INPUT` is an existing file
of at most 4096 bytes. The names `captured`, `output`, and `executions` within
`WORK` must not already exist. `EVIDENCE` is the destination of a provisional
JSON payload; using an existing directory at that path exercises a real
publication failure. Tests create and remove their own disposable directories.
The trusted child must be the adjacent `child.py`, run through `python3` from
the pinned development shell. Arbitrary programs are outside this experiment.

Modes:

| Mode | Actual fixture action |
|---|---|
| `success` | Read captured bytes, write them to the output file, exit zero. |
| `nonzero` | Write captured bytes, exit seven. |
| `spawn-failure` | Attempt an absent executable. On the tested Linux platform Lean returns a child exiting 255; this is recorded as `exit:255`, with missing output. |
| `timeout` | Write `partial:` and captured bytes, then sleep three seconds. |
| `boundary` | Write captured bytes, then sleep 0.99 seconds near the observation budget. Either observed completion or timeout is valid. |
| `mutate` | Lean overwrites live input with `changed\n` after capturing; the actual child consumes the captured original. |
| `overflow` | Write 4097 bytes, exceeding the evidence cap. |
| `missing-output` | Exit zero without producing output. |

Faults are `none`, `spawn-error`, `cleanup-failed`, `cleanup-unknown`, and
`completion-unknown`. These are deterministic adapter-boundary injections,
identified by `injected_fault` in evidence. `spawn-error` raises an IO exception
before OS spawn. Cleanup faults replace the reported cleanup observation after
normal cleanup; they do not deliberately leak a child or claim an observed OS
failure. `completion-unknown` withholds a known completion result to exercise a
conservative decision at an uncertain observation boundary.

## Evidence and bounds

The child uses an owned regular file as its output channel; stdout and stderr
are discarded. This experiment does not implement general stdout/stderr
capture. Every executed controlled child appends one marker to `executions`,
and the tests verify exactly one marker even when publication or completion
is uncertain. The adapter never retries a command.

Lean captures up to 4097 bytes to reject input larger than 4096, writes those
bytes to `captured`, then starts the child. The receipt records the declared
input path, exact captured byte array (an identity without hash collisions),
command vector, and live contents after optional mutation. This demonstrates
consumption of one captured input, not a coherent multi-file historical revision.
Concurrent modification of captured resources, dependency changes, hostile
symlinks, arbitrary/untrusted programs, and descendants are excluded.

Observation performs at most 100 `tryWait` calls, separated by 10ms sleeps.
If no exit is observed it sends SIGTERM and performs at most 100 further polls.
The result remains timeout even if cleanup subsequently observes exit. The
controlled child sleeps at most three seconds and does not create descendants.
Tests additionally impose a 30-second external supervisor timeout. These are
finite observation policies, not unconditional wall-clock termination or
arbitrary-process cleanup guarantees. `tryWait`, filesystem calls, and sleep
remain trusted runtime operations. Cleanup refers to child termination/reaping,
not deletion or crash durability of evidence files.

Output reads are capped at 4097 bytes; only 4096 are emitted. Overflow, missing
output, timeout, and unknown completion cannot produce accepted measurements.
Fixtures emit UTF-8 text. `output_bytes` retains the emitted byte prefix even
when text decoding fails; `output` then carries an explicit decoding marker. `elapsed_ms` measures monotonic elapsed time from
capture through process observation and cleanup, excluding evidence publication.
It includes runtime and observation overhead; no theorem identifies it with an
abstract resource cost or an arbitrary command's exact execution time.

The disk payload has `publication: unknown` and `success: false`: it is the
provisional record being published. After the write returns, stdout receives a
separate receipt with `publication: confirmed` or `failed` and the controller's
final success decision. The CLI exits zero exactly when that decision is true;
other completed observations exit one. Invalid arguments or failed input capture
can fail before an attempt receipt exists. Write completion does not assert
fsync, atomic replacement, or crash durability. A later stdout write failure can
also prevent receipt delivery; callers must treat missing receipts as unknown.

To retain actual receipts and provisional payloads for a run:

```sh
MEASUREMENT_RESULTS=/tmp/measurement-results.jsonl \
  nix develop --command python3 experiments/measurement-attempt/test.py
```

The optional JSONL file is appended to. Paths in records name disposable inputs
that the harness subsequently removes. The report retains a compact result
matrix; rerun the public suite to generate receipts for the current environment.
