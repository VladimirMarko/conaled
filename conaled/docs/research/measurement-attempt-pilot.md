# One measurement attempt through a Lean controller and adapter

This experiment implements the bounded plan in
[#216](https://github.com/VladimirMarko/conaled/issues/216), under
[#194](https://github.com/VladimirMarko/conaled/issues/194), as evidence for
[#195](https://github.com/VladimirMarko/conaled/issues/195). It does not replace
production measurement or verification scripts. The starting revision is
`89dcae55212c7597adb49dc813e817d6d44b39ac`.

## Question and scope

Can a small executable controller reuse the library's observation contracts,
serve as the decision procedure of a Lean IO adapter, and preserve unsuccessful
or incomplete outcomes through evidence publication?

The experiment permits one controlled child attempt, with no automatic retry.
The child uses a private regular-file output channel. This is a cooperative
fixture protocol, not a generic subprocess stdout/stderr collector. Input
capture and live-file mutation are exercised within temporary directories.
Finite polling bounds the number of observation attempts, not arbitrary OS
latency. Crash durability, hostile children, child descendants, distributed
storage, arbitrary dependency mutation and universal wall-clock deadlines are
outside this experiment's guarantees.

## Formal controller and checked cases

[`Applications/Interaction/Measurement.lean`](../../Applications/Interaction/Measurement.lean)
defines an independently stated `Good` observation requirement and executable
`decide`. `decide_iff` establishes both acceptance and rejection. Completion,
output completeness, cleanup and publication remain separate observations;
unknown completion cannot become success because cleanup succeeded.

`begin` consumes the authorization in a retained controller state. The
`begin_safe`, `recording_started` and `no_reexecution` results use the shared
`Safe` and `Stable.closure` interfaces: arbitrary finite observation updates
cannot authorize a second start in that same controller. This does not establish
global exactly-once execution across a program restart or construction of a new
controller. `record` may replace observations; this is not a monotonic history
or recovery journal.

`recording_refines` and `recording_safe` connect the recording operation to its
allowed-record contract using `Refines.property`. The `successful_world` theorem
then connects successful observations to an independent `Completed` world
predicate under four primitive `Corresponds` obligations. It does not establish
those primitive obligations for an arbitrary OS. The reusable laws remove the
invariant/transport steps, but most of the controller is simple evidence
selection; this pilot does not establish that the abstract layer reduces total
proof-author effort compared with a direct proof.

[`Examples/MeasurementAttempt.lean`](../../Examples/MeasurementAttempt.lean)
connects public results to reachable success, nonzero exit, unknown completion,
partial timeout, missing output, unknown cleanup, failed/unknown publication,
and two uncertain observation updates without reauthorization. A false
publication world violates the primitive correspondence premise. The captured
input case reuses `Snapshot.compile_sealed` with captured 17 and live 23; the
runtime fixture separately checks actual consumed bytes. Neither case proves a
coherent historical revision of multiple files.

## Evidence boundaries

The pure controller and its checked applications belong to the integrated Lean
library and its ordinary proof audit. The experimental IO adapter is compiled
and tested separately. Its process/filesystem primitives cross the runtime and
OS boundary; successful compilation does not establish their refinement.

The trusted execution assumptions include truthful returned process status,
correct file contents and identities for successful reads/writes, exclusive
ownership of the experiment directory, operation of the pinned runtime and
compiler, and the controlled child's protocol. Failures and unknown observations
within the supported model remain explicit. The pilot does not prove the OS,
compiler, runtime or storage truthful.

## Adapter protocol and failure evidence

The public command and fixtures are documented in the
[experiment README](../../experiments/measurement-attempt/README.md).
[`Main.lean`](../../experiments/measurement-attempt/Main.lean) imports and calls
the proved `begin`, `record` and `successful` definitions. Its IO branch does
not duplicate their final acceptance predicate. The output observation is a
bounded regular-file read from a controlled child, not an unconstrained pipe.

The evidence file is a provisional payload with publication unknown and success
false. Only after the write returns does the adapter emit a separate stdout
receipt describing observed publication and final acceptance. A failed write
can leave partial data; a missing receipt is not confirmation. There is no
atomic-publication or durability theorem. This deliberately exposes the gap
between process completion, evidence storage and observation of storage.

A real missing executable on the tested platform returned a child exit of 255,
not a caught spawn exception. The fixture retains this distinction: actual
exec failure produces `exit:255` with missing output, while an explicitly
injected pre-spawn exception produces `spawn-failed`. Cleanup-failed and
cleanup-unknown cases replace the reported boundary observation after normal
cleanup; they do not deliberately leak children or demonstrate an actual OS
cleanup failure. Completion-unknown withholds an observed result; a separate
near-budget child exercises an actual timing boundary without requiring one
schedule-dependent outcome.

Capture, process observation and cleanup contribute to `elapsed_ms`, measured
with the monotonic runtime clock. Publication is excluded. The number is an
empirical duration including overhead, not a proof of the mathematical cost or
an unconditional runtime deadline. The fixture's execution marker is observed
through its public filesystem protocol to check that uncertain outcomes do not
lead to another child execution.

## Validation environment

The experiment was developed in a separate worktree. The pinned toolchain is
Lean 4.35.0, revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, on
`Linux-6.18.58-x86_64-with-glibc2.42`. Commands use the Nix development shell.
The initial `lake-manifest.json` SHA-256 is
`dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`;
`flake.lock` SHA-256 is
`8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f`.

## Retained runtime results

The final adapter suite passed 12 tests covering 13 cases. The
[retained JSONL](../../experiments/measurement-attempt/evidence.jsonl) contains
actual receipts and provisional disk payloads from that run; their temporary
paths identify disposable fixtures that were removed afterward. The near-budget
case is allowed to complete or time out depending on scheduling; its recorded
outcome is one observation, not a repeatability claim about that race.

| Case | Completion | Cleanup | Publication | Accepted |
|---|---|---|---|---|
| mutate | exit:0 | confirmed | confirmed | true |
| cleanup-failed | exit:0 | failed | confirmed | false |
| cleanup-unknown | exit:0 | unknown | confirmed | false |
| spawn-error | spawn-failed | confirmed | confirmed | false |
| missing-output | exit:0 | confirmed | confirmed | false |
| nonzero | exit:7 | confirmed | confirmed | false |
| overflow | exit:0 | confirmed | confirmed | false |
| timeout | timeout | confirmed | confirmed | false |
| publication failure | exit:0 | confirmed | failed | false |
| boundary | timeout | confirmed | confirmed | false |
| spawn-failure | exit:255 | confirmed | confirmed | false |
| success | exit:0 | confirmed | confirmed | true |
| completion-unknown | unknown | confirmed | confirmed | false |

The public suite checks the controlled child's execution marker in every case:
one execution when the child runs and zero for injected pre-spawn error or
failed exec. Every rejected case retains a non-successful receipt. Capture
mutation retains the original bytes even after the live fixture becomes
`changed\n`. Output overflow and missing output reject otherwise zero exits.

Integrated verification uses `nix develop --command ./check.sh --jobs 2`, which
freshly checks source and runs the exhaustive audit. The exact-candidate
build/audit and independent review outcomes are recorded with #216. Runtime
coverage comes from the public adapter suite, not from the integrated audit.

## Decision: proceed with a narrower migration specification

The pilot supports reusing a proved decision core from a Lean IO runner. It does
not yet support replacing the production benchmark with this adapter unchanged.
The productive next step is a bounded common-runner specification under #195,
with real measurement workloads and explicit output, identity, process and
publication requirements. A broader effect hierarchy is not a prerequisite.

The current event-list interface was not needed for this fixed one-attempt
policy. Reply-dependent orchestration and recovery should be introduced only
when their concrete obligations justify them. Primitive truth remains a runtime
trust boundary; moving observations into a typed record did not discharge it.

## Production migration boundary

The order-certificate benchmark needs compilation/audit separation, command and
dependency provenance, elapsed-time evidence, and failure records. The numerical
execution consumer also needs domain-specific durations, tolerances, subdivision
counts, numeric sizes and resource cutoffs. A common observation/recording core
can support both, but these workload-specific requirements are not implemented
by a cooperative process fixture.

The next migration specification must exercise both consumers through the
selected support, preserve their public behavior, and justify any stronger
process, timing, resource, capture or publication promises. This experiment
neither closes #194/#196 nor authorizes a production port. A result about one
attempt does not establish retry safety or eventual acknowledgment.
