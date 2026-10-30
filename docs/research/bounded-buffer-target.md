# A concrete target for bounded-buffer costs

Investigation [#250](https://github.com/VladimirMarko/conaled/issues/250) tests
whether the [#239 model](bounded-summary-implementation.md) predicts useful
choices on an accessible execution target. The result supports its every-prefix
and update-heavy rankings on this workload, but does not support treating unit
tariffs as runtime units. The nearly tied batch example illustrates that limit.
Neither existing realization nor its Lean theorem is changed.

## Target choice and semantic obligation

| Candidate | Useful evidence | Additional work for this investigation |
|---|---|---|
| Compiled Lean | Exercise the current definitions and runtime | Explain Vector, closure, recursion and runtime sharing costs before interpreting indexed tariffs |
| Native C | Explicit byte slots and finite machine counters | Introduce compiler provisioning, undefined-behavior obligations and a separate implementation |
| Pinned CPython with bytearray | Existing shell, byte indexing, observable allocation and explicit loops | Account for boxed counters, interpreter dispatch and allocation; no compiled-code cost theorem |

We selected the last option for a bounded feasibility experiment. This is not a
language migration or a preferred production backend. The executable is
[experiment.py](../../experiments/bounded-buffer-target/experiment.py).
The tested interpreter is CPython 3.13.15, built with GCC 15.3.0, running on
Linux 6.18.58 x86_64 with glibc 2.42. Its Nix executable path, compiler build
configuration, CPU details, clock, source hashes, repository base and dependency
pins are retained in the [evidence](../../experiments/bounded-buffer-target/evidence.jsonl).

A target state has a bytearray of capacity `N`, length `n`, a mode tag and a
parity field. Its decoder is the ordered first `n` bytes interpreted as Booleans.
The correspondence condition requires `0 <= n <= N`, all slots in `{0,1}`, and,
for the cached mode, cache agreement with XOR of the decoded sequence. Unused
slots are initialized too. Construction accepts `0 <= N <= 2^32-1`; checking
this range does not guarantee that allocation succeeds. Python counters are
boxed arbitrary-precision integers, **not uint32 machine cells**. The range guard
and append-before-increment check maintain the chosen finite range without
modular wraparound. The experiment does not allocate near the upper bound.

An accepted append writes at `n`, increments it and, in cached mode, updates
parity. At capacity, overflow leaves every field unchanged. Plain query scans
indexed slots; cached query reads parity. Observe returns the full ordered prefix
as bytes. Conversion copies all capacity slots, copies length and scans the
visible prefix for parity while the source remains live. These operations are a
handwritten candidate correspondence to `Buffer.decode`, `plainStep`,
`cachedStep` and `Valid` in the
[semantic source](../../Applications/Sequences/BoundedSummary.lean), not a proved
compiler interpretation. Full histories remain observable; the parity cache
never substitutes for them.

The executable compares exact replies, decoded states and cache validity against
an independent list-and-sum-modulo-two specification on **5,460 traces**: every
command sequence of length zero through five for capacities zero through three.
Commands include both Boolean appends, summary and full observation. This covers
empty, exact-capacity, overflow and repeated-query cases. Converted snapshots
are checked against all four possible next commands. An intentionally invalid
cache yields a different reply; invalid capacities are rejected. Tests also
recover #239's published unit-cost pairs `(26,27)`, `(41,30)` and `(17,26)`.
These finite checks do not establish universal refinement.

## What the costs count

The `model` function projects the existing unit-tariff recurrence; it is kept out
of timed execution. It is not an instrumented count of Python or CPU events.
The [Lean cost source](../../Applications/Resources/BoundedSummary.lean) remains
the authority for those equations. Each target difference matters:

| Model item | Concrete target operation and mismatch |
|---|---|
| `N` construction slot writes, counter and optional cache write | `bytearray(N)` initializes storage in runtime code. Object, mode and parity fields exist even in the plain implementation; these extra writes are outside #239's model. |
| Capacity test, slot write, counter update | Python method dispatch, `len`, comparison, indexed byte assignment and boxed integer arithmetic; no one-instruction interpretation |
| Scan `n+1` visits and `n` combines | `range` iteration, byte reads and Python XOR. Loop machinery and indexing checks have overhead; no recursion frames are used. |
| Cached read and combine/write maintenance | Attribute access and XOR assignment; interpreter specialization and integer reuse affect actual work |
| Output `n+1` visits and `n` constructors | A bytearray slice followed by bytes conversion uses bulk runtime copies and temporary storage, rather than one List constructor per element |
| Copying conversion `2N + 2n + 2` units | Bulk bytearray copy plus Python scan and field setup; the copy's byte bandwidth and the scan's interpreter overhead have different prices |
| Retained `N+1` or `N+2` units | Byte storage, object headers, references, tags and boxed values. Both modes have the same Python object shape, so abstract retained-unit ordering is not a physical-byte ordering. |
| Recursive scan workspace | Replaced by an iterative loop with constant many live scalar references; allocation churn and interpreter machinery remain |

The target returns a sequence snapshot, not a streaming observation. At output
construction a length-`n` slice and a length-`n` bytes value can overlap. The
consumer then folds each byte into a 32-bit checksum and releases the reply.
This consumption, command dispatch and reply tuples are inside the timings but
outside #239's tariff. Commands are prepared beforehand and excluded. No output
queue is retained; retaining one would require an additional bound. Checksum
arithmetic itself uses Python integers before masking, not machine wrapping.
Checksums prevent unused outputs from being discarded and expose every public
reply to the caller; correctness tests compare exact outputs, not checksum
collision resistance.

Conversion has simultaneous source and destination arrays. After assignment the
old buffer becomes unreachable; runtime reclamation and allocator reuse are not
proved or guaranteed to return memory to the OS. `tracemalloc` samples below
observe Python-tracked allocations from a single execution, excluding earlier
input construction and interpreter startup. They are neither RSS nor universal
peak bounds. The official [bytearray documentation](https://docs.python.org/3.13/library/stdtypes.html#bytearray-objects)
describes byte-valued mutable sequences; [tracemalloc](https://docs.python.org/3.13/library/tracemalloc.html)
documents the tracked-memory boundary. These API contracts do not establish our
state relation or a physical allocation-free implementation.

## Reproduction and retained observations

From the repository root, use new output names because existing evidence is
never overwritten:

```sh
direnv exec . python3 experiments/bounded-buffer-target/experiment.py /tmp/buffer-results.jsonl
direnv exec . python3 experiments/bounded-buffer-target/experiment.py /tmp/buffer-failure.jsonl --inject-allocation-failure
```

The first command must exit zero and end with `complete: success`. The second
must exit nonzero with a retained injected `MemoryError` record. Do not run with
`python -O`, which disables the behavior assertions. The output writer is flushed
after each record; no fsync, atomic publication or crash-survival claim follows.
Opening or writing evidence can itself fail, and process kill can leave an
incomplete last line. A missing complete record is not success. The runner does
not supervise timeouts or arbitrary child processes.

The workload seed is 250; all generated commands are retained verbatim. Each
mode receives five warm-up executions. Nine paired samples alternate execution
order, with twenty complete executions per sample. `perf_counter_ns` measures
elapsed time including scheduler interruptions. Python import/bytecode loading,
behavior checks, data generation, warm-up, model calculation and publication are
outside the timing interval. No Lean build occurs. The official
[clock contract](https://docs.python.org/3.13/library/time.html#time.perf_counter_ns)
does not promise nanosecond resolution merely because results use nanoseconds.

Here are per-execution medians and observed ranges in microseconds from the
final evidence, with unit-tariff totals including construction and final history
output. The batch, prefix and update workloads append 512 bits at capacity 512.
The conversion workload starts capacity 4096, appends one bit, optionally
converts, queries twice and observes. Thus it charges the entire construction,
conversion and observation, not just the two cheap cached reads.

| Workload | Model plain / cached | Plain median (range), µs | Cached median (range), µs |
|---|---:|---:|---:|
| Batch-final | 4099 / 4100 | 190.32 (184.77–196.74) | 185.46 (181.59–194.44) |
| Every-prefix | 266242 / 4611 | 2971.61 (2935.05–3002.97) | 371.06 (363.31–374.16) |
| Update-heavy, no parity query | 3074 / 4099 | 182.40 (176.31–184.94) | 190.50 (182.52–200.61) |
| Conversion erases savings | 4109 / 12301 | 1.90 (1.89–2.11) | 2.13 (1.96–2.41) |

Every-prefix timing agrees with the modeled ranking, but not its numerical
ratio. Update-heavy and conversion medians also agree; their timing ranges
overlap, so these small differences do not establish stable speedups. Batch-final
has a lower cached median despite a higher unit cost, with overlapping ranges.
The model does not reliably discriminate such a near tie on this target.
The process was not CPU-pinned or isolated from other work. There is no
cross-machine claim, statistical confidence interval or fitted timing tariff.

Separate traced-memory executions reported 1859 bytes for both modes of each
512-element workload, and 4443 / 8570 bytes for the conversion workload. These
are measured transient peaks, not just slot payloads; the conversion case exposes
the simultaneously live copy. Equal 512-element peaks demonstrate why abstract
counter/cache units cannot simply be relabeled bytes.

The directory retains two initial successful runs, their original source
hashes and `initial-experiment.py`, as well as the final run. The final source adds published-model regression
checks and allocation fault injection. A tooling invocation failed before that
edit was applied; [development-failures.txt](../../experiments/bounded-buffer-target/development-failures.txt)
records it. The [allocation failure evidence](../../experiments/bounded-buffer-target/allocation-failure.jsonl)
is explicitly injected at the bytearray boundary, not a claim that physical
memory was exhausted. Ordinary out-of-range allocation requests are also
retained as rejected service invocations. Real `MemoryError` during construction,
copying or output would abort this candidate; a production total API needs an
explicit resource-failure contract in addition to capacity overflow.

## Trust boundary and follow-up

Trust includes the handwritten adapter, interpreter and its compiler build,
bytearray/int semantics, memory allocator, clock, OS scheduling and truthful
recording. CPython transformations and runtime fast paths are not counted by
#239. No proof connects Lean source to this Python program or to machine code.
The evidence supports a candidate mapping and identifies missing costs; it
establishes neither runtime bounds nor compiler correctness.

[#195](https://github.com/VladimirMarko/conaled/issues/195) is still open. Its
[measurement pilot](measurement-attempt-pilot.md) accepts only its fixed child
protocol, and the existing order-certificate script embeds Lean-specific build
and parsing behavior. Neither is a reusable runner for this in-process workload.
The consumer requirements here are exact source/input identity, separate
check/build/execution intervals, paired raw samples with order, bounded output
consumption, memory-probe scope, and unsuccessful/incomplete publication states.
This script is deliberately one experiment, not a competing measurement framework.

A bounded follow-up should first define an imperative byte-buffer machine with
finite counters and explicit allocation/output-failure replies. Prove a local
step simulation through the decoder, cache closure and overflow preservation,
then instantiate the existing trace-client theorem for both realizations and
copy conversion. Establish an event projection to #239 under successful
allocation, separately counting initialization, bulk copies, output consumption
and scalar workspace. Preserve the original model's theorems rather than
silently changing their meaning to fit Python timings. Validate the concrete
adapter with exact-output differential traces, boundary/failure cases and paired
execution records; a universal Python compiler proof is outside that bounded task.

Hand the observation mismatch to
[#235](https://github.com/VladimirMarko/conaled/issues/235): ordered output content
is shared, but output ownership, temporary storage and environmental failure
are absent from the current pure contract. Factor those only when the concrete
consumer requires them, retaining ordinary pure clients and both realizations.
[#193](https://github.com/VladimirMarko/conaled/issues/193) coordinates concrete
target obligations; #174 retains representation choice. No production backend,
new container or global optimizer is delivered by this investigation.
