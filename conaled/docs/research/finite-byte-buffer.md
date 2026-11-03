# Finite byte buffers with environmental refusals

[#253](https://github.com/VladimirMarko/conaled/issues/253) connects an indexed
byte-slot machine to #239's independent ordered-history specification. It keeps
both existing realizations and all their cost theorems unchanged. The new
[semantic module](../../Applications/Sequences/ByteBuffer.lean),
[event accounting](../../Applications/Resources/ByteBuffer.lean) and
[checked applications](../../Examples/ByteBuffer.lean) are imported by the public
entrypoint and included in the normal exhaustive proof audit.

## State and observation contract

`Machine W N` has `N` slots in `Fin 256`, a counter in `Fin (N+1)`, a parity
field, and a proof `N ≤ W`. `counter` embeds the counter in `Fin (W+1)`.
The decoder reads the ordered prefix, interpreting nonzero bytes as true.
`BytesValid` separately requires every byte, including unused slots, to be the
canonical zero or one encoding. `Valid cached` additionally requires the parity
field to equal the decoded XOR when the cache is enabled. Validity is not assumed
for arbitrary corrupt caches; a checked counterexample obtains the wrong query
reply from an invalid cache.

Append tests capacity before indexing or incrementing. `buffer_push` proves
that the actual byte write commutes with the existing Boolean-buffer projection;
`decode_push` therefore preserves order and duplicates. `increment_no_wrap`
proves an accepted increment equals the old counter plus one and is at most
`W`, rather than a modular increment. Overflow preserves the entire state.
Plain query uses an accumulator loop over indexed reads; `scanAcc_correct`
connects it to the existing parity scan. Cached query reads the maintained
parity. Observe returns the entire prefix, not just parity.

`step_simulation` and `step_valid` give the local law and invariant closure.
`trace_simulation` instantiates #239's `trace_preserves` directly for both modes.
Copying conversion rebuilds every slot and computes parity; `convert_buffer`,
`convert_decode` and `convert_valid` establish its extensional behavior and valid
cache. Physical separation of arrays remains an operational ownership obligation,
not a consequence of extensional equality in Lean.

The extended service distinguishes `allocation` and `output` failures from
capacity overflow. Construction and copy may refuse allocation. Per-command
allocation/preparation may fail before mutation, including before an overflow
reply; output allocation may separately fail on observe. The caller receives
no partial snapshot. `attempt_simulation`, `attempt_valid` and
`attempt_trace_simulation` prove the corresponding refusal-aware history
contract. Both refusals preserve state. Failed copy also preserves its source.
`successful_specialization` and `successful_trace` recover the original pure
step and trace with successful replies embedded in `Except.ok`; pure clients
and their existing proofs remain available.

This is a single-threaded, operation-boundary contract. It assumes that the
commit writes after successful preparation do not fail. It does not describe
asynchronous cancellation, concurrent observers, interruption between writes,
or resource exhaustion while reporting a failure. Reply lists in the trace
proofs are ghost observations, not retained implementation logs.

## Events and ownership

`primitives` independently enumerates each operation's counts: a successful
append has one slot write, two control operations and, in cached mode, a combine
and cache write. Overflow has one control operation. A plain query has `n+1`
visits and `n` combines; `scanLoopCount_exact` derives those counts from the
accumulator-loop recurrence. A cached query has one cache read. Snapshot export
projects to `n+1` visits and `n` emits. `primitive_projection` proves equality
with #239's tariff for arbitrary weights. `projected_cost` reuses #239's measured
trace theorem on the new machine, rather than restating its budget definition.
`measured` exposes those events on successful operations only; failures return
no successful event account. They may still expend work.

The additional fields are a declared target accounting contract, not measured
CPython allocations:

| Operation | Additional accounting |
|---|---|
| Construction | `N` initialized bytes, `N` owned payload bytes |
| Snapshot | Two length-`n` bulk copies (slice and bytes), `n` output bytes created and consumed, at most `N+2n ≤ 3N` owned payload bytes |
| Copy conversion | `N` bytes copied, simultaneous source/destination payload `2N`; parity scan accounted by the primitive projection |
| Iteration | Four scalar temporary slots as a declared register budget, zero recursive scanner frames |

The four scalar slots cover the loop index/accumulator or prepared counter/cache
values. Arguments, stored fields, interpreter frames, boxed values, object
headers and allocator metadata are outside that scalar-slot convention. The
Lean recurrence describes iteration but does not establish compiler tail-call
optimization or physical stack usage. The Python adapter uses explicit loops.
The owned-payload bounds assume each returned snapshot is consumed and released
before the next request and no external output queue is retained. Source
ownership persists through conversion; successful source and destination arrays
can subsequently be mutated independently. Construction/conversion events are
attached to their successful operations and project to the existing construction
and copying-conversion tariffs. None of these equalities is a time bound.

## Adapter choice and behavior checks

Before implementation we retained the accessible CPython/bytearray target from
[#250](bounded-buffer-target.md), with two changes: actual `ctypes.c_uint32`
cells store capacity and length, and fallible preparation/output boundaries have
explicit replies. The [adapter](../../experiments/finite-byte-buffer/adapter.py)
checks finite ranges before constructing cells. `successor` guards the increment
before the ctypes store, so an out-of-range value is never intentionally wrapped.
Python arithmetic and indexing still use boxed temporary integers. All fallible
append preparation precedes the commit writes. The trusted commit boundary is
an in-range bytearray write and assignment to existing uint32/parity fields.
The adapter catches `MemoryError` for allocation/preparation, copy and output;
its declared contract relies on that commit boundary not throwing halfway through.

The [public test suite](../../experiments/finite-byte-buffer/test.py) compares
both modes against independently calculated list histories, sum-modulo-two
parity and exact byte outputs for 5,460 traces of lengths zero through five at
capacities zero through three. It checks converted queries/snapshots, refused
append/output preservation and separately mutable copies. Full uint32 boundary
arithmetic checks `2^32-2 → 2^32-1`, full-capacity rejection, zero capacity and
invalid ranges without allocating a four-gigabyte buffer. Small word maxima
exercise actual service execution at the boundary. These finite tests validate
the handwritten adapter but do not prove it implements the Lean model for every
input. The invalid-cache case is a checked Lean counterexample; the adapter
constructors themselves do not admit externally supplied caches.

The API seams were already specified by #253: exact command replies, finite
counter boundaries, construction/copy and environmental refusal preservation.
Development followed failing public tests before implementation. The first
finite-capacity test lacked the adapter; the next exposed missing copy support;
the boundary test exposed the missing guarded successor. All now pass. Formal
case development similarly exposed the missing byte-write projection and
refusal-trace connection; the retained examples use the resulting public laws.

## Paired execution evidence

The [runner](../../experiments/finite-byte-buffer/experiment.py) reuses #250's
seed-250 workloads and unit-model calculation. #195's current fixed child-protocol
pilot does not accept this in-process workload, so it has not been replaced or
forked into a new generic measurement framework. The evidence retains source
SHA-256 hashes, repository base, toolchain pins, interpreter path/build, OS/CPU,
clock, exact commands, execution order and individual outcomes. Execution uses
CPython 3.13.15/GCC 15.3.0 on Linux 6.18.58 x86_64/glibc 2.42.

Each mode has five warmups and nine paired samples of twenty executions, with
alternating order. Timings include command dispatch, finite-counter checks,
output creation and complete checksum consumption; inputs, tests, warmups,
publication and interpreter startup are excluded. Exact-output correctness comes
from the tests, not checksum collision resistance. Each snapshot is released
before the next operation. The timed runner retains only small result records.

These are per-execution microseconds from the committed
[successful run](../../experiments/finite-byte-buffer/evidence.jsonl):

| Workload | Unit model plain / cached | Plain median (range), µs | Cached median (range), µs |
|---|---:|---:|---:|
| Batch-final | 4099 / 4100 | 428.92 (420.95–437.92) | 418.57 (410.59–422.54) |
| Every-prefix | 266242 / 4611 | 3336.98 (3245.05–3409.46) | 648.18 (622.37–687.52) |
| Update-heavy | 3074 / 4099 | 425.85 (414.67–430.89) | 428.64 (415.33–435.81) |
| Conversion erases savings | 4109 / 12301 | 3.42 (3.05–3.45) | 3.90 (3.52–4.01) |

Every-prefix and conversion agree with the modeled ordering in this run.
Batch-final reverses the near-tied unit ordering and its timing ranges overlap;
update-heavy ranges also overlap. Neither supports a stable small speedup.
There is no CPU isolation, confidence interval, cross-machine result or fitted
timing tariff. The extra finite-counter and failure checks change the adapter,
so these timings are not an isolated estimate of ctypes overhead relative to
#250. Separate tracemalloc probes report 2,315 bytes for both modes of the three
512-element workloads and 5,141 / 9,274 bytes for conversion. Those are tracked
Python allocation peaks, not RSS, retained payload sizes or universal bounds.

The retained [allocation refusals](../../experiments/finite-byte-buffer/allocation-failure.jsonl)
and [output refusals](../../experiments/finite-byte-buffer/output-failure.jsonl)
contain both modes of all four workloads, exit status one and a false completion
marker. These are controlled boundary refusals, not physical memory exhaustion.
The [incomplete attempt](../../experiments/finite-byte-buffer/incomplete.jsonl)
stops deliberately before the first timed pair, exits two and has no completion
marker. Exclusive output creation preserves prior attempts. Each line is flushed,
but no fsync, crash durability, process supervision or timeout guarantee follows.
A missing completion record cannot be interpreted as success.

## Statement review and remaining trust

The semantic claims quantify over every finite `W,N` satisfying the stored
capacity bound, every command and every valid seed, not just empty states or
admitted workloads. Overflow remains observable. The byte-validity premise is
satisfiable by `empty_valid` and preserved by append; cached simulation genuinely
needs cache validity, as the counterexample demonstrates. Copy validity requires
only canonical source bytes, not an already valid source cache. Successful trace
reuse goes through the original independent specification, and refusal traces
use its explicit extension; no simulation hypothesis is assumed as the result.
The finite counter proof establishes mathematical range preservation, not the
physical size of Lean's `Fin` representation.

Resource claims quantify over arbitrary tariffs and actual current prefix
lengths. Construction, copying, output consumption and simultaneous ownership
are not dropped when comparing workloads. Extra event fields and scalar-slot
budgets define the target accounting convention; they do not prove the Python
runtime has those exact allocations. The output ownership bound follows from
the finite counter. Checked cases cover empty and zero capacity, exact capacity,
overflow, conversion, invalid caches, failure interleavings, retained pure
clients and literal snapshot/conversion event totals.

Trust remains in the handwritten correspondence, Python interpreter and compiler
build, ctypes and bytearray semantics, allocator, nonfailing commit boundary,
OS and measurement recorder. A proved modeled machine is not a verified compiler
or a production backend. No universal allocation-free claim or hardware time
bound has been established.

The concrete handoff to [#235](https://github.com/VladimirMarko/conaled/issues/235)
is the snapshot client: it needs an output-ownership/consumption discipline and
allocation/output refusals absent from the old pure square. The local
`attempt`/`specAttempt` extension demonstrates that need while
`successful_specialization`, `successful_trace` and the original trace theorem
retain ordinary pure clients. Generalizing a shared failure/ownership interface
should be driven by a second consumer; this change does not retrofit unrelated
libraries. [#193](https://github.com/VladimirMarko/conaled/issues/193) owns the
remaining target trust obligations; #195 owns reusable measurement support.
