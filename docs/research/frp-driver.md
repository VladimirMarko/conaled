# Bounded external FRP driver

The driver for [#233](https://github.com/VladimirMarko/conaled/issues/233) runs the
existing sequential request lifecycle and its compiled count/total consumer on
stdin/stdout. It retains source knowledge and consumer state between requests.
It supports deterministic replay within a fresh process. It does not recover a
previous session or acknowledge delivery to an external consumer.

## Run and replay

From the development shell, build the imported library once, then run the script:

```sh
lake build Applications.FRP.DriverIO
lake env lean --run scripts/frp-driver.lean <<'INPUT'
begin 0 2
source left 3 1 2 2 3 4
source right 3 1 2 1 3
process 0
begin 1 2
process 1
INPUT
```

The output is:

```text
ok packet - status accepted response - aggregate -
ok packet accepted status - response - aggregate -
ok packet accepted status - response - aggregate -
ok packet - status - response 0 2 3 3 4 3 aggregate 1 10
ok packet - status accepted response - aggregate -
ok packet - status - response 1 2 3 3 4 3 aggregate 2 20
```

The original batch is `[3,4,3]`, in that order. `aggregate 1 10` is the compiled
consumer's first delivery count and accumulated sum. Repeating timestamp 2
with fresh ID 1 reads retained source knowledge and advances that consumer
again. Aggregate observations do not replace the ordered original response.
Save the input in a file and redirect it into a fresh invocation to replay it.
This reproduces the pure transition sequence under successful IO; it does not
make external effects of an earlier invocation safe to repeat.

## Wire format

Each frame is printable ASCII followed by LF. Tokens have exactly one ASCII
space between them, with no leading or trailing space. Numbers are canonical
unsigned decimal: `0` or a nonzero digit followed by digits. Signs, leading
zeros, tabs, CRLF and non-ASCII bytes are rejected. Empty lines are malformed.
Commands are:

| Form | Meaning |
|---|---|
| `begin ID TIME` | Attempt a sequential request. |
| `process ID` | Process the matching current request if its data is ready. |
| `source left FRONTIER N FRAGMENTS` | Submit a complete window to the left source. |
| `source right FRONTIER N FRAGMENTS` | Submit a complete window to the right source. |
| `idle` | Leave the lifecycle unchanged. |

`N` is the number of fragments. Each fragment is `TIME COUNT VALUES`, containing
exactly `COUNT` payload numbers. For example, `source left 1 3 0 1 7 0 0 0 1 8`
has three fragments at timestamp 0: `[7]`, `[]`, `[8]`. The retained batch is
`[7,8]`. `source left 1 0` contains no fragments.

An ordinary decoded command produces one line:

```text
ok packet PACKET status STATUS response RESPONSE aggregate AGGREGATE
```

`PACKET` is `-`, `accepted` or `rejected`; `STATUS` is `-`, `accepted`, `busy`
or `stale`. `RESPONSE` is `-` or `ID TIME COUNT VALUES`. `AGGREGATE` is `-` or
`DELIVERY_COUNT TOTAL`. Both optional observations are present on a delivery.
An empty batch uses count zero and still advances the consumer. `response -`
means silence and leaves the consumer unchanged. Status and packet fields are
separate because packet rejection is not a request rejection.

The decoder reports `error malformed` for invalid syntax/counts, and
`error limit` for numeric or decoded packet limits. A token longer than five
characters is rejected as a limit violation before attempting numeric conversion.
These errors leave lifecycle and consumer state unchanged, but consume one frame
of the invocation budget. Framing errors terminate immediately without applying
a prefix of the frame. There is no retry or resynchronization after a framing
error.

## Limits and identity policy

The driver enforces these fixed limits:

| Resource | Limit |
|---|---|
| Input frames | 256, including malformed or rejected commands |
| Frame contents | 4096 bytes, excluding LF |
| IDs, packet timestamps, frontiers and payload values | 0 through 65535 |
| Query timestamps | 0 through 65534 |
| Fragments per packet | 64 |
| Total payload values per packet | 64 |

The reader requests one byte at a time. It reads at most 4097 bytes for a frame,
including a possible LF, and never calls an unbounded line reader. A 4097th
non-LF byte terminates with `error frame-limit`. EOF in an unfinished frame
produces `error incomplete-frame`; forbidden bytes produce `error non-ascii`.
After the 256th frame, the driver publishes `error frame-budget` and terminates,
even if EOF would be next. It does not read a 257th frame. EOF before that limit
ends normally, including EOF while a request is still pending.

IDs are bounded natural numbers without wrap or reuse, following
[#232](https://github.com/VladimirMarko/conaled/issues/232). Accepted IDs must
increase. Busy takes precedence over stale for supported commands, as in the
original lifecycle. Accepting ID 65535 still permits source delivery and
processing that request. After it completes, no later fresh ID is available;
old IDs return stale, and 65536 is a limit error. There is no automatic reset.
Query timestamp 65535 is rejected as a limit error because readiness requires
a strictly greater frontier, itself capped at 65535. Every supported query
time therefore leaves room for a closing frontier. This does not guarantee
that the environment will supply it.

The loop retains the current state and one frame/result, not its transcript.
The underlying source logs still retain accepted history. Consumer counters
and totals still use `Nat`. The frame and packet caps limit an invocation to
at most `256 * 64` retained fragments and payload values across both sources;
a response can revisit those values, and each of at most 256 deliveries can
add their sum again. These are coarse counting consequences of the caps,
not checked allocator/heap bounds. There is no physical-memory, scheduling,
wall-clock, or indefinite-service theorem for this Lean IO driver.
[#234](https://github.com/VladimirMarko/conaled/issues/234) owns the stronger
indefinite-service realization. Identifier-free repeated protocols remain a
separate investigation under [#236](https://github.com/VladimirMarko/conaled/issues/236).

## Source and session assumptions

Both sources start at frontier 0 with empty logs. A packet closing a window
from the old frontier to the new frontier asserts *all* source observations
in that half-open interval. Omitted timestamps assert empty batches. The
existing `windowValid`/`advance` decision checks nondecreasing frontiers and
fragment containment. It cannot check whether an external producer omitted
an actual event. `Trace.Honest` and `State.Completes` express the additional
truth obligations used by the existing response soundness theorems. Silence
never supplies a complete window or advances a frontier.

A fresh invocation requires fresh isolated channels and a caller contract that
excludes delayed commands or replies from an earlier session. Resetting the
ID high-water mark alone does not establish this. Source packets and request
commands are provided sequentially by that caller; there is no network reader,
background source, timeout, fairness scheduler or implicit source advancement.
A blocked read or write can block the process. Safety does not imply eventual
completion under missing data or missing matching-ID processing.

## Publication and failures

For each complete frame the loop decodes, computes the pure transition,
serializes its observation, writes one output frame, flushes, then reads again.
The transition may therefore have emitted internally before publication fails.
Successful write/flush means only that the selected runtime stream accepted
those operations. It establishes neither receipt by another process nor a
durable external acknowledgment. The protocol contains no acknowledgment
message.

| History | Behavior and remaining knowledge |
|---|---|
| Malformed or over-limit decoded command | Error line; lifecycle state unchanged; fuel consumed. |
| Structurally rejected source packet | `packet rejected`; existing source and consumer state unchanged. |
| Busy, stale or wrong-ID command | Existing lifecycle behavior, including busy/stale precedence and wrong-ID silence. |
| Framing error or frame-budget exhaustion | Error line followed by exit 2 if publication succeeds. |
| Clean EOF before frame-budget exhaustion | Exit 0; a pending request may remain unanswered. |
| Read exception | Exit 3; no transition from the failed read; earlier publications remain effects. |
| Write fails before or after some bytes | Exit 3; publication may be absent or partial; no retry and no next command. |
| Flush fails after a complete write | Exit 3; the complete frame may already be externally visible; no retry. |
| Stderr diagnostic also fails | Still return exit 3; the diagnostic is best effort. |
| Process/OS crash, forced termination or runtime failure outside caught IO errors | No recovery guarantee; an output prefix may have escaped. |

The driver does not roll state back and then retry an ambiguous output. This
uses the distinction in [the interaction evidence model](../../Applications/Interaction/Evidence.lean):
missing acknowledgment does not show that no effect occurred. The model does
not itself verify Lean's IO implementation. Restart, persistent source/ID state,
recovery publication ordering and durable acknowledgment need new contracts
coordinated with [#194](https://github.com/VladimirMarko/conaled/issues/194),
[#225](https://github.com/VladimirMarko/conaled/issues/225) and
[#226](https://github.com/VladimirMarko/conaled/issues/226).

## Checked and tested boundaries

[DriverProtocol](../../Applications/FRP/DriverProtocol.lean) proves command,
packet, response and aggregate roundtrips over numeric token lists. Packet and
response decoders preserve a following token suffix, original order, duplicate
timestamps and empty batches. Bounded decoding returns only supported commands.
The pure adapter runs the actual `Lifecycle.Pipeline.step`; its event and state
agree exactly with that pipeline, and `step_compiled` transports through
`Reactive.joint_correct` to the source consumer. Packet status uses the same
validator as the source update, and rejected packets stutter.

[DriverIO](../../Applications/FRP/DriverIO.lean) proves malformed decoded inputs
stutter, successful decoded steps agree with the pipeline, and finite replay
retains exactly the pipeline state obtained from its successful command
subsequence. Its `replay` list is a specification helper; the IO loop uses one
step at a time. [Checked examples](../../Examples/FRPDriver.lean) apply these
laws to fragmented packets, maximum IDs, empty responses, stale requests and
compiler preservation.

These statements do not prove `String.toNat?`, decimal printing, text tokenization,
ASCII/UTF-8 conversion, byte framing, stream behavior, compilation of Lean itself,
or the OS/FFI. Those form the tested/trusted realization boundary. The pinned
Lean `IO.FS.Stream` contract says `read n` returns at most `n` bytes and an empty
array indicates EOF; the reader relies on it. The numeric codec theorem is not
presented as a theorem about arbitrary external bytes.

Run the public IO fixtures with:

```sh
lake build Examples.FRPDriver
python scripts/test-frp-driver.py
```

The fixtures cover normal and repeated requests, known-empty versus silence,
packet rejection, busy/stale/wrong-ID behavior, malformed and noncanonical
numbers, capacity boundaries, frame and invocation limits, incomplete/non-ASCII
frames, actual `/dev/full` failure, and injected partial-write/flush/read failures.
The injected cases redirect the same `runDriver` streams and check that no next
input is consumed and no publication is retried. These tests do not establish
all operating-system histories or downstream receipt.

The [#231 experiment](preservation-experiment.md) informed the separation of
semantic equality, resource claims and progress assumptions. This driver reuses
the existing exact consumer compilation law; introducing a further relational
record would not remove the IO boundary obligations. Its concrete limitations
feed the continuing architecture work in
[#235](https://github.com/VladimirMarko/conaled/issues/235).
