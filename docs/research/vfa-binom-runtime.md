# VFA Binom: native queue execution and comparative observations

Historical observation scope: measurements, generated-code inspections and
receipt identifiers below describe the original CTB-97 donor increment at the
source/artifact hashes stated. They are not observations of the current receiving
tree. Old external filenames identify historical records; their current availability
is not inferred from a path or a hash. The retained source/test owners provide
reproducible behavior; [CTB](../textbooks/CTB.json) records CTB-97 attribution
and CTB-78 receiving status. Any new receiving result must bind its actual inputs.

The complete [chapter ledger](vfa-binom.md) maps the source mathematics and
mandatory `binom_measurement` exercise. This note describes its actual execution
seam, independent finite observations and reproducible measurement protocol.
The seam extends `scripts/ExtractSearchTree.lean` and
`scripts/test-extract-searchtree.py`; existing Extract and Redblack commands and
tests remain available. Final execution counts, timings, executable identities
and acceptance are recorded in the candidate-specific checkpoint evidence.

## Source correspondence and machine domain

The binomial implementation calls `Search.BinomialQueue.insert`, `deleteMax`
and native `merge` on the actual dense `List (BinaryTree Int64)` representation.
It preserves nil slots, source ties, child/sibling trees and the source's merge
algorithm. The list baseline uses cons insertion, the accepted comparison-first
`SourceSelection` maximum selector through `DecodedBinomialQueue.listDeleteMax`,
and operand-order `List.append` for merge. The benchmark does not substitute a
sorted-list binomial implementation or reinsert the keys when merging.

`Applications/Representations/DecodedBinomialQueue.lean` proves the complete
label-map equations, including arbitrary-continuation unzip and full Option/pair
results. Its `decode_*` laws use the accepted signed comparison correspondence.
The Nat specializations retain their explicit bounded-input hypotheses; the
proof-only maps are absent from the timed queue computation. The connected
clients exercise shared abstract queue operations and duplicate occurrences.

Lean `Int64` has the decoded range `-2^63 ≤ k < 2^63`. Replay checks this full
signed interval. Natural generated keys use `checkedNat64`, requiring `k < 2^63`.
Every conversion and decoded round-trip check completes before timing.
These checks do not identify signed Int64 with the separate BitVec63 backend.
Native execution still depends on the ordinary Lean compiler and native integer
overrides; the mathematical decoding theorem is not compiler verification.

## Public commands and exact inputs

The existing `extract-searchtree` Lake executable supplies two additional
commands. Run all development and final commands through the exact pinned native
profile named in the checkpoint's retained operations. The user-authorized
profile exception applies; no artificial CPU, memory, thread, affinity or elapsed
limit is added. Workload sizes below are explicit finite logical inputs.

```sh
lake --no-cache --rehash build extract-searchtree
lake env lean --run scripts/ExtractSearchTree.lean binom-examples
.lake/build/bin/extract-searchtree binom-workload --implementation binomial --pattern random --size 128 --universe 17 --seed 1729 --schedule merge --warmups 1 --repetitions 3
```

The final compiled validation additionally uses the native profile's
hash-identified executable launch. The actual complete command arrays and profile
paths are retained with their executions; these short commands describe the
public interface rather than replacing those launch records.

`binom-examples` evaluates the literal source left fold
`[3,1,4,1,5,9,2,3,5]`. Its schema-3 result contains the entire four-slot forest,
including every null subtree, the original input and maximum 9. The Python fixture
specifies the exact constructor tree independently of insertion and linking.
The corresponding Lean theorem uses ordinary kernel reduction. The actual
executable smoke run and the formal constructor equality are separate evidence.
The `binom-examples` dispatch prints its observation directly; it does not compare
the independent literal before printing. That complete comparison belongs to the
Python harness and `--check-receipt`, through `expected_binomial_examples`.
Consequently, exit zero from the raw command alone is not independent fixture
validation. The receipt checker also needs external source, executable, replay
input and clock identities before its finite observations can qualify an actual
execution.

| Option | Default and meaning |
| --- | --- |
| `--implementation` | `binomial`; alternatively `list`. |
| `--pattern` | `random`; alternatively `replay`, `ascending`, `descending`, `equal`. |
| `--schedule` | `drain`; alternatively `mixed`, `merge`, `padding`. |
| `--size` | 32 generated keys; replay derives its size from the file. |
| `--universe` | 32, the exclusive upper bound of random natural keys. |
| `--seed` | 1729, passed to pinned `mkStdGen`. |
| `--warmups` | 0 reset warmup samples. |
| `--repetitions` | 1 reset measured sample; must be positive. |
| `--keys-file` | Required only for replay, with one signed decimal key per line. |

Unknown options, duplicate options, missing values and negative natural counts
fail. Replay rejects explicit size, universe or seed flags even when their values
equal defaults. Other patterns reject replay files. Deterministic patterns reject
explicit universe and seed flags; their unused recorded fields keep defaults.
Missing files, malformed decimal lines and out-of-range signed keys fail before
any queue interval.

Random keys use the existing pinned `StdGen`/`mkStdGen`/`randNat` generator with
inclusive call endpoints 0 and universe−1. Universe must be positive for nonempty
input and may be zero when size is zero. The maximum allowed universe is `2^63`,
so every generated key remains strictly below that endpoint. Receipts record
initial/final generator states and the logical number of key draws. The fixture
seed 1729, universe 13, size 8 is independently pinned to
`[10,0,10,11,6,10,0,0]`, initial state `[1730,1]` and final state
`[1689113473,525453832]`. No distribution theorem is claimed.

Ascending inputs are exactly `[0,…,size−1]`, descending inputs their reverse,
and equal inputs are `size` zeros. Ordered sizes greater than `2^63` are rejected
before their list is allocated, because their keys exceed the natural machine
domain. The endpoint is semantically allowed and is not executed by the tests.
Equal and random inputs have no extra arbitrary size cap. Replay and deterministic
inputs report a null generator. Inputs and schedules are prepared once and reused
unchanged across reset samples.

## Actual schedules and persistence

Every queue begins empty. Events explicitly identify `main`, `left` or `right`.
Insertion events include a canonical signed decimal key; deletion events retain
the exact event index, queue identity and Some/None result. Saving retains the
actual persistent queue value, and merge calls the actual selected implementation.
All parity decisions, checked literal zero and event indices are prepared before
the operation clock.

| Schedule | Exact public operation sequence |
| --- | --- |
| `drain` | Insert every key into main; save `built`; delete main N+1 times. |
| `mixed` | Insert each key into main and immediately delete iff its decoded key is odd; save `mixed-prefix`; delete main N+1 times. Random inputs therefore determine the mixed operation pattern too. |
| `merge` | Alternate indexed keys into left/right; save `left-before` and `right-before`; merge them into main; save `merged`; delete left once and right once; delete main N+1 times. |
| `padding` | Insert every key into main; save `peak`; delete main N+1 times; save `drained`; insert checked zero; delete main twice. |

The merge schedule advances both inputs after merging, so it directly checks the
retained input versions as well as the merged version. Saved queues are observed
after the remaining operations. The padding schedule retains the empty forest's
stored slots and checks subsequent reuse; it never trims the source representation.
An empty schedule endpoint still has explicit failed removals, and zero remains a
Some key distinct from None. Negative odd replay keys use the specified integer
remainder condition, covered by a separate `-1` case.

## Timing boundary and complete independent observations

For each sample the driver starts `IO.monoNanosNow`, evaluates the precomputed
event fold through `IO.lazyPure`, and stops `IO.monoNanosNow`. The interval
includes queue operations, dispatch, persistent snapshot retention and removal
result retention. It excludes input generation, parsing, checked conversion,
schedule construction, decoding, independent validation and JSON serialization.
Elapsed nanoseconds are monotonic wall time, not process CPU time. The model's
syntactic cons/node/closure prices are not measured native allocations.

After the clock, the executable independently replays all events on decoded
mathematical integer lists. Its oracle inserts by cons, merges by concatenation,
finds maxima by sorting and erases exactly one selected occurrence. It never calls
the verified queue operations. It compares the complete removal sequence, every
final occurrence multiset, and the ordered identity/multiset of every saved
version. A discrepancy exits nonzero. Checksums cannot replace these checks.

The Python observer independently uses finite lists and `max`/one-copy removal.
It checks every input and event, complete Some/None sequence, and all final/saved
occurrence bags. For binomial states it also parses every preorder/null token,
checks outer-right nil, exact child/sibling ranks and heap bounds, and matches raw
preorder contents to the reported contents. It does not reimplement insertion,
linking or native merge. Stored capacity is checked by the proved endpoint laws:

- Insertion retains `max(oldSlots, bitlength(newMass))`.
- Merge retains `max(leftSlots, rightSlots, bitlength(totalMass))`.
- Deletion, including a failed deletion, retains the old slots.

The observer rejects truncated/extra tree tokens, wrong ranks, wrong heap bounds,
lost duplicates, trimmed padding, overwritten saved versions, incorrect event or
removal identities and malformed schemas. Decimal keys must be canonical strings;
Booleans cannot stand in for integer counts. Exact field sets, duplicate JSON
members and nonfinite numbers are checked. Samples must repeat exactly after
ignoring only phase, sample index and elapsed time. A targeted test first accepts
an alternative valid saved representation alone, then rejects inconsistent repeats.

## Reproducible comparative experiment

`BinomialRuntime.test_comparative_measurement` runs random inputs of sizes
32, 128, 512, universe 17 and seed 1729 under all four schedules for both source
implementations. Each invocation has one warmup and three measured repetitions.
For size index i and schedule index j, binomial runs first when i+j is even and
list runs first otherwise. Each pair receives exactly identical generated keys
and events, and compares the complete removals and final/saved occurrence bags.
The independent observer validates both raw outputs before the test succeeds.

This defines 24 driver invocations and 96 queue samples per execution mode, of
which 72 are measured and 24 are warmups. These numbers describe the fixed protocol;
only actual completed command records establish execution. The final validator
runs the full public harness in direct Lean and standalone compiled modes and
compares their complete semantic outputs after normalizing only elapsedNs and
byte-identified temporary replay paths. It preserves the actual raw outputs and
all input files for each mode. Warmup policy and alternating order do not turn a
finite run on a shared host into an asymptotic or portable speed claim.

The other cases cover empty/singleton/equal/ordered inputs, forced duplicates,
several explicit random seeds, all signed endpoints, malformed options and files,
both implementations, persistence, all schedules and receipt mutation. Legacy
Extract/Redblack tests remain part of the final combined suite. Logical workload
sizes are bounded deliberately; no runtime resource cap or performance threshold
is imposed. The final mode-specific times, medians and digests are evidence of
those finite executions only. The actual resource theorems remain in the separate
measured Lean modules.

## Evidence, source identity and qualification

The exact candidate's retained runtime validation contains command arrays,
start times, exits, full stdout/stderr, input-file bytes, both launch modes,
repetition policy, source/configuration identities, compiler/dependency pins,
host/target information, generated-C and executable identities, and separately
labelled standalone build time. The dependency artifacts and source inputs must
remain unchanged before and after the run. A later verification checks those
same files and identities without inventing or rerunning observations.

The original compact execution envelope and predecessor observations remain
historical evidence in the separately saved checkpoint. This note preserves the
substantive executed seam, observation rules and finite-result limitations;
[CTB-97](../textbooks/CTB.json) owns their candidate-specific qualification.
The former `checkpoint044_runtime_evidence.content_utf8` locator described an
older envelope, not an ongoing requirement to embed prior execution objects in
every successor. Its raw record is not claimed copied into this repository.
Current receiving evidence belongs to CTB-78 and must identify the actual driver,
source/configuration and executable. Historical executions remain bound to their
original source/executable/candidate identities.

Complete source/resource correspondence, actual candidate-bound runtime checks
and independent review remain distinct from whole-library receiving acceptance.
The original Binom qualification does not certify a rebuilt receiving binary.
Current integration and any subsequent formalization follow CTB-78's gate in the
[current catalog](../textbooks/CTB.json); the historical chapter/checkpoint
sequence below no longer steers present work. Concise current evidence is kept
with that task. Old raw logs and preceding envelopes are not perpetual source
documentation dependencies.
