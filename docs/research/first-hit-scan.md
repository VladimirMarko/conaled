# First-hit indexed aggregation

Issue [#590](https://github.com/VladimirMarko/conaled/issues/590) compares native
and compiled execution of a scan with indexed reads. The
[implementation](../../Applications/Resources/FirstHitScan.lean) and
[checked examples](../../Examples/FirstHitScan.lean) retain both interfaces.

## Contract and source argument

The input is a fixed store of natural contributions, a starting index, an
accumulator and a threshold. Before each read, execution stops if the index is
at or beyond the store size or the accumulator has reached the threshold.
The output contains both the stopping index and accumulated sum. Correctness
requires the starting index to be at most the size; execution itself is total
also for larger indices, where it immediately stops.

`sumPrefix read i k` sums exactly the next `k` contributions without consulting
the threshold. `FirstHit` says that the returned index and sum equal that
prefix's endpoint, that it reaches the threshold or exhausts the store, and
that every earlier prefix is below threshold with an in-bounds next read.
`source_correct` proves this statement from finite source steps. It also
preserves the threshold register. `continuing` proves read bounds at each
executed body; `decreases` uses size minus index as the terminating rank.
`source_exists` obtains a finite execution from the existing ranked executor.
The rank is not substituted for the actual number of reads in the cost proof.

The worked store `[0,2,0,3]` has prefix sums `0,0,2,2,5`. Threshold 2 stops at
index 2, threshold 5 reaches the last entry, and threshold 6 exhausts the input
without reaching it. Other checked cases cover an immediate stop, an exhausted
start, an empty store, and a nonzero starting index and accumulator. A changed
legal read changes the terminal result. An immediate stop excludes a post-read
interpretation of the contract.

## Test representation and operation graph

The existing test has two scalar operands and compares them with `≤`.
The chosen left operand is `min (size − index) (threshold − sum)`; the right
operand is zero. Saturating natural subtraction makes this exactly the desired
stopping condition. This requires local subtraction and minimum primitives but
no change to `Test`, the scalar grammar or unrelated targets. An explicit
Boolean disjunction could short-circuit; it would change the graph and need
variable guard accounting. That extension is unnecessary for this consumer.

The native guard executes the same two literals, two subtractions, minimum,
and comparison as the compiled guard, even when the first bound already says
to stop. The body computes the successor index, reads the old index once, and
adds that contribution once. Neither implementation recomputes the read.
The compiled seed passes through the supplied state; the post term projects
the index and sum. Native initialization and observation perform the same
unpriced wiring.

| Stage | Operations charged per execution |
| --- | --- |
| Initialization | 0: supplied registers and an existing read-only store |
| Guard | 6: size literal, two subtractions, minimum, zero literal, comparison |
| Guard dispatch | 1, including the initial and final visits |
| Continuing body | 3: successor, indexed read, addition |
| Final observation | 0: pair formation and projections |

Variables, unit values, tuple construction, projections, binds, store views and
proofs have zero weight. The store is supplied, not copied or allocated by the
scan. Thus `k` reads cost `(k+1)*7+k*3`; zero reads still cost 7. These are
execution-model primitive counts. They establish neither constant-time array
access in Lean nor host runtime, allocation or natural-number bit complexity.
The indexed-read convention agrees with the unit-read abstraction used in
[#583](https://github.com/VladimirMarko/conaled/issues/583), but this scan charges
index arithmetic and control explicitly, unlike that consumer's tariff.

## Proof reuse and representation

`compiled_of_steps` uses `Program.execute_of_steps`, whose scalar soundness
proof supplies local guard and body compatibility. `native_of_steps` uses the
same measured loop's `run_of_steps`. Both discharge their complete costs from
the actual graphs above. `compiled_correct` connects the target output to
`FirstHit`; `routes_equal` compares the complete measured results.

`steps_read_transport` preserves the same finite execution using agreement only
on in-bounds reads. `representation_reuse` then reuses the shared execution and
cost theorem. `array_reads` proves that the concrete array's optional indexed
read, defaulted to zero, agrees with the finite-function view on legal indices.
`array_reuse` preserves the exact index/sum observation and bill. The adapter
contains no whole-program correctness assumption. No array copy is performed;
these are two interfaces to the same already supplied data. The checked
finite-function client derives its last-entry result through this adapter.

## Retrospective author comparison

Shared preparation consists of the independent sum and first-hit contract,
source invariant and rank, and a finite source execution. Both clients reuse
that work. The native route needs the measured guard/body graph and their
constant charges. The compiled route additionally needs six typed primitive
constructors, their interpretation and charges, syntax for four stages, and
definitional connections of the syntax to the source guard and body. Its value
and cost proofs then reuse scalar compiler soundness and loop control.

Changing the supplied store, starting state or threshold introduces no new
compiler proof. Moving from arrays to finite functions needs one local read
preservation lemma and a size conversion in the example, shared by both
routes. Changing the operation graph would require updating its source
compatibility and cost calculations; syntax does not remove those obligations.

For this bounded consumer the compiler adds syntax while the native adapter
already supplies loop accounting. Retain the native route. The result supports
local proof reuse, not compulsory migration or an author-productivity claim.
No independent author timing was performed. Incremental changed-threshold
repair, asynchronous execution, physical array bounds, Wasm and tree annotations
remain outside this issue. The [attempt record](first-hit-scan-attempts.md)
distinguishes encoding failures from mathematical obstructions.
