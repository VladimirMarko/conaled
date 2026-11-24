# Retaining first-hit scans across threshold changes

Issue [#696](https://github.com/VladimirMarko/conaled/issues/696) extends the
[pre-read scan](first-hit-scan.md) at revision
`19f0249c00e8cbb1a08d00071080fb1856b1a36e`. The store, starting index and initial
sum stay fixed. Each update replaces the threshold. The retained implementation
preserves every computed prefix sum, including duplicates and a suffix that a
lower threshold no longer visits. An increase reads the store only after that
prefix runs out. Direct native and compiled recomputation remain available.

The library is [RetainedFirstHit.lean](../../Applications/Resources/RetainedFirstHit.lean).
Its [public examples](../../Examples/RetainedFirstHit.lean) use the store
`[0,2,0,3]`, whose accumulated sums from zero are `0,0,2,2,5`.

## Meaning and retained state

`repair read fuel i a t cache` scans at most `fuel` positions starting at `i`,
with initial sum `a` and threshold `t`. The store endpoint is `i + fuel`.
For a separately supplied size `n` and legal start `i ≤ n`, use `fuel = n-i`.
The pre-read guard stops at exhaustion or when the current sum reaches the
threshold. No store read occurs on immediate stop.

A cache cell contains the accumulated sum *after* one read, not a contribution
or an unordered set of sums. `Valid read i a (b :: bs)` requires
`b = a + read i` and validity of `bs` at index `i+1` and accumulator `b`.
`StateValid` additionally bounds the cache length by the available positions and
connects the current output to fresh native execution. These are satisfiable
invariants: initialization starts with an empty valid cache, and
`repair_stateValid` proves their preservation.

The repair traverses cached sums in order. On a miss it reads once, adds once,
and retains the new sum. On an early stop it returns the unused suffix intact.
`repair_extends` proves that the whole previous cache is a prefix of the new
cache. Thus a decrease invalidates no retained cell. Duplicate sums cannot be
removed: the position of the first crossing is part of the observation.

`repair_steps` constructs the existing `MeasuredLoop.Steps` derivation for the
same native loop. `repair_correct` then uses #590's `source_correct` and
`native_of_steps` to recover both `FirstHit` minimality and fresh native output.
It does not assume equality with recomputation as a repair law.
`updates_outputs` proves positional equality with fresh execution for every
finite threshold sequence; `updates_correct` also retains the cache invariant
and full first-hit statement for every result. `updates_growth` connects the
final cache length to the sum of newly executed reads. Starting empty,
`total_reads_bound` bounds that sum by `fuel`, regardless of the number or order
of threshold changes. `cached_no_reads` covers any update stopping within the
retained prefix.

## Costs and storage

The model uses natural-number tariffs, not measured host time or byte sizes.
It retains #590's seven-unit guard charge, including its control visit and final
guard. A continuing cached step costs four additional units: two for cache
inspection/dispatch, one for incrementing the index, and one for constructing
the returned cache cons. A miss adds a store read and an addition, one unit
each. The miss's second inspection unit is miss handling, not a claimed head
lookup on an empty list. Product wiring, diagnostic bookkeeping and parameter
passing are free in this model. The exhaustion branch is charged the same
logical guard tariff even though the recursive implementation can recognize
zero fuel directly.

For `k` continuing steps and `d` newly read entries, `repair_accounting` proves:

- repair cost: `11*k + 2*d + 7`;
- newly executed reads: `d = k - oldCache.length`;
- retained length: `newCache.length = oldCache.length + d`;
- `k ≤ fuel`.

The previous native/compiled bill is `10*k + 7`. `cost_comparison` proves that
repair adds exactly `k + 2*d`, at most `3*k`. **There is no total-work speedup
under these unit tariffs.** The capability reuses prior reads and additions,
while cache handling and copying cost more than those saved unit operations.
No claim about a more expensive store follows without a different justified
cost model. Direct recomputation remains a usable alternative.

`initialCache` charges one initialization operation and builds no prefixes.
Running the initial threshold is charged separately; `initialization_bill`
proves its combined charge is `13*k + 8`. Every continuing step charges a cons
allocation, including reconstruction of an already cached prefix. No eager
prefix construction or repair allocation is hidden in initialization.

`storage` counts retained cache cells plus nine fixed slots: fuel, starting
index, initial sum, output index/sum, cache root and three result diagnostics.
`storage_bound` proves at most `fuel + 9` after a valid update. It excludes the
resident store and does not measure bytes, arbitrary-precision integer sizes,
transient recursion stack, garbage-collection behavior or peak live allocation.
This is the retained state after the previous state is released. The `updates`
function collects a history for specification and examples; retaining that
whole history uses additional memory and is not covered by this single-state
storage bound. The `stateful` backend keeps only the current result.

## Worked sequence and controls

From zero, thresholds `[2,1,5,0,6,2]` produce:

| Threshold | Output index/sum | New reads | Repair bill |
|---|---|---|---|
| 2 | `(2,2)` | 2 | 33 |
| 1 | `(2,2)` | 0 | 29 |
| 5 | `(4,5)` | 2 | 55 |
| 0 | `(0,0)` | 0 | 7 |
| 6 | `(4,5)` | 0 | 51 |
| 2 | `(2,2)` | 0 | 29 |

The first two updates retain `[0,2]`; the third extends it to `[0,2,2,5]`.
All later updates preserve that full cache. There are four total source reads,
compared with fourteen continuing steps across fresh executions. Repair costs
204, plus one initialization unit; the fresh bills sum to 182. Final retained
storage is thirteen slots/cells in the stated model. Checked examples establish
these numbers and consume the universal correctness/read-bound results.

Further examples cover supplied start index 1 and sum 7, immediate stop,
exhaustion, an empty store, a threshold first reached at the last entry and an
unreachable threshold. The minimality control rejects stopping at the *later*
prefix with sum 2. Other checked rejections show why deduplicating equal prefix
sums, resuming from the old terminal state after a decrease, or retaining the
cache through a store edit would violate the contract. These are mathematical
separations, not failures to elaborate a proof.

## Reuse and next decision

`stateful` and `stateful_laws` instantiate the existing
[initialized-state operations and laws](../../Applications/Incremental/Stateful.lean)
with threshold replacement and exact output-pair replacement. Its repair calls
the retained algorithm, not the semantic recomputation function.
`stateful_project_repair` reuses the old cache projection theorem.
`representation_recovery` reuses #590's local-read representation law; the public
finite-function example recovers the repaired array result through that law.
No compiler syntax conversion or new universal recursion interface is required.

Retain this bounded capability. Existing stateful composition laws already
suffice for semantic composition; this client supplies no need for another
semantic law. Those laws carry no resource guarantee. Composing amortized read
savings or lifetimes across backends would need an explicit resource contract.
Store edits additionally need a rule identifying and invalidating the affected
prefix suffix. These remain opportunities under
[#109](https://github.com/VladimirMarko/conaled/issues/109), coordinated with
[#235](https://github.com/VladimirMarko/conaled/issues/235), not completed work.
A next bounded test can change one contribution at a known index and check which
prefix cells survive, including a decrease followed by an extension. It must
charge discovery/invalidation work and prove equivalence to the edited store.

## Statement review and development evidence

The generic theorems quantify over every total `Nat → Nat` store, all natural
starts, sums and thresholds, and every finite update sequence. Only positions
below `i+fuel` are read; the public representation law requires agreement only
on legal store positions. The invariant fixes the store and start parameters;
it does not permit arbitrary store edits or negative contributions. No new
axiom, recursion-depth setting or heartbeat budget was introduced.

The initial core proof passed. Later failed checks concerned Lean encoding:
`initialize` is reserved; the old cache-projection theorem needed its explicit
recomputation-map argument; closed array examples worked by definitional
reduction rather than partial `simp`; recursive `Valid` needed unfolding before
`decide`; an unavailable `norm_num` tactic was replaced by the already imported
arithmetic reasoning. Failed sources and logs are retained in the task's review
evidence. None changed the independently chosen outputs or acceptance criteria.

Acceptance uses the exact integrated candidate's build and exhaustive proof
audit, followed by independent Standards and Spec review. Pure checked examples
exercise the executable definitions; no external runtime adapter or physical
performance claim is part of this delivery.
