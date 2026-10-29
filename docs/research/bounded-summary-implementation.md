# Bounded append/query realizations and capability limits

Implementation for [#239](https://github.com/VladimirMarko/conaled/issues/239),
using the accepted [ordered-summary laws](ordered-summary-implementation.md),
[resource assessment](data-structure-resource-contracts.md) and
[target comparison](data-structure-target-capabilities.md).

The [semantic module](../../Applications/Sequences/BoundedSummary.lean) implements
a buffer of `N` Boolean slots and a `Fin (N+1)` length. Every slot is initialized,
which is stronger than requiring only the visible prefix to be initialized.
`decode` observes exactly that prefix. `capacity` proves its length fits, and
`decode_push` proves an indexed write extends its ordered observation by one
value. The implementation reuses `Dijkstra.Store.write` and `lookup_write`.
No element equality is needed for append. The Boolean parity cache is a separate
field, not the length already needed to locate the next slot.

`spec` independently describes append, parity query and full-history query on
ordinary lists. The total API reports overflow and preserves state. `Admitted`
bounds the number of requested appends; `admitted_prefix` establishes that bound
on every prefix, and `admitted_within` shows each append has room along the
independent history transitions. Admission is therefore not an assumption that
an overflowing append somehow succeeds.

The concrete scan reads indexed positions directly. Its parity meaning reuses
#185's `FreeMonoid.lift` summary and append laws. `Valid` requires the stored
cache to agree with that independent summary. `cachedPush_valid`,
`cached_closed` and `cached_trace_valid` preserve it, including across overflow.
Plain and cached full-history queries use the same ordered output algorithm.

## Client proof reuse and observations

`trace_preserves` lifts local step simulation through existing reachable fold
fusion. The plain case also uses the existing relational square interface.
`plain_trace` and `cached_trace` instantiate the same client theorem, and
`traces_equal` preserves both the final ordered history and every public reply.
The accumulated reply list is a mathematical observation of emissions, not an
extra bounded field inside the service.

Callers pass their ordinary commands directly to `plainStep`, `cachedStep` or
`trace`; they do not construct internal-language syntax or inspect slot indices.
The commands are the service's actual interface. `batch` builds then queries;
`everyPrefix` queries after each append. Their costs and replies are checked
through these shared results in [the examples](../../Examples/BoundedSummary.lean).

`prefix_elimination` uses `Symmetric.lengths_inits`: generating the prefix-length
sequence needs only the final length and `List.range`, rather than materializing
all prefixes. A checked application connects that result to the existing
`Symmetric.prefixLengths` observer. Full-history observation remains separate.
The examples retain an ordered free-monoid word and show that equal parity or
equal length cannot reflect sequence equality. Word summaries are semantic
diagnostics, with no bounded-space or constant-time claim.

## Primitive cost model

The [resource module](../../Applications/Resources/BoundedSummary.lean) uses
natural-number tariffs for indexed visits/loop tests, parity combinations,
cache writes/reads, slot writes, output constructors, and control/counter writes.
All comparisons therefore have explicit nonnegative weights. These are model
operations, not measured Lean allocator or CPU events.

`scanM` and `exportM` instrument the actual recursive indexed algorithms.
`scanM_exact` and `exportM_exact` prove both their values and costs. At current
length `n`, the scan costs `visit*(n+1) + combine*n`, and ordered output costs
`visit*(n+1) + emit*n`. The extra visit is the terminating loop test. A successful
indexed append costs `control + slotWrite + control`: a capacity check, one slot
write and a counter update. Cached append additionally combines the parity and
writes it. Rejected append performs only the capacity check. Cached query reads
one cache value.

This replaces #177's linked-list append baseline with an indexed-write baseline;
no linked-list visits are assigned to an array append. For admitted commands,
let `a` be the append count, `l_j` the actual length at each summary query, and
`k_j` the length at each full-history query. The per-command equations imply:

```text
B       = a * (2*control + slotWrite)
output  = Σj (visit*(k_j+1) + emit*k_j)
plain   = B + Σj (visit*(l_j+1) + combine*l_j) + output
cached  = B + a*(combine+cacheWrite) + q*cacheRead + output
```

The Lean exact theorem is the more general `budget` recurrence, which follows
the actual current history and also covers overflow. `plain_cost` and
`cached_cost` prove equality to it for measured execution; they are not bounds
on a disconnected counter. `run_erasure` uses `Resources.run_value_fusion` to
recover the semantic trace. `sequential` uses `run_append`, and `change_units`
uses the additive map required by `reweight_run`.

Construction initializes `N` slots and the counter, with one further write for
an empty cache. `plainProgram_cost` and `cachedProgram_cost` connect construction
plus actual measured execution to `total`. Comparison of already-built values
must not silently substitute for this whole-program objective.

The checked unit-tariff examples use four appended Booleans:

| Workload/objective | Plain | Cached |
|---|---:|---:|
| Four appends, then summary, excluding construction | 21 | 21 |
| Same, including capacity-four construction | 26 | 27 |
| Summary after each append, including construction | 41 | 30 |
| Four appends with no query, including construction | 17 | 26 |
| Batch-final summary, cache writes weighted two | 26 | 32 |
| Every-prefix summary, cache reads weighted ten | 41 | 66 |

These are target-model counterparts of #177's examples. The suffix tie survives
the new common append baseline; the extra initialization write breaks that tie
for a whole program. A separate attained tie uses capacity one, one append,
three queries and cache reads weighted two: both complete runs cost fourteen.
The `Optimization.minimizers` examples prove both candidates attain that value.

`clone` reads and writes all capacity slots before conversion. `convert` then
runs the measured scan and writes the cache. `convert_exact` preserves the
buffer and charges `N*(visit+slotWrite) + visit*(n+1) + combine*n + cacheWrite`.
This copying conversion does not assume physical sharing. For an existing
length-one buffer of capacity two, conversion costs eight units; two later
queries cost two cached units versus six plain units. Their four-unit saving
fails to pay for conversion, so the converted run costs ten. `convert_valid`
proves that the resulting cache can be used by the same client theorem.

## Retained state, workspace and restricted optimization

`retained` counts Boolean slot/counter/cache units in the declared model:
`N+1` for plain and `N+2` for cached. A counter is one *bounded counter unit*,
not a claim that arbitrary `N` fits one physical machine word. A target must
supply that counter's representation and arithmetic, including its capacity
check. Old buffer versions are not retained by this model.

`conversionPeak` counts simultaneously live source and copied destination
buffer fields. `scanFrames` separately counts a recursive scanner's conceptual
frames. `conversionWorkingPeak` includes those frames, and `operationPeak`
also permits an ordered output of current length. `operation_peak_bound` bounds
this explicit workspace expression using the buffer's capacity. These resource
projections are not additive charges. They do not model compiler closure layout,
garbage collection, retained external reply logs, or sharing across versions.
The full-history value is an output transcript; a backend that queues outputs
instead of consuming them needs an additional retention bound.

The restricted `eligible` set contains the two proved representations and
excludes the state-free candidate. `admittedCandidates` additionally requires
the workload to fit capacity. Checked optimization examples apply both the
capacity restriction and the tariff objective; an over-capacity workload has
no candidate in this no-rejection comparison even though the total API still
handles it correctly. The deliberately zero-cost state-free candidate stays
unavailable instead of winning by ignoring its semantic obligation.

For every-prefix queries at capacity four, the work/retained-space costs are
`(41,5)` and `(30,6)`. They are incomparable in the product order, and both are
proved Pareto candidates. Neither is a universal optimum. The exclusion of a
state-free candidate concerns the capacity-one-or-more full-history service;
it is not an impossibility claim about a zero-capacity service or pure batch.

## Missing state and statement review

`no_stateless_trace` quantifies over deterministic executors whose reply depends
only on the current command. Applying its proposed correctness to the two
admitted capacity-one histories `append false; observe` and
`append true; observe` forces the same query reply to contain two distinct
sequences. Thus no such executor implements the contract. A bounded pure batch
receiving all commands/history in one invocation is a different function and is
not excluded by this result. An external retained witness also changes the
capability boundary.

The initial worked case expected `append true; append false; query; observe`
to emit parity true and ordered history `[true,false]`, with a subsequent append
rejected at capacity two. The missing obligations were indexed-write observation
and one shared trace proof; the existing Store and ListFusion laws supplied the
local foundations. The cost case independently expected a scan of two slots to
perform two combinations and three visits. Measured recursion, rather than
formula assignment to a query result, establishes that count.

Statement review covered all new claims:

| Claims | Review and checked connections |
|---|---|
| Parity monoid, scan meaning | All Boolean values, associative XOR, false identity. #185 summary laws supply the independent fold; noncommutative word observations remain available separately. |
| Buffer capacity, push, overflow and admitted prefixes | Bounds are carried by finite indices/counter. Exact-capacity, zero-capacity and rejected-overflow cases verify the total API. `Within` checks requested appends against independent evolving histories. |
| Cache and trace preservation | Cache agreement is a premise only for cached observation. Constructed caches inhabit it; a wrong parity cache is rejected. The same trace theorem is applied to both batch and every-prefix clients. |
| Instrumentation, erasure, exact recurrence | Quantification includes all tariffs and commands, including failure replies. Costs depend on actual intermediate length; scan/export results agree with semantics. Whole-program tests include construction. |
| Conversion and workspace | The nonempty conversion example uses `convert_exact`, `convert_valid` and measured bind. Peak counts distinguish buffer fields, frames and output from total physical memory. |
| Optimization | Both tie members, attainedness, unavailable candidate, admitted workloads, and product-order Pareto cases are checked. Candidate restriction makes no coverage or global-optimality claim. |
| Prefix elimination and state absence | The existing symmetric observer is preserved only at its length observation. Both distinguishing state-free histories are admitted; the negative claim does not rely on impossible inputs. |

Validation uses focused builds, the public-entrypoint coverage check, full
candidate build and exhaustive proof audit. Candidate-specific logs, statement
review and independent review outcomes belong to the orchestration record.
No library/toolchain change, runtime benchmark or production adapter is included.
#235 retains broader observation/reflection interface work; #226/#227 own crash
survival, session identity and recovery. The present buffer contract makes no
durability or branching-history guarantee.
