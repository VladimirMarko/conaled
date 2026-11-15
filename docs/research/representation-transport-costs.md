# Costs of representation transport and its consumers

Research for [#406](https://github.com/VladimirMarko/conaled/issues/406).
Inspected on 2026-11-09 at `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
Reuse measured executions and evaluate a retained-conversion workload before
adding a transport-cost abstraction. This report adds an actual conversion
consumer and a sharing experiment beyond
[#407](algebra-and-program-specification.md) and completed
[#409](counted-stack-contracts.md).

## What is evaluated and charged

The selected evaluator is the recursive Lean definition of each measured
algorithm, with its explicit abstract tariff. For tree flattening this charges
visited constructors and copied list cells. For downstream random-access
construction and lookup, retain the counts already returned by `toRARun` and
`fetchRARun`. These are source algorithm observations, not Lean allocation,
normalization time, native instructions or elapsed seconds.

| Phase | Observation needed | Status here |
| --- | --- | --- |
| Apply an equivalence's forward/backward map | Steps of the chosen implementations | Must instrument the map; equivalence laws alone give no tariff |
| Transport a structure | Cost of constructing transported operations, then of calling them | A closure may defer conversions until each call; account for both |
| Elaborate or normalize a transport term | Elaborator/normalizer operations, time and memory under a pinned toolchain | No such measurement follows from runtime counts |
| Execute emitted code | Steps of its specified target interpreter | #409 supplies one unit per typed stack instruction, including primitives |

**Literature.** [calf, POPL 2022](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf),
§§1–2 and Theorems 2.4–2.6, separates extensional behavior from intensional cost
using modalities and proves noninterference. A plain value/cost pair does not
inherit that discipline: Lean code can inspect its second projection. The
local erasure proofs are therefore essential. [Licata's computational transport
example](https://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/)
explains transporting a monoid operation by pre/post-composing conversions.
It gives no claim that those conversions are free. The present assessment
requires no univalent universe and does not estimate the cost of general `ua`.

## Existing conversion and a real resource consumer

**Local source audit.**
[TreeFlattening/Core](../../Applications/Resources/TreeFlattening/Core.lean)
defines recursive append flattening `fromTWithCost` and pending-stack flattening
`fromTsWithCost`. The former costs `nodes t + copies t`; the latter on `[t]`
costs `nodes t + 1`. Their outputs are the same fringe. The
[cached versions](../../Applications/Resources/TreeFlattening/Cached.lean)
operate directly on cached trees and prove equality of the full measured result
to erasure; they do not execute an erasure prepass.

[Observation](../../Applications/Resources/TreeFlattening/Observation.lean)
provides `recursiveSquare`, `stackTreeSquare`, and `flattenQuery`. Both
conversions feed the *actual* result into random-access construction and then
lookup. `flattenQuery_agreement` proves the same query answer;
`flattenQuery_cost` states the sum of conversion, construction and lookup
counts. This already meets the basic need for a behavioral and cost comparison.

[Growth](../../Applications/Resources/TreeFlattening/Growth.lean) proves exact
perfect-tree formulas. For rank p, the stack traversal costs `2 * 2^p`; the
recursive cost R satisfies `2*R + 2 = (p+4)*2^p`. A paper specialization at
p = 3 gives 16 versus 27, with eight leaves. Since the downstream construction
and lookup receive identical lists, the eleven-step conversion difference
survives in the complete query pipeline. This arithmetic is derived from the
inspected theorems; no new executable test was run for this report.

Tree-to-list decoding is many-to-one, so this is semantic representation
agreement, not a bijection or universe path. To test a literal equivalence
without that ambiguity, use the subtype of cached perfect trees of a fixed
rank with correct caches, versus vectors of length `2^p`, after proving a
canonical rebuilding inverse. A list alone does not retain arbitrary shape or
cache data. This equivalence is a **proposal**; the existing cost comparison
does not require or establish it.

## Existing equivalence-based witness transport

[ParserWorkload](../../Applications/Languages/ParserWorkload.lean), completed
[#304](complete-parser-workloads.md), is a stronger direct transport example.
`Map.iso` gives witness isomorphisms on finite Boolean-list payloads; `Map.run`
executes identity, complement, composition and prefix-shift presentations, with
`Map.run_result` proving the actual isomorphism application. `Spine.packRun`
and `normalizeRun` charge normalization; `setup` and `execute` compare direct,
retained, normalized and combined policies. `execute_exact` preserves the
selected decisions, and `execute_count_repeated` separates setup from repeated
query counts. Thus equivalent witness presentations with different conversion
costs already feed an actual parser consumer. These source-level normalization
counts are not elaborator normalization measurements.

The frozen twenty-request/eight-map workload costs 5180 work units directly
and 868 with combined normalization/retention; the one-short-request workload
costs 173 versus 733. These are the existing report's checked controls under
its declared tariff, not new benchmark results. Exact native parsing agreement
has wider scope than the cost theorem, which is restricted to the explicit
`Spine`/`Map` fragment. Arbitrary function-valued transport is not charged by
guesswork. [#239](bounded-summary-implementation.md) likewise already charges
plain/cached conversion and distinguishes query savings from setup/storage.
Neither omission of these consumers nor another generic preparation interface
would justify a new issue.

## Composition, sharing and repeated calls

[Measured](../../Applications/Resources/Measured.lean) defines additive ordered
sequencing with `bind`, `bind_assoc`, `bind_erases` and `reweight_bind`.
The latter requires an additive homomorphism; arbitrary tariff changes cannot
be assumed to commute with composition. Bounds additionally need order
compatibility. `erasureSquare` forgets cost deliberately.

For measured f and g with value functions f₀ and g₀, the contract is
`value(bind (f x) g) = g₀(f₀ x)` and
`cost(bind (f x) g) = cost(f x) + cost(g(value(f x)))`.
A bound for g must apply at that actual intermediate value. Equality of f₀
alone does not equate the first summands. #409's `append_padding` is already
a checked rejection of value-implies-cost equality; no duplicate padding
experiment is needed. #410's returning/stuck distinction likewise prevents
attaching a finite execution cost merely to a semantic value.

For transport of a binary operation through e : A ≃ B, the proposed execution
is `e (op (e⁻¹ x) (e⁻¹ y))`. Under a sequential tariff its cost sums two reverse
conversions, the original operation at converted inputs, and one forward
conversion. Inverse laws prove behavior, not cancellation of executed work.
A compiler may eliminate adjacent conversions only with its own semantics
and cost improvement proof. This formula is a design calculation, not a
checked theorem of computational univalence.

Repeated `flattenQuery` calls rebuild the target each time. Retaining the
converted list and constructed random-access value could pay those setup costs
once, then sum lookup costs. That is an explicit state/workload change; ordinary
function sharing or a proof of equivalence does not establish it. Retention
also needs a storage observation and an input-update/invalidation policy.
Neither the measured pair nor stack unit tariffs automatically account for
these. Source normalization and native caching must remain separate experiments.

## Bounded successor and decision

Defer a new standalone cost-framework issue: #304 already realizes the
transport/normalization/retention comparison, and #239/#305 supply conversion
and preparation contracts. A possible additional consumer experiment under
#208/#211/#200, if required by the representation client chosen in #393, is
to compare k queries on one
immutable cached tree via repeated `flattenQuery` with an explicit prepare-once
value followed by the same lookups. Reuse the current measured algorithms,
preparation/workload interfaces where their hypotheses fit, and the perfect-rank
family. Prove equal answer sequences, exact setup-plus-query sums, and the
retained representation's size bound. Check k = 0, k = 1 and repeated/missing
indices; do not assume setup is worthwhile at k = 0. Measure native time only
as a separately labeled experiment with pinned toolchain and allocation policy.

[Prepared](../../Applications/Resources/Prepared.lean) already supplies
`Ops`, `Laws`, `Storage`, `Bounds`, `queries_meaning`, `queries_bound` and
`Reduction.preparation_work`/`query_work`. These distinguish setup, retained
state, query cost and the conversion boundary.
[Workload](../../Applications/Resources/Workload.lean) supplies ordered
execution and `run_append`. Reuse these APIs: the proposed experiment is a
consumer specialization, not missing generic preparation composition or a
new storage abstraction. The new evidence should be the repeated-query
tradeoff and retention bound, not another wrapper around a single execution.
Coordinate #393 on any later genuine equivalence; defer general universe
transport-cost laws, runtime claims about normalization, and mandatory compiler
changes. The ordinary semantic and resource clients remain direct Lean clients.

This is documentation-only research. Existing Lean results were inspected,
not rebuilt here. A successor adding algorithms or claims needs statement
review, checked examples, executable controls, and the README build/proof audit.
