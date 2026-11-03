# FRP runtime scope: complete batches and knowledge frontiers

**Status: experimental, developed on `master` alongside other implementations.**
The protocol and interface may evolve. The proved claims and normal verification
requirements apply throughout; see the [repository policy](../../README.md#parallel-and-experimental-developments).
Merging this experiment does not select it as the sole FRP implementation or
close #27.

Research for [issue #27](https://github.com/VladimirMarko/conaled/issues/27),
2026-10-18. This note proposes an exploratory slice: a pure executable source
protocol and complete-batch merge observation. It does not adopt the full
scheduler proposal or establish that #27 is complete. The implementation and
its checked cases should determine whether this slice is a useful foundation.

## Existing semantics and the missing implementation claim

[`Spec.lean`](../../Applications/FRP/Spec.lean) uses real semantic time,
finite ordered batches, finite support before every observation horizon, and
strict switching. `Event.merge` concatenates the left and right batches at each
time. `Prefix.Sound` certifies every timestamp strictly below its frontier;
`Prefix.Refines` preserves that certified prefix. These are mathematical
contracts over event functions. They supply neither executable finite queues
nor a source transition protocol. `RNF` also leaves the phase representation
abstract. The [integration record](../frp-integration.md) distinguishes these
contracts from the completed carrier equivalences and finite-history merge
proofs.

Elliott's *Push-Pull Functional Reactive Programming*, sections 9–11, motivates
partial temporal information: lower bounds can decide an event-time comparison
before both exact times become available. Its `unamb` construction requires
agreement wherever both computations succeed. A source of lower bounds conveys
non-occurrence information even while no event arrives. These observations
support explicit knowledge as an implementation concern; they do not establish
correctness of the frontier protocol proposed here.
[Author's paper](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)

The preserved [discussion, response 1 §§3.3–3.6](../history/frp/frp-chat.md)
proposes frontiers, pure graph transitions and correctness for every completion
of the known input. Its productivity, cancellation and retention requirements
are separate obligations. The current total
[co-list equivalence](../../Applications/FRP/Equivalence.lean) explicitly excludes
bottom, partial spines and partial elements. None of these results verifies
execution of a lazy `filter` followed by `last`.

## Selected exploratory slice

Use a timestamp type with decidable linear order for the protocol and
specialize executable cases to rational time. The protocol needs ordering,
not real analysis. Treat timestamp conversion to the real-time native event
model as a separate bridge requiring an exact embedding theorem. A rational
execution alone must not be described as an implementation of arbitrary
real-valued behavior sampling.

The exploratory [`Frontier.lean`](../../Applications/FRP/Frontier.lean) stores
a finite log and a frontier. `advance` receives a new frontier and a finite
packet covering the whole interval from the old frontier inclusive to the new
frontier exclusive. Validation checks monotone frontiers and that every entry
lies in this interval. Omitted timestamps assert an empty batch. Entries may
be unsorted and repeat a timestamp within one packet; `batch` concatenates
same-time fragments in packet order. Once a packet advances past a timestamp,
a later packet cannot add another fragment there.

`State.Completes` relates the finite state to a total timestamp-to-list
function agreeing below its frontier. Unknown timestamps can differ between
completions, including completions with an infinite future. Structural
validation does not establish source honesty: `advance_sound` separately
requires agreement with the truth throughout the newly closed window,
including timestamps omitted from the packet. `initial w` also asserts that
the entire past below `w` is empty. An input with earlier occurrences needs an
initialization packet or a different initial-state contract.
[Protocol definitions](../../Applications/FRP/Frontier.lean)

For two inputs, expose the batch at `t` only when `t` is strictly below both
frontiers. Return `left(t) ++ right(t)`, retaining duplicates and the order
within each input. An absent entry then means a known empty batch. Before that
point, return an explicit unknown result. `none` and `some []` must have
different meanings. This matches the existing `Event.merge` equation and the
strict boundary in `Prefix.Sound`.
[Native specification](../../Applications/FRP/Spec.lean)

The checked safety claims are `advance_valid`, `advance_refines`,
`advance_completion`, `advance_sound`, `observeMerge_sound`, and
`observations_agree`. `completion_exists` shows that every state has a total
completion, including states constructed directly rather than by `advance`.
Stored entries outside the certified prefix are ignored by this relation.
The separate `Valid` invariant rules those entries out for protocol states.
The observation code returns a batch exactly when both frontiers cross the
query. General trace progress and eventual readiness are not modeled.

`mergeObservation` packages completion soundness using the existing
[`Relational.RelRep` and `RelSquare`](../../SquareKit/Relations.lean).
`mappedMergeObservation` composes it with `mapObservation` through
`Relational.compose`. A mapped consumer therefore inherits the universal
completion contract without choosing one future as the source's meaning.

## Checked cases

[`Examples/FRPFrontier.lean`](../../Examples/FRPFrontier.lean) checks these
invented timestamps and values through kernel proofs and decidable reduction.

| Case | Checked result |
|---|---|
| Left has `[3, 3]` and right has `[7]` at time 2; both frontiers are 3 | `some [3, 3, 7]`, connected to `observeMerge_sound` |
| Right frontier is exactly 2 | Unknown at 2, even though its log is empty |
| Right is silent but advances to 3 | Its batch at 2 is known empty, enabling `[3, 3]` |
| A source sends a batch below its frontier or at its proposed new frontier | Rejected transition |
| A source moves its frontier backwards | Rejected transition |
| One packet splits `[3, 3]` into two same-time fragments | Same ordered merged output |
| A timestamp equals the frontier | Two explicit completions disagree there |
| Distinct packet layouts represent the same inputs | `layout_independent` uses `observations_agree` |
| A merge consumer increments every value | Shared relational composition gives `[4, 4, 8]` |

`left_sound` and `right_sound` exercise `advance_sound`, with source honesty
proved for explicit total event functions. `ordered_duplicates` uses these
results and `observeMerge_sound`. The initial missing connection was an
executable source transition with a completion contract; `Prefix.Sound` alone
had neither the operation nor its transition preservation theorem. The expected
list `[3, 3, 7]` follows from the existing left-before-right merge convention.

Complete windows move work to the adapter: a device reporting individual
simultaneous occurrences must know when all batches in a window have ended.
The runtime cannot infer this from an empty callback queue. The experiment
retains the full log and scans it for each query; it establishes no history or
cost bound. Interleaved scheduler traces and repeated polling are not modeled.

## Felix comparison

The reference revision remains
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, pinned in
[`SOURCES.md`](../SOURCES.md). The inspected upstream definitions support the
following comparison:

| Upstream capability | Consequence for this experiment |
|---|---|
| `CategoryH` has congruence, identity and composition preservation, with identity and composite homomorphisms | Keep operations and their preservation proofs distinct; reuse composition rather than proving only isolated examples. [Homomorphism.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda) |
| `LawfulCategoryᶠ` transports category laws using equality induced by the interpretation | A storage equality theorem is unnecessary for semantic law transport. Existing shared transport remains available when a lawful category interface is needed. [MakeLawful.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda) |
| A comma object contains a semantic arrow; a comma morphism contains two arrows and a commutation proof | A completion relation can use the local relational square construction; choosing one completion as a decoding function would lose the universal completion contract. [Comma/Type.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda) |

These inspected modules supply completed generic preservation machinery. They
are not evidence of a completed frontier scheduler in Felix. The shared relational composition above demonstrates reuse for a merge
consumer, but it does not settle full Felix
parity, tracked separately in [#25](https://github.com/VladimirMarko/conaled/issues/25).
A typed program language, normalization, general runtime graph interpretation,
and scheduler refinement remain gaps beyond this protocol slice.

## Statement review of the exploratory proofs

`advance_valid` checks the stored-log invariant after a successful transition.
`advance_refines` proves frontier monotonicity and equality of the previously
certified batches. `advance_sound` preserves a chosen completion under the
source-honesty hypothesis for the new window. Its hypothesis quantifies over
all timestamps in the window, so silence is covered. `observeMerge_sound`
quantifies over every pair of completions and preserves exact lists.
`observations_agree` assumes both executions share completions; it proves
conditional observation agreement without asserting legal-trace confluence
or fairness. These statements match the proposed safety claims.
[Exploratory proofs](../../Applications/FRP/Frontier.lean)

The real-time `logEvent` bridge obtains finite past support from the finite
log, and `completes_iff_prefix_sound` connects the completion relation directly
to the existing prefix specification. This specializes the protocol to real
timestamps. It does not prove a rational-to-real evaluator or a timestamp
embedding. Arbitrary total completions in the generic theorem need not satisfy
native finite-history restrictions; the bridge is stated for native `Event`
completions, where those restrictions are already present.
[Bridge definitions](../../Applications/FRP/Frontier.lean)

`completion_exists` supplies a witness rather than assuming consistency.
`advance_completion` reverses the transition direction on completion sets:
every completion of the new state is a completion of the old state. Neither
claim says the source reports the external world honestly. `batch_append` and
`batch_empty` are list calculations used by these proofs; they preserve packet
order and account for silence. `initial`, `windowValid`, and `advance` make the
half-open interval convention explicit.

The relation on partial observations permits any semantic batch for `none`.
For `some out`, it requires exact list equality. `mapObservation` preserves
that relation, and the composed consumer example checks its connection to the
merge theorem. This relation proves safety only: an implementation returning
`none` forever would also preserve it. Readiness comes from the actual branch
condition in `observeMerge`; liveness needs an additional operational model.

## Deferred decisions and completion criteria

The [issue](https://github.com/VladimirMarko/conaled/issues/27) also asks about
executable phases, rational-to-real evaluation, dynamic switching and residual
state, initialized well-founded feedback, analytic primitives, partial spines,
and nested events. This experiment excludes all of them. In particular, the
existing [ordered-bind counterexample](../history/frp/ordered_event_bind_counterexample.py)
prevents adopting max-retiming with stable ties as a lawful `Monad` without
changing or proving the intended algebra.

A graph scheduler will need a trace semantics and explicit fairness/source
progress assumptions. No-lost-wakeup, cancellation ownership, reclamation,
latency and bounded retained history require states and transitions absent
from this slice. Calling the local readiness theorem productivity would hide
that missing work. These obligations come from the preserved
[implementation proposal](../history/frp/frp-chat.md), not from the total
carrier equivalence.

Before promoting the experiment to a runtime design, resolve whether adapters
can provide complete windows or need incremental chunks, whether rational
timestamps are the public contract, whether consumers request monotonically
increasing horizons, and how
a switched-in branch initializes residual state. The first implementation is
useful if its checked boundary and completion examples expose these choices
while its general soundness lemmas compose through existing infrastructure.
A next experiment should add a two-source trace model and prove that legal
source interleavings preserve the same completed observations. Progress should
then be stated under explicit frontier advancement and fair processing
assumptions. That supplies evidence for choosing a graph scheduler interface
before adding phase evaluation or dynamic switching.

## Validation

Run from the worktree with the pinned Nix/direnv environment:

```sh
direnv exec . lake build Examples.FRPFrontier
direnv exec . ./check.sh
direnv exec . lake env python3 scripts/test-proof-audit.py
```

The targeted build passed. A temporary `#eval` probe returned
`some [3, 3, 7]` for the complete merge, `none` at the quiet source's frontier,
and `some [3, 3]` after the quiet source advanced. The retained examples prove
these expectations in Lean without native-decision axioms. Local research
links and new-file whitespace checks passed.

The fresh source check passed all 99 modules, including both new modules
through the public entrypoint. The exhaustive audit passed with transitive
axioms restricted to `propext`, `Classical.choice`, and `Quot.sound`. Existing
module-system migration warnings remain; the new modules build without warnings.
The four audit regression cases also passed: unused external axiom, private
transitive forbidden axiom, private admission, and source unsafe declaration.

## Two-source trace extension

The [#29 trace experiment](frp-traces.md) now supplies ordered two-source traces,
observation persistence, interleaving agreement, and conditional progress under
explicit source advancement, availability, and fair-processing assumptions.
The preceding unimplemented-trace statements describe the original protocol
slice. The extension retains its boundaries around phase evaluation, switching,
and general graph scheduling.

The [one-shot demand extension](frp-demand.md) now models a registered request
and atomic response emission, including no-lost-work and conditional delivery
proofs. Concurrent callbacks, cancellation, and general runtime scheduling
remain outside that experiment.
