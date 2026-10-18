# Two-source traces and conditional progress

Status: experimental. This extends the [complete-window protocol](frp-runtime-scope.md)
for [issue #29](https://github.com/VladimirMarko/conaled/issues/29); it does not
complete #27 or select a sole FRP runtime.

## Model and contracts

[Trace.lean](../../Applications/FRP/Trace.lean) uses two fixed, total streams of
messages indexed by natural numbers. A message contains a proposed frontier and
a finite packet. `process` uses `advance` for acceptance. Rejection leaves the
source state unchanged and consumes the message position. Retrying requires a
new stream entry. Acceptance still closes a complete half-open window, including
silence. Structural checks never establish honesty.

A schedule chooses left, right, or idle at each natural-number step. `count`
counts consumed messages separately for each source. `run` computes each source
state from its consumed prefix; `run_step` proves that this definition implements
one local transition on the selected source and leaves the other unchanged.
This factorization prevents skipping or reordering messages within a source.
The model retains all logs, recomputes prefixes, and makes no execution-cost claim.
Finite inputs can leave the remainder of their total streams undelivered.

Safety holds for any schedule. A `Delivery` additionally describes monotone
available prefix lengths and requires that each scheduled message is already
available. Its `Fair` predicate requires every available finite prefix eventually
to be consumed, at or after the step where its availability is used. It permits
unbounded delays and arbitrary idle steps, but excludes starvation of an
available message. Legal delivery is a scheduling constraint; packet acceptance
is the separate structural test inside `process`.

`eventual_observation` assumes, for each source, a finite prefix whose frontier
strictly exceeds the query and a step at which that prefix is available. These
are source-progress and delivery assumptions. Together with fair processing,
they imply a returned observation at some finite step which persists forever.
Neither fairness nor source progress mentions the desired observation. The proof
finds processing steps for both prefixes, takes their maximum, and uses monotone
knowledge. It does not assume honesty: honesty is needed to identify the returned
batch with an external truth, via `run_sound` and `observeMerge_sound`.

## Checked cases and statement review

[FRPTrace.lean](../../Examples/FRPTrace.lean) grows the theory around the expected
left batch `[3, 4, 3]` and a silent right source at rational time 2. The first
missing connection was a trace operation relating consumed source prefixes to
state transitions; the existing one-packet proofs could not express schedules.
The original [frontier cases](../../Examples/FRPFrontier.lean) remain imported.

| Claims | Statement review and checked uses |
|---|---|
| `Refines.refl`, `Refines.trans`, `process_refines`, `prefix_refines` | Frontier monotonicity and exact preservation strictly below the old frontier; no validity or honesty premise is concealed. Used by future-observation and completion cases. |
| `Refines.completion` | Every completion of a later state completes the earlier state, in the reverse direction from execution. The rejected-packet prefix case exercises this direction. |
| `process_valid`, `prefix_valid`, `run_valid` | Initial validity is required; arbitrary accepted and rejected messages preserve it. The ordered-packet trace specializes the result for every global step. |
| `Honest`, `process_sound`, `prefix_sound`, `run_sound` | Initial completion and validity plus honesty of accepted windows suffice. Honesty quantifies over all timestamps in a window, including omissions; rejection needs no semantic promise. The silent-window and nonempty ordered-packet cases supply these hypotheses explicitly. |
| `count_mono`, `run_step`, `run_eq` | Counts are monotone; exactly the next selected message is consumed; equal per-source counts give identical states even at different global steps. No equal-global-step comparison is inferred. |
| `observe_ready` | Existence of a returned batch is equivalent to both strict frontier inequalities. Time 3 remains unknown when both frontiers equal 3. This is local readiness, not progress. |
| `observe_persists`, `run_persists` | Every returned list persists under refinement and all future steps. The late packet `[9]` is rejected and cannot alter the output. |
| `interleavings_agree` | Any two returned observations from the same initial states and streams agree, even at unequal source-prefix lengths. A common longer prefix provides agreement without assuming external completions. The examples compare left-left-right with right-left, retaining `[3, 4, 3]`. |
| `Delivery.Fair`, `eventual_observation` | Available message counts eventually get processed; each source supplies an available closing prefix. A legal right-left schedule with only one delivered message per source witnesses satisfiability and progress. |
| `traceRep`, `executionSquare` | The relation includes initial validity, initial completions, and adapter honesty. The implementation runs the trace; the semantics retains the same source truths. Composition with the existing mapped merge proves the mapped output contract. |

At global step 2, left-left-right is still unknown while right-left returns the
batch. This checked inequality rules out comparing schedules by elapsed steps.
When every source packet ends at time 2, the fair right-left delivery still
returns unknown forever: processing cannot manufacture source progress. When
closing packets are available but the scheduler always idles, its fairness
predicate is false and every observation remains unknown. These cases separate
source progress from processing fairness. All examples use kernel proofs or
decidable rational reduction, with no native-decision axiom.

## Shared constructions and Felix correspondence

`executionSquare` composes with `mergeObservation`, `mapObservation`, and
`mappedMergeObservation` through the existing `Relational.compose`. Its checked
mapped consumer quantifies over arbitrary honest adapters and schedules. This
uses the same local-relation preservation contract as the relational compiler
in ADR 0002. A source-language primitive could use this square once a language
and its schedule inputs are chosen. This experiment introduces neither a new
language nor a compiler instance without such a caller.

The repeated obligations are reflexive/transitive knowledge refinement, lifting
one-step preservation over finite prefixes, and restricting completion sets.
They are factored locally into `Refines`, `prefix_refines`, and `prefix_sound`.
The existing relational square interface already handles the semantic composition
needed here. No missing shared construction with demonstrated independent callers
emerged, so this experiment adds no general framework or new #8 dependency.

The architectural comparison uses Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, pinned in [SOURCES.md](../SOURCES.md).
The inspected [CategoryH definitions and composition](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
separate operations from congruence, identity, and composition preservation and
compose the preservation proofs. Local relational-square composition follows
that discipline. It does not prove architectural parity with Felix's entire
homomorphism hierarchy. The upstream commented product-homomorphism construction
has holes; it supplies no scheduler, fairness theorem, or generic feedback law
for this experiment. Full parity remains tracked by #8 and #25.

## Remaining gaps and validation

This is a pure two-source model, with no general graph scheduler, switching or
residual initialization, phase evaluation, analytic primitives, feedback,
partial spines, nested-event bind, cancellation, reclamation, or history/cost
bounds. No rational-to-real evaluator is claimed. Generic completions can have
infinite futures; the existing native real-time bridge retains its separate
finite-history restrictions. Initial states still assert their certified past,
including the empty-past contract of `initial`.

Validation commands from the pinned environment:

```sh
direnv exec . lake build Examples.FRPTrace
direnv exec . ./check.sh
```

The targeted build passed. Full source-check and review results accompany the
implementation handoff. Proof infrastructure is unchanged, so audit regression tests
are not required for this change. Both new modules are imported by the public
entrypoint and included in the normal exhaustive proof audit.
