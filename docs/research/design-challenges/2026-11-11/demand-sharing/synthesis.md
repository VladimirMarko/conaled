# Demand and sharing: reconciled assessment

Compare small consumer-specific request runners before selecting a shared evaluator. Retain the current partial-spine semantics and measured collapse/materialization results. All three lenses favor a bounded operational experiment; none finds that the existing single-pass runners promise memoization and fail to deliver it.

The source assessed is `e80c51d968925be3809ba3acc3259de7041b504b`. Initial reports are preserved unchanged. The coordinator inspected the label type, the producer transition type and completed-end exclusion, and the append/difference-concat boundaries used below.

## A concrete interface boundary

`CollapseDemand.Label` contains a function returning a measured sum. `cachedAux` retains an accumulated scalar and consumes selected labels once. It has no API for requesting a previous label again. Its value, selected-prefix and exact-work theorems remain useful; they do not establish reusable cell memoization.

`Progress.Producer` emits or performs silent work. It has no completed-end transition, and `SpineObservations.ofList_not_mem` explicitly excludes completed finite-list observations. A head-of-concatenation runner therefore cannot infer exhaustion from silence, a missing delivery or fuel exhaustion. Reusing this stream interface for terminating inner lists requires an explicit terminal protocol or a separately stated finite-source realization.

The semantic owner already distinguishes bottom from known nil. Its append and concat laws retain the obstruction to fallback and permit output from an infinite first inner stream without completing the outer source. These laws should remain the independent observation specification. They do not determine scheduling costs.

## What a bounded runner must expose

The reports agree on semantic information rather than a prescribed record layout: stable cell identity when references can alias, suspended or completed evaluation state, resumable source/control state, distinct unknown/nil/cons observations, and ordered requests with declared prices. A trace can be proof evidence without being allocated by the runner. A scalar total cannot recover event order.

Start with total atomic callbacks if a two-state cache is intended. Partial-progress callbacks need retained continuation state; recursive reentry or concurrency would require further behavior, but the present clients do not justify adding it speculatively. Derive at-most-once successful evaluation under a retained, no-eviction policy from transitions. Do not ask callers to separately supply equivalent memoization laws. Cache-hit lookup/delivery cost is a chosen tariff, not automatically zero.

The alternatives lens's broader heap evaluator remains a legitimate candidate. It inspects a concrete external sharing semantics, while the other reports make no external evaluator claim. That literature comparison does not establish this repository's event tariffs, finite-end protocol or runtime costs. A general evaluator should earn its extra binding and adequacy machinery through consumers that need it.

## Differences worth retaining

The implementation lens distinguishes head traversal from observation of an already-built append history. `DifferenceConcat`'s strict outer fold agrees with finite concatenation under completion, but remains bottom on an infinite outer stream. Deferred history cannot gain right-fold productivity merely because completed finite values agree. Keep its construction bill attached to later partial observation.

The contract lens identifies two further limits. A positive first-output predicate alone can map both unknown and known-empty input to false, so it is insufficient to certify their operational distinction. Also, partial-spine information orders fix labels: they do not already model arbitrary refinement inside labels. An operational cache can relate to fixed semantic observations without redefining that domain; claims about changing inner information require their own proof.

These points qualify the common recommendation rather than reveal conflicting verdicts. No lens demonstrated that a common cache already reduces author work. Separate runners remain a real outcome of the experiment.

## Frozen comparisons to prepare

1. Request one allocated cell twice, then request an equal-valued but distinct cell. Compare delayed recomputation and retained memoization, including every request, lookup, update and callback charge. Value equality must not collapse identities.
2. Construct/count an outer spine of delayed payloads without forcing them; then fully observe selected payloads, retaining empty cases, callback bills and terminal observations. This supplies a second consumer for any shared forcing component.
3. Request a head through completed empty blocks and stop at the first value. Replace the first known empty block with unknown bottom and require that fallback remain unavailable. Suspension is neither nil nor a divergence proof.
4. Use the existing emit-once outer source with guarded and paused infinite inner sources. Preserve delivered values and their distinct step bills without requesting outer completion. Separately preserve strict difference-concat's infinite-outer boundary.
5. Suspend and resume a request, and compare the combined trace with uninterrupted execution. Compare left-associated append history and right-associated traversal on the same finite blocks, retaining arbitrary-tail value equations and their distinct full bills.

Require an independent event/accounting specification and a bridge from actual executions to partial-spine observations. Exact finite-prefix costs remain meaningful even when a complete request does not terminate. Extract a shared force/cache component only if another consumer reuses its transition invariants without importing concat control. Broader adoption returns to the owner after that evidence.

The [contract](contract.md), [implementation/use](implementation.md), and [alternatives/generality](alternatives.md) reports and [brief](brief.md) record the evidence boundaries. No new Lean proof, build, operational experiment or productivity measurement was performed for this challenge. All proposed runners and test outcomes remain design work; publication does not implement or adopt them.
