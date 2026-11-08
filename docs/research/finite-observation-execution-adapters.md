# Finite observation and execution adapters

This is the checked experiment for [#353](https://github.com/VladimirMarko/conaled/issues/353),
following the [reuse audit](compositional-reuse-audit.md). The native contracts
were frozen at `16956a592b633482eb1568d741473eeffc9eafbc`. Their definitions and
statements remain unchanged. This experiment adds optional adapters; it does
not replace the parser or runtime execution loops.

## Word observations and a second client

[`FiniteObservation`](../../SquareKit/FiniteObservation.lean) packages a typed
path with its endpoint decoder into the public result type. Its morphism law
is an application of `Behavior.observe_morphism`. The package adds no new
mathematical preservation assumption and does not change the coalgebra.

[`WordPathObservation`](../../Applications/Languages/WordPathObservation.lean)
constructs the path for every word satisfying the native depth bound. The
recursive construction follows exactly one transition per symbol. Packaging
the endpoint keeps the residual language/depth index out of the caller's result
type. `observe_wordPath` identifies observation with the independently retained
native `read`; `read_morphism_via_path` then derives the original public
selected-decision equation through generic path preservation. The theorem
`unfold_lookup_via_path` connects parser and trie lookup, retaining the actual
selected parse or refutation. No arbitrary type-valued language is assumed
executable, and the finite depth bound is retained.

[`DepthObservation`](../../Examples/DepthObservation.lean) uses the same package
for a non-parser machine. A bounded list of increment commands observes the
whole final counter. A second representation toggles an otherwise redundant
Boolean flag. Local coalgebra morphism evidence derives all-command observation
preservation. The worked input `[2,3,1]` from counter 7 produces 13, independently
specified as the initial counter plus the command sum. Both clients pay for
their path construction and native-observation identification; the generic
morphism proof is shared.

## FIFO state and measured execution

[`FIFOExecutionFusion`](../../Applications/Resources/FIFOExecutionFusion.lean)
identifies native `AbstractFIFO.run` with a list fold. It recovers the exact
`FIFOContracts.run_erases` statement through `Resources.run_value_fusion`.
The changing-decoder version uses a native FIFO simulation to establish the
one-step commuting law, then derives preservation for every command list.

The redundant queue representation stores a list and a counter that increments
on every command. Its decoder forgets the counter, while instrumentation charges
one unit per command. The theorem quantifies over arbitrary starting lists,
counters and command lists. A worked enqueue/delete sequence checks the retained
queue `[4,7]`. This is stronger evidence of the decoder parameter's use than the
identity-decoder specialization alone.

Cost preservation is not inferred. The checked control compares equal unit
values with costs zero and one: the cost-zero bound holds for only one. The
existing accounting contracts remain responsible for quantitative comparisons.

## FRP factorization through the same fold infrastructure

[`TraceFold`](../../SquareKit/TraceFold.lean) identifies a native trace-producing
recursion with a fold accumulating state and outputs. Its inputs are the native
empty/cons equations; it does not define a replacement evaluator. Appending to
the output accumulator is proof-side and carries no runtime efficiency claim.

[`ExecutionFusion`](../../Applications/FRP/ExecutionFusion.lean) decodes an
engine state and its accumulated response list by running the native consumer
on those responses. The one-step compatibility theorem uses the native
consumer's append law and preserves every event position. Applying
`ListFusion.foldl_reachable` derives `run_factor_via_fusion`, with exactly the
original `Pipeline.run_factor` statement for arbitrary initial states and command
lists. FIFO's `run_value_fusion` uses this same existing fold fusion theorem.
Thus the shared component is finite fold fusion, rather than a new universal
runner imposed on both applications.

[`FiniteExecutionAdapters`](../../Examples/FiniteExecutionAdapters.lean)
reuses the independent FRP packet script and calculates four silent positions
followed by the timestamped batch `(2,[3,4,3])` and selected consumer result
`(1,10)`. These expectations are proved through the new factorization theorem.
The selected consumer state is also checked. A negative control shows that
forgetting silence identifies two differently positioned traces.

## Setup, recurring work and adoption

The native proofs are short. The adapters require more total source: a path
package, each client's path/native-read identification, a trace/fold adapter,
and the FRP decode/step lemma. The benefit is that a new representation with
local coalgebra or step compatibility can reuse observation or execution
preservation without another all-path or all-command induction. The existing
framework already supplied those generic theorems; this experiment exposes them
at additional native boundaries.

Keep the native APIs and their current proofs. The checked adapters are optional
reuse points, not grounds for migrating every consumer. The decoder-changing
FIFO case and non-parser observation client demonstrate reuse, but do not prove
that the setup cost is amortized in normal authoring. A future prospective trial
must count this setup separately from incremental work. No measured agent or
human productivity advantage, runtime speedup or memory improvement is claimed.

## Statement review and validation

The public conclusions retain selected decisions, full state, exact optional
outputs and native initial-state parameters. Depth hypotheses restrict only
finite observations; FIFO and FRP execution theorems quantify over arbitrary
finite command lists. The relation on redundant queues has inhabited examples,
and its local simulation is proved rather than assumed as the all-run result.
The observation decoder is identical on both routes, justified by the typed
path package. It does not assert that every decoder preserves every possible
observation.

New application claims use the shared theorems, while native expected results
remain independent. The negative controls isolate absent cost information and
lost event positions. The public aggregate imports the examples and their
supporting modules. Acceptance requires the complete committed-candidate build,
exhaustive axiom audit and independent Standards/Spec review.
