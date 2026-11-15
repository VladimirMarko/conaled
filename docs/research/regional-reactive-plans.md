# Bounded regional reactive plans

Issues [#481](https://github.com/VladimirMarko/conaled/issues/481) and
[#485](https://github.com/VladimirMarko/conaled/issues/485) share a local checked
catalog. It composes raw categorical sum/case code with Boolean circuits and
preserves an independently stated delayed computation. Ordinary compiler,
circuit and Lean function interfaces are unchanged.

The source input is `Bool + (Bool × Bool)`. Its pure front region returns the
left Boolean, or `x && !y` on the right. Each accepted tick emits the negation of
the previous retained Boolean and stores the front region's result. The initial
state is false. This meaning does not depend on a finite encoding or backend.

## Existing contracts and the added boundary

| Existing construction | Reused capability and remaining obligation |
|---|---|
| [Compiler](../../Compiler.lean) | Typed sums, case, functions and target-parametric compilation. `compile_sound` connects the front region's actual raw code to its source. `closed_beta` removes an immediately applied closure; it does not remove the residual sum. |
| [FirstOrder](../../FirstOrder.lean) | A weaker cartesian source/target contract. Its circuit target needs no sum or function operation. Adding such fields to this target is unnecessary for the mixed plan. |
| [ReactiveCompiler](../../SquareKit/ReactiveCompiler.lean) | Separate seed/body compilation, initialization, transition and finite-run preservation. The current experiment uses the existing initialized circuit programs directly. |
| [ListFoldCompiler](../../SquareKit/ListFoldCompiler.lean) | Finite list recursion and scalar soundness. Compilation terminates structurally, independently of runtime input length; the fold equation is an extra target law. It does not certify indefinite bounded storage. |
| [GuardedStreamCompiler](../../SquareKit/GuardedStreamCompiler.lean) | Guarded body compilation, causal operations and solution transport. Guardedness is not a physical resource certificate. |
| [Staging, #214](arithmetic-staging.md) | Static arithmetic is evaluated and substituted into first-order residual syntax. This is separate from the local closure-elimination equation used here and from #483's proposed specialization trial. |
| [Recursive compilation, #218](recursive-compilation.md) | Checked finite folds and actual counted execution, including value-preserving fusion whose cost can change. It does not supply a constant-space bound for arbitrary richer state. |
| [Squares](../../Squares.lean), [relations](../../SquareKit/Relations.lean), [synchronization](../../SquareKit/Combinators.lean) | Representation maps, relational preservation and compatible interpretations of the same specification. They do not themselves execute different regions with joint retained state. |
| [Initialized feedback](../../Applications/Progress/Reactive.lean) | `seq`, `par`, `run_seq`, `run_par` and `run_related` supply ordered, state-preserving assembly. These are the composition laws used here. |
| [Scans](../../Applications/Progress/SeededScan.lean), [parallel scans](../../Applications/Parallel/Scan.lean) | Initialized sequential observations and shaped scan factorization. Their observation/schedule assumptions cannot be replaced by a generic claim of physical parallelism. |
| [Prepared resources](../../Applications/Resources/Prepared.lean) | `compProfile`, `compStorage` and `comp_bounds` demonstrate lifetime-sensitive peaks with both states live. Their query protocol is not the reactive tick protocol, so this experiment defines its own explicit copy/reclaim schedule. |

Successive lowering preserves one computation through representations. A
synchronized interpretation compares several meanings of the same computation.
The mixed plan instead executes different computations in different regional
representations. It retains the actual raw code and circuit bodies, not merely
backend labels.

## Local language and construction

[RegionalPlans](../../Applications/FRP/RegionalPlans.lean) defines a typed finite
language with concrete leaves, sequential composition and parallel composition.
Its state type is computed from the chosen plan; serial and parallel composites
retain both component states. `compile` constructs these supplied cuts:

- `fused`: raw F followed by one circuit program containing delay and negation.
- `split`: raw F, circuit delay, and a separate circuit negation program.
- `checked`: raw F, redundant encoding, checked decoding, then the split circuit
  programs. The boundary value is `(b,!b)`, with its validity proof erased at
  runtime; decoding executes the existing validation function.

The grammar also contains a direct native reference, a direct circuit gate,
unchanged side input and an explicit shared-input copy. The latter copies one
immutable source input into two branches. Parallel means left then right within
one synchronous tick. There are no effectful speculative branches, instantaneous
cycles, asynchronous queues or live changes of partition.

`Plan.correct` composes leaf preservation. `continuation` applies the shared
relational finite-run theorem from any supplied live state, including an empty
suffix, and preserves both outputs and logical final state. `initial_correct`
separately establishes the seed. `parallel_correct` uses `run_par` to preserve
ordered zipped outputs and the delayed continuation. Queries observe retained
state and leave the executor unchanged; only accepted ticks advance it.

Direct Bool ports need no conversion. Redundant ports require validation and
projection; invalid raw pairs return `none` before a consumer step. Omitting the
adapter is a rejected catalog request. The subtype is local to this boundary,
not a universal interchange representation. No ownership is transferred across
sessions: each selected plan owns its state for its entire invocation. External
publication, crash recovery and asynchronous cancellation remain outside this
pure executor; they cannot be inferred from successful value conversion.

Two ad hoc whole runners would have been smaller, but would not provide the
required typed sequential/parallel construction. A general graph IR would add
scheduling and extensibility obligations unused by these clients. The local
catalog leaves both ordinary routes available.

## Requirements, admission and separate guarantees

[RegionalAdmission](../../Applications/FRP/RegionalAdmission.lean) returns an
actual realization with its state interpretation and semantic law. Bounded
admission additionally carries proof of analyzer coverage and the selected
plan's capacity inequality. `assess` also checks arbitrary compositions in this
local grammar, including the boundary-capacity counterexample.

| Request | Result |
|---|---|
| Native semantic execution | Accepted with the native executor and source relation. |
| Native bound without analyzer evidence | Unsupported analysis. This says nothing about impossibility. |
| A regional cut with sufficient capacity | Accepted with its actual plan and bound evidence. |
| The same cut below its modeled peak | Rejected with required and available capacities. |
| Residual sum code sent directly to the first-order circuit route | Rejected for the missing sum operation in this catalog. This is not a claim that finite sums cannot be lowered. |
| Redundant port connected without its adapter | Rejected for incompatible ports. |

The author supplies the finite cuts, primitive meanings, boundary relation and
execution schedule. Typed construction checks ports and retained state shapes.
Raw analysis checks the selected finite first-order code; it rejects closure
creation/application for resource purposes. The closure-elimination theorem
proves the lowering's meaning and removes that requirement before analysis.
Residual sum elimination remains confined to the raw region. #482 can add its
separate lowering as another plan without requiring the circuit region here to
support native sums.

Compiler termination follows structural recursion on finite syntax and the cut
catalog. Raw step termination has an operational derivation; circuit step
termination uses `Circuit.Executes`. Initialization, storage, work and conditional
service are separate theorems. The executable growing-list client proves that
semantic execution alone does not imply a uniform retained-list bound. Missing
analysis is represented by `unsupportedAnalysis`, never a zero-cost certificate.
Internal work helpers on unanalyzed leaves are not resource evidence.

## Operational resources and progress

[RegionalResources](../../Applications/FRP/RegionalResources.lean) counts raw
syntax dispatches and reserves frames plus finite input/output copies. The raw
arena budget includes both case arms conservatively, while actual execution
allocates and dispatches only the selected arm. F's derived maximum is 18 dispatches and 133 arena units.
`Rich.Executes` follows the actual compiled code; `regional_execution` connects
its output to the independent F equation. Circuit leaves reuse existing work,
arena and execution derivations.

Encoding charges read, complement and pair-copy operations. Decoding charges
complement, equality, branch and projection-copy operations. Serial assembly
charges a frame dispatch and copying the left output. The checkpoint schedule
reserves the boundary buffer before evaluating the left region, reclaims the left
arena after copying, retains the intermediate during the right region, and counts
both outputs when they coexist. Parallel assembly also retains the right input
while the left region executes; it uses a left-first schedule. All delayed states remain counted throughout.
Adapters retain no state between ticks. Shared-input duplication charges six
payload-cell copies; its frame, source and destination cells occupy ten units.

[RegionalSpace](../../Applications/FRP/RegionalSpace.lean) connects those budgets
to execution. `Rich.Allocates` records each entered node's frame and typed
input/output copies, composes actual intermediate values, and selects the actual
case arm. `Allocates.result` identifies its output with the raw interpreter;
`allocations_le` bounds that execution's allocation sum by the static raw arena.
`occupancies` includes every allocation-prefix total before reclamation.

`Plan.SpaceRuns` composes those raw derivations and the existing circuit
allocation traces in executor order. Its serial and parallel constructors expose
buffer reservation, arena release, retained intermediate values and the parallel
right input. `SpaceRuns.result` identifies the whole transition with the actual
selected executor. `live_dominated` relates every actual occupancy to a static
checkpoint, and `live_bound` adds all retained states. `sufficient_storage` thus
constructs a space execution fitting the admitted capacity, rather than bounding
an unrelated numerical list. A checked counterexample observes the enclosing
capacity failure in the actual execution trace. This is a copied-value arena model,
not a theorem about Lean's host allocator, serialized bytes or elapsed time.
Code and proof data are fixed configuration. Histories and logical times occur
only in specifications or the finite test driver, never in executable plan state.
The runner exposes neither queues nor pending external effects.

`Operational` composes actual leaf work derivations in executor order. `scheduled`
constructs a round from this evidence, the work inequality and the corresponding
`SpaceRuns` derivation. The round reserves
the maximum work budget, allowing unused budget as idle time. Finite input,
scheduler and sink waits are explicit environmental premises. `bounded_service`
combines these rounds with a bound on their actual live traces for arbitrarily
long service. It
makes no progress promise when those environmental waits are unbounded.
`circuit_recovery` invokes the unchanged finite-circuit productive-service theorem.

Checked counterexamples show that two individually fitting leaves fail after
boundary storage is included, and that a cheaper bare negation gate loses its
work advantage after redundant encoding, validation and copies. No performance
win or optimal placement is claimed.

## Validation and continuation

[Examples](../../Examples/RegionalPlans.lean) retain both sum branches, unequal
right payloads, live-state continuation, independent parallel order, shared input,
query inertness, reset and negation-movement failures, malformed redundant values,
capacity rejection, cost reversal and growing state. The process-level
[test](../../scripts/test-regional-plans.py) compares 9,330 executions against an
independent Python oracle: three cuts, both Boolean continuation seeds, and all
words over six inputs through length four. It also checks parallel output order,
all four raw boundary pairs and admission outcomes. Its finite driver is not an
indefinite IO service or a claim about buffered host input size.

#486 owns runtime policy selection after whole-plan admission; it can reuse
#436's choice contracts without evaluating effectful alternatives speculatively.
#487 owns live split/fuse and continuation transfer. #480 still owns pending-work
publication/acknowledgment decisions. #483 and #484 own richer specialization
and resource trials. #488 owns an external artifact target and its ABI/toolchain
trust contract. None is silently implemented by the local Bool adapter.

Broader source traversal, extensible region packages and inferred requirements
remain follow-up design work under #235/#481's coordinated trials. This delivery
adds no mandatory IR, global capability ontology, backend ranking policy or new
trust axiom.
