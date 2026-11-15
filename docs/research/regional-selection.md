# Selecting two regional execution sites

Issue [#486](https://github.com/VladimirMarko/conaled/issues/486) extends the
[regional plans](regional-reactive-plans.md) with session-boundary selection.
Each of two sites offers fused, split and checked cuts of the same F/D/N
machine. Their enclosing `Plan.par` is an actual executable composition, giving
nine constructed candidates. Its tick runs the left side before the right;
this is not a claim of simultaneous host execution.

`Sites.continuation` relates every candidate and every supplied current state
to an independent pair of native machines. Each native side emits the complement
of its previous Boolean state and retains the current rich-input result.
The relation preserves the output list and final logical state on every finite
suffix. The frozen worked case starts from `(false,false)` and produces
`[(true,true),(false,true),(true,false)]`, ending at `(false,true)`.

## Admission and evidence

`eligible` checks the enclosing plan's supported boundary protocol, ordering,
finite-wait declaration, analysis availability and storage bound before scoring.
Typed construction prevents a missing conversion from becoming a valid plan.
The existing admission interface reports incompatible ports and unsupported
native analysis separately. A checked separating example shows that the two
fused leaves each fit a capacity at which their enclosing product does not.
The split/checked order requires 144 cells, while checked/split requires 147;
a capacity of 145 accepts only the former. The existing conversion counterexample also remains in the checked examples:
a cheaper Boolean gate loses after redundant encoding, checking and copying.

`select` reuses `Choice.choose`. `selected_execution` transports admission to an
actual `Plan.SpaceRuns` witness, bounded at every live checkpoint. The resource
model counts payload cells, frames and copies under the declared schedule.
It does not bound Lean's heap or external queues. `selected_continuation` lifts
the native observation contract through `choose_contract`.

Evidence identifies implementation, target, workload, the two sites and their
F/D/N program, boundary protocol, requirements and the admitted catalog.
A complete epoch supplies one successful sample per admitted candidate.
Mismatched or incomplete epochs return the entire catalog to the fixed work
score. They do not mix nanoseconds with modeled work or bypass admission.
The tests use explicitly synthetic epochs to force different choices; those
values are not reported as performance measurements.

`Certificate` retains the concrete plan, requirements, state interpretation
and native observation theorem in its indices. Ranking cannot change this
association. This is the local coordination point for #489/#490, not an
implementation of their author-facing proof frontend.

## Installation, continuation and costs

`Session` pairs a selected site configuration with that configuration's state.
A new epoch can select a different configuration for a new session. It cannot
cast the current session's state. Runtime tests continue an old checked session
after a newer epoch selects split cuts. Active migration remains #487's scope.
An independent stateless preprocessing example may choose on each invocation.

The instrumented installation path executes candidate filtering, short-circuit
epoch validation, duplicate/missing-sample scans, sample-total extraction and
recursive minimum selection. The operation log comes from those traversals. Fallbacks retain the failed
primary bill and run the same admission checks before preparing a supplied plan.
Value-erasure theorems connect their results to `Epoch.complete`,
`Thinning.argmin` and the public `Choice.choose` result. Primitive comparisons
and plan-analysis operations use explicit logical tariffs, with payload sizes
recorded. These tariffs are a declared model, not a claim about Lean instruction
counts. Validation charges depend on the evidence actually examined, including
rejected epochs; there is no constant-price epoch assumption.

Installation and preparation are separate from ticks. A tick records actual
`Plan.stepWork` plus two observed output cells. Adapter validation and boundary
copy work already occur inside the regional execution charge. The [recorded observations](regional-selection-measurements.json) include
modeled per-plan work, storage and three-tick execution bills. The public test
runner reports fixed, selected and direct native observations for the same
fixture, with preparation and execution timings in separate columns. Each timing is one diagnostic sample, not a statistical comparison. Host
timing observes the current Lean toolchain; no speedup or global optimum is
claimed. Selection itself executes no unchosen candidate. Producing measured
evidence requires a separately requested bounded experiment.

## Validation entry points

- `Examples/RegionalSelection.lean`: independent native fixtures, arbitrary-state
  theorem specializations and separating admission/cost cases.
- `scripts/regional-selection-main.lean`: continued executions, epoch changes,
  stale contexts, fallbacks and separately reported timing observations.
- `scripts/test-regional-selection.py`: independent native-state oracle for
  1,296 continued runs and 17 public admission/evidence checks.

The normal integrated build and exhaustive proof audit include these modules
through `SquareApplications.lean`. The orchestration handoff records the exact
accepted candidate and its validation; focused author checks alone do not
constitute that acceptance.
