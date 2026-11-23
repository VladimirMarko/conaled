# Native lattice transport

Issue #621 consumes the total native structure-identity construction from #625
for the existing meet/join lattice specification. The direct entry point is
`Examples.LatticeTransportBridge`; the native consumer is
`Examples.NativeLatticeTransport`, with concrete cases in
`Examples.NativeLatticeTransportCases`.

## Mathematical contract

`orderIso_preserves` derives the independently defined algebraic preservation
relation from Mathlib's `OrderIso.map_inf` and `OrderIso.map_sup`.
`orderIso_transport` identifies transport of the entire law-bearing lattice model
with the target's independently supplied lattice model. This uses the existing
`latticeModel` bridge; it introduces no new lattice axioms or signature framework.

`OrderedPair X` stores two elements together with their order witness.
`solutionOrderEquiv` identifies this subtype with the admitted formula asserting
that the meet is its first argument. `solution_transport_direct` compares the
formula-based transport with the direct `OrderIso` route, including the dependent
proof field. The exact direct composition law and inverse recovery remain usable
without any cubical admission.

In each native model, `admission` constructs a small code for the lifted constant
carrier using an actual filling operation and its lawfulness proof. `carrierSet`
proves native sethood through the discrete decoder presentation. `laws` reconstructs
native witnesses of the existing lattice equations. `sourceObject` and
`targetObject` therefore inhabit the law-bearing total object family.

`structuredEquivalence` retains the decoder-conjugated carrier isomorphism, its
selected native equivalence witness and independent field preservation.
`rawPath` applies the actual selected-ua map from #625. `latticePath` extends that
whole path through the proposition-valued law fibers. Its projection recovers the
raw path by a native homotopy, and `rawPath_carrier` identifies the raw projection
with the selected carrier ua. The projection of the law-bearing path is not
asserted to be a strict equality. Whole-path and whole-equivalence recovery use
the public recovery homotopies from #625.

`movedFields_meet` and `movedFields_join` recover the target operations.
`movedWitness` uses the same carrier isomorphism and field action in the native
formula-solution recovery API. `readMovedWitness` retains the resulting order
witness; `native_direct` identifies that complete dependent value with direct
order-isomorphism transport. `movedWitness_recovery` recovers the complete native
solution, including its native law witness.

`latticeTransportedPoint` uses the actual universal decoder transport along the
carrier projection of `latticePath`. `carrierProjection` connects that projection
to `rawPath` by a native two-path. Evaluating the two-path, then using the selected
ua comparison, proves that discrete observation of each transported value agrees
with the supplied order isomorphism.

`pathOrderedPair` transports both values by that native map and reconstructs the
target order proof. `pathOrderedPair_direct` identifies the complete dependent
pair with direct transport; `pathSolution_moved` identifies its reconstructed
native formula solution with `movedWitness`, including the native law witness.
The discrete presentation's solution equivalence supplies full witness recovery.
The checked concrete clients and cross-model dependent comparison use this path
route. This bounded construction does not supply a general formula-family filler
or a computation rule for arbitrary path induction or arbitrary filling choices.
Native paths remain distinct from Lean equality and definitional conversion.

## Consumers and comparisons

The Boolean product lattice uses coordinate swap, which is nonidentity and
preserves both operations. Its ordered pair from `(false,false)` to `(true,false)`
moves to the pair from `(false,false)` to `(false,true)`. Complementing both
coordinates is a carrier bijection that fails meet preservation; both native
preservation families reject it.

The dual Boolean lattice checks a change of meet/join presentation. The
function/product bridge `OrderIso.finTwoArrowIso Bool` connects distinct carriers
of the four-element Boolean lattice. Each model admits both carriers and builds
its own native structure path. `tupleWitness_recovery` recovers the complete
ordered pair after transport from the function presentation to the product.

The geometric bridge uses #626's `GeometricMatroids.booleanFlats`, connecting
`Set (Fin 2)` with the flat lattice of its atom matroid. Issue #691 supplies the
concrete native consumer in `Examples.NativeGeometricLatticeTransport`. Both
models construct actual admissions, the law-bearing path and its projection,
whole-path recovery, and recovery of the complete selected equivalence. The
inclusion of the empty set into `{0}` transports to a strict pair of flats.
`inclusionWitness_eq` compares the complete dependent value with direct geometric
transport; `nativeSolution_recovery` recovers the entire source native solution.
`meet_recovery` and `join_recovery` retain the target operations. `models_inclusion`
compares the whole dependent observations across models.

The consumer uses the endpoint package described below. This does not supply an
internal powerset constructor or classification of arbitrary matroid structures.

`Comparison.models` is a natural isomorphism of the presented law-bearing model
families after restricting the original model to Cartesian cubes. Its recovery
law retains the complete host model. `Comparison.models_transport` proves that
the natural comparison commutes with complete presented-model transport.
`Comparison.ordered_transport` proves
agreement of the decoded dependent values produced by the two constructions.
These are proved cross-model observations; independently selected ua paths are
not identified. Broader comparison remains #688.

## Reuse, effort and remaining scope

The reused library supplies descriptor interpretation, field preservation,
small-family coding, native law semantics, total structure identity and recovery.
The application supplies the order-isomorphism bridge, concrete admissions and
observations. No new recursion or heartbeat allowance is introduced.

For this presented order witness, the direct route is shorter: it maps both
components and applies monotonicity. The native route additionally supplies an
internal law-bearing structure path, with exact selected-ua and recovery
contracts. That is a mathematical capability beyond the direct subtype map;
it is not evidence of lower authoring cost. There has been no independent
held-out author trial in this implementation. Any such trial must pin the
published interface and retain preparation cost separately from author effort.

#680 retains universe generalization of the law grammar; these consumers live
in its existing `Type 0` range. #687 retains coherence for independently selected
structured-equivalence composition/inversion. Existing direct and strict-carrier
laws do not establish that broader result. Further signature or higher-law
extensions require their own consumer and admission contract.

## Concrete geometric specialization and conversion cost

The direct declaration at commit `5b05aaa48f018d5e263776db633e033f371d1c66`
reproduces the problem from #621:

```lean
import Examples.NativeLatticeTransportCases
open SquareKit.Cubical.Presheaf
open Examples.NativeLatticeTransport.Presheaf
open Examples.LatticeTransportBridge
noncomputable def geometricPath {Γ : Context.{1}} :=
  admittedPath (Γ := Γ) flatsBridge
```

A `#check` of the same application succeeds quickly. The definition exceeds a
15-second process bound. An explicit result annotation does not remove the cost.
With a diagnostic 10,000-heartbeat limit and `trace.profiler`, Lean emits the
expected elaborated term and then reports a kernel deterministic timeout while
typechecking the declaration. Thus this reproduction reaches kernel conversion;
it is not a failure to find the lattice isomorphism or elaborate its application.
Separate declarations for admissions, the carrier map, moved fields, the complete
structured equivalence and raw path pass. The law-bearing path is the failing
step. Making admissions opaque did not resolve it. Earlier #621 probes also
encountered elaborator recursion and heartbeat limits for differently annotated
clients; those observations concern those probes, not this kernel diagnosis.

### Retained interface

`PathData A` contains two terms of `A` and their actual homogeneous path.
`PathData.ofPath` simply packages an existing path with its endpoints.
`latticePathData` applies it to the existing `latticePath`; the checked
`latticePathData_source`, `latticePathData_target` and `latticePathData_path`
equations retain both endpoints and the same whole path. No new mathematical
proof or equivalence selection is introduced. `equivalenceRecoveryData` and
`latticeProjectionData` package the existing selected-equivalence recovery and
law-bearing projection homotopies in the same way.

The geometric consumer first specializes this package to a named `transport`,
then accesses `transport.path`. Kernel checking can use the named package's
endpoints instead of repeatedly converting the expanded concrete result type.
Its `source_eq`, `target_eq` and `path_eq` instantiate the generic equations;
`selectedRecovery_target` retains the entire supplied structured equivalence.
The package stores native witnesses, not merely their existence.

The original direct interfaces remain unchanged. Merely changing `admittedPath`
to return the path projection of a generic package still reached the process
bound: retaining the specialized package at the consumer is the useful boundary.
Fully expanding concrete endpoints, or reproving their equations by reduction,
can reintroduce the cost. The retained client uses proved projection equations.
There is no blanket claim that all equivalent spellings now check cheaply.

### Bounded measurements

Measurements used the repository's pinned Lean 4.35.0 and dependencies, the normal
`direnv`/`lake env` environment, with recursion depth 512, 200,000 heartbeats and `Elab.async=true` unless
a row states otherwise. Each row is
one process observation, not a benchmark distribution or an exact minimum budget.
The process bound was 15 seconds. Successful checks used full kernel checking;
no kernel bypass or production transparency/resource override was used.

| Check | Result | Wall time | Peak RSS (KiB) |
|---|---|---:|---:|
| Baseline direct geometric definition, default budgets | Process timeout | 15.05 s | 4,256,516 |
| Same baseline definition, recursion depth 1024 | Process timeout | 15.05 s | 4,274,320 |
| Baseline swap, dual and function/product path controls together | Passed | 0.63 s | 2,204,148 |
| Geometric module with both models, recovery and dependent consumers, emitting an olean | Passed | 1.04 s | 2,254,920 |

The baseline is the #621 tree pinned above; the last row is the #691 module.
For the successful module check, run:

```sh
direnv exec . lake build Examples.NativeGeometricLatticeTransport
direnv exec . lake env lean -o /tmp/NativeGeometricLatticeTransport.olean \
  Examples/NativeGeometricLatticeTransport.lean
```

Timing used a Python `subprocess` invoking `timeout --kill-after=2s 15s lean ...`
inside `lake env`, recording monotonic elapsed time and `RUSAGE_CHILDREN` CPU/RSS.
The shared compiler lock serialized probes. RSS includes imported libraries; it
is not an allocation count. The diagnostic 10,000-heartbeat kernel failure took
4.12 seconds, while the initial endpoint-package probe passed at that same budget
in 0.75 seconds. Production declarations keep the existing finite defaults.

The result supports this small computational boundary, with shared proofs and
exact recovery, under the #636 policy. It does not establish a general Lean defect
or justify a global limit increase. An upstream report would need a smaller
independent reproducer. Authoring productivity remains unmeasured; #692 retains
the separate held-out trial.
