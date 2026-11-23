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

The direct geometric bridge uses #626's `GeometricMatroids.booleanFlats`,
connecting `Set (Fin 2)` with the flat lattice of its atom matroid. The inclusion
of the empty set into `{0}` transports to a strict pair of flats. Its concrete
native path is not part of the delivered checked cases: specialization exposed
a conversion-cost problem described below. The generic adapter's statement
retains arbitrary `Type 0` lattices, but a practical checked specialization of
that concrete path remains follow-up work. No internal powerset constructor or
classification of arbitrary matroid structures is claimed.

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

## Concrete geometric specialization cost

The generic adapters and the Boolean, dual and function/product consumers check
at default resource settings. Separate diagnostic probes admitted the geometric
source and target carriers and constructed both endpoint objects. Applying the
native path adapter to those concrete admissions caused extensive reduction of
representable classification, decoding and family expressions. An explicitly
typed probe reached the default recursion guard; local depth 1024 then reached
200,000 heartbeats, and a 400,000-heartbeat diagnostic probe also timed out.
Neither factoring a generic admission wrapper nor separating the consumer into
an importing module removed the observed problem. These probes establish a
local specialization-cost issue, not a mathematical obstruction or a general
Lean limitation. No experimental budget or transparency override is retained.

The follow-up should retain this exact geometric consumer, compare explicit
argument/type boundaries and decoder-normalization contracts, measure bounded
local budgets, and keep the completed Boolean/function consumers as controls.
It must preserve full paths and supplied equivalence data. The direct geometric
transport remains available during that investigation.
