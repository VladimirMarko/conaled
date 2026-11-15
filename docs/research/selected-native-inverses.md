# Selected inverses for native family equivalences

[Issue #554](https://github.com/VladimirMarko/conaled/issues/554) adds
`HomotopyEquivalence.selectedInverse` for a map `f : A ⟶ B`
over an arbitrary cubical context. At each generalized point `b`, the map
projects the first component of the center supplied by `E.fibers`. It retains
that choice even when constructing a genuine equivalence witness for the
inverse. Neither family needs a universe code.

The implementation is in
[SelectedInverse.lean](../../SquareKit/Internal/Cubical/SelectedInverse.lean),
with the checked consumer in
[CubicalSelectedInverse.lean](../../Examples/CubicalSelectedInverse.lean).

## Inputs and recovered paths

`selectedInverse`, `selectedRight`, and `selectedLeft` require only
`E : HomotopyEquivalence f`. The right recovery path is the path component of
the supplied fiber center. The left recovery path projects the supplied fiber
contraction at `(a, refl)`. These are native paths, with orientations
`f (g b) → b` and `g (f a) → a`. They do not assert host equality of their
endpoints.

`selectedInverseEquivalence E FA hFA FB hFB` additionally requires chosen
fillers for both families and proofs of their `Filling.Lawful` laws. Its result
is `HomotopyEquivalence E.selectedInverse`, including a chosen center and a
native contraction of every generic inverse fiber. No triangle equation,
filler regularity, discreteness instance, or isomorphism is an input.

The implementation reuses these existing interfaces:

| Existing interface | Use |
| --- | --- |
| `HomotopyEquivalence.fibers`, `genericFiberPath` | Original centers, contractions, and center paths |
| `discreteInverse` | Center projection, whose definition itself needs no discreteness |
| `pathLam`, `pathApp`, `homogeneousReverse`, `homogeneousConcat` | Native path construction and composition |
| `Glue.filling`, `Glue.fullFaceIso` | A filled line between arbitrary families |
| `IntervalTransport.equivalence` | Genuine equivalence of endpoint transport |
| `HomotopyContractible.retract` | Transfer of a supplied contraction using a native recovery path |
| `genericFiberReindexIso`, `pathReindexIso`, `HomotopyEquivalence.reindex` | Explicit substitution presentations |

## Constructing inverse fibers

`NativeEquivalenceLine` forms the Glue line with ambient family `B`, face
family `A`, and face map `f` at the zero endpoint. Its endpoints are explicitly
isomorphic to `A` and `B`. Reversing this line supplies an auxiliary map from
`B` to `A`, a genuine equivalence witness, and a native right recovery path.
This construction uses `Glue.filling` for the given native families directly.

`selectedComparison` projects the original fiber contraction to compare that
auxiliary map with the original center-selected inverse. `ofMapHomotopy`
transfers the auxiliary equivalence across this comparison. It fills the
family of fibers along the map homotopy, obtains an endpoint equivalence,
and uses its selected inverse and right recovery path in
`HomotopyContractible.retract`. Thus the auxiliary map supplies the inverse
fiber witness without replacing the map selected by `E`.

The reusable `ofMapHomotopy` API accepts maps `f` and `g`, a native homotopy
`f → g`, lawful fillers of their common source and target, and a genuine
equivalence witness for `f`. It returns a genuine equivalence witness for `g`.

## Substitution and presentations

`SelectedInverseSubstitution` compares the recomputed selected map and both
recovery paths with their substitutions. Native path comparisons use `HEq`
where their endpoint expressions differ in presentation; they compare the
whole path, including its interior.

`SelectedIntervalTransportSubstitution` proves that chosen interval transport
and its complete contractible-fiber witness commute with family isomorphisms.
The proof follows the actual filling operations used to construct fiber
extensions. It also proves substitution and family-isomorphism transport for
`HomotopyContractible.retract` and for the concatenation used in its
contractions. `SelectedEquivalenceIsoSubstitution` supplies full-record laws
for reindexing and composing endpoint presentation isomorphisms.

`SelectedMapHomotopySubstitution` proves
`HomotopyEquivalence.ofMapHomotopy_reindex`. This states equality
of the recomputed full equivalence record after substitution, using the
reindexed input witness, homotopy, and chosen fillers.
`selectedInverseEquivalence_reindex` then compares the entire chosen inverse
equivalence record with recomputation from the reindexed original witness
and fillers. The Glue auxiliary construction tracks the complete witness
and native recovery path through its endpoint and family presentations.
These statements concern the specified choices of
fillers; they do not identify results obtained from unrelated filler choices.

All constructions work over arbitrary contexts of the existing cubical
presheaf model. They use its interval reversal, connections, faces, and
additional interval coordinates. There is no added bound on cube dimension.
No path is converted to host equality in the generic construction.

## Glue consumer and controls

`Examples.CubicalSelectedInverse` applies the construction to the actual
`Glue.unglueEquivalence` witness. Its `recover` map is the selected inverse
of unglue. `recoverLeft` and `recoverRight` retain both native recovery paths;
`recoverEquivalence` uses the lawful Glue filler to construct genuine fibers
for this exact recovery map.

The face map flips Booleans. `recovered_face` proves that every face readout,
including a face reached after restricting a generalized point, is the
opposite Boolean from the ambient input. `proper_face_recovers_false`
specializes to an inhabited proper interval face with ambient `true` and
recovered face `false`. `recovered_whole` proves equality of the entire glued
element after unglue and recovery, using ambient and all face observations.
The Boolean family's discreteness justifies host equality in these consumer
observations.

A direct reconstruction would require choosing a compatible Glue element,
proving naturality of its face assignment, checking compatibility with the
ambient value, and constructing recovery witnesses. Here the map and both
native witnesses come from the supplied unglue fiber data. The consumer only
proves its Boolean observations and supplies the existing lawful fillers.

`selected_ofIso` checks that an ordinary isomorphism selects its supplied
inverse. The interval-to-unit control has genuine contractible native fibers
but is not a categorical isomorphism: its two distinct endpoints have the
same image. It instantiates the selected map and both native recovery paths.
This control does not claim a lawful interval filler or instantiate the
inverse-fiber construction for that interval. The Glue consumer exercises the
full inverse-fiber construction with lawful fillers.

Existing universe-selected inverse clients remain available. This extension
does not compare their chosen full witnesses with these witnesses, assert
triple coherence or pentagons, or add universe constructor admission.

An earlier construction developed `piFilling_transport_second` and
`contrFilling_reindex` helpers. Their development source is preserved in the
[#529 follow-up](https://github.com/VladimirMarko/conaled/issues/529#issuecomment-6893323711)
for possible reuse in arbitrary-context constructor work. Those earlier
helpers are not integrated APIs of this change and have not received its
independent review; reuse requires porting and revalidation. The interval,
path, retract, and presentation laws described above are integrated here.
