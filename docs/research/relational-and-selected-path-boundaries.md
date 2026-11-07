# Relational and selected-path semantic clients

[#348](https://github.com/VladimirMarko/conaled/issues/348) extends the client
boundary experiments with two separate contracts. A relational client may
observe a set of possibilities or a selected member with its relation witness.
A path client may observe its selected arrow and the arrow's action on a
dependent value. Neither contract is equality of raw representations.

## Existing machinery and the choice of boundary

[ADR 0002](../adr/0002-relations-and-synchronization.md) already distinguishes
many-valued interpretations from exact decoders. `Relational.RelSquare` supplies
forward preservation, and `witnessSquare` derives an exact square on total
relation witnesses. The FIFO [abstract client](abstract-fifo-client.md) derives
representation independence for admitted finite command words. These results
do not establish invariance of every arbitrary function on a raw carrier.

The earlier [exact boundary](semantic-client-boundaries.md) supplies that latter
guarantee for pure functions on quotient handles. Its equivalence is equality
of decoded *data*. It need not truncate selected parses or selected arrows:
those can be part of the data being decoded. But it cannot identify parallel
paths by mere existence and still recover a selected path's action.

[GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean) already
derives dependent transport preservation from naturality and composes/reindexes
routes. [GroupoidRoutes](../../Examples/GroupoidRoutes.lean) exercises genuine
monodromy and retains ineffective path labels. The current two-family model
also retains selected two-cells through source-context weakenings; it is not
limited to a first-identity model. This work reuses those proofs and adds
boundaries around the selected data, rather than redefining their semantics.

## Relational clients: possibilities and selection differ

The independent finite client has possible meanings `{false}`, `{false,true}`,
`{true}`, and the empty set. Its redundant representation adds a Boolean flag
that is absent from the meaning. A selected client first flips its chosen
Boolean and then widens the represented possibility set. The output selection
must be the flipped Boolean, independently of the flag or the replacement of
the direct representation by the redundant one.

[RelationalSemanticBoundary](../../SquareKit/RelationalSemanticBoundary.lean)
provides two opt-in specializations:

- `possibilities` decodes to the *entire* relation fiber, including empty and
  non-singleton fibers. `Handle` identifies exactly equal fibers. It neither
  chooses an element nor asserts totality of the original relation. Its
  `client_invariant` applies to every pure function of these handles.
- `Selected` uses the existing total witness representation and retains the
  selected semantic component. `selectedMap` needs only a `RelSquare`;
  `selectedMap_meaning` and `selectedMap_compose` derive the selected result and
  composition from the existing witness-square construction.

A possible-set operation needs its own contract. `PossibilityMap` is an
existing square between the full-set representations, so descent, meaning,
identity and composition follow from the existing exact-handle theorems. It
is not automatically supplied by a forward relational simulation. The checked
`no_possibility_descent` control has two source representations with the same
singleton meaning. A forward-preserving implementation chooses either that
singleton or a larger target set according to the raw flag. It preserves every
selected input meaning, yet cannot descend to equal full-set handles.

The [relational examples](../../Examples/RelationalSemanticBoundary.lean)
check local flip/widen preservation, the selected composite result, direct/
redundant replacement, forbidden flag observation, and distinct ambiguous
selections. They also check empty fibers, failure of a decoder preserving
*all* meanings, and nontransitivity of sharing some meaning. A decoder choosing
one meaning under additional hypotheses is a different contract; its general
impossibility is not claimed. Closing the sharing relation transitively would
identify the disjoint endpoint fibers and change the specified observation.

`graph_fibers_iff` and `graphEquiv` recover the exact boundary for graph
relations. This is an actual equivalence of handles, not only a resemblance of
notation. No arbitrary equivalence on a relation's raw carrier is assumed.

## Selected paths and dependent action

The independent path client is the existing C₄ action on a two-element family.
The generator sends 0 to 1. Label 2 acts trivially on this family but remains a
distinct path from label 0. These calculations specify both the dependent
output and information that a mere output-value observer would miss.

[SelectedPathBoundary](../../SquareKit/SelectedPathBoundary.lean) retains a
chosen arrow and source value as `Input B x y`. Its `transport` square returns
the same arrow together with its action on that value. Direct and flagged
realizations have the same meaning; the generic `replacement` theorem hides
only the flag. The semantic path remains data.

`routeInput` and `routeOutput` use the existing route's functor and natural
fiber map. `route_transport` derives their comparison from `Route.transport`,
and `route_compose` derives composite correctness from the existing composed
route. `substituted_transport` uses the existing reindexing comparison. No
whole-client preservation field is added. The [checked client](../../Examples/SelectedPathBoundary.lean)
uses two nonidentity routes and two nonidentity base substitutions. It retains
both selected label and dependent value, rejects an endpoint-only observer of
the action, and distinguishes labels even when their actions agree.

There is also a connection to the current higher model, rather than a claim
that the C₄ example alone exercises higher identity.
`SelectedTwoCellBoundary.source_witness_retained` uses the existing
`normalizedPathOperands_retained` theorem to connect the full normalized
selected two-cell of the original source context, after its two weakenings,
to the handle's meaning. The cell carries its integer value; handles for 0
and 1 remain distinct. This reuses a proved source comparison, rather than
assuming that comparison as a field of a new interface.

This is a bounded boundary around selected paths and selected cell data in the
current Lean models. It is **not** a quotient by existence of a path, a universal
higher quotient, or a construction of all higher coherence laws for arbitrary
representations. In particular, host equality of full cell data hides the
extra flag; it does not replace a required cell by a proposition asserting
that one exists. A representation comparison by a nontrivial higher cell,
instead of exact decoded equality, still needs its chosen coherent comparison
and a client language respecting it. #200/#235 retain that broader scope.

## Enforcement and architectural consequences

| Layer | Guarantee | Required evidence |
|---|---|---|
| Raw representation | No universal client invariance | Representation-aware compiler code has its own correctness contract. |
| Certified relational/path operation | The selected interpretation is preserved; composites inherit it | Local relation preservation or naturality, using existing composition. |
| Full-set or selected-data handle | Every pure total handle function respects the specified decoded equality | The quotient boundary; existing squares justify lifting operations. |
| Arbitrary higher-equivalence clients | Not supplied by these set-valued handles | Chosen higher comparisons, coherent action and an appropriate certified syntax or richer boundary. |

A certified client syntax is useful when operations preserve a relation but
no suitable exact observational equivalence has been supplied. Its induction
covers admitted terms, as the FIFO client already demonstrates. An abstract
module or parametricity argument could enforce another interface, but merely
making a Lean definition private is not such a proof. The new handle claims
are type-theoretic invariance for pure total functions, not security, timing
or effect noninterference guarantees.

The progressive design shares the existing exact boundary where its meaning
fits, and keeps the two relational capabilities separate. Selected-data
operations can use ordinary relational squares. Full-set observations add a
stronger comparison. Path-dependent clients add functorial action and
naturality; they do not require that two parallel paths be identified.

The setup cost is two small boundary modules and their concrete comparisons.
Providers reuse local square or route evidence. Consumers of a handle do not
repeat invariance proofs, while raw compiler code remains available. This is
an obligation comparison, not measured agent-productivity evidence. No
repository-wide migration or change to the existing square interface follows.

## Statement review and validation scope

The negative examples have inhabited, independently specified input types.
Nonfunctionality and non-totality are exercised separately. The forbidden
single decoder quantifies over every related meaning, not just a chosen one.
`no_possibility_descent` tests a real forward-preserving map, so it isolates the
missing full-fiber requirement. Graph recovery keeps exactly the old semantic
equality. The path comparison retains the arrow even when its action is not
faithful, and the higher-cell comparison uses the original source witness.

The focused cases are connected to the public boundary and route theorems.
They are included in `SquareApplications` and the exhaustive proof audit.
Existing parser decisions and two-family consumers remain unchanged and in
the same integrated verification scope. No external adequacy, runtime erasure
or universal higher-boundary theorem is claimed.
