# Finite dependent witness retention

[#703](https://github.com/VladimirMarko/conaled/issues/703) implements the fixed
[dependent correspondence experiment](dependent-correspondence-experiment.md).
The public application is [FiniteDependentCorrespondence](../../Examples/FiniteDependentCorrespondence.lean);
its definitions and proofs are in the
[finite model](../../SquareKit/FiniteDependentCorrespondence.lean).

## Finite admission and recovery

The label fiber has one object, arrows `Q = ZMod 2`, and cells
`{r : ZMod 4 // m = n + π r}`, where `π` is reduction modulo two.
Vertical composition adds witnesses. Both whiskerings retain the witness,
and horizontal composition adds them. Equality transports have witness zero.
These operations satisfy the actual `Bicategory.Strict` interface. Fiber
arrows have strict inverses, and fiber cells form groupoids.

`finiteFamily` is a `TwoFamily.Family` over
`DoubleDelooping.Space (Multiplicative Q)`. Its constant fiber is the finite
bicategory. Its base-cell action has component `α`, with arrow naturality from
commutativity and `naturality₂` from witness retention and zero-label
transports. All family laws are proved interface fields. No recovery or
coherence conclusion is a premise.

`dependentCellEquiv` identifies
`{(α,r) // m = n + α + π r}` with the actual morphisms
`arrow m ⟶ arrow n` of the total hom-category `H`. Its two inverse laws retain
the fiber witness. `vertical_coordinates`, `inverse_coordinates`,
`horizontal_labels`, and the whiskering label laws refer to the public total
operations. `packetView_injective` shows that endpoints, base action, and
witness determine the entire endpoint/cell packet. `packet_boundary` derives
the boundary from the actual dependent fiber cell.

The selected parallel cells have `(α,r)=(1,1)` and `(1,3)` at endpoints zero.
They have observations 1 and 3. Their composites are `(0,2)`, which is not
identity, and `(0,0)`, which is identity. `no_reconstruction` proves that their
shared base coordinate cannot recover both observations. After interpretation,
`interpreted_no_reconstruction` retains both endpoints as well as that base
coordinate. `packet_zero_rejected` rules out any actual packet with equal
endpoints, base action one, and witness zero. This is a typing failure, separate
from the information loss between the two admitted parallel cells.

All selected object, arrow, and cell carriers are finite in `Type 0`.
`Finite H` and `Finite (p ⟶ q)` are derived from the complete equivalences;
the Boolean hom-category has the corresponding finite instances. The
classifier target of `TwoFamily` keeps its existing universe parameters.
No finiteness claim is made for that classifier.

## Comma presentations and interpretation

`J : Discrete Q ⥤ H` selects `arrow m`. `Boundary`, `Tail`, `Left`, and
`Right` are the actual Mathlib comma categories specified by #703. Their
normal forms retain `(m,n,c,k,l)`, with `c` the actual total cell, not a copied
observation. `reassociate` reuses `GroupoidCorrespondence.discreteEquivalence`
and the discrete-comma instance. Its unit and counit retain every coordinate.
`dimensional_bridge` identifies the stored boundary arrow of `H` with that
same dependent total 2-cell.

`interpretLeft` and `interpretRight` return complete endpoint/cell packets.
The first performs two actual right whiskerings, the second one whiskering
by the actual composite of the later arrows. `threefold` applies the existing
`TwoFamily.whisker_right_compose`, with the total category's associativity
equalities. It proves precisely the equality with both `eqToHom` endpoint
conversions. The corresponding functors target the discrete category of
packets; their source arrows are identities because the apices are discrete.
This does not make `H` discrete or truncate its parallel cells.

The checked applications use both witnesses with tails `(1,1)` and `(1,0)`.
The first whisker changes endpoints from zero to one. The cancelling tail
returns them to zero; the other leaves them at one. Both interpretations
retain base action one and witness 1 or 3. The right-route and represented
loss controls reuse the full comparison laws.

## Representation change

The `Boolean` namespace admits its own actual fiber and family. Its reduction
map is the label reduction followed by the inverse of `SecondIdentity.encode`,
viewed additively. Thus its boundary is the same equation expressed in Boolean
coordinates. The witness carrier remains `ZMod 4`. The two finite admissions
are kept local to this experiment; no higher correspondence framework is added.

`homRepresentation : Boolean.H ≌ H` maps the arrow and base-action coordinates
through that prescribed equivalence and retains the actual fiber witness.
`encode_compose`, `encode_whiskerRight`, and `encode_whiskerLeft` prove compatibility with the actual
total operations, displaying the endpoint conversions. `packetRepresentation`
then gives full packet recovery in both directions.

`mapLeft` and `mapRight` are independently defined using Mathlib `Comma.map`.
The right map uses the direct `mapTail` and its pointwise alignment; it is not
conjugated by reassociation. `representationComparison` gives the natural
comparison of the two routes. `mapLeft_recovery` and `mapRight_recovery`
recover whole comma objects. The two interpretation-square theorems and
`interpreted_reassociation_representation` connect these maps to the actual
whiskered packets. Their inverse-recovery theorems retain the whole original
packet. The selected represented applications check all four coordinates.

The delivered `CommaUniversal`, `CommaPullback`, and `CommaExactLawful`
contracts were inspected. This client uses Mathlib's cospan-changing maps and
#694's discrete equivalence helper. It does not need another fixed-cospan lift
or an arrow-category pullback proof. Neither ordinary comma universality nor
its arrow-category presentation supplies the family action or total
whiskering coherence proved here.

## Ordinary clients and limits

The application imports the existing
[ordinary correspondence clients](../../Examples/GroupoidCorrespondence.lean)
and checks the arbitrary discrete-cospan `discretePullback_encode` equation.
Those clients retain the actual chosen pullback, ordinary compositor, native
whole-selected-value recovery, and slice interpretation. Their noninjective
apex-map, non-left-exact forgetting, and failed truncation-preservation controls
remain under their original hypotheses. `SpanAction` still requires pullbacks;
`SpanInterpretation` requires preservation of the relevant pullbacks. #633's
ordinary coherence is unchanged.

The comma boundary is a 1-arrow of a hom-groupoid and hence a 2-cell of the
specified total bicategory. This is not a general higher correspondence
bicategory, a higher comma universal property, or an unbounded coherence result.
Equality of the retained cells does not add a third identity level.

## Validation and failed experiments

Focused development checks use the pinned Lean/Mathlib environment and default
Lean resource budgets. Direct rewriting through dependent cell labels initially
failed to construct well-typed motives; destructuring the subtype before the
arithmetic proof fixed those obligations. Coercions at `SingleObj` and total
hom boundaries required explicit types. These were encoding failures.

Two direct packet-equality proofs exceeded the default heartbeat budget.
Proving injectivity of the complete `packetView` and reusing the operation
formulas avoided that unfolding. No resource limit was raised, and neither
failure established a mathematical obstruction. Failed diagnostics and the
review handoff are retained outside the source diff in the task evidence.

Acceptance requires the integrated build and exhaustive axiom audit on the
immutable candidate, followed by independent Standards and Spec review.
The coordinator retains the exact candidate, receipts, logs, and review record.
