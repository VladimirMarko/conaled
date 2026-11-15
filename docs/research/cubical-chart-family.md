# Finite-label cubical chart families

[Issue #565](https://github.com/VladimirMarko/conaled/issues/565) constructs the
native semantic consumer requested in the preserved
[Myers checkpoint 129 report](../history/orbifold/agda-checkpoints/checkpoint-129/conaled.md),
under “Larger contexts containing codes”. The implementation is
`SquareKit/Internal/Cubical/ChartFamily.lean`, with checked clients in
`Examples/CubicalChartFamily.lean`.

## Inputs and output

For `Ξ : Context.{u+1}`, `Count Ξ` is a natural-number section with an explicit
`ULift` into the context universe. `labels n` reuses `discreteFamily` and
`discreteFilling` with fiber `ULift (Fin n)`. Its small presentation has fiber
`ULift.{u} (Fin n)` and the equivalence removes one lift and inserts the other.
`labelCode` returns an actual code, decoding isomorphism and lawful selected
filler through #529's `LargeConstructors.construct`. Zero counts remain empty.
The label context `Λ` is the total native finite family. Its projection is
explicit; `labelContextIso` retains both maps and inverse laws relating it to
the decoded label-code context.
No small-context replacement of `Ξ` occurs.

`Inputs` takes code maps `Y : Ξ → U` and `D : Λ → U`, a target section over
the D extension, and an endpoint section of decoded Y. `display` is the
composition of the D and label projections. `weakenedEndpoint` pulls the
endpoint along that exact display. `paths`, `inner` and `outer` are respectively

```
Path_(Y γ)(s(γ,i,d), e(γ))
Σ d : D(γ,i), Path_(Y γ)(s(γ,i,d), e(γ))
Σ i : Fin(n γ), Σ d : D(γ,i), Path_(Y γ)(s(γ,i,d), e(γ)).
```

`pathResult` applies `LargeConstructors.path` to the actual weakened Y code.
`innerResult` and `outerResult` use its small-presentation construction with
the existing native Σ and Path providers. Their codes, decoder isomorphisms,
selected fillers and law proofs are outputs. Each Σ filler first fills its
first component, then fills the second over the display formed with that
actual first filler. `genericEndpoint` extends by decoded Y and uses its
actual generic variable for e.

## Selected operations and substitution

`path_selected`, `inner_selected` and `outer_selected` identify the entire
returned `Result.filling` after transport through the decoder. The inner
provider uses the selected native Path algorithm. These are equalities of
filling records, including every box, face and dependent display.

The stock nested-code route is also exposed: `encodedInner` applies
`LargeConstructors.sigma D pathResult.code`. `encodedInnerDecoding` composes its
decoder with the second-component Path decoder. `encodedInner_selected`
retains the precise operation on that route: its second provider is
`NativeDecode.filling pathResult.code`, transported through the Path decoder.
It is not asserted equal to `pathResult.filling` or to `innerResult.filling`.
This distinction implements the #529 originator clarification without erasing
the selected operation.

`substitute` independently rebuilds all inputs, with `labelLift` and
`domainLift` retaining the dependent display maps. `innerComparison` and
`outerComparison` compare the pulled-back decoded code with reconstruction
from those inputs. Their filling theorems preserve the complete returned
constructor fillers. The intervening comparisons use `pathReindexIso`,
`sigmaSecondIso`, `pathFilling_reindex_iso` and
`sigmaFilling_transport_second`. They do not assert equality of code maps.
The laws apply to arbitrary substitutions, including composites.

## Checked cases and statement review

The concrete client keeps the earlier genuinely large context containing a
universe-code parameter. Its actual base count gives Fin(0), Fin(1) and Fin(2)
fibers. `zero_labels` and `zero_charts` reject decoded inhabitants at zero;
`varying_labels` separates the one- and two-label fibers by cardinality.
D reuses the earlier varying Fin(n+1) code. `positive` constructs a decoded
chart section after successor substitution; `positive_label` recovers its
selected label. `empty_domain` rejects the returned outer code for empty D.
`incompatible_endpoints` rejects charts with discrete natural target 0 and
endpoint 1 after successor substitution, where the positive 0/0 client
has a section. The rejection therefore does not rely on zero labels.

Successor and doubling are proved nonidentity in the retained #529 client.
The new checked clients instantiate both and their composite, observe counts
3, 4 and 5 at base count 2, and compare each original decoded construction to
an independent rebuild, preserving its selected filler. `fullEquivalence`
retains the actual map and homotopy-equivalence record of the composite
comparison.

`genericData` uses two independent universe-code parameters, a generic function
from decoded D to decoded Y supplying the target section, and the actual
generic Y variable as endpoint after context extension. `genericCharts` and
`genericStockInner` exercise both constructor routes on those inputs.

Statement review checks that no conclusion code, equivalence or preservation
law is an input; the count may be zero; both dependent display projections
are retained; and the endpoint is a section of the same weakened decoded Y
as the target. Family isomorphism, equality of semantic terms, equality of
selected filling records and native Path remain distinct. No proposition-valued
specialization is claimed.

## Source boundary

The checkpoint archive and report retain SHA-256 values
`947dac685ec31c14bd357a9eedc3cdf4c32a8dc5c61310aa3b3b9986088b3d12`
and `cc24988b13dd8f5017dede90806b64c8c9eb76426e2a922700673296305baf68`.
The baseline for this work is accepted #529 commit
`de152de88298762dcf8484578e7cf309d61f5620`, which supplies the larger-context
constructors absent from the checkpoint's reviewed commit
`08dbb2a71c8c9236ef2a1283e66f17b5622c3b9e`.

This correspondence covers the requested native chart-family formula, its
code construction and substitution. It does not interpret ordinary Agda
identity/J, classify Myers Dedekind sheaf families, prove source judgmental
conversion, or construct a smooth/cohesive model. The checkpoint's external
checking receipts are attributed evidence, not an Agda replay here. #422
continues to own unchanged-source admission and conversion. No resizing or
cumulative-universe claim follows.

In the archived `myers/src/Orbifolds/Intensional/FiniteBranchAtlas.agda`,
`BranchArrows` (lines 40–45) is the outer finite Σ with an inner domain Σ and
ordinary identity to the endpoint. `chart-subfinite-witness` (lines 58–65)
uses that inner predicate with separate `domain-prop` and `isSet Y`
hypotheses. Here `outer` has the corresponding Σ shape with native cubical
Path; neither those proposition hypotheses nor the subfiniteness conclusion
are inferred. This is a formula correspondence, not a translation theorem
between Agda identity and native Path.
