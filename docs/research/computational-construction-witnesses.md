# Computational construction witnesses (#456)

The separate computational layer now covers the active product, squared,
monoid, comma, arrow, identity and subcategory constructions at Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. It reuses #455's witness laws and
preservation interfaces and the established raw operations. Existing
Prop-valued APIs and quotient adapters are unchanged.

## Statement review and representation boundaries

Product relations retain two component witnesses. Squared relations instead
retain a target witness between the interpreted product arrows. Its unsquaring
map, middle-four product comparison and terminal comparison are the existing
raw constructions; their selected laws and induced-relation transport are now
computational. No injectivity of unsquaring is assumed.

Comma objects are the existing connector-bearing objects. Computational comma
arrows retain the target square witness as data. Their hom relation is a pair
of source-side relation witnesses; it imposes no equality between the square
witnesses. Category and Cartesian laws concern this relation. Target category
laws and interpretation preservation construct raw composition. Source laws
are required only for the resulting sidewise laws. The raw product connector
uses the accepted normalized formula; `product_connector_comparison` returns
a selected target witness relating it to Felix's conjugated tensor formula.
It does not assert equality of raw connectors or selected proof expressions.

Vertical pasting takes an explicit selected relation between interpreted middle
arrows. `verticalEq` recovers the source's equality premise using the supplied
reflexivity witness. Arrow specialization uses identity interpretations and
retains arbitrary middle-object equalities through `verticalAlong`. Transpose
applies the selected symmetry operation. Transposing twice preserves the two
side arrows, but equality of complete squares would require an extra law on
symmetry. A checked non-involutive model rejects that unintended strengthening.
Erasure recovers the existing transpose because its square proof is irrelevant.

Object reindexing imposes no injectivity on the object map. Its structural
comparisons may be nonidentity arrows. Morphism restriction retains the existing
Type-valued admissibility witness, independently of the induced relation
witness. Monoid relations retain their original witness types and operations;
no associativity, involution or uniqueness of witness operations is imposed.
Object, arrow, admissibility and relation universes remain independently
polymorphic. There are no new axioms, trust options or heartbeat limits.

Identity preservation and inverse/Cartesian comparison laws reuse #455 directly.
The active raw feedback constructions already retain Type-valued evidence in
`SelectedFeedback.product` and `SelectedFeedback.reindex`; no duplicate trace
interface is introduced. Their availability does not imply trace congruence
for arbitrary selections, which remains the explicit #451 boundary.

## Erasure and EDD evidence

`WitnessProduct.erase_relation` identifies the erased pair of witnesses with
the existing conjunction of erased component relations. Squared, object
reindexing, morphism restriction and monoid erasure have exact relation-package
recovery. Comma `eraseMap_laws` and `erase_relation` recover the accepted side
relation and category preservation; `erase_fst` and `erase_snd` commute with
projections as raw maps. The terminal, projection, pairing, composition,
identity, vertical and transpose erasure equations preserve the existing raw
arrows. None reconstructs a selected witness from an erased proposition.
All structural-law records additionally use #455's explicit `.erase` adapters.

Before these extensions, the retained #453 examples could distinguish raw
square witnesses but had no computational comma relation, Cartesian laws,
composed projection preservation or Squared induced-law consumer. These were
missing connections to public constructions, not failures of the intended
mathematics. `Examples.WitnessConstructions` now consumes those public results.
It computes unequal component witnesses through projections and their composite,
uses a relation between unequal squares, checks Arrow product laws and erased
recovery, exercises Squared transport, and transports product laws along a
noninjective object map with nonidentity comparisons. It also distinguishes
morphism-admissibility witnesses and computes raw monoid law witnesses.
The non-involutive transpose case records the counterexample discovered during
statement review. The examples' Bool witness relations are deliberately
operations-only models permitted by the source.

## Pinned declaration correspondence

Every indexed active locator in the following source modules has an entry.
Names without a namespace in a row continue the namespace explicitly named
in that row. `ProductMapLaws.felix`, identity and universal-property adapters
refer to `SquareKit.WitnessEquivalence`; raw constructors keep their established
`SquareKit` namespaces. The source's single-field arrow wrappers are represented
by their underlying arrows where no information would be lost.

### Construct/Product.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`Obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L18) | `O × Q` |
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L22) | `CategoryProduct.ops.Hom` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L27) | `CategoryProduct.ops` |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L30) | `CategoryProduct.terminal`, `products` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L33) | `CategoryProduct.terminal`, `products` |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L43) | existing `SelectedFeedback.product` (Type-valued WF pair) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L69) | `WitnessProduct.equiv` |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L81) | `WitnessProduct.congr`, `laws` |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L93) | `WitnessProduct.terminalLaws`, `productCongr`, `productUniversal` |
| [`Hₒ₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L132) | `CategoryProduct.fst.obj` |
| [`H₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L135) | `CategoryProduct.fst.map` |
| [`Hₒ₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L138) | `CategoryProduct.snd.obj` |
| [`H₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L141) | `CategoryProduct.snd.map` |
| [`catH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L144) | `WitnessProduct.fst_laws` |
| [`catH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L148) | `WitnessProduct.snd_laws` |
| [`pH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L152) | `CategoryProduct.fstTerminal`, `fstProducts` |
| [`spH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L155) | `WitnessProduct.fstTerminal_inverse`, `fstProducts_inverse` |
| [`pH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L164) | `CategoryProduct.sndTerminal`, `sndProducts` |
| [`spH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L167) | `WitnessProduct.sndTerminal_inverse`, `sndProducts_inverse` |
| [`cartesianH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L176) | `WitnessProduct.fstTerminal_laws`, `fstCartesian` |
| [`cartesianH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L187) | `WitnessProduct.sndTerminal_laws`, `sndCartesian` |

### Construct/Squared.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`unsquare`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L23) | `Squared.unsquare` |
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L32) | `Squared.unsquare.obj` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L36) | `Squared.unsquare.map` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L40) | `WitnessSquared.map_laws` |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L43) | `Squared.terminalMap`, `productMap` |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L46) | `WitnessSquared.terminalMap_inverse`, `productMap_inverse` |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L52) | `WitnessSquared.terminalMap_laws`, `productMap_laws`, then `ProductMapLaws.felix` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L61) | `WitnessSquared.induced` |
| [`catL`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L67) | `WitnessSquared.induced_congr`, `induced_laws` |

### Construct/Monoid.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`_⇒_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L15) | raw carrier as `SetoidMonoid.ops.Hom` |
| [`constructor mk⇒`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L16) | identity representation on raw carrier |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L26) | `SetoidMonoid.ops` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L31) | `WitnessMonoid.equiv` |
| [`lawful-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L34) | `WitnessMonoid.congr`, `laws` |

### Construct/Comma/Type.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`Obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L24) | `Comma.Obj` |
| [`constructor mkᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L25) | `Comma.Obj.mk` |
| [`{ τ₁ }`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L27) | `Comma.Obj.left` |
| [`{ τ₂ }`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L28) | `Comma.Obj.right` |
| [`h`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L29) | `Comma.Obj.connector` |
| [`_↬_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L34) | `WitnessComma.Hom` |
| [`constructor mkᵐ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L35) | `WitnessComma.Hom.mk` |
| [`f₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L37) | `WitnessComma.Hom.left` |
| [`f₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L38) | `WitnessComma.Hom.right` |
| [`↻`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L39) | `WitnessComma.Hom.commutes` |
| [`_⇉_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L45) | `WitnessComma.Hom` at explicit `Comma.Obj.mk` endpoints |
| [`Hₒ×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L56) | `WitnessComma.toProduct.obj` |
| [`H×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L59) | `WitnessComma.toProduct.map` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L62) | `WitnessComma.equiv` |
| [`Hₒ₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L66) | `WitnessComma.fst.obj` |
| [`H₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L69) | `WitnessComma.fst.map` |
| [`Hₒ₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L73) | `WitnessComma.snd.obj` |
| [`H₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L76) | `WitnessComma.snd.map` |

### Construct/Comma/Raw.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`id′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L47) | `WitnessComma.ident` |
| [`comp`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L66) | `WitnessComma.comp` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L73) | `WitnessComma.ops` |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L87) | `Comma.terminalObj`, `productObj`; connector comparison: `WitnessComma.product_connector_comparison` |
| [`!′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L107) | `WitnessComma.terminate` |
| [`fork`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L124) | `WitnessComma.fork` |
| [`exl′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L146) | `WitnessComma.first` |
| [`exr′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L166) | `WitnessComma.second` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L175) | `WitnessComma.terminalOps`, `productOps` |

### Construct/Comma/Homomorphism.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`categoryH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda#L32) | `WitnessComma.fst_laws` |
| [`categoryH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda#L36) | `WitnessComma.snd_laws` |

### Construct/Comma/Vertical.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`_◎_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Vertical.agda#L41) | `WitnessComma.verticalEq`; weaker selected middle relation: `vertical` |

### Construct/Arrow.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L20) | `RawMap.id.obj` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L23) | `RawMap.id.map` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L26) | `WitnessEquivalence.Preservation.id` |
| [`productsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L40) | `TerminalMap.id`, `ProductMap.id` |
| [`strongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L43) | `WitnessEquivalence.Comparison.id_laws` |
| [`cartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L46) | `WitnessEquivalence.TerminalMap.id_laws`, `CartesianH.id` |
| [`_ᵀ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L57) | `WitnessArrow.transpose` |
| [`composableᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L63) | middle-object equality argument of `WitnessArrow.compose` |
| [`_○_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L67) | `WitnessArrow.compose` (reuses `RawArrow.compose`) |
| [`vcomposable`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L72) | middle-arrow equality argument of `verticalEq`, dependent `HEq` argument of `verticalAlong` |
| [`_◎_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L78) | `WitnessArrow.verticalAlong`; fixed-endpoint `verticalEq`; semantic extension `vertical` |
| [`Id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L85) | `WitnessArrow.identityObj` (reuses `RawArrow.identityObj`) |
| [`idᵀ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L88) | `WitnessArrow.identityHom` |

### Instances/Identity.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L18) | `RawMap.id.obj` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L21) | `RawMap.id.map` |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L24) | `TerminalMap.id`, `ProductMap.id` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L36) | `WitnessEquivalence.Preservation.id` |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L39) | `WitnessEquivalence.Comparison.id_laws` |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L42) | `WitnessEquivalence.TerminalMap.id_laws`, `CartesianH.id` |

### Subcategory/Object.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L28) | `ObjectReindex.ops.Hom` |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L29) | identity representation on the original arrow |
| [`un`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L31) | `ObjectReindex.forget.map` |
| [`refl≈↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L35) | `WitnessEquivalence.refl` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L40) | `ObjectReindex.ops` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L43) | `ObjectReindex.terminal`, `products` |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L52) | `ObjectReindex.initial`, `coproducts` |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L61) | existing `SelectedFeedback.reindex` (Type-valued WF unchanged) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L69) | `ObjectReindex.forget` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L72) | `WitnessObjectReindex.equiv` |
| [`categoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L75) | `WitnessObjectReindex.forget_laws` |
| [`productsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L78) | `TerminalMap.id`, `ProductMap.id` on the reindexed raw operations |
| [`strongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L82) | `WitnessEquivalence.Comparison.id_laws (WitnessObjectReindex.laws F L)` |
| [`cartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L92) | `WitnessObjectReindex.terminal_preserves`, `products_preserve`, then `ProductMapLaws.felix` with selected inverse witnesses |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L104) | `WitnessObjectReindex.congr`, `laws` |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L107) | `WitnessObjectReindex.terminal_laws`, `product_congr`, `product_laws`, then `ProductLaws.universal` |

### Subcategory/Morphism.agda

| Pinned declaration | Computational counterpart |
|---|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L23) | `MorphismRestriction.Hom` |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L24) | `MorphismRestriction.Hom.mk` |
| [`f`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L26) | `MorphismRestriction.Hom.arrow` |
| [`sat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L27) | `MorphismRestriction.Hom.sat` |
| [`refl↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L30) | `WitnessEquivalence.refl` |
| [`identityʳ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L33) | `WitnessEquivalence.Laws.comp_id` |
| [`sym-identityˡ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L38) | selected `E.symm (L.id_comp _)` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L47) | `MorphismRestriction.forget` |
| [`eq`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L50) | `WitnessMorphismRestriction.equiv` |
| [`cat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L53) | `MorphismRestriction.ops` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L59) | `WitnessMorphismRestriction.forget_laws` |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L64) | `WitnessMorphismRestriction.congr`, `laws` |
| [`cart`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L69) | `MorphismRestriction.terminal`, `products` |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L77) | `WitnessMorphismRestriction.forget_terminal`, `forget_products`, then `ProductMapLaws.felix` |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L85) | `WitnessMorphismRestriction.terminalLaws`, `productCongr`, `productLaws`, then `ProductLaws.universal` |

`Construct/Comma.agda` only reexports its constituent modules. The source
Monoid wrapper's `un⇒` is represented by the identity on the raw carrier.
The source's commented Boolean/Logic structures and comma closed-preservation
proposal declare no active theorem. Their dispositions remain in the full
correspondence and source index; they are not claimed as selected-witness
implementations here. The general comma vertical proposal is implemented by
`WitnessComma.vertical`, with equality specialization retained. Identity-instance
and object-subcategory maintenance TODOs reuse the shared identity comparisons.

## Validation

The focused build of `Examples.WitnessConstructions` passed at default limits.
The public entrypoint imports that module, reaching every new construction.
Exact-candidate full build, exhaustive audit and independent Standards/Spec
review are recorded by the orchestration separately; this report does not
claim those gates before their receipts exist. This package alone does not
close #8.
