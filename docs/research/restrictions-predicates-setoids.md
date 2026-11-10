# Restrictions, predicates and setoids (#452)

This report records R4 of [#8](https://github.com/VladimirMarko/conaled/issues/8),
implemented under [#452](https://github.com/VladimirMarko/conaled/issues/452).
The source pin is `6f36d28097db7ea5f5df3263db3e8be08f74e490`; the
[full declaration index](felix-full-correspondence-source-index.md) retains its
hashes, line links and inactive proposals. This addendum preserves that inventory.

## Contracts and statement review

`ObjectReindex.ops C F` uses precisely `C.Hom (F a) (F b)`. It requires no
injectivity or equations. Raw terminal/product and initial/coproduct choices
use independently supplied comparisons. They impose no inverse laws: projection
and copair directions use `hom`, while pairing and injection directions use
`inv`. Primitive preservation follows definitionally from the construction.
Category law recovery only needs the corresponding laws of `C`; product and
coproduct law recovery additionally uses the target congruence/law packages
and both comparison inverse equations. Terminal and initial recovery expose
strong comparison packages; their reused transport theorems identify which
inverse equation is actually consumed. No source law is assumed as a premise
of its own recovery.

The dependency-light [ObjectReindexBasic](../../SquareKit/ObjectReindexBasic.lean)
owns the raw construction. `SelectedFeedback.reindexed` remains a definitionally
equal abbreviation, so the existing #451 client keeps its behavior without
making reindexing depend on feedback. Mathlib `InducedCategory` uses a hom
wrapper; `toInduced/fromInduced` preserve operations and give both arrow round
trips for any object function. The object/hom/index universe levels are independent.

`MorphismRestriction.Hom` stores both the original arrow and `sat : M arrow`,
where `M arrow : Type w`. Category, terminal and product closure provide the
selected witnesses for their operations. `equiv` is pulled back through the
forgetful map and ignores those witnesses. It does not identify the raw records.
The source's `Categoryᴾ` and `Cartesianᴾ` obligations are recovered by
`CategoryClosure`, `TerminalClosure` and `ProductClosure`. The structural
comparisons of the forgetful map are identities, with explicit inverse and
preservation theorems.

`PredicateCategory.Obj.{u,w}` stores a carrier in `Type u` and predicates in
`Type w`. A morphism is a **total** function plus a witness transformation at
each input. Equivalence compares the entire underlying function, even on
inputs with an empty predicate. Witness transformations remain data; their
equality is not part of semantic equivalence. Products pair witnesses; sums
select the predicate of the selected branch. Terminal and initial predicates
use `PUnit` and `PEmpty`. The forgetful map preserves category, terminal,
product, initial and coproduct structure, with selected identity comparisons.

`SetoidCategory` specializes relation evidence to `Prop`, using Mathlib's
`Setoid` and `Sum.LiftRel`. Its arrows retain total congruent functions; its hom
relation is pointwise codomain relation. Composition uses arrow congruence in
addition to pointwise relation. Exponential objects are congruent functions
with the pointwise relation. Evaluation uses both function-relatedness and
argument congruence; currying proves both obligations separately. Both raw
distribution choices are implemented directly and their inverse equations are
proved. This is the proof-erased specialization requested by #452, not a
replacement for #453's computational relation witnesses. The unfinished
setoid trace in the source remains under #451's selected-feedback analysis.

## Declaration recovery

Each row names the concrete definition or theorem that implements the pinned
declaration. Namespace qualifications for each table are given above it;
shared interfaces retain their `SquareKit` qualification. Private source
reflexivity helpers use the existing equivalence interface. The source's
one-field object-reindexed arrow wrapper is omitted; its constructor and
projection become identity functions, rather than additional semantic data.

### Subcategory/Object.agda

Local namespace: `SquareKit.ObjectReindex`.

| Pinned declaration | Checked recovery |
|---|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L28) | `ops.Hom` |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L29) | `identity (wrapper omitted)` |
| [`un`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L31) | `forget.map` |
| [`refl≈↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L35) | `HomEquiv.refl` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L40) | `ops` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L43) | `terminal/products` |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L52) | `initial/coproducts` |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L61) | `SelectedFeedback.reindex (existing #451 client)` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L69) | `forget` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L72) | `equiv` |
| [`categoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L75) | `forget_laws` |
| [`productsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L78) | `TerminalMap.id/ProductMap.id on reindexed operations` |
| [`strongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L82) | `Comparison.id_laws with ObjectReindex.laws` |
| [`cartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L92) | `terminal_preserves/products_preserve` |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L104) | `laws` |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L107) | `terminal_laws/product_congr/product_laws` |
### Subcategory/Morphism.agda

Local namespace: `SquareKit.MorphismRestriction`.

| Pinned declaration | Checked recovery |
|---|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L23) | `Hom` |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L24) | `Hom.mk` |
| [`f`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L26) | `Hom.arrow` |
| [`sat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L27) | `Hom.sat` |
| [`refl↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L30) | `HomEquiv.refl` |
| [`identityʳ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L33) | `CategoryLaws.comp_id` |
| [`sym-identityˡ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L38) | `HomEquiv.symm (CategoryLaws.id_comp _)` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L47) | `forget` |
| [`eq`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L50) | `equiv` |
| [`cat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L53) | `ops/CategoryClosure` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L59) | `forget_laws` |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L64) | `congr/laws` |
| [`cart`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L69) | `terminal/products; TerminalClosure/ProductClosure` |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L77) | `forget_terminal/forget_products` |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L85) | `terminalLaws/productCongr/productLaws` |
### Instances/Pred.agda

Local namespace: `SquareKit.PredicateCategory`.

| Pinned declaration | Checked recovery |
|---|---|
| [`PRED`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L24) | `Obj` |
| [`constructor mkᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L25) | `Obj.mk` |
| [`{ty}`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L27) | `Obj.Carrier` |
| [`pred`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L28) | `Obj.pred` |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L32) | `terminal/products` |
| [`coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L35) | `initial/coproducts` |
| [`_⇒_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L42) | `Hom` |
| [`constructor mkᵐ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L43) | `Hom.mk` |
| [`{f}`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L45) | `Hom.toFun` |
| [`imp`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L46) | `Hom.imp` |
| [`rawCategory`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L53) | `ops` |
| [`rawCartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L59) | `terminal/products` |
| [`rawCocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L67) | `initial/coproducts` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L81) | `equiv` |
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L96) | `forget.obj` |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L99) | `forget.map` |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L102) | `forget_laws` |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L109) | `terminalComparison/productComparison` |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L114) | `terminalComparison_inverse/productComparison_inverse` |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L118) | `forget_terminal/forget_products` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L133) | `congr/laws` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L136) | `terminal_laws/product_congr/product_laws` |
### Instances/Setoids.agda

Local namespace: `SquareKit.SetoidCategory`.

| Pinned declaration | Checked recovery |
|---|---|
| [`Zoid`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L39) | `Obj` |
| [`_⟶_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L42) | `Hom` |
| [`A`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L47) | `polymorphic object parameter` |
| [`pattern tt`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L49) | `PUnit.unit` |
| [`pattern _⊨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L52) | `Hom.mk` |
| [`𝟘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L59) | `zero` |
| [`𝟙`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L69) | `unit` |
| [`absurd`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L74) | `initial.initial` |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L82) | `terminal/products` |
| [`coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L85) | `initial/coproducts` |
| [`exponentials`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L88) | `exponential` |
| [`rawCategory`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L96) | `ops` |
| [`rawCartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L102) | `terminal/products` |
| [`rawCocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L110) | `initial/coproducts` |
| [`rawCartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L118) | `closed` |
| [`rawDistributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L127) | `distribution/rightDistribution` |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L153) | `equiv` |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L166) | `congr/laws` |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L175) | `terminal_laws/product_congr/product_laws` |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L184) | `initial_laws/coproduct_congr/coproduct_laws` |
| [`cartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L193) | `closed_congr/closed_laws` |
| [`distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L201) | `distribution_laws/rightDistribution_laws` |

The object-reindexed coproduct law recovery is a local extension to the source's
raw coproduct construction. Predicate initial/coproduct laws and forgetful
preservation are also checked, beyond the source's final category/Cartesian
instances. The source's identity-comparison TODOs use the existing
`TerminalMap.id`, `ProductMap.id` and `Comparison.id_laws` interfaces.

## Comparison with existing presentations

[PredicateComparisons](../../SquareKit/PredicateComparisons.lean) provides three
explicit maps, each with `MapLaws`:

- `toRelation` sends a predicate to the relation between its carrier and `PUnit`
  defined by `Nonempty (pred x)`. It erases computational witness distinctions.
  The function and constant semantic projection form a `RelSquare`.
- `ofRelation` sends a binary relation to a predicate on the **pair** of its
  implementation and semantic carriers. Its witness is `PLift (Rel r s)` and
  its underlying function retains both horizontal maps. It is not an inverse
  to `toRelation`.
- `ofAssembly` sends an assembly element to the predicate `PLift (∃ n, realizes n x)`.
  For an assembly morphism, its existential tracking proof establishes that an
  input's realizer existence implies output realizer existence. It does not
  select or retain a tracker. `assembly_lift_requires_computable` records the
  additional obligation for recovering an assembly map on natural numbers;
  an arbitrary predicate morphism supplies no recursive tracker.

These maps preserve the original `RelationalCategory` and `Assembly.Hom` APIs.
Neither is identified with the witness-transforming PRED representation.

## Checked cases and validation

The cases are imported through `SquareApplications`:

- [Examples.ObjectReindex](../../Examples/ObjectReindex.lean) uses tagged types
  with a noninjective carrier map, product swaps and sum swaps as nonidentity
  comparisons, and terminal/initial recovery. `projection_recovers` and the
  coproduct law package consume the generic law-transport results. The two
  `bad_*_law_rejected` theorems exhibit raw comparisons that yield operations
  but violate product or coproduct laws. This distinguishes operation formation
  from semantic law recovery. The selected-feedback alias is checked directly
  and the existing selected-feedback consumer is rebuilt.
- [Examples.MorphismRestriction](../../Examples/MorphismRestriction.lean) keeps
  two Boolean witnesses for `Nat.succ`. They yield distinct raw arrows and
  equal semantics. Its product witness calculation violates raw witness equality
  while `product_semantic_recovery` follows the generic product-law theorem.
- [Examples.PredicatesAndSetoids](../../Examples/PredicatesAndSetoids.lean) rejects
  equating distinct constant functions on an empty predicate, retains distinct
  witness transformations with identical function semantics, and instantiates
  independent carrier/predicate universes. Predicate products transform witnesses
  componentwise. The relation and assembly consumers use the explicit maps.
  The parity setoid relates identity with addition by two while their functions
  are unequal. Products, sums, currying and both distribution equations consume
  the public law packages on that nontrivial setoid.

The initially missing connections were comparison-based raw reindexing,
Type-valued PRED witnesses with total functions, and a reusable congruent-function
setoid instance. The checked cases now instantiate those APIs. Statement review
checked universes, totality on empty predicates, direction of each comparison,
which witnesses are retained or erased, and the distinction between raw arrow
equality and semantic equivalence. Closure and congruence hypotheses are supplied
by the consumers; no empty hypothesis package stands in for the intended models.

Focused validation uses `lake build Examples.ObjectReindex
Examples.PredicatesAndSetoids Examples.MorphismRestriction Examples.SelectedFeedback`
inside direnv. Full isolated candidate validation, exhaustive proof audit and
independent Standards/Spec review remain acceptance steps; this report does not
claim their result in advance. This package does not close #8, whose remaining
scope retains its other issue owners.
