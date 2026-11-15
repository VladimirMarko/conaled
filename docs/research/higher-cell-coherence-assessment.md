# Faithful observations in higher coherence proofs

For #336, retain the native reflection proofs for the original path contraction.
Two later constructions justify bounded shared helpers: substitution data
normalization and reconstruction of a rooted contraction from a coherent image.
The latter now uses `TwoStrongReflect` and `TwoFamilyReindexStrong`. The earlier
recommendation to defer a new coherence API applied to the original three
normalization proofs; it does not describe this additional consumer.

The checked rooted contraction has whole-transformation reflexive normalization
and substitution laws. The arbitrary finite-tail construction also has beta and
substitution laws. The frozen-memo adoption gate still requires its specified
source interpretation and clients, together with final candidate acceptance.

## Existing consumers and caller obligations

`TwoFamilyPathFaithful.pathFirst_cell_injective` proves that first projection
reflects equations between parallel cells in the actual path context. Its proof
uses the base cell, first endpoint cell, and the path-action equation to recover
the second endpoint cell. The discrete fiber proof is used only after those
actual cells have been recovered. There is no assumption that an arbitrary
projection is faithful and no replacement of higher cells by equality proofs.

The three contraction consumers have different normalization obligations:

| Consumer | Reflection | Remaining work after reflection |
|---|---|---|
| `contractionNaturality_id` | One application of `pathFirst_cell_injective` | Normalize mapped unit comparisons, unitors, whiskering of equality boundaries, and the observed contraction cell. |
| `contractionNaturality_comp` | The same application | Normalize mapped composition comparisons, associators, both whiskering directions, and the observed contraction cells. |
| `contractionNaturality_naturality` | The same application | Normalize whiskering comparisons, retain the arbitrary observed 2-cell, and use `pathFirst_reflexivity_cell_heq` plus identity-whiskering boundary comparisons. |

The unit and composition proofs each have one normalization block. The cell
naturality proof needs two identity-whiskering lemmas and the exact reflexivity
retraction on cells. Those lemmas express its particular dependent endpoints;
they cannot be removed by giving the observation an injectivity instance.

## Mathlib comparison

At the pinned Mathlib revision in `lake-manifest.json`,
`CategoryTheory/Bicategory/Functor/Prelax.lean` supplies
`PrelaxFunctor.mapFunctor`: every fixed pair of objects gives an ordinary functor
between hom-categories. `CategoryTheory/Functor/FullyFaithful.lean` supplies
`Functor.Faithful`, `Functor.map_injective`, and faithful composition.
A faithful instance for the first-projection hom-functor could be filled directly
by `pathFirst_cell_injective`. Each consumer could then replace its existing
reflection application with `map_injective`. This changes the spelling of the
same obligation and adds an instance adapter; it removes no boundary proof.

The existing proofs already use Mathlib's pseudofunctor preservation equations
for vertical composition, whiskering, and equality boundaries. The assembled
`pathContraction` is a `Pseudofunctor.StrongTrans`, with its unit, composition,
and arbitrary-cell naturality laws proved from the constructed comparison.
A new constructor requesting those three observed equations would require
callers to supply the current normalization blocks unchanged. Requesting the
unobserved equations would merely rename the desired laws.

`RawMap.transportLaws` treats ordinary category operations. Its use here would
still require a hom-category adapter and separate proofs about horizontal
composition, whiskering, object boundaries, and arrow boundaries. It therefore
does not replace the higher obligations.

## Native path contraction decision

Retain the existing local-faithfulness theorem and native pseudofunctor laws.
The original three consumers share injectivity and Mathlib normalization lemmas, but their residual equations
are different. No sequential-observation API is introduced or claimed here;
ordinary faithful hom-functor composition remains available when a caller needs
it.

`Examples.TwoFamilyPathContractionStrong.strong_comparison_retains_integer`
connects the assembled transformation to the actual integer comparison `-k`.
`strong_comparison_nonzero` rejects the strict zero shortcut at `k = 1`.
`pathFirst_reflexivity_cell_heq` and `contractionNaturality_naturality` quantify
over genuine path-context cells, with their endpoints retained. The existing
higher-erasure observer remains part of #322's validation. This assessment
changes none of those statements or their assumptions.

The cost comparison is about caller obligations, not source-file length: both
presentations require the same local-faithfulness proof and the same three
normalization arguments. A new wrapper would additionally require packaging
those arguments and adapting dependent boundaries to its parameters. This
comparison concerns the original contraction proofs. The rooted construction
below supplies a different reuse case.

## Substitution data normalization

During the resumed #322 construction, endpoint and path-context substitution
provided a separate factoring case. A proved equality of families gave an
existing lawful substitution functor, but its casted object and arrow data did
not reduce to the intended explicit operations. Reproving strict functor laws
for each explicit presentation would duplicate reindexing coherence.

`strictFunctorOfEqualData` constructs a strict higher functor from supplied raw
object, arrow, and cell operations equal to those of an existing strict functor.
Its returned operations reduce to the supplied data, while identity,
composition, and both whiskering laws are derived. `reindexOfData` specializes
that construction to a family equal to a pullback. Its six observations retain
the base and fiber in each dimension; they imply equality with the existing
substitution functor. They do not ask for the final coherence equations.

`endpointReindex` and `pathReindex` each supply their explicit operations and six
reflexive observations. Both reuse the same normalization and law proof. The
checked projection example retains each integer path arrow and genuine endpoint
cell. This is the bounded adopted helper: it removes duplicate substitution
coherence proofs and their cast bookkeeping from two actual consumers. It does
not replace the contraction unit/composition/cell-naturality normalization
arguments, claim faithfulness of a projection, or provide the more general
non-strict interpretation comparison owned by #325.

## Rooted contraction law reconstruction

The fixed-endpoint context contains `y : A` and `p : Id(x,y)` for an arbitrary
chosen section `x`. Its embedding into the two-endpoint path context retains
all path cells. `rootedContractionMapped` restricts the existing coherent
`pathContraction` along this embedding. `rootedBaseContraction` takes its
second-endpoint image. Their whole-transformation compatibility is proved by
both endpoint observations in `TwoFamilyRootedCompatibility`.

The shared constructors separate the chosen operations from the laws they
recover:

| Constructor | Caller supplies | Constructor proves |
|---|---|---|
| `strongReflect` | Components, invertible comparison cells, a strict observer injective on parallel 2-cells, an existing coherent image, and matching component/comparison images with their boundaries. | Identity, composition, and arbitrary-cell naturality for the supplied operations; exact recovery of the coherent image. |
| `reindexStrongLift` | A higher family and reindexing functor, coherent base and image transformations, their whole compatibility equation, local groupoid structure, and injectivity of the reindexing functor on parallel 2-cells. | Lifted components and comparisons, their required image equations, and all three strong-transformation laws through `strongReflect`. |

For the rooted consumer, the base functor is `rootedEndpoint`. Its second
projection is the identity, which proves the required injectivity. The pullback
construction supplies the lifted arrows and cells through `reindexLiftHom` and
`reindexLiftCell`. Local groupoid structure makes the lifted comparison cells
invertible. These premises already hold for every admitted higher family and
chosen section; they add no restriction on J motives.

This saves a second proof of the three coherence laws for the rooted
contraction. The caller proves a commuting geometric pair of transformations
and their dependent boundaries, rather than supplying those three final laws
as fields. `strongReflect` still performs the generic whiskering, associator,
unitor, and equality-boundary calculations. The native construction of the
original `pathContraction` remains the source of the coherent image.

`strongPostcomp_heq_reflect` in `TwoStrongFaithful` then reflects equalities of
whole strong transformations. It requires injectivity on both arrows and parallel
2-cells, explicit source/target functor equalities, and the mapped equality.
`rootedContraction_reflexive` and `rootedContraction_reindex` use it to recover
normalization and substitution from the existing path laws. Whole-functor
cancellation in `TwoFunctorFaithful` additionally requires object injectivity;
it supplies the rooted inclusion's substitution square. These are explicit
higher-dimensional obligations. Ordinary faithfulness on one-dimensional
arrows alone would not justify either reconstruction or cell-law reflection.

No general sequential-observation interface is claimed. The adopted helpers
serve the checked rooted pullback, while the two-endpoint contraction retains
its original proofs. `Examples.TwoFamilyRootedContraction` checks a selected
variable branch over the integer-cell family, recovers that whole branch by
beta, and applies contraction naturality to two successive substitutions.
At checkpoint `18a1c14`, its focused build passed 984 jobs; the imported audit
checked 2,188 kernel-safe declarations in 139 project modules, with only
`propext`, `Classical.choice`, and `Quot.sound`. Final repository acceptance
remains separate from this focused evidence.
