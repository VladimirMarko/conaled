# Category presentations and compositional extensions

Initially surveyed on 2026-11-24 against repository baseline
`040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e` and pinned Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Updated on 2026-11-25 against project `96e2189394fe32a346ca306bd75da3197db246c9`
to account for the delivered comma interfaces and #703–#706. The nLab readings
remain the 2026-11-24 source assessment; this update does not claim a new page
review or an exhaustive survey. The coverage table below separates available
interfaces, adoption work and further research.

The library already connects several presentations through maps, categorical
equivalences and coherent substitution. These mechanisms are substantial, but
unevenly available. There is no established generic procedure that takes an old
object definition and supplies its intended morphisms, comparison cells and
coherence. Some apparent gaps are already covered by Mathlib; others are missing
project adapters or broader mathematical contracts. This report
separates those cases and recommends a bounded programme of shared constructions.

Here, extending a definition with morphisms and coherence does **not** mean
categorical enrichment over a chosen monoidal category. That is a separate
technical notion. The question here is how to organize structure over existing
objects, its preservation maps, and comparisons between those maps.

## Selection and source verification

The selection starts with direct imports of `Mathlib.CategoryTheory.*` in the
local import closure of `SquareApplications`, then inspects the associated
project APIs and their dependencies. At the baseline, the closure has 4,132 local
modules. The leading direct-import counts include:

| Module suffix | Importing local files |
|---|---:|
| `SingleObj` | 14 |
| `Whiskering`; `Limits.Types.Pullbacks` | 11 each |
| `Types.Basic`; `Equivalence`; `Bicategory.Functor.LocallyDiscrete` | 8 each |
| `Limits.Shapes.Pullback.IsPullback.Basic`; `Sites.LocallyBijective` | 7 each |
| `Grothendieck`; `Limits.Shapes.BinaryProducts.ProdComparison` | 6 each |
| `Elements`; `Comma.Over.Basic`; `Comma.Over.Pullback`; `Sites.LeftExact`; `Sites.Limits`; `Category.Cat`; `HomCongr`; `Category.Preorder` | 5 each |

This ranks explicit imports, not mathematical importance, theorem calls or
transitive use. Imports through local facades undercount shared foundations.
The survey therefore also includes the raw category/compiler layer, adjunctions,
closed structure, monads and Yoneda used by the selected modules. It is a
reproducible sample, not an exhaustive classification of category theory in the
repository. In particular, the presheaf, sheaf and higher-identity developments
are too broad to audit theorem by theorem here.

The following read-only script reproduces the import selection at a chosen
checkout. It recognizes this repository's single-line local import format; it
is a survey aid, not a replacement for the native build graph or coverage check.

```sh
direnv exec . python3 - <<'PY'
from pathlib import Path
from collections import Counter
import re
paths = list(Path('.').glob('*.lean'))
for root in ('SquareKit', 'Applications', 'Examples'):
    paths += list(Path(root).rglob('*.lean'))
files = {str(p.with_suffix('')).replace('/', '.'): p for p in paths}
seen, todo, counts = set(), ['SquareApplications'], Counter()
while todo:
    name = todo.pop()
    if name in seen or name not in files:
        continue
    seen.add(name)
    imports = set(re.findall(r'^import (\S+)', files[name].read_text(), re.M))
    todo.extend(imports & files.keys())
    counts.update(i for i in imports if i.startswith('Mathlib.CategoryTheory.'))
print('Local modules:', len(seen))
for name, count in sorted(counts.items(), key=lambda item: (-item[1], item[0]))[:35]:
    print(count, name)
PY
```

The linked nLab pages were fetched and their article text inspected. The browser
reader rejected their `application/xhtml+xml` content; direct HTTPS retrieval
with Python's `urllib.request` and `html.parser.HTMLParser` succeeded. The links
identify live pages, accessed on the survey date, rather than pinned nLab
revisions. Mathematical assertions below use those articles; implementation
assertions use the checked-in Lean source and the pinned Mathlib source. A
negative finding means that the specified interface was not found in the
inspected modules, not that no equivalent theorem can exist elsewhere.

## Coverage and adoption table

This table indexes the inspected presentations; the sections below contain
nLab links and declaration-level source references. “Available” means the
specified interface exists, not that every old caller has adopted it. Universe
restrictions belong to individual adapters; the linked reports give their exact
signatures. The common-universe Cat pullback and the context universe maxima
in the family bridge must not be generalized silently.

| Presentation | Existing declaration or entry point | Assumptions and morphism/coherence coverage | Recovery guarantee | Remaining work |
|---|---|---|---|---|
| Raw categories/maps → lawful quotient | `HomQuotient.category`, `RawMap.quotientFunctor`, `LawfulQuotient.equivalence` | Semantic equivalence, congruence and laws; the Mathlib quotient comparison takes an ordinary category and congruent hom relation. Functors preserve composition. | Quotient classes and their arrows, not representatives. | Available; inspected older callers have explicit dispositions in the #712 ledger. Total-arrow/internal-category comparison is outside the inspected bridge. |
| Raw transformations → ordinary transformations | `RawTransformation.Natural`, `quotient`, `quotient_eq_iff`, `toNatTrans`/`ofNatTrans` | Fixed raw maps; target laws/congruence where used; postwhiskering requires preservation. Quotient boundary also requires source laws. Independent source/target universes. | Pointwise semantic relation exactly matches quotient transformation equality; lawful specialization round trip. | Available; adoption ledger #712. No automatic Type-valued witness coherence. |
| Monoids/groups → one-object categories | Mathlib `SingleObj.toEnd`, `mapHom`; `SetoidMonoid` | Monoid maps correspond to functors; groups give groupoids. | One-object map correspondence. | Available. Full two-dimensional correspondence needs specified intertwining cells and pointedness; research only. |
| Products/pullbacks/limits → representability | `CartesianMapQuotient.binaryFanIsLimit`; Mathlib `IsLimit.homEquiv`, `representableBy`, `ofRepresentableBy` | Raw beta/eta and congruence for the quotient bridge; ordinary cones and natural cone maps afterward. Chosen pullback substitution uses comparison isomorphisms. | Universal-property recovery and uniqueness up to the stated isomorphism. | Available; #706 checks a product client. Further raw adapters need a selected construction. |
| Comma objects → universal cones and arrow-endpoint pullback | `CommaUniversal.equivalence`, `precomposeNat`; `CommaPullback.arrowPullbackIsLimit` | Functors and compatible natural transformations, composition and test-category changes. Cat bundling uses common object/hom universes; unbundled API retains independent levels. | Strict functor round trips; factorization and uniqueness for the strict endpoint pullback. | Delivered. Reuse in older callers where appropriate; not an isocomma or higher-comma theorem. |
| Function squares → bundled arrows | `CommaExactLawful` | Lawful function categories; exact objects/arrows and composition. | Exact object/morphism round trips. | Delivered; retain raw weak-assumption routes. |
| Adjunctions → hom bijections/unit–counit; closed structure → product adjunction | Mathlib `Adjunction.mkOfHomEquiv`, `mkOfUnitCounit`; `ClosedMap`, `AdjointComparison` | Naturality and triangle laws; raw transport needs its comparison/reflection hypotheses. Beck–Chevalley requires the specified pullback/adjunctions. | Selected hom bijections and adjunction data; curry/uncurry laws. | Available; checked #706 client. No automatic higher coherent adjunction translator. |
| Monoidal categories → one-object bicategories | Mathlib `MonoidalSingleObj` | Associator/unitors and their laws; strictness is not implicit. | Existing construction and endomorphism recovery. | Full biequivalence remains beyond the inspected interface; no migration selected. |
| Monads → monoids in endofunctors | Mathlib `Monad.monadMonEquiv`; `programLiftMonad` | Ordinary categorical equivalence including morphisms; concrete multiplication laws proved first. | Monad/monoid category equivalence. Does not recover an arbitrary inducing adjunction. | Available; #706 checks operations and a morphism. #617 owns the separate Lawvere–finitary-monad correspondence. |
| Presheaves/Yoneda/elements → evaluation and totals | `SheafifiedYoneda.evaluation`, `subcanonicalIso`; Mathlib `Elements`, `grothendieckTypeToCat` | Natural evaluation; representable-sheaf comparison requires subcanonicity; discrete-fibre total comparison has its stated variance. | Selected evaluation and elements/total comparisons, retaining action arrows. | Available selected routes; deeper presheaf/sheaf coverage remains #708. |
| Indexed coherent families → fibred total categories | `CoherentFamilyFibration.totalEquivalence`, `codeFiberEquivalence`, `directFiberEquivalence`; `CoGrothendieckMap.homFunctor` | Contravariant context reindexing, strong transformations and invertible recovery modifications. All family maps, including noninvertible ones; cartesian arrows preserved. Context universe `max v (u+1) (w+1)`. | Total equivalence over the same base, fibre recovery and base-trivial unit/counit components; not equality of arbitrary cleavages. | Selected bridge delivered. Other family adapters and converse/biequivalence remain #708. |
| Sheaves/descent → reconstructed categories | `SheafActionQuotientDescentCategory.quotientDescentEquivalence` | Local surjectivity and the stated action/descent hypotheses; arrows and natural comparison retained. | Selected category-level descent equivalence. | #678/#679 delivered [labelled action stackification and atlas independence](action-stackification-morita.md). General groupoid presentations and arbitrary-input stackification remain outside that contract; coverage research remains #708. |
| Equivalent presentations of structured objects | `Lawvere.Recovery` model maps, `modelFullyFaithful`, `modelEquivalence`; matroid object/order comparisons | Lawvere algebra maps become natural transformations; object/order equivalences alone do not select matroid morphisms. | Lawvere categorical recovery; matroid recovery at the existing object/order level. | #630 owns the isomorphism-functorial matroid extension; no arbitrary morphism category inferred. |
| Dependent higher witnesses → finite correspondence representations | `FiniteDependentCorrespondence`; existing `TwoFamily` | Fixed finite dependent cells, actual whiskering and independently constructed representation maps; endpoint transports retained. | Full selected-cell recovery; distinct witnesses survive the comparison. | #703 delivered. Native #700–#702 and general higher interfaces remain separate. |

At `96e2189394fe32a346ca306bd75da3197db246c9`, rerunning the selection script
finds 4,151 local modules. Leading direct-import counts are `SingleObj` 14,
`Whiskering` 12, `Limits.Types.Pullbacks` 11 and `Equivalence` 9. There are no
direct imports whose names contain `Kan`, `Ends` or `Coend` in that sample;
this is not evidence that those concepts or transitive APIs are absent.

Local-import checks locate `RawTransformation` in `Examples.RawTransformations`,
`CoherentFamilyFibration` in `Examples.CoherentFamilyFibration`, and
`CommaPullback` in `Examples.CommaUniversal` (with `CommaUniversal` imported
through the pullback module). `CategoryQuotient` is imported by
`Examples.CategoryInstances` and `Examples.CategoryCharacterizations`.
These are concrete entry points, not a proof-call census or evidence of broad
migration. The [#712 caller assessment](reconstructible-presentations-search.md#remaining-adoption-decisions-27-november-2026)
records the subsequent adoption and retain decisions; this earlier import sample
is not their coverage claim.

The included families are the rows above. Deferred depth includes the full
presheaf/sheaf developments, general higher coherence, converse fibration
comparisons, and facade/transitive-use assessment of additional families.
#708 retains that research rather than treating this table as exhaustive.

## Presentations already connected, and remaining interfaces

### Categories, functors and semantic equality

nLab presents both a total collection of arrows with source/target maps and a
family of hom-sets indexed by objects. These lead respectively to internal and
enriched generalizations; those generalizations require additional ambient
structure. Its [category](https://ncatlab.org/nlab/show/category) and
[functor](https://ncatlab.org/nlab/show/functor) articles do not justify treating
an arbitrary chosen relation on arrows as Lean equality.

[Category](../../SquareKit/Category.lean) deliberately separates `CategoryOps`,
`HomEquiv`, congruence and laws. `ofCategory` recovers the Mathlib equality-lawful
case. `HomQuotient.category` turns congruent equivalence laws into an ordinary
category, identifying exactly the chosen relation by `mk_eq_iff`.
[CategoryMap](../../SquareKit/CategoryMap.lean) supplies `RawMap`, `MapLaws`,
composition, law transport with explicit reflection, and `quotientFunctor`.
Its `toFunctor_ofFunctor` is an exact recovery equation.

[CategoryQuotient](../../SquareKit/CategoryQuotient.lean) already compares the
local lawful quotient with Mathlib's quotient by hom equivalences and a
composition-preserving functor. The subsequent [checked characterization work](category-characterizations.md)
packages this as `LawfulQuotient.equivalence`, with an explicit quotient-class
inverse. It recovers neither raw representatives nor erased witnesses. A total-arrow/internal-category bridge was not found in
the inspected foundational modules; it would need its own size and ambient
pullback contract. Neither bridge warrants forcing raw compiler clients to
assume equality laws before their quotient is constructed.

### Natural transformations and changes between interpretations

nLab's [natural transformation](https://ncatlab.org/nlab/show/natural+transformation)
article relates componentwise naturality to arrows in a functor category and to
functors from the interval times the source. Ordinary natural transformations,
vertical composition and whiskering are already supplied by Mathlib and used
throughout the selected library.

[GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean) is a
concrete reusable example: `Route B A` contains a base functor and a natural
transformation `B ⟶ base ⋙ A`. `transport` follows from naturality; `comp_assoc`
and `reindex_comp` establish composition and substitution. Despite the filename,
the construction itself permits arbitrary categories with Type-valued families.

[RawTransformation](../../SquareKit/RawTransformation.lean), delivered in #704,
now separates component data, `Natural` modulo the target `HomEquiv`, and
pointwise semantic `Rel`. It supplies identity, composition, whiskering,
horizontal composition and interchange under explicit laws. Prewhiskering
needs only a raw map; postwhiskering needs preservation. Its ordinary lawful
adapter recovers Mathlib natural transformations; `quotient_eq_iff` identifies
exactly pointwise semantic equality for fixed endpoints. It does not recover
raw representatives or arbitrary Type-valued coherence witnesses. The
[extension assessment](compositional-interface-extension.md) records the
hypothesis controls and the adopted scope.

### Monoids, groups and one-object categories

The leading `SingleObj` imports have an existing answer. nLab's
[monoid](https://ncatlab.org/nlab/show/monoid) and
[groupoid](https://ncatlab.org/nlab/show/groupoid) articles explain one-object
categories and invertible arrows. Pinned Mathlib's [SingleObj][M-single]
provides `toEnd`, `mapHom`, composition equations and a groupoid instance for a
group. `mapHom` is an equivalence between monoid homomorphisms and functors
between the chosen one-object categories.

Project consumers include [SetoidMonoid](../../SquareKit/SetoidMonoid.lean),
[GroupoidCorrespondence](../../SquareKit/GroupoidCorrespondence.lean) and the
[GroupoidTransport examples](../../Examples/GroupoidTransport.lean). No new
object-level presentation is needed. At the next dimension, natural
transformations between one-object functors carry intertwining elements; they
are not equality of group homomorphisms. A claim about equivalence of the entire
2-dimensional presentations must specify pointedness and allowed 2-cells.
Likewise, an orbit set does not recover stabilizer arrows of an action groupoid.

### Products, pullbacks and limits

nLab's [limit](https://ncatlab.org/nlab/show/limit) article gives universal cones,
representability of cones and, when all limits of the shape exist, the right
adjoint to the constant-diagram functor. The [pullback](https://ncatlab.org/nlab/show/pullback)
article specializes the universal property to a cospan. Pinned Mathlib already
has `IsLimit.homEquiv`, `representableBy`, `ofRepresentableBy` and uniqueness up
to isomorphism in [IsLimit][M-limit]. These alternatives are available rather
than missing library mathematics.

[CartesianMapQuotient](../../SquareKit/CartesianMapQuotient.lean) supplies the
project bridge: `binaryFanIsLimit`, `terminalIsTerminal`,
`preserves_binary_product` and `preserves_terminal` turn the raw beta/eta and
comparison laws into ordinary universal properties after the stated laws and
congruence are supplied. [FamilyCoherence](../../SquareKit/FamilyCoherence.lean)
proves naturality, units and associativity for chosen pullback substitution.
[TypeFamilyCoherence](../../SquareKit/TypeFamilyCoherence.lean) compares it with
split Type substitution. These are comparison isomorphisms; arbitrary choices
of pullbacks are not literally the same object.

The residual opportunity is to expose more raw constructions through these
existing universal-property adapters where useful, rather than rebuild general
limit theory. A claim of strict recovery must name the chosen objects and
maps. A pullback up to isomorphism cannot silently replace a homotopy pullback
whose objects retain a comparison isomorphism.

### Comma categories and exact squares

nLab's [comma category](https://ncatlab.org/nlab/show/comma+category) presents
objects and commuting pairs, a comma object in the 2-category of categories,
and a strict pullback of the arrow-category endpoint functor along `F × G`.
The last presentation is a pullback over `T × T`, not the ordinary pullback of
`F : A ⥤ T` and `G : B ⥤ T`. The comma comparison is an arbitrary arrow;
requiring it to be invertible gives the isocomma construction instead.

At the baseline, [CommaLawful](../../SquareKit/CommaLawful.lean) provides the
lawful/raw and quotient routes, while [CommaExact](../../SquareKit/CommaExact.lean)
has exact object and arrow round trips with `Squares.Rep` and `Squares.Square`,
preserving identity and composition. The absent project-facing capability was
a usable functor-and-transformation universal property and the explicit
arrow-pullback package. [CommaUniversal](../../SquareKit/CommaUniversal.lean)
now supplies `lift`, `toCones`, `fromCones`, strict functor round trips and
`equivalence`. The cone category itself uses Mathlib's comma of postcomposition
functors, so it retains compatible transformations and their category laws.
`precompose`, `precomposeNat` and their identity, composition and whiskering
laws cover changes of test category, including transformations.
[CommaPullback](../../SquareKit/CommaPullback.lean) supplies `pullbackLift`, both
factorization equations and uniqueness, with `arrowPullbackIsLimit` and
`isPullback_arrow` bundling the ordinary Cat result. Only that bundling restricts
all three categories to a common object/hom universe; the unbundled results
retain independent universe levels.

[CommaExactLawful](../../SquareKit/CommaExactLawful.lean) connects raw function
squares to Mathlib's bundled function arrows with exact object/morphism round
trips and composition preservation. [Checked clients](../../Examples/CommaUniversal.lean)
use noninvertible connectors, nonidentity transformations between nonconstant
functors, composed reindexing, strict uniqueness and the existing increment/double
square. The [three-perspective design assessment](comma-interface-design/decision.md)
records the alternatives, adopted scope and witness-coherence limits.

The raw construction's weak assumptions must survive: making comma operations
needs the target's congruence/laws and preservation by the two maps; laws for the
result additionally need the source laws. The [witness version](../../SquareKit/WitnessCommaCategory.lean)
retains a commutation witness but its chosen relation compares the two sides.
`eraseMap` and `erase_relation` establish their stated erasure contracts, not
recovery of each erased witness or a general bicategorical universal property.

### Adjunctions and closed categories

nLab's [adjoint functor](https://ncatlab.org/nlab/show/adjoint+functor) presents
natural hom-set bijections, unit/counit with triangle identities, and universal
arrows. Pinned Mathlib's [Adjunction][M-adjunction] already converts hom
bijections and unit/counit data via `mkOfHomEquiv` and `mkOfUnitCounit`.
[AdjointComparison](../../SquareKit/AdjointComparison.lean) and
[AdjointSquareTransport](../../SquareKit/AdjointSquareTransport.lean) connect
chosen adjunction comparisons to currying and pasting of mates.
[DependentBaseChange](../../SquareKit/DependentBaseChange.lean) proves its
Beck–Chevalley comparison under an actual pullback and specified adjunctions.
An arbitrary square does not yield an invertible mate.

The [cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category)
article identifies exponentials by the product/right-adjoint hom bijection.
Mathlib's [closed structure][M-closed] provides that adjunction and curry/uncurry
laws. [ClosedMap](../../SquareKit/ClosedMap.lean) transports the raw closed
laws with explicit comparison and reflection premises;
[SheafCartesianClosed](../../SquareKit/SheafCartesianClosed.lean) transports an
adjunction across two monoidal dictionaries instead of assuming their identity.
These are established alternative interfaces. A generic automatic translator
from all raw closed witnesses to all higher coherent adjunction data is not
established by these modules.

### Monoidal categories and monads

nLab's [monoidal category](https://ncatlab.org/nlab/show/monoidal+category)
article distinguishes tensor/unit with associator and unitors from strict
associativity and presents the one-object bicategory view. Mathlib's
[MonoidalSingleObj][M-monoidal] constructs that bicategory and recovers the
endomorphism monoidal category. Its own module documentation leaves the full
biequivalence, including the precise pseudofunctors and transformations, as
further work. That broader comparison is not a reason to replace the project's
ordinary monoidal or Cartesian APIs.

nLab's [monad](https://ncatlab.org/nlab/show/monad) identifies a monad as a monoid
in endofunctors and explains its relation to adjunctions. Mathlib's
[monadMonEquiv][M-monad] is already a category equivalence, including morphisms.
[AssemblyLiftMonad](../../SquareKit/AssemblyLiftMonad.lean) exposes
`programLiftMonad` after proving the concrete multiplication laws. The general
alternative is available on import; a duplicate local monoid presentation is
unnecessary. Different adjunctions can induce the same monad, so recovering an
arbitrary original adjunction requires more than the monad alone.

### Presheaves, Yoneda, Grothendieck constructions and descent

The [presheaf](https://ncatlab.org/nlab/show/presheaf) and
[Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma) articles connect
contravariant functors and evaluation by representables. Mathlib's
[Elements][M-elements] supplies category-of-elements/comma equivalences, and
[Grothendieck][M-grothendieck] has `grothendieckTypeToCat` for discrete fibres.
[SheafifiedYoneda](../../SquareKit/SheafifiedYoneda.lean) derives `evaluation`
from sheafification and Yoneda, proves its naturality, and supplies
`subcanonicalIso` under subcanonicity. It does not assume every representable
presheaf is already a sheaf.

nLab's [Grothendieck construction](https://ncatlab.org/nlab/show/Grothendieck+construction)
connects pseudofunctors with (op)fibrations; variance and cartesian-preserving
morphisms matter. [GrothendieckEquivalence](../../SquareKit/GrothendieckEquivalence.lean)
handles strict diagrams `C ⥤ Cat`: component equivalences yield an equivalence
of total categories, and `extendEquivalence` also changes the base. Components
need not be bijections of object representations. Pinned Mathlib additionally
has a pseudofunctor [CoGrothendieck construction with a fibered projection][M-fibered]
and equivalences with its specified fibres. Thus pseudofunctor support is
already available. #705 added [CoGrothendieckMap](../../SquareKit/CoGrothendieckMap.lean)
and [CoherentFamilyFibration](../../SquareKit/Internal/CoherentFamilyFibration.lean):
the selected coherent local diagrams and direct families have equivalent total
categories over the same context base, recover their fibres and preserve
cartesian arrows. Modifications induce total natural transformations. The
[family report](coherent-family-fibration.md) states variance, universe maxima
and recovery comparisons. A converse from arbitrary fibrations, a full
biequivalence and adapters for every local family API remain outside this result.

nLab's [sheaf](https://ncatlab.org/nlab/show/sheaf) article describes unique
gluing of compatible sections. Category-valued descent must also retain arrows
and their compatibility. The project does this concretely:
[SheafActionQuotientDescentCategory](../../SquareKit/SheafActionQuotientDescentCategory.lean)
has `descentFunctor`, a natural comparison, and `quotientDescentEquivalence`
under local surjectivity. This is already more than object reconstruction.
It does not establish effective descent for every kind of added structure.

### Equivalence and recovery strength

nLab's [equivalence of categories](https://ncatlab.org/nlab/show/equivalence+of+categories)
distinguishes inverse functors up to natural isomorphism from isomorphism of
categories, and explains the choice qualification in passing from full,
faithful, essentially surjective functors to selected quasi-inverses.
Mathlib's [Equivalence][M-equivalence] supplies the ordinary equivalence
interfaces used locally.

[Lawvere/Recovery](../../SquareKit/Lawvere/Recovery.lean) demonstrates the right
level of completion: algebra maps become natural transformations,
`modelFullyFaithful` recovers those maps, and `modelEquivalence` connects the
categories. By contrast, the matroid presentations documented in the
[reassessment](../language-direction.md#reassessment-after-library-and-ctb-applications)
recover object/order data without choosing a category of matroid morphisms.
An object equivalence alone does not specify that category. Adding morphisms
requires a mathematical choice, not a mechanical strengthening of `Equiv`.

## Architecture for adding structure and coherence

The following mechanisms are concrete and reusable now:

| Existing mechanism | What it establishes | Boundary |
|---|---|---|
| `RawMap`, `RawTransformation`, operation-specific maps, law transport and hom quotients | Compose interpretations and ordinary transformations while separating operations, equivalence, preservation and reflection. | The transformation layer observes semantic equality; it does not reconstruct arbitrary erased witnesses. |
| Functor categories, natural transformations, full subcategories | Reuse identity/composition and naturality instead of restating component equations. [CoherentFamilyClassification](../../SquareKit/Internal/CoherentFamilyClassification.lean) restricts arrow-indexed functors by a coherence property, then gives code/decode and reindexing comparisons. | A full subcategory adds object properties without changing allowed arrows. Extra operations whose preservation restricts arrows need a different construction. |
| Families, chosen pullbacks and Grothendieck totals | Assemble dependent objects and arrows; prove base-change comparisons, units and associativity. | Strict diagrams and pseudo diagrams have different input contracts; fibrewise equivalence alone without natural compatibility does not assemble a total equivalence. |
| Model-specific categories of structured objects | Lawvere recovery and quotient descent recover morphisms and natural comparisons along with objects. | Their operation or cover hypotheses are part of the construction, not generic consequences of object-level recovery. |
| Witness and higher-identity modules | Keep selected relation/path witnesses in domains that need them. | A witness-valued relation with reflexivity, symmetry and transitivity is not by itself all bicategory coherence. |

These mechanisms occur across foundations, internal languages, algebra and
geometry. That supports describing them as a recurring architectural practice.
It does not support saying the complete practice is ubiquitous. The object-only matroid comparisons and the specialized family adapters
show different levels of completion. Import frequencies above do not measure
how many old definitions have all morphism/coherence layers.

There is also a concrete higher-level framework choice in the span work.
[PseudofunctorCoherence](../../SquareKit/Internal/PseudofunctorCoherence.lean)
uses Mathlib's existing pseudofunctors, strong transformations and invertible
modifications, adding precomposition, complete extensionality and target
normalization. [SpanInterpretationComposition](../../SquareKit/SpanInterpretationComposition.lean)
derives complete pseudofunctor identity/composition comparisons and packages
slice-action comparisons as modifications, with triple-composition and unit
diagrams. It retains chosen pullbacks and requires their preservation by the
interpretations, rather than requiring equivalences or all finite limits.
This is implemented compositional infrastructure, not merely a proposal.
The [framework assessment](span-interpretation-composition.md#framework-choice-and-universes)
also names its limits: it does not supply a general tricategorical framework
or unrestricted cross-universe span interpretations.

The [six-functor assessment](six-functor-presentations.md) similarly retains
derived ordinary Künneth, adjoint-comparison and mate coherence, while
distinguishing higher observable cells from propositional laws. The
[native-coherence contract](native-coherence-contracts.md) describes further
higher comparisons as proposed theorems, with an existing checked starting
point. These records show why the answer is neither “nothing was settled” nor
“every older definition can now be enriched automatically.” The adopted
frameworks have concrete admission and recovery contracts.

A useful general organization is a **category of structures over a base
category**, represented by a displayed category when dependent indexing helps.
The [displayed category](https://ncatlab.org/nlab/show/displayed+category) article
organizes objects over each base object and arrows over each base arrow; its
total category comes with a forgetful functor. This is a settled mathematical
construction. It still requires the structure's arrows and their composition
to be supplied. Existence of cartesian liftings is an additional fibration
property, not automatic for every displayed category.

There is a related concrete project implementation:
[PathTransport/DisplayCategory](../../SquareKit/Internal/PathTransport/DisplayCategory.lean)
constructs a category of a structural model's display maps, with **all commuting
squares** as arrows, a fully faithful comprehension functor, chosen pullback
squares and a cartesian lifting theorem. Its fullness is not fullness for maps
preserving every chosen cleavage or filler. This module is evidence for a
reusable specialization, not an already adopted generic displayed-category
framework for every legacy definition.

The completed [extension design assessment](interface-extension-design/decision.md)
adopts the bounded raw transformation layer and retains Mathlib lawful
transformations, operation-preserving morphism restrictions and complete span
comparisons. Canonical span comparisons can be rebuilt from the retained
functor, chosen pullbacks and preservation evidence. This does not justify
recovering arbitrary supplied witnesses after erasure. The
[family design assessment](coherent-family-fibration-design/decision.md) adopts
the selected total-category bridge. A universal structure-over-base framework
remains research; neither decision mandates a global rewrite.

For old interfaces, identify the information and laws needed for later maps and
coherence early. Implement shared layers when they provide mathematical
capability or reusable proofs, without requiring an immediate blocked client.
[#712](https://github.com/VladimirMarko/conaled/issues/712) records the completed
adoption decisions below. Route newly justified work through an existing open
owner or a scoped successor under [#235](https://github.com/VladimirMarko/conaled/issues/235),
with explicit retain, update or defer decisions and a next review checkpoint.
A deferral is not a conclusion that the present encoding should remain forever.

The [preservation architecture](preservation-architecture.md) already chooses
compatible native layers, and the [contract inventory](preservation-contract-inventory.md)
records their wider obligations. Its first experiments establish particular
shared laws and author outcomes, not the limits of future infrastructure. The
[later presentation search](reconstructible-presentations-search.md) and
[language direction](../language-direction.md#complementary-presentations-and-reconstruction)
require reconstruction, composition and preservation of existing clients.
History confirms concrete advances, including Lawvere's category-level recovery
in commit `09fe9368`; it does not make older object-only comparisons obsolete.

The following distinction should guide planning:

- **Settled mathematics and checked implementations:** ordinary functors and
  natural transformations; hom-bijection/unit-counit adjunctions; universal
  cones and representability; specific quotient, family, Lawvere and descent
  comparisons cited above.
- **Delivered interfaces with adoption work:** raw transformations, the lawful
  quotient equivalence, comma presentations and the selected family/fibration
  bridge. Their availability does not establish that older callers use them.
- **Missing or incomplete comparisons in the inspected scope:** systematic
  adapters for the remaining family APIs and the broader pseudofunctor/fibration
  comparison. These need their own precise contracts and source assessment.
- **Architectural research:** which common structure-over-base interface
  should be adopted, how far strict/pseudo/witness layers can share proofs,
  how structure extensions expose requirements, and how to retain concrete
  usability across domains. No current trial settles those questions generally.
- **Impossible without added information:** recovering erased path labels,
  stabilizers, selected fillers or probability masses from observations that
  identify distinct such data. Existing separating examples in the preservation
  inventory must remain regression cases.

## Adoption and further research

The original four priorities have delivered results: comma presentations in
`511f0c89`, checked characterizations in #706, the raw transformation and
extension study in #704, and the selected coherent-family bridge in #705.
#703 additionally checks finite dependent witness retention and independent
representation maps; it does not supply a general higher comma construction.

[#712](https://github.com/VladimirMarko/conaled/issues/712)'s
[adoption ledger](reconstructible-presentations-search.md#remaining-adoption-decisions-27-november-2026)
records the completed caller checkpoint. Linear decoding uses raw transformations;
geometric mixed base change now specializes the shared comparison and pasting
proofs. The inspected comma, quotient, span and coherent-sheaf callers have
explicit retain decisions under their original contracts. The final textbook
source was integrated at `6e6805dc` before this assessment; external delivery is
no longer a waiting condition. The ledger distinguishes its bounded caller
search from the remaining broader survey.

[#708](https://github.com/VladimirMarko/conaled/issues/708) tracks further
coverage and interface research. It retains the remaining facade-aware usage
audit, deeper presheaf/sheaf and higher coverage, and comparison of chosen
pullback families, structural display maps, `SplitSheaf` and restricted span
actions. New consequential adoption decisions require the design challenge;
the existing #704/#705 decisions need not be reopened for routine reuse.

[#235](https://github.com/VladimirMarko/conaled/issues/235) coordinates both
tracks, with [#8](https://github.com/VladimirMarko/conaled/issues/8),
[#289](https://github.com/VladimirMarko/conaled/issues/289) and
[#647](https://github.com/VladimirMarko/conaled/issues/647). Existing substantive
owners include [#617](https://github.com/VladimirMarko/conaled/issues/617) for
Lawvere/monad correspondence and [#630](https://github.com/VladimirMarko/conaled/issues/630)
for matroid functoriality. Native whole-path sethood and coherence remain
[#700](https://github.com/VladimirMarko/conaled/issues/700) →
[#701](https://github.com/VladimirMarko/conaled/issues/701); cross-model admission
is [#702](https://github.com/VladimirMarko/conaled/issues/702). Ordinary categorical
adapters discharge none of those native obligations.

[M-single]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/SingleObj.lean
[M-limit]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Limits/IsLimit.lean
[M-adjunction]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Basic.lean
[M-closed]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean
[M-monoidal]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/SingleObj.lean
[M-monad]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monad/EquivMon.lean
[M-elements]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Elements.lean
[M-grothendieck]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Grothendieck.lean
[M-fibered]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean
[M-equivalence]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Equivalence.lean
