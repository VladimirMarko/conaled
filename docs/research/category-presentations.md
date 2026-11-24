# Category presentations and compositional extensions

Surveyed on 2026-11-24 against repository baseline
`040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e` and pinned Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

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

The raw foundational map API above has no corresponding generic transformation
record with a naturality witness in `HomEquiv`, composition, whiskering and a
quotient comparison. Mathlib's ordinary transformations cannot be applied to
arbitrary raw operations without first supplying the missing laws. A shared
raw transformation layer is a plausible next construction. A Type-valued
witness version would additionally need specified coherence between witness
composites; replacing witnesses by their mere existence does not supply that.

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
`preservesBinaryProduct` and `preservesTerminal` turn the raw beta/eta and
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
already available; a full converse biequivalence and a shared adapter for the
project's varied family APIs were not located in this survey.

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
| `RawMap`, operation-specific maps, law transport and hom quotients | Compose interpretations while separating operations, equivalence, preservation and reflection. | Supplies no generic raw 2-cell layer or recovery after witness erasure. |
| Functor categories, natural transformations, full subcategories | Reuse identity/composition and naturality instead of restating component equations. [CoherentFamilyClassification](../../SquareKit/Internal/CoherentFamilyClassification.lean) restricts arrow-indexed functors by a coherence property, then gives code/decode and reindexing comparisons. | A full subcategory adds object properties without changing allowed arrows. Extra operations whose preservation restricts arrows need a different construction. |
| Families, chosen pullbacks and Grothendieck totals | Assemble dependent objects and arrows; prove base-change comparisons, units and associativity. | Strict diagrams and pseudo diagrams have different input contracts; fibrewise equivalence alone without natural compatibility does not assemble a total equivalence. |
| Model-specific categories of structured objects | Lawvere recovery and quotient descent recover morphisms and natural comparisons along with objects. | Their operation or cover hypotheses are part of the construction, not generic consequences of object-level recovery. |
| Witness and higher-identity modules | Keep selected relation/path witnesses in domains that need them. | A witness-valued relation with reflexivity, symmetry and transitivity is not by itself all bicategory coherence. |

These mechanisms occur across foundations, internal languages, algebra and
geometry. That supports describing them as a recurring architectural practice.
It does not support saying the complete practice is ubiquitous. The raw map
layer, the object-only matroid comparisons and the specialized family adapters
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

The design recommendation is to assess a small shared structure-over-base
interface, with reusable total categories, forgetful functors, change of base,
composition of structured maps and comparisons. It should support adding a
property as a full subcategory and adding operations with preservation-restricted
arrows. Separate strict equalities, natural isomorphisms and relevant witness
cells at the interface. Do not put all optional laws into one record or claim
that an arbitrary object definition determines its morphisms canonically.

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
- **Settled mathematics with missing or incomplete project interfaces:** a raw
  transformation layer, packaged comparison equivalences, systematic adapters
  between structured-family APIs, and the broader pseudofunctor/fibration
  comparison. Their implementation and usable specialization remain work.
- **Architectural research:** which common structure-over-base interface
  should be adopted, how far strict/pseudo/witness layers can share proofs,
  how structure extensions expose requirements, and how to retain concrete
  usability across domains. No current trial settles those questions generally.
- **Impossible without added information:** recovering erased path labels,
  stabilizers, selected fillers or probability masses from observations that
  identify distinct such data. Existing separating examples in the preservation
  inventory must remain regression cases.

## Priorities and acceptance contracts

1. **Complete the lawful comma universal property and its bridges.** This is
   the present implementation task. Require functor and natural-transformation
   recovery, composition, substitution/coherence, the exact-square client and
   the arrow-endpoint pullback with its actual universe and strictness contract.
   Retain raw weak assumptions and distinguish witness erasure from equivalence.
2. **Complete inexpensive presentation bridges before inventing replacements.**
   Package the existing lawful quotient comparison when a category equivalence
   is the intended claim. Surface existing Mathlib adjunction, limit, monad and
   elements constructions in focused examples or facade documentation. Existing
   mathematics should be reused rather than counted as missing.
3. **Develop a reusable transformation and structure-extension slice.** Compare
   the raw/quotient route with a displayed or structured-category route using
   one old operation-preservation API and one family/coherence API. Acceptance
   should include identity/composition, naturality, a comparison between the
   presentations, old clients under their original assumptions, and a
   witness-sensitive separating example. This is justified foundational work;
   it need not wait for a client to fail before being investigated.
4. **Extend coherent family interoperability.** Connect a current chosen-pullback
   or structural-model family to the pinned pseudofunctor/fibered machinery.
   State variance, cleavage choices, allowed maps, recovery strength and
   comparison coherence. Broader biequivalence or descent claims need their
   own proofs, not a pointwise isomorphism table.

[#235](https://github.com/VladimirMarko/conaled/issues/235) is the existing
coordination owner for compatibility and specialization, with
[#8](https://github.com/VladimirMarko/conaled/issues/8) for categorical foundations
and [#289](https://github.com/VladimirMarko/conaled/issues/289)/
[#647](https://github.com/VladimirMarko/conaled/issues/647) for dependent and
classification interfaces. These are proposed work allocations using the
repository's documented ownership, not new issue-state claims or completed
implementation commitments. The current task does not require blanket
migration or completion of every nLab presentation.

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
