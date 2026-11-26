# Dependent presentations after coherent classifier recovery

For [#649](https://github.com/VladimirMarko/conaled/issues/649), retain direct
split sheaf families as the author interface and use coherent classification
as a comparison layer. The #655 extension below connects the existing sheaf
dependent-product operations to classification on a proper cover. This
comparison needs no new weak-model
strictifier, cubical filler, or univalence assumption.

The comparison uses the completed #645/#646 constructions described in
[representable classification](representable-classification-generalization.md).
It refines the decisions in [#292](dependent-coherence-comparison.md),
[#318](concrete-dependent-coherence.md), and
[#474](design-challenges/2026-11-11/local-universes/synthesis.md).
Their higher-model and historical implementation gaps are not current absence
claims; the [architecture reassessment](dependent-architecture-reassessment.md)
records subsequent constructions. The Type-family Σ/Π parameter experiment
remains owned by the open [#518](https://github.com/VladimirMarko/conaled/issues/518).
This comparison does not implement that experiment again.

## Frozen fragment and consumer

The fragment consists of contexts and substitutions, dependent context
extension, terms as sections, all family maps, and repeated substitution.
For any sheaf context Γ, admit every sheaf display `d : B → Γ`. A comparison
must recover B over Γ, every map commuting with its display, its sections,
and the identity/composition comparisons for substitution. Family equivalence
means a specified isomorphism over Γ; it does not mean equality of codes or
of arbitrary chosen pullbacks. Object-language Σ, Π, Id and universes are
extensions to this fragment, not consequences of its structural laws.

The concrete consumer is the diamond site in
[SheafSlices](../../Examples/SheafSlices.lean): a proper cover of X by U and V,
with overlap W. Over the Boolean sheaf D, `falsePoint` has a singleton fiber
at false and an empty fiber at true. The display `E × D → D` has E as its
fiber: E has no section at X, singleton sections at U and V, and Boolean
sections at W. The U restriction selects false and the V restriction selects
true. Thus local inhabitants of this family do not form compatible gluing
data. `varying_no_matching` proves that distinction; `false_matching` supplies
a positive matching family on the same proper cover.

This consumer distinguishes preservation of values and restrictions from
mere local inhabitation. It also exposes vacuous section tests: the varying
display has no global section, so the false-point family supplies the positive
term case after reversing its Boolean base and restricting to the true point.
All maps remain part of the contract, including noninvertible ones.
The generic comparison applies to arbitrary displays; these finite cases do
not narrow its quantifiers.

## What the four presentations retain

| Presentation | Data and arrows for this fragment | Derived comparison and remaining obligation |
|---|---|---|
| Direct families and displays | `Γ.Elements ⥤ Type`, with every natural transformation; sheaf families require sheaf total spaces. Ordinary displays use every commuting square. | `ElementFamilies.equivalence` and `SheafSlice.equivalence` recover both directions, including arrows. `SplitSheaf` derives comprehension, term recovery and pullback comparisons. |
| Coherent representable codes | A functor on `Arrow Γ.Elements` that sends squares with invertible target maps to isomorphisms; arrows are all natural transformations. | Evaluation at identity arrows recovers families. The square from an arrow to its target identity derives recovery. Composition with the direct display equivalence gives a comparison with actual displays. |
| Local parameter universes | A parameter context V, a family E over V, and a name `n : Γ → V`; arrows are maps between decoded displays. | Decode by substitution. Reindex by composing n. Represent A by `(Γ,A,id)`; comprehension and arrows are inherited through decoding. A weak-model constructor still needs its own existence and stability proof. |
| Natural model or one chosen universe | A natural model uses type and term presheaves on the category of contexts. A chosen universe inside the semantic category instead supplies one display whose pullbacks are the admitted families. | The direct structural laws derive the natural-model representability square below. A chosen universe additionally owes coverage of every admitted display and any requested constructor closure. |

The local implementation is
[LocalUniverses](../../SquareKit/LocalUniverses.lean), a Type-family
specialization with `comprehensionEquiv`, `sigma_reindex`, `pair_twice`, and
`displayCurry_natural`. It does not contain a general sheaf local-universes
framework. For the matched sheaf fragment, the following is a paper
specialization using existing operations: take `E : SplitSheaf.Ty V`, decode
`(V,E,n)` as `SplitSheaf.tySub E n`, and obtain terms and comprehension from
that decoded family. Both substitutions replace n by `n ∘ σ ∘ τ`.
`(Γ,A,id)` decodes to A. Using all decoded display maps makes comprehension
fully faithful by the existing family/display hom correspondence. This
construction establishes coverage for local parameters; it does not identify
different parameter records or demonstrate a saving over the direct split
implementation it uses.

For direct displays, the fiber at `(I,x)` is
`{b : B(I) | d_I(b)=x}`. Totalization sends it to `(x,b)` and reconstruction
forgets the redundant x and its equation. A map over Γ restricts to these
fibers; conversely a natural family map acts on `(x,b)` without changing x.
These are the maps implemented in
[ElementFamilies](../../SquareKit/ElementFamilies.lean).
Their inverse equations give fullness on the actual hom-sets. Restricting
the maps to isomorphisms or selected-lift-preserving maps would change the
contract and would require a different fullness statement.

## Checked connection and proper-cover cases

[ClassifierDisplayComparison](../../SquareKit/Internal/ClassifierDisplayComparison.lean)
constructs `Code F.Elements (Type w) ≌ Over F` for every
`F : C ⥤ Type w`, with independent object, hom and value universes.
Presheaf contexts use this with the opposite site as C. `equivalence` composes
the existing coherent-family recovery with the inverse family/display
equivalence. Its object is the actual dependent total with its projection;
`map_projection` retains every code map over F. The category equivalence
includes both recovery isomorphisms, functoriality and the triangle law.

`displayReindex` totalizes the existing `decodeReindex` comparison, so it
compares reindexing the code with substituting its decoded display.
`extension_pullback` gives the actual pullback square for that substituted
display. Identity/composition coherence comes from `decodeReindex_id`,
`decodeReindex_comp`, total-functor functoriality, and the existing split
display coherence; it is not assumed as a new field. `comprehension` gives
the all-context hom-bijection into the constructed extension and
`comprehension_natural` gives pairing under another substitution.

[ClassifierPresentationComparison](../../Examples/ClassifierPresentationComparison.lean)
connects these operations to the diamond families. The decoded varying code
has empty X fibers, inhabited U/V fibers and the distinct false/true W
restrictions. The reversed false-point family has an inhabited restriction;
its pairing and two successive substitutions are checked through the new
comprehension equivalence. Its extension square is checked through
`extension_pullback`. A separately supplied non-strict coherent code's collapse
map remains noninvertible under the display equivalence, testing more than
literal encodings and isomorphisms.

The generic new equivalence concerns underlying presheaf displays. Existing
`SplitSheaf.ofDisplay`, `displayIso`, and
`PresheafFamily.decodeSheafIso` recover every input sheaf display, including
its sheaf certificate and projection. The finite examples use those existing
split families. No arbitrary coherent code is asserted to have a sheaf total,
and no new equivalence with Mathlib's sheaf-over pseudofunctor is claimed.
That additional structured decoder remains #652's scope.

## Representability is a comprehension property

Awodey's Definition 1 calls `p : Ũ → U` representable when every pullback
along `yΓ → U` is representable. Proposition 2 identifies this with a category
with families, for a small context category with terminal object; Definition 3
names the natural model. The representing object is context extension, and
the pullback property gives pairing and its uniqueness. Constructor structures
are additional: §2 treats products, sums and identity types separately.
[Awodey, version 4, §1 and §2](https://arxiv.org/html/1406.3219v4).

In the repository, `System.codes` instead restricts data on presheaf contexts
along the base site's representables. `coherentCodes` does the corresponding
restriction of a Cat-valued pseudofunctor. Those constructions alone supply
neither a term presheaf nor a representable typing map. Even a recovered total
presheaf need not be represented by an object of the original site. The site
objects and the semantic contexts are different categories.
[RepresentableClassification](../../SquareKit/Internal/RepresentableClassification.lean),
[CoherentRepresentableCoding](../../SquareKit/Internal/CoherentRepresentableCoding.lean).

Here is a paper derivation of the natural-model square from the checked direct
sheaf operations, rather than an added representability field. Let K be the
category of small sheaf contexts. Define `U(Γ)=SplitSheaf.Ty Γ` and
`Ũ(Γ)=Σ A:U(Γ), Tm(A)`, with substitution from `tySub` and `tmSub`.
Let p forget the term. The strict substitution equations make these
presheaves and p natural. For A over Γ, the required representation is

```text
Hom_K(Δ, Ext A)  ≃  Σ σ:Hom_K(Δ,Γ), Tm(A[σ]).
k                  ↦  (k ≫ p_A, q_A[k])
pair(A,σ,t)         ↤  (σ,t).
```

`pair_p`, `pair_q`, and `pair_eta` prove the two inverses, while
`pair_natural` proves naturality in Δ. This is exactly the pullback of p along
the Yoneda element A. In particular, a map `Ext A → Ext B` over Γ is recovered
as a term of `B[p_A]`; noninvertible family maps survive the presentation.
These component laws are checked in
[SplitSheaf](../../SquareKit/SplitSheaf.lean). Packaging U, Ũ and this square
as a Lean natural-model structure is not part of the new checked comparison.

The universe distinction prevents an invalid coverage claim. Fix a small site
with objects and homs in `Type u`, and sheaf sections in `Type u`. Contexts and
the collection of all small families require `Type (u+1)`; the natural-model
presheaves above therefore take values there. Total spaces still have
`Type u` sections. This is a universe-relative small category of contexts,
not a same-size sheaf U classifying every family. A fixed same-size universe
map cannot generally cover all such displays: already on the terminal site,
all its fibers are subsets of its fixed total set E, whereas the constant
family with fiber `Set E` has greater cardinality. This is a paper size
counterexample, not a new Lean theorem. A larger universe or an explicitly
bounded class with proved coverage can support the chosen-universe route.

The shared classifier has more general declared levels:
`C : Type v`, `Category.{w} C`, section and family values in `Type (max u w)`,
and codes in `Type (max v (u+1) (w+1))`. `ULift` makes these levels explicit;
it supplies no resizing theorem. The diamond consumer fits `u=v=w=0`.
`SplitSheaf` and `SheafSlice` themselves permit an independent section
universe. The existing sheaf Π and slice-exponential constructions use
`Type (max u v)` for a base `C : Type u` with `Category.{v} C`.

## LF, strictification and the next constructor

Lumsdaine–Warren Definition 3.1.1 constructs the local-universes replacement.
Theorem 3.4.1 transfers the listed weakly stable constructors for a full
comprehension category satisfying LF. Fullness means full faithfulness of
comprehension. LF requires finite products and dependent exponentials for
`Z →g Y →f X`, with f a display and g a display or product projection
(Definitions 3.1.2–3.1.3). These exponentials need not be types. Lemma 3.4.2.4
handles Π. The separate right-splitting result needs pseudo-stability
(Lemma 2.4.2); §4.1 does not transfer arbitrary type-equality rules. Selections
from existential weak structure use witnesses or choice (§2.3).
[Lumsdaine–Warren, version 2](https://arxiv.org/html/1411.1736v2).

The structural fragment above uses no LF theorem. For a sheaf constructor
extension, the actual slice exponentials already provide useful ambient
representation: [SheafSliceFunction](../../SquareKit/SheafSliceFunction.lean)
constructs closure via the site-of-elements equivalence, with hom-bijections,
β/η, parameter naturality, and curry/evaluation comparison. Establishing a
named LF package for a chosen comprehension category would still require
connecting those slice constructions to its dependent exponentials and size
conventions. It should not be assumed as an adapter field merely because the
semantic category is familiar.

[SplitSheafPi](../../SquareKit/SplitSheafPi.lean) already supplies dependent
functions, abstraction, application into the actual dependent result family,
and repeated substitution. [SplitFunctionSheaf](../../SquareKit/SplitFunctionSheaf.lean)
proves the needed sheafness by expressing dependent sections as an equalizer
inside a sheaf of natural functions. The #655 consumer below retains λ,
application, the selected β/η laws and
two nonidentity substitutions, with empty and varying argument fibers on the
proper-cover site. It reuses these constructors without constructing a complete
new model.

The cubical alternative already has stronger selected-operation evidence:
[SharedCubicalConstructors](../../Examples/SharedCubicalConstructors.lean)
recovers dependent sums and their whole selected fillers in the De Morgan and
Cartesian settings. Its hypotheses include lawful input fillers and the
appropriate face/cap data; the second box depends on the first selected
section. Those requirements do not occur in the sheaf fragment. The
[constructor comparison](shared-cubical-constructors.md) also records that
the native Π algorithms use different interval structure. A sheaf Π consumer
therefore broadens tested semantic reuse while the cubical work continues to
test preservation of filling choices. Neither result implies the other.

Transporting an operation along a recovered family isomorphism defines a
selected operation on the recovered presentation. Agreement with a separately
constructed native operation is another theorem, owned where applicable by
[#607](https://github.com/VladimirMarko/conaled/issues/607). No operation
preservation is inferred merely from a category equivalence. Univalence is
unneeded here: the contract asks for explicit isomorphisms and equations of
maps, not identification of equivalences with identity paths. The separate
non-univalence control remains with
[#650](https://github.com/VladimirMarko/conaled/issues/650).

## Sheaf Π operations through classified sections

[#655](https://github.com/VladimirMarko/conaled/issues/655) adds
[ClassifierSheafPi](../../SquareKit/Internal/ClassifierSheafPi.lean) and its
[diamond cases](../../Examples/ClassifierSheafPi.lean). Fix `C : Type u`,
`Category.{v} C`, a topology J, and sheaf contexts with sections in
`Type (max u v)`. The inputs are `A : SplitSheaf.Ty Γ` and
`B : SplitSheaf.Ty (extension A)`. Each includes total-space sheafness; the Π
total's sheafness follows from `SplitFunctionSheaf.piType`. Substitutions are
arbitrary sheaf morphisms. Neither an inhabited argument fiber nor a global
argument section is required for formation or abstraction.

The frozen direct operation is `SplitSheafPi.pi A B`. The classified route
codes this family, decodes its actual display through
`ClassifierDisplayComparison`, and represents a term above `σ : Δ → Γ` by a
map from Δ into that display whose projection is σ. `sections` derives an
equivalence with `Tm (A[σ])` using comprehension, pairing and term recovery.
The selected codes come from existing split families; this API does not
accept arbitrary coherent codes as sheaf families without a sheaf certificate.
For these codes, decoding the family is definitionally exact, while recovering
all display sections uses the proved pairing inverse. There is no adapter
record containing a final preservation or recovery assumption.

`lam` and `unlam` transport `lamAt` and `unlamAt` through this equivalence.
Their β/η equations are derived from the existing laws. Application is
uncurrying followed by the actual argument pairing. Its target is the section
type of B above `pair A σ a`, rather than a constant codomain. `app_sections`
proves agreement with the original split application after its required Π
substitution transport. `pi_reindex`, `lam_sub_twice`, and `app_sub_twice`
retain formation and operations through two substitutions; `display_pullback`
retains the actual output display square. `map` accepts every code morphism,
and its identity, composition and substitution equations retain noninvertible
maps as well as isomorphisms.

This constructs selected operations by transport. The agreement statements
refer to the original split operations used in that construction, so they
are not evidence of agreement with an independently selected native Π
algorithm. `SplitPiComparison`, used by the existing diamond examples, connects
the same split constructor to the ordinary sheaf dependent product; that
construction uses `SheafSliceFunction`'s slice closure. We reuse its mathematical
proofs without adding a second sheafness or slice-exponential argument.
Native cubical filling agreement remains #607's separate contract. No filler,
univalence, LF, or general strictification hypothesis is added here.

The checked positive case recovers a chosen Boolean from lambda at an inhabited
false fiber and applies the function to `falseArgument` after restriction.
`lambdas_distinct` separates the false and true bodies. A constant map on the
function family collapses those two classified terms and still commutes with
two substitutions. The λ and collapse-map tests use Boolean negation twice,
proved nonidentity;
the examples check the actual extension maps and their projection too.
Application additionally commutes with the base map followed by negation.
The dependent-result control has an inhabited false output fiber but no global
function because its true output fiber is empty. The E-input control has an
empty top fiber and incompatible U/V overlap restrictions. Its classified Π
still cannot be replaced by functions between top-stage fibers, reusing the
existing separating theorem. These cases preserve the proper-cover semantics
instead of treating empty input fibers as sufficient evidence for the laws.

Builder setup consists of the term/section equivalence and the transport and
naturality proofs above. Recurring direct callers still supply split families,
terms and substitutions. A caller choosing the classified view additionally
uses `sections` to cross the display-section boundary; it supplies no new
β/η or recovery proof. We have not run a matched author-effort or elaboration
benchmark for this extension and make no performance claim. #648 owns the
separate classifier elaboration comparison.

This consumer starts with sheaf families and uses the canonical family codes,
so neither the full #652 sheaf-over decoder nor #654 extension across
sheafification is needed. #647/#289 retain broader constructor and model
development; #235 retains preservation-interface reassessment. #518 remains
the separate Type-family local-parameter Σ/Π experiment.

## Fibred categories and descent remain complementary

#645 supplies pseudonatural coding/decoding and invertible recovery
modifications for the concrete category-valued family system. Its
arrow-diagram presentation retains all natural transformations and derives
identity/composition comparisons. A fibred category with chosen cartesian
lifts is useful when semantic input already comes as displays and pullbacks;
its pseudofunctor records precisely the comparison isomorphisms that a strict
family presentation hides in substitution. The existing result does not
classify arbitrary pseudofunctors. The conventional coherent-local-data
comparison belongs to [#651](https://github.com/VladimirMarko/conaled/issues/651),
and actual sheaf-over decoding to
[#652](https://github.com/VladimirMarko/conaled/issues/652).
[RepresentableCoherentRecovery](../../SquareKit/Internal/RepresentableCoherentRecovery.lean).

Descent adds topology and effective gluing to that context coherence. #646
proves `HomSystem.codes_isSheaf_iff`: Hom codes glue exactly when their target
presheaf does. Its diamond control is subcanonical but has a non-sheaf code
presheaf, so subcanonicity and restriction laws are insufficient. Its torsor
client first constructs effective descent, then classifies, retaining the
display, action and compatible equivariant maps. A sheaf total, a sheaf of
codes, and a stack of structured objects remain separate claims.
[HomRepresentableClassification](../../SquareKit/Internal/HomRepresentableClassification.lean),
[ClassifierDescent](../../Examples/ClassifierDescent.lean),
[TorsorClassifierDescent](../../SquareKit/Internal/TorsorClassifierDescent.lean).

The Mathlib stack-contract comparison is owned by
[#653](https://github.com/VladimirMarko/conaled/issues/653). Decoder extension
across sheafification is owned by
[#654](https://github.com/VladimirMarko/conaled/issues/654) when a consumer
needs it. This consumer starts with sheaf displays and requires no
sheafification. None of these successors is an automatic prerequisite for
the matched structural comparison.

## Cost and disposition

| Dimension | Assessment for the frozen fragment |
|---|---|
| Shared mathematics | Keep generic-element recovery, all-map family/display equivalences, and context-coherent recovery. They eliminate repeated proofs of the same comparison. |
| Builder setup | Direct sheaf families need total-space sheafness. Coherent local input needs functoriality and invertibility of restriction comparisons. Local parameters additionally introduce names and generic families. A chosen universe needs coverage. |
| Recurring author work | Existing split callers supply families, terms and substitutions. Coding an existing family should require no new recovery proof. Independently authored coherent diagrams still owe their local compatibility evidence. |
| Constructor maintenance | Preserve result-family dependence and selected operations explicitly. A generic decoder does not replace native filling or sheafness proofs. |
| Lean elaboration | The added categorical equivalence introduces functor and isomorphism adapters. No timing or author-effort experiment is reported here; #648 owns the separate classifier budget comparison. Mathematical coverage does not predict reduction cost. |

Adopt the bounded comparison as a reusable connection; retain the direct
interfaces and native cubical specializations. Adopt the sheaf Π section comparison below
under #647/#289 and the preservation owner #235. Keep #518
as the Type-family Σ/Π reuse experiment, including its weak-unit controls.
Defer a general local-universes framework until a selected weak model has the
needed semantic operations and strict stability is its remaining obstacle,
or a matched construction demonstrates recurring work removed by transfer.
Defer a chosen-universe migration until its size, coverage and requested
constructor closure are constructed. These decisions leave both routes
available for different consumers.

## Evidence boundary

The natural-model packaging, sheaf local-parameter specialization and size
counterexample above are paper arguments. Existing Lean declarations are
identified at their source files. The new #649 module and connected examples
passed their focused Lean builds. Integrated build/audit and independent
review belong to the implementation handoff for the exact candidate; this
report does not substitute earlier results for those checks. No general
strictification theorem, new univalent model, or comparative productivity
result is claimed.
