# Torsor descent as a Mathlib stack

[SheafTorsorStack](../../SquareKit/SheafTorsorStack.lean) proves Mathlib's
`Pseudofunctor.IsStack` for the existing torsor restriction functor. Clients can
now use Mathlib's sieve-indexed descent equivalences, while the split-display
interface retains its explicit gluing construction.

## Site and scope

For `C : Type u`, `[Category.{v} C]`, a Grothendieck topology `J` on `C`, and
`G : Sheaf J GrpCat.{max u v}`, the base category is
`Sheaf J (Type (max u v))`. The fiber over `X` is `SheafTorsor.Torsor G X`.
Restriction is the existing strict split-family restriction. Its arrows include
all equivariant maps: principality and local existence prove these maps
invertible, as recorded by `equivariantArrowEquiv`.

The new `Stack.topology` is a topology **on sheaf contexts**. A sieve covers
exactly when it contains a map whose underlying presheaf map is locally
surjective for `J`. This is not a claim about descent over every covering sieve
of the original category `C`. No representability or subcanonicity assumption
on `J` is needed. No chosen global sections or trivializations are required.
The universe of contexts may be larger than the universe of section fibers.

Pullback stability is witnessed by the split family of actual fibers of a
locally surjective map. Composition preserves local surjectivity. These facts
supply the topology axioms without adding a sheafification assumption or a new
sheafification construction.

## Comparison and effectiveness

[SheafTorsorStackDescent](../../SquareKit/SheafTorsorStackDescent.lean) compares
Mathlib's generalized overlap data with the existing Čech transport:

- `datum` evaluates transitions on the universal overlap. Identity, cocycle,
  naturality and equivariance follow from the Mathlib datum.
- `datumMapEquiv` is a bijection on all compatible maps. The universal property
  of the overlap reconstructs compatibility on every generalized intersection.
- `ofDatum` translates a constructive datum through its glued torsor.
  `ofDatumRecovery` and `ofDatumRecoveryInv` recover the original local object
  and transport, with both inverse equations proved.
- `localComparison` identifies the Mathlib restriction of the constructed
  glued torsor with the original datum. Its component is exactly
  `Descent.comparison`; `localComparison_natural` checks every compatible map.
- `fullyFaithful` and `isEquivalence_split` establish effective singleton
  descent. `display_sieve` and `isStackFor_cover` extend this to arbitrary
  locally surjective maps by the actual-fiber display isomorphism.

For morphism sheafness, `overCoverage` supplies singleton locally surjective
covers in each slice of contexts. The singleton full-faithfulness proof gives
sheafness of Mathlib's morphism presheaf. The coverage criterion and
`over_topology_le` then prove `IsPrestack`. Every covering sieve contains one
of the effective singleton covers, so Mathlib's enlargement theorem gives
`IsStack`. Neither prestackness nor final essential surjectivity is an input.

`Stack.glue` is definitionally the existing constructive torsor.
`classifierComparison`, `classifier_localComparison`, `classifiedMapEquiv`
and `classifier_map_comparison` connect it to
[TorsorClassifierDescent](../../SquareKit/Internal/TorsorClassifierDescent.lean).
The display projection is retained by `classifier_projection`; arbitrary
substitution preserves the map comparison square by `classifier_map_reindex`.
These are equivariant torsor comparisons, not just bijections of bare fibers.

## Checked examples and boundaries

[Examples/TorsorStack](../../Examples/TorsorStack.lean) checks the actual stack
instance and Mathlib's sieve-indexed descent equivalence on the quarter-turn
clutching torsor's total-space cover. The cover sieve is proved proper: an
identity factorization would supply a forbidden global section. The glued
torsor is still not globally trivializable. Distinct C4 loops remain distinct
after restriction, constructive descent and classifier recovery.

The empty-family control proves that the descent functor is not faithful:
without any covering observations, the two distinct loops become equal.
Coverage is therefore essential even to recovery of morphisms. This result
does not establish descent for arbitrary coherent diagrams, selected fillers,
or additional operations. It also does not reconstruct smooth manifolds from
sheaf torsors.

## Setup and maintenance

The new work consists of the overlap bridge, the topology and morphism-sheaf
argument, classifier comparison lemmas, and checked clients. The torsor action,
principality, local existence, constructive object/map gluing and strict
restriction laws are reused. There is no duplicate torsor implementation.
The bridge uses Mathlib's `DescentData`, `IsPrestack`, `IsStack` and coverage
APIs, so changes to those interfaces are the principal new maintenance cost.
No recursion or heartbeat budget override was added.

[SheafCover](../../SquareKit/SheafCover.lean) owns the shared local-surjectivity
and actual-display lemmas. [SheafContextTopology](../../SquareKit/SheafContextTopology.lean)
builds their topology and slice coverage for both stack clients. Constructive
quotient base change uses the primitive cover module without importing stack
topology machinery. The torsor stack no longer imports quotient descent for
cover machinery, and its old public names remain available.

The classification programme remains tracked by
[#647](https://github.com/VladimirMarko/conaled/issues/647). This result supplies
its torsor-stack consumer. It does not complete coherent sheaf decoder recovery
(#652) or the smooth reconstruction work (#640).

## Action-quotient stack

[SheafActionQuotientStack](../../SquareKit/SheafActionQuotientStack.lean) proves
Mathlib `IsPrestack` and `IsStack` for a group-sheaf action `a : Action G M`,
with the same universe convention and sheaf-context topology described above.
Its fiber is `Object a X`: an actual `G`-torsor over `X`, a natural equivariant
map from its total sheaf to `M`, and every torsor arrow preserving that map.
Restriction uses the existing strict `restriction` functors. Stabilizers are
retained, including elements acting trivially on the target.

The [quotient bridge](../../SquareKit/SheafActionQuotientStackDescent.lean)
forgets Mathlib descent data to torsor descent data and reuses the torsor overlap
proofs. It derives target compatibility from the actual transition arrows.
`datumMapEquiv` retains every compatible map; `datumFunctor` composes with
`quotientDescentEquivalence` to define `glueFunctor`. `localComparison` recovers
the original Mathlib datum, with precisely the existing constructive quotient
comparison as its component. `ofDatumRecovery` and `ofDatumRecoveryInv` recover
constructive local objects and transport, with both inverse equations. The
canonical hom equivalence proves full faithfulness, while the constructed
comparison proves essential surjectivity. Neither is an adapter assumption.

`glue_value` and `glue_action` identify the chosen construction.
`localComparison_target`, `localComparison_action` and
`localComparison_projection` retain the target map, action and display. `baseChangeComparison` uses the existing direct
base change of local quotient cocycles. Its recovery, naturality, identity and
composition equations relate that construction to restriction of the selected
glued object and every descended map. There is no choice of torsor trivialization.

[ActionQuotientStack examples](../../Examples/ActionQuotientStack.lean) use the
quarter-turn clutching torsor with its actual total sheaf as target. The target
map is the display isomorphism sending a fiber element to its underlying section.
Recovery preserves this map and the torsor remains nontrivial. Separate examples
retain distinct C4 stabilizers for an ineffective action, through both the
Mathlib bridge and constructive gluing. The empty-cover control loses those
stabilizers. A varying local group-valued target map fails compatibility with
identity torsor transport, despite being equivariant; that compatibility cannot
be omitted from descent data.

The additional setup is the target-preserving bridge and its checked clients.
Constructive quotient object/map gluing and base-change coherence are reused;
the shared cover extraction removes duplicate instances and the reverse
module dependency. Maintenance remains concentrated in Mathlib descent and
coverage interfaces. These are structural costs, not timing measurements or
claims of lower elaboration cost.

This is the singleton-topology result of
[#656](https://github.com/VladimirMarko/conaled/issues/656).
[#657](https://github.com/VladimirMarko/conaled/issues/657) separately owns joint
families and transfer to the original site for this quotient client; that
extension does not follow merely from the torsor instance. No additional sheaf
replacement operation from #654 is needed. This result does not classify the
quotient by an orbit sheaf, stackify arbitrary groupoids, or reconstruct smooth
manifolds; the geometry work remains with #32/#640 and the shared language
coordination with #36/#647.


## Joint families and aggregate covers

[SheafFamilyCover](../../SquareKit/SheafFamilyCover.lean) supplies stage 1 of
[#657](https://github.com/VladimirMarko/conaled/issues/657), tracked by
[#662](https://github.com/VladimirMarko/conaled/issues/662). For `C : Type u`
with `Category.{v} C` and any topology `J`, the index type and sheaf values lie
in `Type (max u v)`. A family is jointly locally surjective when the sieve of
restrictions admitting a lift through some member covers every target section.
This local-lift definition does not mention an aggregate map.

`jointlyLocallySurjective_iff_sigmaDesc` compares this condition with local
surjectivity of the induced map from Mathlib's categorical coproduct of the
sheaves. The construction first takes the coproduct in presheaves, then applies
Mathlib's `sheafifyCocone` and proves its colimit property. `coproductIso`
compares it with the chosen sheaf coproduct, and `aggregate_comparison`
identifies the induced maps. Local surjectivity of the sheafification unit is
the step connecting local lifts to that actual sheaf coproduct. Mathlib's
sheafification and coproduct instances discharge existence in these universes;
no extra existence or sheafification hypothesis is required of callers.

Refinements induce actual maps of coproducts commuting with their aggregate
maps. A jointly covering refinement makes the coarser family cover. Pulling
back every member along an arbitrary context map preserves joint coverage;
the selected split-family squares are proved categorical pullbacks. The
singleton condition is exactly ordinary local surjectivity. For an empty
index, the exact condition is that each existing target section admits the
empty covering sieve. It is not unconditionally false on arbitrary sites.

[Checked cases](../../Examples/SheafFamilyCover.lean) use the two singleton
inclusions into a two-point sheaf on the bottom topology. They jointly cover,
although neither member alone is locally surjective. Their aggregate map is
proved absent from the sieve generated by the members, so sieve enlargement
cannot substitute for family descent. The cases also check a nonidentity
family permutation, repeated base change along Boolean negation, singleton
recovery, and empty-family success and failure. On the top topology the empty
sheaf coproduct has a section, demonstrating why a pointwise empty presheaf
cannot silently replace it.

The new setup consists of the local-lift sieve, the sheafified coproduct
comparison and the refinement/pullback lemmas. Colimit construction,
sheafification and local-surjectivity laws are reused from Mathlib. Maintenance
centres on those interfaces. The separate family module leaves the existing
primitive cover module and its clients' imports unchanged. No timing or general
productivity conclusion is claimed.

The cover comparison is consumed by the family descent construction below.
[#664](https://github.com/VladimirMarko/conaled/issues/664) and
[#665](https://github.com/VladimirMarko/conaled/issues/665) retain the
subcanonical and arbitrary original-site/slice comparisons. The parent #657
remains open. Using established sheafification to construct a coproduct does
not require the decoder extension across a non-sheaf code unit owned by #654.

## Effective coproduct assembly

[SheafCoproductGeometry](../../SquareKit/SheafCoproductGeometry.lean) proves
that the supported categorical coproducts of sheaves are Van Kampen colimits.
The proof uses the corresponding coproducts of types, evaluation in presheaves,
and Mathlib's left-exact sheafification. It derives disjointness of distinct
summands, pullback stability, decomposition above a coproduct, and component
fiber comparisons. The site, value and index universes are those of
`SheafFamilyCover`; callers need no additional colimit or sheafification
assumptions. Empty index types are included.

[SheafTorsorCoproduct](../../SquareKit/SheafTorsorCoproduct.lean) constructs a
torsor over the coproduct of its contexts. Its total sheaf is the categorical
coproduct of the local total sheaves. The action is assembled through the
sheaf exponential, and principality and local surjectivity follow from local
summand decomposition and the component fiber comparisons. The resulting
restriction functor is full, faithful and essentially surjective. Component
isomorphisms recover each supplied torsor, and recovery over the whole
coproduct respects every equivariant arrow.

[SheafActionQuotientCoproduct](../../SquareKit/SheafActionQuotientCoproduct.lean)
uses that construction for the underlying torsors and assembles their actual
equivariant maps to the fixed target. It proves the same restriction
equivalence on objects and all arrows. Target compatibility is proved from
the supplied equivariant maps; stabilizer arrows remain arrows in the
resulting category.

[SheafFamilyTopology](../../SquareKit/SheafFamilyTopology.lean) constructs the
least topology containing the independently jointly locally-surjective
families. Its transitivity proof composes local lifts; its pullback proof uses
the selected categorical pullback squares. A covering sieve contains a joint
family. It need not contain that family's aggregate map. The former
singleton topology maps into this topology, while the two-point example
proves that the inclusion can be strict.


## Family descent and recovery

[CoproductDescent](../../SquareKit/CoproductDescent.lean) proves the presentation
comparison for a category-valued pseudofunctor with effective coproduct
restriction and Van Kampen coproducts. Its restriction functor sends singleton
descent over the aggregate map to the original family. Fullness and faithfulness
are proved on all compatible arrows. For essential surjectivity, the proof
assembles transition maps on pairs of summands, checks them on arbitrary charts,
and derives identity and triple cocycle laws. The recovery isomorphism and the
comparison with canonical descent are consequences of these constructions.
Neither the final equivalence nor its laws are adapter fields.

[SheafFamilyDescent](../../SquareKit/SheafFamilyDescent.lean) discharges both
coproduct hypotheses for the existing torsor and action-quotient
pseudofunctors. `aggregateEquivalence` compares their Mathlib descent categories
with singleton descent over the actual sheaf coproduct map. Combining it with
constructive singleton gluing proves `torsorEquivalence` and
`quotientEquivalence`, and `IsPrestack`/`IsStack` for the family topology. Both
old singleton constructions agree with family-topology recovery through
`torsorSingletonComparison` and `quotientSingletonComparison`. These preserve
the original `Unit`-indexed singleton categories even when supported covering
families live in a larger universe.

The supported setting is a site `C : Type u` with `Category.{v} C`, sheaves
valued in `Type (max u v)`, and families indexed by `Type (max u v)`.
Mathlib supplies the required coproducts, pullbacks and left-exact
sheafification. The generic comparison states its Van Kampen and effective
coproduct hypotheses explicitly; both clients prove them. The topology also
handles sieves with larger arrow-index types through Mathlib's stack interface.

`recoveryNaturality` is a natural isomorphism between pulling family data then
recovering and recovering then reindexing. It applies to refinements and base
change, including every compatible arrow. The checked
[family examples](../../Examples/SheafFamilyDescent.lean) specialize it to a
permutation of the two charts and two successive nonidentity scalings of the
smooth doubled-origin context. Their composite is built from the two natural
comparisons and functorial transport; separate computation equations identify
the pseudofunctor maps with the established composite reindexing operation.

The same two-chart family is jointly covering with neither chart locally
surjective. Its recovered quarter-turn torsor is globally nontrivial. The
quotient example retains the genuine equivariant target from the singleton
client, and the ineffective-action example retains distinct stabilizers.
Object and arrow round trips use the equivalence unit and counit; distinct
compatible arrows remain distinct under recovery. Empty families recover both
clients over the empty context. The existing non-covering empty-family controls
remain failures of faithfulness, so empty descent is not asserted without its
coverage hypothesis.

The reusable setup comprises actual sheaf coproduct assembly, the generic
transition-map comparison and the family topology. The generic comparison
imports only Mathlib's Van Kampen, descent-data and product-category interfaces;
it does not import the sheaf clients. Existing primitive cover and singleton
modules retain their imports. This adds proof and maintenance obligations at
those interfaces, not a measured claim of reduced authoring or elaboration
cost. The final examples use ordinary resource settings: no local heartbeat or
recursion-limit increases. Two initial concrete examples hit kernel deterministic
timeouts while reducing chosen recovery equivalences directly to composite
reindex notation. Naming the functor-level comparison and checking the separate
reindex equation with the public composition theorem avoids that reduction; the mathematical two-step comparison
is unchanged. No recursion-depth failure was observed.

The subcanonical original-site and slice comparisons are developed below.
[#665](https://github.com/VladimirMarko/conaled/issues/665) retains the
arbitrary-site route and non-subcanonical control. Parent #657 remains open.
No decoder extension across a noninvertible code unit was needed, so this work
does not activate #654.

## Subcanonical original sites and slice torsors

[SheafSliceTorsor](../../SquareKit/SheafSliceTorsor.lean) defines a torsor on the
ordinary slice site `C/U` independently of represented-context torsors. Its data
are a sheaf for `J.over U`, an action of the group sheaf restricted along
`Over.forget U`, sectionwise principality, and local inhabitance. Local
inhabitance is a covering-sieve condition; it does not choose a global section.
The shared [RepresentableElementSite](../../SquareKit/RepresentableElementSite.lean)
comparison `Over U ≌ ElementSite.Site (yoneda.obj U)` preserves the actual
covering sieves. It also supplies the existing coherent-sheaf decoder, with
separate object and morphism universes and compatibility names retained. It converts a principal slice sheaf into a displayed torsor
and recovers the slice sheaf. The resulting categorical equivalence retains
all equivariant arrows and commutes with the display projection. Local
principality also constructs inverses for arbitrary equivariant natural maps,
so requiring an isomorphism in the groupoid's arrow structure excludes no maps.

[SheafSliceQuotient](../../SquareKit/SheafSliceQuotient.lean) adds the actual
natural equivariant map to the restricted target sheaf. Its comparison retains
that map and every compatible arrow. Stabilizers remain distinct arrows;
there is no passage to isomorphism classes or orbit sets.

[SubcanonicalSheafStack](../../SquareKit/SubcanonicalSheafStack.lean) works with
`C : Type u`, `Category.{u} C`, a subcanonical topology `J`, a group sheaf in
`GrpCat.{u}` and a target in `Type u`. Original covering families have index
`Type u`. These common-universe assumptions align raw representables with the
existing sheaf-context stack. No pullbacks in `C` are required. The local
lifting sieve of a Yoneda-image family is exactly the pullback of the sieve
generated by the original arrows. Evaluating at the identity section proves
the converse, giving an iff between original coverage and joint local
surjectivity of the sheaf-valued Yoneda family.

The induced original-site pseudofunctors compose sheaf-valued Yoneda with the
existing torsor and quotient functors. Descent transitions given on original
objects extend to arbitrary sheaf-context tests by evaluation at generic
represented sections. Naturality, equivariance, identity and cocycle laws are
proved for the extension, and evaluation recovers the original transitions.
This construction transfers the established effective family descent to the
original topology. The resulting stack claims are proved for both clients;
they are not assumptions supplied by a comparison adapter.

Restriction on the independent slice categories is ordinary precomposition
along `Over.map f`. [SubcanonicalTorsor](../../SquareKit/SubcanonicalTorsor.lean)
proves that its comparison with represented pullback commutes with identity
and composition isomorphisms. The composition equation includes the actual
associativity transport of represented sections. The quotient equation is an
equality of target-preserving arrows. Both comparisons are natural in all
morphisms, so repeated restriction retains the full categories.

The [checked examples](../../Examples/SubcanonicalTorsor.lean) use a proper
two-open original-site cover of the real line, omitting `1` and `-1` respectively.
Neither member is locally surjective. The induced original-site descent
comparison starts from the independently defined slice categories and recovers
objects and arrows. Two nonidentity line scalings check repeated restriction
through the public coherence equations. The quarter-turn clutching example
also retains its nonconstant transition and actual target map through the
slice comparisons on represented charts. Its global doubled-origin base is a
sheaf context, not an asserted original-site representable. Its previously
proved nontrivial family recovery is connected to these chart comparisons.
Distinct stabilizers of the ineffective action remain distinct after the
slice comparison.

The reusable setup is the ordinary slice/element-site equivalence, principal
sheaf conversion, and generic-section extension of original descent maps.
The shared site comparison imports only `ElementSite` and Mathlib's slice-site
interface. The slice modules import it and the existing torsor/quotient primitives; they do not require the family-stack comparison. The
original-site stack module consumes that comparison, and the coherence module
joins the two interfaces. The coherent-sheaf decoder now imports the shared
site comparison instead of owning a duplicate proof. Existing singleton and
direct clients retain their resource budgets; the torsor primitives do not import
the coherent classifier. These are new proof and maintenance obligations,
not a measured reduction in authoring or elaboration cost. All new statements
use ordinary heartbeat and recursion settings. Initial canonical-descent proofs
hit a kernel deterministic timeout and, separately, an elaborator `whnf`
heartbeat timeout. Explicit identity compositions, typed canonical arrows and
named equality-transport equations replaced broad simplification and resolved
both checks without changing resource limits. No recursion-depth failure was
observed.

The subcanonical construction uses raw representables as sheaves only with
that hypothesis. The arbitrary-site construction below replaces them by their
sheafifications and compares the two routes explicitly.

## Arbitrary sites and sheafified representables

[SheafifiedYoneda](../../SquareKit/SheafifiedYoneda.lean) uses the actual
sheafification functor to define `H(U) = a(y U)`. Its evaluation equivalence
`Hom(H(U), X) ≃ X(U)` is the sheafification adjunction followed by Yoneda.
Evaluation composes with the sheafification unit before applying the identity
arrow; it is not the old definitional generic-element computation. Original
covering families correspond exactly to jointly locally-surjective families
of the `H(U)`. The converse uses local lifting and local equality along the
unit, so it also detects which empty families cover.

[ElementSiteLocalEquivalence](../../SquareKit/ElementSiteLocalEquivalence.lean)
proves that a locally bijective map of presheaves induces a dense equivalence
of their element sites. The image of an element sieve has exactly the same
underlying base sieve. Local injectivity supplies local fullness and local
surjectivity supplies cover density. Mathlib's dense-subsite equivalence then
extends sheaves; restriction is its inverse. This helper keeps separate base,
arrow, and section universes and permits an arbitrary target category with the
stated structured-arrow-shaped limits. Its sheafification specialization uses
common-universe type-valued sheaves, where those limits are available.

[PrincipalSheaf](../../SquareKit/PrincipalSheaf.lean) records an action on a
specified sheaf, sectionwise principality, and independent local inhabitance.
[PrincipalSheafLocalEquivalence](../../SquareKit/PrincipalSheafLocalEquivalence.lean)
extends the action and its uniquely determined division operation across a
dense subsite. The division laws recover principality, while cover density
recovers local inhabitance. Empty sets of sections do not imply local
inhabitance. The extension and restriction recover the structures and detect
equivariance of every sheaf map.

[SheafifiedSliceTorsor](../../SquareKit/SheafifiedSliceTorsor.lean) applies these
facts to the unit `y U → a(y U)` and the existing ordinary-slice/element-site
comparison. It constructs an equivalence with the independently defined
torsors on `C/U`. [SheafifiedSliceQuotient](../../SquareKit/SheafifiedSliceQuotient.lean)
adds the actual target map. Both comparisons retain all equivariant maps;
principality derives their inverses. The display comparisons commute with the
projection and target. Automorphisms, including stabilizers, are retained by
the equivalences. Restriction compares ordinary precomposition along
`Over.map f` with restriction along `H(f)`; the unit's naturality supplies the
section comparison and its identity/composition diagrams.

[SheafifiedSheafStack](../../SquareKit/SheafifiedSheafStack.lean) extends original
transition data to arbitrary sheaf-context tests. First it evaluates on raw
representable sections, then extends the resulting maps across the locally
bijective sheafification unit. For an arbitrary overlap it uses the
sheafification of the raw presheaf pullback. Preservation of finite limits
supplies the map into this overlap, so no pullbacks in the original category
are required. The extension satisfies identity, cocycle and restriction laws,
recovers every original transition, and is fully faithful on compatible maps.
The canonical comparison transfers the established sheaf-context family
descent theorem to the original site. The quotient extension additionally
reflects equality of target maps along the same dense presentation.

[SheafifiedSubcanonical](../../SquareKit/SheafifiedSubcanonical.lean) compares
`H` with the existing sheaf-valued Yoneda functor by the adjunction counit.
Whiskering this natural isomorphism gives the torsor and quotient comparisons
on entire categories. Their identity, composition and refinement equations
are equalities of functors, hence retain objects and all arrows. The inverse
counit is proved to be the sheafification unit. This identifies the resulting
ordinary-slice forwards with the old slice forwards, including actions and
target sections. The recovery comparison for descent itself now accepts an
arbitrary base category and independent index universes; its equivalence
calculus proof needs no sheaf-specific hypotheses.

The [arbitrary-site controls](../../Examples/SheafifiedTorsor.lean) use the top
topology on `Discrete Bool`, where the representable of `true` fails the empty
cover at `false`. The replacement is a sheaf, has the proved evaluation
adjunction, and supports both stack and ordinary-slice comparisons with an
actual terminal group sheaf. Empty original covers have effective descent on
this site. Smooth controls separately retain distinct clutching arrows and
ineffective stabilizers, so empty descent there is still not faithful. The
proper original two-open cover, chart recovery from the nontrivial global
clutching construction, permutation of cover members, and two nonidentity
line scalings exercise the final route and its comparison with the prior one.

The supported client setting is `C : Type u`, `Category.{u} C`, a group sheaf
in `GrpCat.{u}`, a target in `Type u`, and covering families indexed by
`Type u`. Mathlib supplies sheafification and the needed limits in this
setting. There is no subcanonicity or original-category pullback hypothesis.
The common-universe client boundary is unchanged from #664; the reusable
element-site comparison is more general. Extending the client stack and its
finite-limit comparison across different size bounds needs a specified theorem
target and its limit hypotheses, rather than an assertion of unrestricted
universes.

Two quotient canonical-comparison proofs use a scoped `maxHeartbeats 400000`
after kernel deterministic timeouts at the default setting. Named projection
and identity-reindex equations avoid expensive normalization in the remaining
comparison, which checks at the default budget. The constructions and final
stack theorems retain their full statements; no recursion-depth setting changes.

Using sheafification here does not extend a classifier decoder across a
noninvertible code-sheafification unit. No #654 decoder equation is used.
Ordinary total-manifold reconstruction remains #640, and the continuing
application and presentation roadmap remains #666 under #647.

## Parent #657 contract and continuing scope

The four delivery stages together supply the requested path:

| Parent obligation | Formal contract and controls |
| --- | --- |
| #662 family to aggregate cover | `SheafFamilyCover` proves independent local lifting iff local surjectivity of the actual sheaf coproduct map; `Examples/SheafFamilyCover` retains proper-family, singleton, empty and base-change controls. |
| #663 descent presentations and family topology | `SheafCoproductGeometry`, `SheafFamilyDescentCore` and both clients give object/all-map aggregate comparison and family stacks; `Examples/SheafFamilyDescent` retains nontrivial gluing, target maps, distinct arrows, refinements, repeated recovery and empty behavior. |
| #664 subcanonical original site | `SubcanonicalSheafStack`, the independent slice categories and `SubcanonicalTorsor` supply original-site stacks, all-map slice recovery and coherent restriction; their original examples remain compiled. |
| #665 arbitrary original site | Sheafified representables, dense element-site comparison, principal-action extension, both original-site stacks and slice equivalences remove the subcanonical assumption in the stated size setting. `SheafifiedSubcanonical` compares the earlier route and `Examples/SheafifiedTorsor` connects the controls to the final one. |

These results concern the specified torsor and action-quotient clients. They do
not assert descent for every category-valued pseudofunctor, invariance under
an arbitrary presentation functor, or ordinary total-manifold reconstruction.
The original singleton/direct clients remain in place. #666 retains future
applications and selected presentation comparisons after the #657 milestone;
#647 remains the broader classification and recovery programme.
