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

[#664](https://github.com/VladimirMarko/conaled/issues/664) retains the
subcanonical original-site and slice comparisons, and
[#665](https://github.com/VladimirMarko/conaled/issues/665) retains the
arbitrary-site route and non-subcanonical control. Parent #657 remains open.
No decoder extension across a noninvertible code unit was needed, so this work
does not activate #654.
