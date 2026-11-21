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

This is cover mathematics only. [#663](https://github.com/VladimirMarko/conaled/issues/663)
retains object/all-map family descent and both stack consumers;
[#664](https://github.com/VladimirMarko/conaled/issues/664) and
[#665](https://github.com/VladimirMarko/conaled/issues/665) retain the
subcanonical and arbitrary original-site/slice comparisons. The parent #657
remains open. Using established sheafification to construct a coproduct does
not require the decoder extension across a non-sheaf code unit owned by #654.
