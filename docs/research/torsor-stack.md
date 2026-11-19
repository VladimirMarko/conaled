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

The implementation imports the existing quotient-descent base-change module
for its generic split-cover local-surjectivity instance. This adds a dependency
on that module; it does not use quotient objects in the torsor stack proof.
If additional site-level clients need these facts, moving the cover lemmas to
a shared sheaf-cover module would remove this dependency without changing the
mathematics.

The classification programme remains tracked by
[#647](https://github.com/VladimirMarko/conaled/issues/647). This result supplies
its torsor-stack consumer. It does not complete coherent sheaf decoder recovery
(#652), preservation of dependent products (#655), or the smooth reconstruction
work (#640).
