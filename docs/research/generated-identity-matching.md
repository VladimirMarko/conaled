# Selected identity matching

`CechMatching.Identity.Fiber` supplies a local arrow and its actual overlap
square between independently supplied matching endpoints. `arrowEquiv`
identifies this data with arrows of the matching groupoid. `family` acts by
conjugation with both endpoint arrows, and `comparison` proves this
identification natural over an arbitrary parameter category. `family_reindex`
retains the same data under parameter substitution.

`restrictionIso` recovers every supplied matching path from a fully faithful
restriction functor. Essential surjectivity is unnecessary for this identity
step. Its forward map is exactly the given restriction on arrows. These are
paths in the whole groupoid; dependent identity in a relative fiber additionally
requires verticality and is not inferred from the unrestricted statement.

`Examples.CechMatchingIdentity` checks a nonidentity integer loop, its distinction
from reflexivity, recovery of arbitrary supplied local paths, and the general
conjugation formula. The non-discrete example rules out interpreting identity
as equality of endpoint objects. The module and examples pass focused checks
at unchanged limits. Full #445 integration, audit and review remain pending.

`CechMatchingComprehensionIdentity` supplies the dependent specialization.
Its input is a local total arrow satisfying both the actual overlap square and
identity action on the supplied base datum. `arrowEquiv` identifies this data
with vertical arrows of the explicit relative matching groupoid. Its natural
comparison, reindexing law, conjugation formula and `restrictionIso` retain
these selected arrows. The latter requires full faithfulness of relative
restriction; this module does not assume or prove full generated effectivity.
Checked generic consumers recover the entire supplied vertical path and its
identity base action.

`CechMatching.restriction_equivalence_of_contractible` supplies
an empty-context helper without unfolding the restriction implementation. Its
source is inhabited with exactly one arrow between each pair of objects;
the local category has the same property, and the overlap category is thin.
These hypotheses construct full faithfulness and essential surjectivity for
any supplied restriction functor. A checked discrete-unit specialization uses
an arbitrary such functor. This does not replace the unrestricted matching
construction or impose thinness on nonempty generated contexts.

`CechMatchingAsSmall` lifts an arbitrary matching diagram and constructs
`UniverseLift.asSmallEquivalence` from `AsSmall (Datum D)` to matching in the
lifted diagram. It wraps the original local objects, overlaps and arrows,
with checked inverse functors and exact projection/arrow formulas. The tests
include the primitive hom-universe-0/object-universe-1 shape and a selected
nonidentity integer loop. No quotient, discreteness premise or effectivity
assumption is introduced by universe lifting.

`CechMatchingConeMap` proves whole-functor compatibility with a strict diagram
map. Inputs are the local functor equation and equality of the selected overlap
after the explicit first/second/local comparison transports. Neither effectivity
nor faithfulness is a premise. An identity-diagram specialization retains an
arbitrary coherent selected overlap; generated substitution uses the same
interface with its separately constructed comparison square.

`transportedOverlap_of_square` converts the endpoint-square equation into
that normalized overlap equality. Its hypotheses retain both endpoint
equalities and the full natural-isomorphism square; proof irrelevance only
normalizes equality transports. The checked identity-map case allows an
arbitrary overlap, so no identity-overlap premise is hidden in the adapter.

`GroupoidFiberFaithful` reduces faithfulness of a groupoid functor to its
endomorphism kernels. In a commuting square with faithful base comparison,
`faithful_of_vertical_kernel` needs only the vertical kernel. It makes no
splitting-preservation claim and requires no strict natural transformation
between extracted fibers. The integer-loop example uses projection to a point,
so the projection itself is not assumed faithful. This helper proves only
faithfulness, not fullness or effective descent.

`GroupoidFiberFull.full_of_vertical` supplies the complementary fullness step.
Its base functor is full, the source projection lifts each base arrow to a
selected isomorphism, and every target arrow over an equality of base objects
has a source preimage. Factoring by the selected lift leaves a vertical arrow.
The complete square controls the equality transports; the theorem does not
assert that extracted fiber functors commute strictly with base transport.
The point-projection example retains arbitrary integer-loop arrows.

`GroupoidFiberEssential.essSurj_of_fibers` isolates the essential-surjectivity
step: lift a target along a base isomorphism into a fiber over the base functor's
image, then use that fiber's essential-image witness. The hypotheses retain the
chosen isomorphisms and impose no equality between object representatives.

`GeneratedIdentityFamilyMap` extracts the identity-type constructor on the
complete family comparison. `generatedIdentityMap_arrow` applies it to every
supplied identity arrow: first use the component functor's map, then the
endpoint transport determined by the two generated term comparisons. The
open identity type in `Authoring.CongruenceCaller` specializes the constructor
formula. The theorem assumes neither reflexive identity objects nor a
faithful primitive comparison.
