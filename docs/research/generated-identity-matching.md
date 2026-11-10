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
