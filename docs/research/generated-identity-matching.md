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
