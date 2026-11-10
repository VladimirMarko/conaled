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
