# Prospective client for internal setting construction

Frozen before #319 implementation, from base
`9b0a0fe143c6f97f399632d4bb34a179db012181`.
This document specifies expected mathematics, not completed results.

## Presentation and constructed settings

Use the existing finite geometric presentation with two complementary predicates
p and q and the bound p implies r. The internal parameter in the base Set/Nat
is r(n) := 0 < n. Its classifier object is the dependent family
A(n) := PLift(r(n)) + Unit. The setting S(P) is the slice of Set/Nat at that
constructed object, equivalently Set/(Sigma n, A(n)). The previous coproduct
universal property and section correspondence are reusable evidence, not a
promise that the new nested comparisons are already proved.

Inside this setting the first generic model has a selected summand a:A(n).
Define the second internal parameter q(n,a) := a.isLeft = true. Its classifier
object is B(n,a) := PLift(q(n,a)) + Unit. Form the slice at B in S(P).
Thus the second setting depends on the first generic model, including its
selected summand. It is not an external list of supplied models indexed by n:
P is predicate data, A is constructed by sum/comprehension, q reads the generic
model, and B is built by applying the same formation inside the first setting.

The base language here is the repository's interpreted finite geometric scheme
in Set families. Natural-number and Boolean predicate data are expressed in the
Lean-hosted base. This is a shallow semantic specialization, not a claim of a
new parser, a syntactic universe of all theories, or arbitrary internal sites.
No categorical model is supplied as the parameter.

Existing declarations make that boundary explicit. `FiniteSetting.Formula`,
`Sequent`, `axioms` and `Formula.eval` express and interpret the finite geometric
scheme; `Presentation.parameter` supplies its internal predicate in Set/X.
The concrete arithmetic predicate n>0 and the generic-tag predicate are
Lean-hosted predicate expressions, not trees in a new arithmetic source syntax.
`Total`, `genericSection`, `genericModel`, `modelSectionEquiv` and the recovery
laws construct and interpret its generic model. `formedDisplay`,
`formedCoproduct`, `formedClassifierIso` and `modelPartitionEquivalence` in
`SquareKit/Internal/FiniteClassifierComparison.lean` connect that construction
to the categorical classifier object in Set/X. The slice formation itself is
a metatheoretic construction interpreting the internal presentation, not an
object-language term whose result is an externally supplied category.

The new nested result must connect both generic models to this universal
section interpretation: a first selected model followed by a second model in
its induced context determines a unique map into the nested total, and
reindexing along that map recovers the two dependent sections. A proof only
about the cardinalities or pointwise tags of the displayed fibers will not
satisfy this fixture.

## Selected argument and independent observations

Choose a(n) left when n>0 and right at n=0. Choose b(n) left when a(n) is left
and right otherwise, retaining its dependent evidence. The result is the whole
pair (a(n), b(n)), not only its existence. Expected tags are (false,false) at0
and (true,true) at every successor. Both choices of first summand remain
available when n>0; the second family is inhabited by a left value only for
the first left summand. This detects genuine dependence beyond base n.

The two substitutions are sigma(n)=n+1 and tau(n)=2*n. Applying sigma and then
tau to the context yields original parameter 2*n+1, not 2*(n+1). At n=0 the
selected result must be the pair of left summands, with its full dependent type.
Retain an arbitrary dependent family and section over the nested total as well:
comparison must transport its type and selected term, not only these two tags.

## Two representations and required comparisons

Compare split dependent families with actual display objects and their
pullbacks, including equality certificates over the base. Construct the nested
comparison between forming P then q after substitution and pulling back the
already formed nested total. Prove inverse laws, projection/value compatibility,
identity and composition for successive substitutions. Connect the display
objects to actual slice categories and the existing classifier coproduct
construction. Determine which second-stage laws follow from these constructions
and whether any additional admission hypothesis is necessary.

Compare those representations with primary-source categorical accounts. Treat
mode-indexed judgments separately: no lock, restricted variable access or modal
adjunction is part of this client. A modal result alone cannot establish its
internal construction contract.

## Failure and architectural questions

Collapse the first generic summand to right. At a positive n this loses the
promised first tag and removes the second left alternative. No comparison that
preserves the requested first and second data can repair that collapse.
A map deliberately forgetting those observations remains a valid map for a
weaker contract; do not call it an invalid interpretation merely for being lossy.

Assess whether authors need to repeat alignment for each nested construction
or whether a single interpretation/comparison package supplies it. Allow a
changed judgment organization if needed. Preserve #107's paused repair and
#108's independent theorem gate. Native equality is extensional in this case;
this fixture neither supplies contextual higher J nor passes #316's higher
observation requirement.
