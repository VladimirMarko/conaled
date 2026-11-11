# Native contract for tagged self-reference

Issue #460, frozen before the shared-rule adapter is implemented.

The native language has named propositional atoms, bottom, implication and one
unary operator. A theory supplies named axiom witnesses. Proof trees live in
`Type`, with occurrence-indexed ordinary hypotheses, implication introduction
and elimination, embedding of a closed theorem in a context, distribution,
positive introspection and necessitation of closed theorems only. There is no
constructor admitting a formula merely because a semantic evaluator says it
is valid. Transparency is supplied by explicit derivations, not by identifying
the operator with Lean truth.

A selected diagonal supplies a sentence and two closed proof trees connecting
it to the implication from its unary image to a target sentence. Curry's
construction additionally needs transparency at that selected sentence. The
conditional Löb construction additionally needs a closed reflection theorem
for the target. Both return retained proof trees, not just proposition-valued
existence. Neither constructs an arithmetic diagonal sentence.

The independent observations are the selected sentence, rule applications,
ordered premise occurrences and the ordinary context of every judgment.
Graph data separately retains node identities, a quotation/reference edge to
the selected node, an implication edge, the target parameter and a
Truth/Provability tag. Erasing the tag must preserve all remaining graph data;
it does not certify translation of transparency rules.

The positive consistency test uses two worlds, root accessing leaf only.
The bottom diagonal sentence holds just at root. The target implication
`box L → bottom` then agrees with L at each world. Soundness must cover every
native rule and ordinary context. This model must refute open-assumption
necessitation and bottom reflection. A separate diagonal for the theorem
`p → p` must give a positive application of conditional Löb.

Only after these contracts and native cases are established will the shared
`DependentTheoryMaps` presentation be assessed. Its meta-assumptions are whole
contextual judgments; they must not be confused with ordinary hypotheses.
Any adopted adapter must retain actual trees and premise indices and remove
a repeated transport obligation. Source formula substitution and grafting of
proofs are separate operations. Substitution changes or certifies the theory's
selected axioms, and never silently substitutes inside arithmetic quotation.
