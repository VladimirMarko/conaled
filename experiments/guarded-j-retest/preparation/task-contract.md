# Nested selected J certificate and root computation

Selected after interface-freeze approval at
`e376ba585603ae8f2c174d5ceaab374242942cbd`. This is a preparation contract, not
a dispatch approval. No measured author has seen it yet.

Given an admitted point x:A in Γ, an arbitrary finite dependent telescope T
over its based path context, and a section p:Q over total T, construct:

- eta, the selected J section at Id_Q(p,p), with branch reflexivity of p
  pulled back along the root-tail map r;
- kappa, the selected J section at Id_{Id_Q(p,p)}(eta,eta), with branch
  reflexivity of eta pulled back along r.

Retain these exact J recipes. Replacing either by plain reflexivity is not a
solution. Derive the root map from the admitted point and telescope premises;
derive branch alignment without an added semantic alignment premise.

Establish the outer root computation with typed left and right operands.
Substitute that equation and both operand judgments along an arbitrary valid
substitution σ into the total pulled-back tail. Give a constructed instance of
σ: weaken that context by the family of eta restricted to the root. This family
is the pulled-back Id_Q(p,p), so its endpoints retain the varying section p.
Prove semantic agreement from the source equality under satisfied assumptions.
Retain the exact selected left operand, including its type, under stable Sigma
extension/reduct reuse. Show the selected source recipe explicitly.

The baseline's existing reflexive command application generates an identity
argument substitution. Its left semantic code is kappa reindexed along r
composed with that identity, then σ. Retain that exact code and its family
conversion; also check the existing exact-root beta theorem for the same outer
command. The guarded route substitutes directly along r and then σ. These are
the existing source presentations of the same root computation, not identical
raw syntax. State the distinction when comparing obligations.

Novelty is the complete nested-certificate/root-computation/substitution
contract. Public #320 provides one certificate with repeated substitution.
Public authoring modules already contain nested-J ingredients. Neither fact
makes those ingredients fresh exposure. Their presence must be disclosed in
both arm guides. This task does not consume #108's separate theorem.
