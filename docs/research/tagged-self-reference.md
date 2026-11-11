# Tagged self-reference and retained derivations

Issue [#460](https://github.com/VladimirMarko/conaled/issues/460) extends the
[semantic diagonal experiment](diagonal-construction-assessment.md) to a
bounded contextual proof calculus. It constructs Curry and conditional Löb
proof trees, a consistent finite modal interpretation, and a local-certificate
substitution adapter. The named diagonal remains supplied data. There is no
arithmetic coding, universal truth evaluator or theorem-discovery procedure.

## Checked constructions

[Native.lean](../../SquareKit/SelfReference/Native.lean) defines formulas with
named atoms, bottom, implication and one unary operator. `Derives T Γ P` is in
`Type`. A hypothesis stores its position in the list Γ; two occurrences of the
same formula need not be the same tree. `Theorem T P` has empty Γ.

The constructors are hypothesis, witnessed theory axiom, implication
introduction/elimination, insertion of a closed theorem into a context,
closed-theorem necessitation, distribution and positive introspection. There
is no constructor that admits arbitrary semantically valid formulas. The unary
operation is interpreted by the supplied rules and model. Truth and provability
tags on the separate graph do not change those rules automatically.

`Diagonal T A` retains a sentence L and two closed trees:

- L → (□L → A);
- (□L → A) → L.

`curry` additionally takes closed transparency trees L → □L and □L → L.
Under L, the forward direction and transparency derive A; discharge gives
L → A. Reflection then gives □L → A, the backward direction gives L, and
modus ponens gives A. No modal rule is used in this construction. The bottom
instance in `FiniteModel.curryBottom` demonstrates inconsistency of that
explicit extended axiom theory, not an inhabitant of the consistent theory.

`lob` instead takes a **closed** tree □A → A. Necessitating the forward
selected diagonal and using distribution yields □L → □(□L → A).
Distribution and positive introspection give □L → □A, and the supplied
reflection theorem gives □L → A. The backward diagonal gives a closed L;
necessitation now applies to that closed derivation, completing A.
This is a transformation from a theorem of reflection to a theorem of A. It
does not necessitate an open assumption of reflection or assert the formula
(□A → A) → A as a theorem without further assumptions.

The reconstruction follows the theorem-level premise and the final
truth-based paradox in Löb, [*Solution of a Problem of Leon Henkin*](https://math.umd.edu/~laskow/Pubs/713/Lob.pdf),
1955, printed pp. 116–117. Löb also constructs a sentence through definable
substitution on codes. That arithmetic step is **not** implemented here;
`Diagonal` is its explicit conditional replacement. The modal distribution,
necessitation and introspection rules isolate the part needed by these proof
trees, rather than formalizing all arithmetic conditions of the paper.

## Inhabited interpretation and rejected rules

[FiniteModel.lean](../../SquareKit/SelfReference/FiniteModel.lean) has two worlds,
root and leaf, with only root accessing leaf. □P means P at every accessible
world. Implication is ordinary implication at each world. The accessibility
relation is transitive, so distribution and introspection hold. Closed
theorems hold at every world, which makes closed necessitation sound.
`Derives.sound` proves this by induction on every native constructor, including
contextual discharge.

The selected bottom sentence is atom 0, true only at root:

| World | L | □L | □L → bottom |
|---|---|---|---|
| root | true | false | true |
| leaf | false | true | false |

The theory has four named axioms: the two bottom-diagonal directions and the
two directions for a positive diagonal. All four are proved valid. Soundness
at root gives `FiniteModel.consistent`; consistency is constructed, not merely
assumed for this fixture. This does not make □ an arithmetic proof predicate.

For the positive application, A is atom 2 → atom 2 and the selected sentence
is atom 1, true at both worlds. The actual reflection theorem is constructed
from contextual identity. `positiveApplication` calls the public `lob` on the
selected diagonal and that reflection tree. Its truth is also obtained from
soundness of the resulting tree.

Three rejection results identify different missing obligations:

- `rejected_reflection`: no closed □bottom → bottom tree exists in this theory.
- `rejected_open_necessitation`: the context [L] derives L but cannot derive □L.
  At root the hypothesis holds and its proposed necessitation fails at leaf.
- `no_truth_elimination_certificate`: a generic certificate translating the
  contextual elimination step from □bottom to bottom cannot exist. Grafting
  the actual hypothesis proof into such a certificate and decoding would give
  the contextual reflection excluded by consistency and conditional Löb.

This last claim rejects the specified elimination certificate. It does not
claim that every map between every truth and provability theory is impossible.
External soundness of the two-world interpretation does not supply internal
reflection in its proof calculus.

## Graph erasure and selected witnesses

[Graph.lean](../../SquareKit/SelfReference/Graph.lean) retains five nodes:
selected sentence, quotation, unary application, implication and parameter.
Five labeled edges retain the quotation reference and the cycle through the
selected definition. These are finite edge data, never a cyclic inductive
formula or an evaluator that unfolds the cycle.

Erasure removes only the Truth/Provability tag. Checked laws preserve the
selected name, target parameter and every edge. The two tagged constructions
have identical erasures but are distinct; no restoration function recovers
both original tags from erased data. `NamedConstruction` separately connects
the selected graph name to an actual `Diagonal` and retains its trees.
The graph's quotation edge is a reference to a named node. It is not a Gödel
number, a proof-code decoder or capture-avoiding arithmetic substitution.

## Reuse through local rule certificates

[Transport.lean](../../SquareKit/SelfReference/Transport.lean) presents each
native constructor as a `DependentTheoryMaps.Rules` rule. A judgment is the
pair (Γ, P). The adapter encodes native trees, and `decode_encode` recovers the
actual native tree, including axiom witnesses and hypothesis positions.
Decoding also handles arbitrary generic trees with no meta-assumptions.

The distinction between two kinds of assumptions is essential. Γ is the
ordinary hypothesis list inside one judgment. A generic `Derivation`'s H is
a family of assumed **whole judgments**. The necessitation rule's sole
meta-premise is ([], P), so grafting must supply a closed P derivation. An
arbitrary (Γ, P) derivation cannot fill that occurrence.

The adopted bounded adapter is `substitution`. Its caller supplies an atom-to-
formula function and a witnessed map of theory axioms to substituted axioms.
Each local certificate preserves the premise index. `TheoryMap.transport`
then substitutes the entire derivation; `substitute` decodes it. There is no
second native proof-substitution induction. `substituteDiagonal` uses that
route to retain the selected sentence and both proof trees after substitution.

[TaggedSelfReference.lean](../../Examples/TaggedSelfReference.lean) exercises
nonidentity atom shifts on the positive conditional Löb derivation and its
selected diagonal. `Image` retains original axiom witnesses while changing
the axiom formulas. A separate open tree contains two meta-premise occurrences
of the same judgment. Its observed occurrence list is [0, 1] before and after
transport. Distinct proofs of that judgment have checked node counts 2 and 5;
grafting chooses by occurrence, so the duplicated judgment does not collapse
their identities. The graft comparison and two successive nonidentity
substitutions use the existing `transport_graft` and `comp_transport` theorems
as equalities of actual trees.

The finite presentation costs an explicit label family, premise/conclusion
functions, and encoding/decoding adapters. Its benefit here is removal of the
recurring proof-substitution recursion and reuse of graft/composition laws.
This is a checked mathematical comparison, not an independent author trial
or a measured productivity claim. It does not establish preservation for an
arbitrary logic translation whose local rule certificates are absent.

## Substitution and scope decisions

`Formula.subst_id` and `subst_comp` prove identity and composition for
propositional atom substitution. There are no formula binders. Contexts map
pointwise; implication discharge keeps the corresponding ordinary context.
Named diagonal atoms can be changed only with the same axiom obligations as
other atoms. Proof grafting is a separate operation on judgment-indexed
meta-premises. Neither operation implements quotation-aware arithmetic
substitution or a general syntactic diagonal lemma.

| Route | Decision for this bounded task | Remaining obligation or reason |
|---|---|---|
| Native contextual trees | Adopt for the selected derivations | Small constructors expose theorem-level necessitation and retain witnesses. |
| `TheoryMap` local certificates | Adopt for propositional proof substitution | Recursion, actual graft and composition are reused; new logical rules still need certificates. |
| Graph tag erasure | Adopt as a structural observation | It preserves named references, not transparency or reflection. |
| #444 semantic diagonal and compiler | Retain alongside this route | Callers supply evaluation/representation laws there; callers supply syntactic diagonal trees and logical rule evidence here. Neither discharges the other's obligations. |
| Unrestricted transparent-truth restoration | Reject the specified bottom-elimination certificate | The inhabited modal fixture and conditional Löb prove its failure. |
| Arithmetic realization | Defer outside #460 | Coding, definable substitution, representability and a syntactic diagonal lemma remain unimplemented. |
| Institution `ProofMap` packaging | Defer | It requires a supplied proof map and interpretation compatibility; it cannot generate the missing reflection certificate. |
| Repository-wide syntax or automatic interpretation discovery | Investigate only with owner direction | This bounded adapter makes no shared architectural change. |

[#290](https://github.com/VladimirMarko/conaled/issues/290) retains arithmetic
realization and broader derivation-interpretation research;
[#235](https://github.com/VladimirMarko/conaled/issues/235) owns whether later
consumers justify adapting this presentation beyond the bounded experiment.
[#461](https://github.com/VladimirMarko/conaled/issues/461) tests practical
construction consumers separately. No universal-syntax decision or global
migration is needed to use these checked constructions.

## Validation and statement review

The native contract was committed before the shared adapter. Focused compilation
covers all five new modules through `Examples.TaggedSelfReference`; the public
entrypoint imports that example. Full candidate build, exhaustive proof audit
and independent Standards/Spec reviews are coordinated by the parent wave;
focused compilation alone does not constitute final acceptance.

Statement review checked quantifier scope and theorem-level reflection, ordinary
versus meta-contexts, actual proof values rather than only provability, the
inhabited consistency fixture, and the exact rejected certificate. The positive
fixture is deliberately modest: it shows usable selected inputs and exercises
`lob`; it is not arithmetic provability or a nontrivial arithmetic theorem.
The negative fixture supplies both diagonal directions under the same theory
whose consistency is proved. The graph equality only forgets the tag, and the
proof-transport equality only holds for supplied local certificates.
