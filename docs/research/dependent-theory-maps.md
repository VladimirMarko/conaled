# Dependent theory maps: checked construction and limits

This records the bounded implementation for
[#344](https://github.com/VladimirMarko/conaled/issues/344). The
[earlier framework assessment](dependent-calculus-frameworks.md) fixes the
independent pair calculi, declarations, client and separator. The
[boundary comparison](dependent-theory-map-boundaries.md) explains the choice
of scoped sequential templates with contextual typing evidence. This experiment
supports coexistence with the existing reference calculus and guarded engine;
it does not establish that either should be replaced.

## Source construction and adaptation

Bauer–Haselwarter–Lumsdaine, v1 §6.5, Definitions 6.22/6.24 and Propositions
6.23/6.25 already provide syntax-changing theory maps, local rule certificates
and functorial derivation transport. The implementation adapts that construction;
it does not claim to invent a missing theorem. Haselwarter–Bauer's boundary
presentation supplies the comparison, not an automatically imported
presupposition theorem. See the primary-source references and ordered boundary
calculations in the [comparison](dependent-theory-map-boundaries.md).

`DependentTheoryMaps` has finite binding signatures, scoped expressions and
capture-avoiding simultaneous substitution. `DependentTheoryTemplates` adds
explicit argument metavariables, their arities and simultaneous instantiation.
A `TemplateMap` supplies one closed expression over argument metavariables per
source symbol. Its interpretation derives substitution compatibility from the
generic instantiation lemmas. The concrete `Gtemplate` expands projections to
split expressions; `Gtemplate_act` proves agreement with the independently
written raw translation. Identity templates are checked as well.

This is a bounded contextual adaptation, not a literal transcription of every
BHL judgment form. The raw expression carrier is unclassified; contextual
judgments distinguish types, terms and both forms of equality. Contexts are
actual finite telescopes. The closed `DependentSequentialRules.Rule` representation carries ordered
relative telescopes for abstracted premises and a conclusion in the empty
variable context. Its instantiation supplies an arbitrary ambient Γ. Concrete
projection and eliminator raw templates instantiate to exactly the independent
contextual schemas, including the two-variable branch and common fiber of
second beta. The shared N/B/C/s/d/t/u declaration templates have the same exact instantiation
bridges in both languages. `Rule.Ordered` checks that each premise telescope
mentions only earlier metavariables, each premise form may additionally mention
its own metavariable, and the conclusion mentions only declared metavariables.
All these primitive and declaration templates satisfy the check; reversing the
formation premises fails it. This syntactic dependency check is separate from
predecessor-rule derivability and full BHL acceptability. Constructor congruence
remains an independently checked contextual table, rather than a claimed
instance of BHL's complete acceptable-theory package.

Contextual premise occurrences retain their indices; neither
dependencies nor repeated premises are erased. Γ is restored by instantiation,
not encoded as an unexplained context metavariable.
The implementation does not introduce a second HB syntax and claim an unproved
bridge to it. Nor does it claim full BHL acceptability, HB context-free
correspondence, inversion or uniqueness of typing.

A necessary repair emerged during implementation: an ordinary assumption leaf
for `Γ,x:A ⊢ B(x) type` cannot simply be reused as a proof of `B(a)` in another
context. `MetavariableCertificate.apply` records the premise occurrence, target
context, substitution and a typing certificate for every argument. Its `graft`
operation erases that application using proved typed-substitution admissibility.
`CertificateEnvironment` builds these arguments by variables, weakening and
context extension. There is no new object-language substitution rule hiding
this obligation.

## Preservation contracts

| Construction | What is established | What is not inferred |
|---|---|---|
| Raw expressions and templates | Renaming, substitution and template instantiation commute; concrete G expands under the motive and both branch binders. | Well-scoped syntax alone is not well typed. |
| Ordinary `TheoryMap` | Local certificates derive whole-proof transport; identity and compressed composition preserve actual Lean derivation trees. | This does not imply semantic reflection or equivalence of calculi. |
| Typed certificate maps | Local typed premise applications are discharged into ordinary derivations by substitution admissibility. | Arbitrary open assumptions are not automatically stable under substitution. |
| `CertificatePipeline` | Staged maps compose; running identity, composition and reassociation gives equal resulting derivation trees. | Staging alone is not compression of local certificates. |
| Administrative certificate maps | Arbitrary local maps compose by substituting their certificates, including typed-substitution instructions. Identity, associativity and composition preserve whole administrative proof trees; actual F/G erases to the retained compiler exactly. | This does not identify trees produced by arbitrary independent ordinary substitution algorithms. |
| `RuleReplay` composition | Precomposition of any typed map by a rule replay produces one local certificate map. The actual F/G composite `fullFG` has exactly the same transported proof tree as executing F then G. | This does not establish arbitrary typed-map fusion without a compatible substitution action. |
| Selected declaration meaning | Independent quotations of the selected source and target expressions have the same dependent tuple, including the chosen `6 : Fin 7`. | This is not a semantic interpretation of every raw expression or a soundness theorem for all model rules. |

`DependentBranchTheoryMaps` supplies generic maps for rule tables with indexed
premise families. `Administrative.rules` extends the proof representation with a
typed-substitution instruction whose children are the source proof, destination
context proof and every typed argument proof. These are administrative proof
instructions, not additional rules of the object calculus. `erase` removes them
using the already checked substitution theorem; `erase_embed` recovers every
original derivation.

`Administrative.lift` turns any syntax-induced `MetavariableTheoryMap` into a
map of these trees. The substitution instruction's local certificate follows
from syntax substitution and context-lookup naturality, with no assumed global
transport law. Generic `TheoryMap.comp` substitutes complete certificates into
one another, including nested administrative instructions. Its identity,
associativity and action laws use literal Lean equality of the retained trees.
The representation permits arbitrary expansion followed by expansion, rather
than restricting the first map to rule replay. `erase_lift` connects the lifted
action on ordinary input proofs to the old translator by equality of complete
ordinary proof trees. The actual `pairF`, `pairG` and `pairFG` instantiate this
construction; `pair_erases` and the selected client's
`administrative_afterBoth` recover the existing compiled derivation exactly.
Erasure after administrative composition is therefore a specified compilation
route. It is not a claim that all independently selected ordinary substitution
reconstruction algorithms yield identical intermediate trees.

Derivation trees live in `Type`, retain premise occurrence and rule choices, and
are compared with Lean propositional equality. The ordinary identity/composition
proofs inspect those trees; proof irrelevance is not doing the work. Pipeline
laws are definitional because the pipeline explicitly records sequential
execution. The modeled calculus's type and term equality judgments are different
objects. Neither is silently replaced by Lean definitional equality.

`TypedSubstitution.Local` supplies rule-local reconstructions, and `substitute`
is one generic recursion over derivations. The full projection and eliminator
tables instantiate every case: structural rules, pair rules, constructor
congruence, ordered client declarations and their congruence. Closed derivations
need no hypothesis-closure assumption. For open derivations, the required
instantiation action on assumptions is explicit.

`projectionPresuppositions` and `eliminationPresuppositions` derive the actual
contextual boundaries of every closed derivation in the full tables. Context
boundaries retain each variable's type; term equalities retain both endpoints
at their common type. The eliminator's split-beta endpoint uses typed branch
substitution. These results instantiate a generic boundary recursion with
checked local cases; they are not merely records awaiting the relevant laws.

## Independent tests of the construction

The projection beta and beta/eta presentations share structural machinery but
are separate rule tables. The eliminator presentation independently declares
formation, pack, dependent split, split beta and eta, with its own constructor
congruence. `GPrimitiveCertificate` checks every projection primitive. `fullG` supplies every certificate, including the constructor congruence cases,
with no remaining law parameters. `fullFG` compresses the actual F/G pair;
`compressed_compiles` proves equality of the resulting ordinary proof trees. First
uses a constant motive and variable branch. Second's motive applies the family
premise to a typed first projection; its branch uses first beta and family
congruence to convert the second variable. Its beta certificate uses split beta
and another common-type conversion. These are derived certificates, not
projection rules added to the eliminator table.

`ProjectionBoundary.secondBetaLeftEarlier` restricts the derivation to rules
before second beta. It uses first beta to type the second-beta endpoint in the
announced common fiber. This prevents the new equation from certifying its own
boundary. Eta's boundary requires the formation rules; the chosen order does
not imply that beta is necessary merely to state eta.

`DependentPairTypedClient` derives the selected variable at the type containing
the second projection of a constructed pair. Both nonidentity substitutions
are typed environments and use the general substitution theorem. The resulting
term is exactly `u(d(k))`. `DependentPairCompilation` compiles the original
client and its instances after each substitution, and checks the staged and
compressed routes against the same proof tree. `DependentPairSelectedMeaning` interprets the selected
declaration fragment independently, connecting it to the complete tuple
`(5, 5 : Fin 7, 6 : Fin 7)`. The zero certificate is rejected. The choice is not
replaced by a theorem that some inhabitant exists.

`DependentPairTheoryModels` ranges over arbitrary context-indexed sets and
families. Its flagged pair model satisfies both projection beta laws, with
second beta explicitly transported along first beta, and fails representation
eta in every inhabited fiber. The flag-dependent motive also refutes unrestricted
split. Forgetting the flag recovers semantic eta. Therefore this is a separator
for the projection-only contract, not a countermodel to the stronger primitive
dependent-eliminator contract. The choice of equality and permitted observations
is part of the statement.

## Setup cost and recurring work

The reusable part is substantial: expression renaming/substitution, explicit
metavariable instantiation, proof-tree grafting and transport, typed environment
operations, substitution recursion, certificate grafting and contextual boundary
recursion. These are distinct layers with different obligations. Counting only
the short final transport definition would conceal their setup cost.

Adding E required five primitive substitution reconstructions and three
constructor-congruence reconstructions. It did not require another
whole-derivation substitution induction. Four local lemmas reconcile its
simultaneous two-variable branch scope with nested telescope extension:
`branchPair_subst`, `branchType_subst`, `flatten_subst` and `branchAt_subst`.
Split and split beta each rebuild the motive and double branch environments.
The first/second translation certificates likewise construct typed motives,
branches and conversions. Those obligations have moved into local code; they
have not disappeared.

The explicit G templates and handwritten raw G also incur an agreement proof.
Keeping both is useful for this comparison, but it is maintenance cost rather
than additional mathematical functionality. Ordinary typed environments and
certificate environments have related builders because their proof carriers
differ. Full-table inclusion maps still contain repetitive sum injections.
These are candidates for later factoring after more clients, not evidence that
arity information alone can generate dependent typing proofs.

Compared with #339, the new construction supports changing binding syntax and
retains occurrence-indexed premises and proof-tree laws. It pays separately for
the dependent syntax, telescopes, typed instantiation and local boundaries.
Compared with #326's explicitly represented substitutions, it proves a different
admissibility theorem. Neither comparison is a matched agent-productivity trial.
No human-productivity advantage, agent-time advantage or general executable
compiler requirement has been established.

Before broader adoption, test higher identity/J, relations and selected higher
witnesses against the same boundaries. A reverse translation, reflection,
round trips and full model soundness remain separate claims. The present result
makes none of them prerequisites for the forward compilation experiment.
