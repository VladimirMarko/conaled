# Mathematical structure challenge

Independent review of revision `d108142f9b5875437c49441a4b45b3ad4988e5e5`,
2026-11-04, for #289. I inspected the complete
[StructuralModel](../../../SquareKit/Internal/PathTransport/Model.lean),
[contextual construction and Model](../../../SquareKit/Internal/PathTransport/ContextualModel.lean),
and [boundary examples](../../../Examples/LocalUniversesBoundary.lean), plus
the annotation definitions in `Typed.lean` and the structural instance in
`GroupoidSoundness.lean`. I read the [#292 report](../dependent-coherence-comparison.md)
and [external memo](../dependent-coherence-discovery/292-external-memo.md).
This is a targeted mathematical review, not a complete audit of source
soundness, concrete J, model morphisms, or all clients. No Lean changes or new
machine-checked results accompany it. Other reviewers' notes were not consulted.

The proposed separation of author requirements, judgment interpretation, model
construction, and comparisons is useful as an allocation of obligations. It is
not yet a mathematical architecture: it leaves the common notion of model and
the admissible comparisons unsettled. Its strongest justification is that LF
belongs to a construction theorem, whereas a proof author needs the resulting
rules. Its greatest risk is preserving today's semantic assumptions behind a
new judgment interface without testing whether those assumptions express the
intended fragment.

The evidence does **not** justify a general diagnosis of missing laws. Three
different questions have been conflated: independent missing structure,
consequences of an existing universal property, and compatibility with a chosen
external theorem. They need different responses.

`StructuralModel` already supplies a category of contexts, strictly functorial
type substitution, term substitution with heterogeneous equality, and
comprehension with both projection equations and eta. `pair_ext` is a proved
uniqueness principle. The file then derives lifted substitutions, path-context
maps, and commuting squares for arbitrary finite dependent tails. These are
substantial positive results. `Model` adds contextual J, its computation law,
and substitution compatibility; it does not merely postulate identity objects.
The structure/law pairing for J is therefore appropriate in the inspected
interface.

Some apparently missing equations should be derived. For example, pairing
naturality follows by comparing the projection and generic-variable components
of `pairSub A σ t` composed with another substitution. The existing
`weaken_pair`, `variable_pair`, `subTm_comp`, and `pair_ext` give the proof
strategy, with explicit type transports. The same strategy should establish
the pullback universal property of `lift`, and its identity/composition laws.
These are proposed derivations to check, not newly verified declarations.
Awodey's representability account explicitly derives pairing naturality and
the identity pairing from uniqueness; terminality is separately needed for
the conventional CwF formulation. [Awodey, §1, Proposition 2](https://arxiv.org/pdf/1406.3219)

Full comprehension deserves a sharper challenge to #292's inventory. One can
try defining family morphisms as all commuting squares between the existing
display maps. Comprehension is then fully faithful by construction; its
cartesian property requires the pullback result above. Equivalently, a vertical
map from A to B can be represented by a term of B reindexed to Γ.A. This is a
credible reconstruction from the present laws, without a new fullness axiom.
Clairambault–Dybjer construct the context-indexed category of types using maps
of context extensions over the base. [§2.2, Proposition 1](https://arxiv.org/pdf/1112.3456)
The unproved part here is the complete Lean construction and its correspondence
with any separately chosen concrete family-morphism category. Restricting those
morphisms, for example to transformations preserving a selected cleavage, could
make fullness fail. A missing packaged category is therefore a representation
and proof gap; it is not evidence that every suitable category is unavailable.

Terminality has different evidence. `MissingTerminal.model` satisfies the full
current interface while its discrete Bool context category has no terminal
object. Thus terminality is independently absent. Whether this is a defect
depends on the advertised language. A relative theory over a distinguished
context can be legitimate. A standard empty context with unique empty
substitution needs the additional operation and universal property. The
counterexample does not establish failure inside the source-generated
component, which stays at false. Audit empty substitutions, context uniqueness,
and the intended scope of semantic contexts before deciding. Calling `empty`
terminal without this audit would be incorrect; adding terminality merely
because the field is named `empty` would bypass the design question.
The inspected `SubDeriv` constructors contain no general empty-substitution
constructor, which supports investigating a deliberately restricted fragment.

LF is stronger again. Lumsdaine–Warren require finite products and certain
categorical dependent exponentials, independently of whether the object
language has function types. Full comprehension alone does not discharge these
hypotheses. Their theorem transfers specified weakly stable constructors; its
generalization discussion excludes conclusions asserting type equality.
[Definitions 3.1.2–3.1.3, Theorem 3.4.1, §4.1](https://arxiv.org/pdf/1411.1736)
The Bool example blocks an unconditional application of that theorem. It does
not show that direct interpretation is defective or that the concrete groupoid
setting fails LF. There is no reason to burden every direct strict model with
LF solely to support an optional construction route. If that route is selected,
its products and exponentials need actual representations and naturality
proofs, not fields whose names merely restate the desired conclusion.

There is also evidence of **excess structure**. The structural record bundles
the primitive `base`/`fiber` signature with identity formation and reflexivity.
A reusable comprehension interface need not require these particular symbols.
Conversely, it has no Σ constructor: semantic telescope extension is not an
object-language dependent sum. The memo's pair `w` therefore needs either a
Σ-equipped fragment or an explicitly stated interpretation as a contextual
package. That choice changes the author contract. Neither simply adding
terminality nor replacing the record with a larger CwF resolves it. Investigate
a small structural core, separate signature assignments, and constructor
packages whose operations, computation, and stability requirements are stated
together. A uniform package template must accommodate interactions between
constructors, rather than assume independent extension is automatic.
Additional required laws should accompany the capability whose meaning needs
them. That need not mean adding a new operation: an eta rule or a stronger
stability requirement can constrain existing operations. Conversely, a law
already implied by a universal property belongs in the derived interface, not
among new obligations imposed on every model builder.

The equality distinction is already partly sound. `identity` returns a
`Family`; its sections need not be Lean equality proofs. In contrast, `Eq` and
`HEq` express metatheoretic substitution and computation equations. Proof
irrelevance for those equations does not by itself identify two sections of
an object identity family. The boundary file's retained higher observation
rejects replacing selected object witnesses by native equality. Its ordinary
groupoid and algebraic two-loop tests do not jointly constitute one dependent
higher model. The adoption test must still interpret the memo's dependent
`apd_η(h)` and preserve its stated second-identity observation in one suitable
setting.

Strict models also need not have exclusively strict morphisms. A comparison
between presentations can preserve comprehension and substitution through
coherent isomorphisms. Those comparisons must act on terms through their type
comparisons and respect composition; disconnected isomorphisms cannot justify
transport. Clairambault–Dybjer specify pseudo CwF morphisms for precisely these
structural comparisons. Their LCCC biequivalence additionally assumes
extensional identity and other structure, so it cannot justify erasing the
present intensional witnesses. [§§3–5](https://arxiv.org/pdf/1112.3456)
For this project, preservation of the chosen identity eliminator and its
dependent branch data remains a separate obligation.

This constrains the proposed separation. Interpretation and change of
presentation must share a comparison calculus; postponing that calculus to a
fourth independent layer risks duplicating the hardest coherence work. The
all-model annotations in `Typed.lean` ask for equality across every current
`Model`. A useful comparison that gives only an isomorphism will not become
such an equality automatically. The report's unequal local-universe
presentations with equal decoding supply a concrete rejection case. A new
author boundary may therefore require replacing those annotations and their
conversion discipline, not wrapping them.

The following investigations discriminate between the competing diagnoses.
They should permit replacement of the current foundation when their evidence
warrants it.

| Priority | Bounded investigation and acceptance evidence | Decision it resolves |
|---|---|---|
| P0 | Inventory every structural field and admitted source rule; derive pairing naturality, lift pullbacks, and the display-map comprehension category without new axioms. Record any precise failed obligation. Include the Bool countermodel. | Missing independent laws versus an incomplete derived interface. |
| P0 | Specify one dependent fragment, including the status of Σ and empty substitution; compare a signature-independent CwF/natural-model presentation with the present records. Give translations or an explicit rejected rule, without requiring immediate compatibility with all old annotations. | Legitimate minimality, accidental restriction, or a need to replace the semantic foundation. |
| P1 | Interpret the memo's argument through two presentations of one setting, once using strict comparisons and once coherent pseudo comparisons. Check both substitutions on terms, types, and J branches. | A local authoring repair versus replacement of the judgment boundary. |
| P1 | Supply one dependent higher model for the admitted fragment, or identify the exact obstruction. Retain monodromy and second-identity observations together with contextual elimination. | Whether the selected model interface has the required witness capacity. |
| P2 | When a concrete weak model needs strictification, establish its family morphisms, LF representations, and eliminator stability; compare local universes with a direct construction on the same fragment. | Whether general strictification earns its cost. |

The four responsibilities should remain a research hypothesis. Adopt them as
module boundaries only after these comparisons identify shared interfaces and
their laws. The current evidence supports preserving the established direct
model results while allowing a different author language, structural core, and
comparison theory to replace the present arrangement.
