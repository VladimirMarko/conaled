# Dependent structure, laws and interpretation boundaries

The three requested independent assessments support a substantial investigation
of the dependent architecture under #289. They do not establish that the current
model is unsound or that stronger assumptions are the answer. They identify both
specialized structure bundled into the interface and reusable consequences that
may be recoverable from its existing laws. The proposed separation of author
requirements, interpretation, model construction and comparisons remains useful
as a list of responsibilities. It is premature to adopt four independent layers.

This reassessment follows [#292](dependent-coherence-comparison.md) at revision
`d108142f9b5875437c49441a4b45b3ad4988e5e5`. The owner requested three challenges
from different perspectives, then follow-up issues. Each agent completed its
assessment without reading the other drafts:

- [Mathematical structure](dependent-architecture-review/mathematical-structure.md)
  checked the existing laws, universal properties and external hypotheses.
- [Implementation boundaries](dependent-architecture-review/implementation-boundaries.md)
  traced semantic-code indices, source judgments, constructor capabilities and
  the known authoring obstruction.
- [Alternative foundations](dependent-architecture-review/alternative-foundations.md)
  compared author representations, model morphisms, modal contexts and internal
  setting construction against primary sources. This agent disclosed its prior
  role coordinating the completed integration review; it was independent of the
  other assessments, not unexposed to the project.

The original assessments are retained as research proposals, not checked
theorems. The results section below records subsequent reviewed evidence;
the individual assessments retain their historical wording.

## Reviewed results from the follow-up investigations

The [structure audit](dependent-structure-audit.md) derives pairing naturality,
lift coherence and display pullbacks from the existing laws. It constructs
full comprehension for the category of all display-map squares and gives an
independent representability presentation. These results support reusing the
derived operations without adding model fields. Fullness depends on the chosen
morphisms: the Type-family correspondence is checked, while an actual groupoid
shear refutes identification with strict cleavage-preserving family maps.

The audit also corrects an earlier inference about empty substitutions.
Every generated context admits one by recursion on its derivation. The absence
of a named primitive did not establish missing existence. Terminal uniqueness
is a different requirement: a complete model refutes it even in the full
subcategory of reachable objects. That result does not refute uniqueness in
a category restricted to source-generated arrows. No such uniqueness theorem
is assumed here.

The [internal-setting construction](internal-setting-construction.md) supplies
two nested settings with a second presentation depending on the first generic
model. Their slice interpretations and selected dependent payloads commute
coherently with repeated substitution. This establishes the bounded internal
presentation case: finite geometric syntax with Lean-hosted predicate data,
interpreted by a metatheoretic slice construction. It does not supply an
object-language term returning an arbitrary category.

The [higher-identity investigation](dependent-higher-identity.md) checks the
frozen argument in pinned Cubical Agda, including both dependent substitutions,
a nontrivial second-identity observation and nonconstant monodromy. Its Lean
adoption condition remains unmet. The direct higher-groupoid route still needs
constructed families, sections, contextual J for arbitrary admitted motives,
dimension closure and a sound interpretation of that argument. Those exact
obligations belong to [#322](https://github.com/VladimirMarko/conaled/issues/322);
[#321](https://github.com/VladimirMarko/conaled/issues/321) owns the separate
cubical model and source-compatibility programme. External source checking is
partial evidence, not a Lean interpretation.

These results establish derived structure and bounded semantic constructions.
They do not yet select a replacement author interface, prove constructor
admission for that interface or measure its author benefit. Those decisions
remain with #315, #317 and #320.

## What the earlier account understated

The current interface already pairs contextual identity elimination with its
computation and substitution laws. Its structural core provides pairing with
beta/eta equations, and the library derives uniqueness and dependent telescope
comparisons. The concrete groupoid implementation constructs the eliminator and
its compatibility. These are positive examples of the structure/law discipline
we want to reuse.

#292 adds a constructed Type-family mechanism: retain a family with a parameter
map, then implement substitution by composition of that map. Its dependent-sum
construction preserves a selected pair through two substitutions. This gives
one concrete way to move coherence into infrastructure. It does not yet measure
an improvement in generated-language authoring or supply the dependent higher
model required by the [external memo](dependent-coherence-discovery/292-external-memo.md).

The counterexamples diagnose different limits. They should not be accumulated
into an undifferentiated verdict against the model.

| Question | Current evidence | Consequence for investigation |
| --- | --- | --- |
| Are more comprehension laws needed as assumptions? | The subsequent audit derives display pullbacks and full comprehension for all display-map squares from pairing beta/eta and substitution. | Reuse the construction; establish any claimed correspondence with a different category of family maps separately. |
| Is the distinguished `empty` terminal? | Complete countermodels refute global existence and full-reachable uniqueness. Generated empty substitutions nevertheless exist by a checked recursion. | Specify the objects and arrows of the intended category before requiring terminality; generated-arrow uniqueness remains a separate question. |
| Does the concrete groupoid setting satisfy LF? | No failure was proved. The categorical package remains unconstructed. | Prove the exact hypotheses if a selected construction needs them; direct models need not all provide LF. |
| Is the structural interface sufficiently general? | `base`, `fiber`, Id and reflexivity are bundled with context structure; semantic-code indices quantify over the entire J-equipped model. | Compare a signature-independent core and constructor capabilities with a replacement foundation. |
| Is the requested pair already an object-language term? | Context extension exists, but the current generated fragment has no Sigma constructor. | Specify object-language Sigma versus a contextual package explicitly; neither can silently stand in for the other. |

“Additional required laws should come with additional structure” is a useful
design question, with three cases. Some laws follow from existing universal
properties and should be proved once. Some specify the meaning of a new
operation, including its computation and stability. Others constrain an
unchanged signature, such as an extensionality principle. Those stronger
capabilities need explicit scope and witnesses; they need not introduce new
operations. The goal is to expose the actual requirements of an argument, not
minimize or maximize the number of fields.

The [mathematical assessment](dependent-architecture-review/mathematical-structure.md)
proposed the display-map reconstruction now supplied by the audit. Its warning
about the choice of concrete family morphisms remains necessary: constructing
all-square fullness does not identify that category with every proposed
category of family maps.

## Revise the proposed separation

The implementation assessment identifies an existing coupling: raw judgments
carry semantic annotations quantified over the full current model interface.
Replacing an annotation by one with the same decoded meaning is not generally
valid. Requiring ordinary authors to reconcile those presentations is the
observed problem. A new record which asks callers for the same equalities would
leave it unresolved. Compare derived repairs, fixed templates, controlled
parametric arguments and a fresh judgment representation on the same capability.

Interpretation and change of presentation must be designed together. Type
comparisons determine how terms and dependent witnesses are transported; their
composition and constructor compatibility cannot be assigned unrelated proofs.
Likewise, “an argument in every model” is weaker than a uniform argument under
the intended model maps. The alternative-foundations assessment proposes a
Bool-symmetry rejection test for arbitrary classical selection and examines
generalized-algebraic uniform families as a possible bridge to initial syntax.
It does not claim that arbitrary Lean-polymorphic functions satisfy that bridge.

Changes of setting may also participate in judgments. Modal context operations
are one external stress case. The project's stronger internal-setting ambition
needs its own example: presentation data P varying over a base context, a
constructed setting S(P), and dependent reasoning in it. Constructing after
substitution must compare coherently with reindexing an already constructed
setting. External model instances and modal locks do not by themselves establish
this capability. This test can change the proposed boundaries before we freeze
them into modules.

Keep direct strict, local-universe and chosen-universe model constructions
eligible. Compare them on a needed model and fragment. A larger framework is
justified by a constructed capability or reusable theorem; satisfying its named
hypotheses alone is not the project goal. Conversely, research may recommend
replacing current syntax, equality judgments or semantic organization without
first supplying an adapter into the old representation. Adoption then needs
explicit mathematical recovery and migration evidence.

## Follow-up graph

The linked issues own live scope and completion status. Their scope bounds
the questions, not the research effort. The reviewed results above are from
the ongoing implementation of this graph; later experiments retain their
dependency and review gates.

| Issue | Discriminating outcome |
| --- | --- |
| [#314: structure, derived laws and foundations](https://github.com/VladimirMarko/conaled/issues/314) | Classify and construct missing consequences; distinguish independent assumptions, specialization and a need for replacement. |
| [#315: judgment representations](https://github.com/VladimirMarko/conaled/issues/315) | Compare repair with a boundary not indexed by the entire semantic model; construct interpretation and coherent comparisons. |
| [#316: dependent higher model](https://github.com/VladimirMarko/conaled/issues/316) | Connect the memo's dependent argument and elimination to the nontrivial second-identity observation. |
| [#319: internal setting construction](https://github.com/VladimirMarko/conaled/issues/319) | Construct a context-varying setting and dependent use with composable reindexing comparisons. |
| [#317: constructor admission](https://github.com/VladimirMarko/conaled/issues/317) | Derive compatibility for one dependent constructor extension and recover the specified old arguments. |
| [#318: concrete categorical hypotheses](https://github.com/VladimirMarko/conaled/issues/318) | Establish a model-construction benefit, then construct the exact categorical package it needs. |
| [#320: frozen interface trial](https://github.com/VladimirMarko/conaled/issues/320) | Compare ordinary author obligations on the same mathematical requirements after reviewed interface freezes. |

The structure audit should inform the judgment experiment's implementation.
External representation discovery, higher-model feasibility and the internal
setting test can proceed alongside that audit. Constructor admission uses an
explicit reviewed judgment contract; author dispatch waits for reviewed frozen
interfaces. The categorical-package task starts with a concrete-benefit decision
and proceeds to construction when that benefit is established.

#297 keeps the broader modal/higher comparison, with separate questions for
context restrictions and higher identities. #301 remains an external challenge
to the whole agenda, including the proposed responsibilities themselves. The
new work must not filter out a competing foundation because it lacks an easy
adapter or is absent from current modules.

#107's repair and #108's fresh theorem remain separately owned and gated. The
known public failures can inform these experiments without resuming the paused
repair or preparing the independent retest. #288 coordinates extension claims;
#290 coordinates author evidence; #36/#235 coordinate any resulting shared
architecture. No universal framework, default local-universes model or general
strictifier is adopted by this reassessment.
