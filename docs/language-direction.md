# A language whose mathematical setting is a first-class parameter

**Make the mathematical setting a first-class parameter of programming and
proof.** Authors should be able to express a construction or argument in
familiar mathematical language, identify the structure and principles it uses,
and reuse it in every setting that supplies them. This is a shared long-term
direction for categorical compilation and internal-language reasoning.

Agreed with the project owner on 2026-10-19. This document records the ambition
and the criteria by which to develop it. The language's architecture remains
open: checked work in both workstreams should progressively constrain its
shape. It is not a claim that the current library already provides this language.

## The author should be able to factor out the setting

Internal languages let mathematicians reason using familiar variables,
functions, constructions and logical arguments inside different mathematical
settings. Reusing that reasoning makes analogies visible. An author can
recognize that a construction only needs products, or that a proof uses
intuitionistic logic together with a particular differential principle, and
then extract that common requirement.

Our language should support that act of discovery. The author should work with
the mathematics, with the alterations that the chosen setting actually demands.
Routine manipulation of encoded syntax, variable indices, interpretation
wrappers and derivation trees should belong to the implementation. Making
those operations look prettier is insufficient if the author must still carry
the same bookkeeping through every argument.

The desired abstraction includes meaning and admissible reasoning. Functions,
equality and quantifiers may receive different interpretations in different
settings, while retaining the specified behavior that justifies a shared
argument. Semantic differences must remain expressible. Higher identity,
constructive existence and crisp-context restrictions cannot be erased merely
to make every setting look alike.

## Compilation and proof share this requirement

| Categorical compilation | Internal reasoning |
|---|---|
| A program uses particular operations. | A proof uses particular constructions and rules. |
| A target supplies the required operations and laws. | A setting validates the required constructions and principles. |
| Compilation interprets the program. | A model interprets the argument. |
| Preservation establishes the stated correctness contract. | Soundness establishes validity in that model. |
| Changing targets can preserve the program. | Changing settings can preserve the argument. |

The requirements belong to the reusable construction or proof. A selected
target or setting supplies evidence that it meets them. We want authors to be
able to state these requirements, tooling to help reveal them, and reusable
interpretations to discharge them. Inference or minimization of requirements
is a design question, not an assumption that every weakest requirement can be
computed automatically.

Changes of setting need their own preservation contracts. A result may
transport along one map of models but not another. The language should make
the reusable argument and the missing obligation visible without requiring
authors to reconstruct the semantics at each use.

This goes beyond sharing a parser or concrete notation between workstreams.
The common design problem is which constructions and reasoning principles can
be abstracted, how their requirements compose, and which interpretations
preserve them. Shared implementation should follow demonstrated commonality;
the two workstreams need not be forced into identical fragments.

## What remains open, and what guides the design

Lean can remain the host and trusted checker. Explicit syntax and derivations
are possible implementation mechanisms; they are not the intended ceiling on
the author's experience. A language hosted in Lean can still make its own
settings and judgments first-class. No decision to leave Lean, change its
kernel, or adopt a standalone surface language follows from this direction.

Lean's native axioms can express assumptions within its existing logic. They
do not replace its equality or kernel rules when a mathematical setting changes.
The broader capability requires checked interpretations of the supported
language. Existing proof-audit requirements remain in force, and ordinary Lean
clients must retain their direct interfaces without additional setup.

Use future compilation and internal-language work to answer concrete questions:

- Can the same construction or proof serve distinct settings with its required
  capabilities stated and satisfied, without duplicating the argument?
- Can an author recognize and extract a common abstraction without manipulating
  its representation as syntax throughout the proof?
- Does using an additional principle expose an additional requirement? Does a
  setting lacking it produce a precise obligation rather than silently importing
  a stronger ambient logic?
- Does a change of interpretation preserve the intended result through an
  explicit checked contract, including relevant equality and witness data?
- Which differences between settings are mathematically essential, and which
  recurring author obligations should the implementation absorb?

These are design tests for successive bounded developments, not a requirement
to build a universal language before delivering useful mathematics. Record what
each development teaches us about the language and revise proposed interfaces
accordingly. A small working fragment can be valuable while its author interface
remains below the long-term goal.

## Selecting research by semantic requirements

Agreed with the project owner on 2026-10-30: evaluate literature against the
language ambition above. Familiarity within this repository, citation counts,
and the number of published variants do not establish suitability. Compare a
tradition's semantic commitments and explanatory power before spending effort
comparing its algorithms. Existing integrations are evidence about particular
constructions, not a representative survey of the available mathematics.

Prefer compositional denotational accounts whose meaning is specified
independently of a chosen execution mechanism. Operational semantics can help
establish implementation correctness, adequacy and resource properties. Read
work presented operationally for useful mathematics, while asking which
independent semantic contract it supports. Neither popularity nor presentation
style alone settles that question.

Separate discovery, comparison and integration. Begin external discovery from
the ambition and required author capabilities before using the local inventory
to assess fit. Include approaches that might replace or subsume our architecture;
do not filter them out because they need a difficult Lean encoding or cannot
produce a small example immediately. Compare explicit assumptions, composition,
extension obligations, preserved equality and witnesses, and author effort.
Record omitted traditions and uncertainty. Propose discriminating experiments
that our current approach could fail, rather than only examples it already fits.
#235 owns this external comparison, coordinated with #36, #200 and #8.

The duality agenda in #266–#270 is promising but remains a set of hypotheses,
not a ranking established by an external comparison. Investigating variance,
inclusion, implication and explicit coercion evidence likewise does not commit
the language to global implicit subtyping. #257's evidence contracts remain
useful if the optional #260 elaborator is declined. Before activating #260,
compare explicit evidence and constraint-based alternatives on the same author
tasks, select the semantic algebra and preservation obligations, and record why
inference earns its additional assumptions. Experience with Java or Haskell
alone cannot decide the suitability of Dolan's algebra. Type-class encodings of
subtype relations do not establish a need for global value subsumption; see the
[video clarification](research/language-design-and-type-systems.md#the-supplied-video).

## Construction, observation and verified presentations

The constructor–destructor investigation adds a design test: where the laws
permit it, can authors change between constructor-oriented and observer-oriented
presentations without rewriting the underlying equations or losing their meaning?
Treat source organization as a candidate verified view, not an obligatory choice
of one universal intermediate language. Preserve ordinary clients and the
semantic distinctions of fragments that do not fit the same presentation.

Make the observation contract explicit when extending a language. Adding a
representation under an unchanged contract differs from adding an observer that
can distinguish previously equivalent representations. Old theorems remain
scoped to their stated assumptions and observations; stronger observations need
compatibility proofs, and may require a richer representation. New type
interpretations must meet their stated admissibility laws, and new operations
must supply the compatibility proofs needed to reuse existing client theorems.
Neither retaining old equations nor adding axioms alone establishes arbitrary
metatheorem preservation.

Investigate whether local construction/observation laws compose into reusable
semantic interpretations, and whether forward representation transport and
backward observation transport fit the existing preservation architecture.
Explore symmetric producer/consumer proof syntax while keeping logic, polarity,
evaluation order and their equality laws explicit. These are questions to test
against existing indexed and witness-sensitive examples, not commitments to a
Chu model, a distributive-law framework, a sequent calculus, or a fixed execution
strategy for every setting.

The [duality findings and agenda](research/duality-language-directions.md)
distinguish checked results, source theorems, design inferences and conjectures.
#256 supplies a bounded syntax transformation; it does not establish an
isomorphism between arbitrary data and codata, a generic semantic lifting, or
infinite productivity. Scoped follow-ups are #266–#270, coordinated with #262
and the existing #235/#36/#200/#8 owners.

## Evolving preservation laws and usable specializations

The [preservation inventory](research/preservation-contract-inventory.md) is a
revisable set of architectural tests. New clients may expose missing judgments,
comparison data or composition laws. When a client does not fit, retain its
native contract and identify the mismatch: an additional assumption, a missing
adapter, a new compatible layer or an existing interface that needs revision.
Track unresolved work with a scoped owner. The initial examples do not define
the limit of the family, and recording a gap does not resolve it.

A justified expansion may require retrofitting foundations and existing
consumers. Evaluate that change against both the new client and prior concrete
specializations. Recover the prior guarantees under the same assumptions,
including witnesses and observations. Use checked migrations or specialized
facades when interfaces change. Keep executable and resource claims explicit;
semantic preservation alone does not establish implementation performance.

Generality must remain usable by authors and agents. Compare direct/native
and shared/specialized solutions to the same representative tasks. Record the
concepts and obligations the author must supply, internal wrappers or casts,
diagnostics, assistance and successful completion. Preserve familiar concrete
operations where they suffice; authors should not need unrelated structures
or the entire framework to use a specialization. Checked examples establish
meaning, while independent author trials test whether the public interface and
documentation expose that meaning effectively. Agent trials are evidence about
those trials, not a claim of usability for every human author.

[#235](https://github.com/VladimirMarko/conaled/issues/235) owns continued
compatibility, retrofits and specialization usability within
[#200](https://github.com/VladimirMarko/conaled/issues/200), coordinated with
#36's models and #8's categorical foundations. The bounded
[#231](https://github.com/VladimirMarko/conaled/issues/231) experiment must hand
off its applicability findings and remaining work there. Revisit the record
when new families or author difficulties appear and at experiment completion.
Closing one experiment does not close the architectural programme; any successor
must retain explicit ownership of unresolved work.

## Elegance, author capability and language constraints

Evaluate mathematical structure, its encoding in Lean, and the experience of
using that encoding separately. An elegant construction can have an awkward
host-language realization; concise Lean code can also conceal restrictive
assumptions. Record the layer responsible for a difficulty and the evidence for
that diagnosis. Distinguish missing mathematical structure, interface design,
documentation, language expressiveness, elaboration behavior and author
capability. A failed attempt alone establishes neither a language limitation
nor the impossibility of a practical encoding.

Author trials measure effectiveness for recorded authors, tasks and tools.
Retain model/version, configuration and resource budget, available documentation,
Lean/toolchain revision, assistance, attempts and outcomes. Record unavailable
metadata explicitly. Agent capability can change with newer models or the
choice of cheaper workers. Separate present adoption cost from mathematical
quality and long-term generality; difficulty for a current agent is evidence
to investigate, not by itself grounds to reject an elegant design. Near-term
usability still matters when selecting a practical implementation.

Prefer useful specializations of shared constructions over disconnected levels
of interface sophistication. A specialization should discharge recurring
requirements, infer routine structure or supply a common interpretation; its
guarantees should follow from the general laws. Preserve the concrete client's
capabilities and assumptions, shared vocabulary, and a path to the general
interface. Compare wrapper and conversion costs as well as convenience: several
interfaces can fragment use and undermine the value of a common abstraction.
Elegance and ease of use need not conflict, but record the trade-off when they do.

Revisit abstractions when new consumers expose missing laws, stronger assumptions,
repeated adapter work or author difficulties, and when language/tooling or author
capabilities change. At workstream planning checkpoints, also reconsider promising
alternatives that individual tasks may not surface. #235 owns this reassessment;
these checkpoints do not create a scheduled automation. Preserve prior evidence
and compare unchanged tasks where possible so improvements in a model, toolchain
and design are not conflated.

A proposed replacement should identify the benefit, migration and refactoring
cost, affected consumers, and checked recovery of established specializations.
Small fixes to documentation or inference may suffice; a deeper redesign may be
worth its cost. Neither current usability nor mathematical elegance alone settles
that choice. Record decisions and remaining constraints without treating a
current Lean encoding as the limit of the mathematical direction.

## Current evidence and ownership

The [preservation architecture assessment](research/preservation-architecture.md)
records a first bounded comparison of direct and shared author routes. Existing
indexed certificates hide dependent equality bookkeeping while preserving the
result type; a simple effect bound remains shorter through its native invariant.
Keep both interfaces available. These checked examples and agent trials inform
specialization design without establishing general human usability or a single
interface for all preservation families.

The [toolkit author trials](research/toolkit-author-effectiveness.md) extend
that evidence to an established DList client and a new reverse-list realization.
Two independent authors retained full sequence and ordered-summary contracts
through direct and shared routes. The record separates successful specialization,
local normalization and audit-harness repairs, and defines #235's repeatable
reassessment protocol without inferring a capability trend from one configuration.

The existing [compiler](../Compiler.lean) and
[first-order compiler](../FirstOrder.lean) provide target-dependent compilation
interfaces. The [internal graph proof](../SquareKit/Internal/Graph.lean) and
[synthetic scalar proofs](../SquareKit/Internal/SyntheticScalar.lean) provide
restricted derivations. The [geometric product rule](../SquareKit/GeometricProductRule.lean)
connects a source derivation to model mathematics. These are sources of design
constraints and checked examples, not evidence that arbitrary Lean arguments
already transport across settings.

[#36](https://github.com/VladimirMarko/conaled/issues/36) owns the constructed
internal-language/model objective. The [internal-language research record](research/internal-languages-lean.md)
tracks its interfaces and evidence. The [compilation extension agenda](extensions.md)
and broader [Felix workstream](https://github.com/VladimirMarko/conaled/issues/8)
supply the other side of this shared direction. Keep scoped acceptance criteria
in GitHub Issues; this document establishes the direction against which those
choices should be assessed, without prescribing a speculative implementation
sequence.

The [2026-10-24 language architecture research](research/language-architecture-research.md)
records the owner's constraints for continued embedded development, the proposed
`slean` dialect and multiple surfaces, Agda reuse, Lean self-modeling, and
composable internal settings. It investigates semantic contracts and low-cost
design tests without selecting a replacement implementation or fixed pipeline.

Landin's [*The Next 700 Programming Languages*](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/landin-next-700.pdf)
separates a common expressive framework from choices of abstract entities and
primitives. The project's ambition extends that separation to the structure
and logical principles supporting programming and proof. This is our design
direction, not a claim that Landin specified the proposed language.
