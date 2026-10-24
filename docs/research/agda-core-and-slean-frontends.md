# Agda core and possible slean frontends

Research record, 2026-10-24. This investigates Agda import and LLM authoring
without replacing the existing Lean-embedded language. `slean` is the owner's
proposed name for a Lean-like surface, with the successor-of-Lean pun. Neither
its semantics nor a single preferred surface has been selected.

The [shared language direction](../language-direction.md) remains the goal:
factor out the mathematical setting and expose the principles a proof needs.
The [existing transfer interface](agda-transfer-interface.md) supports a
restricted proof fragment and no Agda frontend. An importer would be an
additional producer of checked objects, not a prerequisite for continuing that
development.

## Which Agda core can preserve the mathematics?

Agda's documented stages distinguish concrete syntax, scoped/desugared
abstract syntax, typechecked internal syntax, and treeless syntax for execution
backends. Instance resolution and constructor disambiguation happen during
typechecking. Letting Agda perform these tasks avoids reproducing its surface
elaboration. The appropriate candidate boundary for proof transfer is
**internal syntax before conversion to treeless**.
[Agda 2.8.0 core-language documentation](https://agda.readthedocs.io/en/v2.8.0/language/core-language.html)

Treeless is unsuitable as the sole proof interchange format. Its `TTerm` has
`TErased`, `TSort`, and `TUnit` (used for levels), and lacks dependent function
types. It targets execution and explicitly distinguishes evaluation strategies
for erasure. Recovering the original dependent judgments from this representation
would require additional information.
[Agda 2.8.0 treeless syntax](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Syntax/Treeless.hs)

Internal syntax retains dependent `Pi`, sort and level expressions, constructor
and definition references, and elimination spines. Types have sort annotations;
sorts include ordinary universes and special interval, size, and level sorts.
Its domains retain modality information and the distinction for partial types.
However, `MetaV`, `DontCare`, and internal dummy forms also exist. The Haskell
datatype is not itself a certificate that an arbitrary value is a completed,
valid declaration. Nor should source distinctions already ignored by Agda's
irrelevance rules be assumed recoverable.
[Agda 2.8.0 internal syntax](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Syntax/Internal.hs)

A term alone is insufficient. Agda's `Interface` includes a signature,
imported-module hashes, metavariable bindings, builtins, options used during
checking, partial definitions, and opaque-block information. `Defn` distinguishes
postulates, functions, data, records, constructors, and primitives. Rewrite
rules belong to the signature. These structures show why an export must account
for the declaration environment rather than serialize just term constructors.
An interface can also be associated with a scope-check-only mode, which must
not be mistaken for completed typechecking.
[Agda 2.8.0 checking state](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/TypeChecking/Monad/Base.hs)

The following are proposed export obligations, not claims of an implemented
format:

| Information | Why the bridge needs it |
|---|---|
| Declaration types, bodies, inductive declarations and dependencies | Reconstruct the source judgment and the rules its proof uses. |
| Universe expressions and constraints | Avoid silently replacing polymorphism by an unsuitable fixed universe. |
| Relevance, quantity and modal restrictions | Preserve which uses of variables are legal. |
| Builtins, reduction rules and source options | Identify the conversion and elimination principles used by checking. |
| Assumptions and unsupported features | Expose requirements instead of accepting an external verdict as a Lean proof. |
| Source names, locations and version manifest | Review correspondence to the intended source declaration. |

Cubical code particularly needs its primitive meanings: interval/path types,
transport, homogeneous composition, Glue and higher inductive constructions.
The compiler's internal representation does not make these ordinary Lean
equality. A supported interpretation must validate the rules used by the
source fragment. The Agda documentation gives the primitive inventory and the
distinction between cubical and erased-cubical modes.
[Cubical Agda documentation](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html)

User rewrite rules are another semantic obligation: they extend Agda's
evaluation relation and can make a reflexivity proof check where ordinary
pattern-matching computation would not. An importer must preserve the relevant
conversion or insert justified propositional steps; retaining the surface word
`refl` does not establish this.
[Agda rewriting](https://agda.readthedocs.io/en/v2.8.0/language/rewriting.html)

**Assessment:** ordinary desugaring is not evidence of lost logical expressive
power. Internal syntax plus its checking environment is a plausible input for
preserving supported Agda judgments. This inspection does not establish a
complete export, a stable public interchange API, or lossless recovery of every
author-level distinction. Runtime erasure is a separate, demonstrably unsuitable
boundary for that purpose. Pin the exporter to an Agda revision and define our
own small, reviewed interchange schema if this path is pursued.

There is also a project-specific distinction. A source proof may specialize
an argument to concrete operations even though it could have been generalized
to fewer assumptions. Exporting a checked term preserves that specialization;
it does not automatically recover the author's intended generality. Keeping
source structure and explicit capability parameters can help subsequent
generalization. We should not confuse loss of that information with loss of
the validity of the original theorem.

## Superficial translation into slean

Treat superficial translation as an acceptance criterion for chosen source
libraries: keep definitions, theorem statements, dependency structure, and
proof strategy; allow mechanical notation changes, qualification, and module
adaptation. Count every required change of mathematical argument as a failure
of that criterion for the tested fragment.

This requires more than a Lean-like parser. The receiving judgment must support
the source's universe behavior, identity/elimination rules and conversion
principles, or provide an interpretation that preserves them. A library that
depends on cubical paths cannot meet this criterion through a change of
punctuation to native Lean equality. A slean surface over an embedded calculus
could retain those distinctions, subject to the calculus and model actually
supporting them. This is a design inference from the source-rule inventory
above, not an existing compiler result.

Several surfaces can share a fragment and its interpretation: current Lean
constructors/combinators, an Agda-like form, a slean form, and eventually an
Agda-internal importer. Each should expose its supported judgments and any
additional elaboration obligations. Sharing does not require every frontend to
support every fragment, nor require all translations to pass through one
mandatory intermediate language.

## What LLM studies establish

The evidence supports testing familiar surfaces without training. It does not
establish that a Lean dialect will work well, or that a novel dialect necessarily
causes confusion. No source examined here directly compares Lean/Agda with a
nearby dialect whose logical rules change while mathematical tasks stay fixed.

| Primary study | Evidence and limits for this project |
|---|---|
| [Bogin et al., NAACL 2024](https://aclanthology.org/2024.naacl-long.279.pdf) | Code-like output and structured domain descriptions improve in-context semantic parsing. Language-variation experiments suggest resemblance to general-purpose code matters, beyond corpus prevalence. Tasks are semantic parsing, not dependent proofs. |
| [Patel et al., NAACL 2024](https://aclanthology.org/2024.naacl-long.161.pdf) | Models can use novel libraries from descriptions or implementations, and show some ability to learn a language in context. Restricting generation to prescribed library functions can hurt. This cautions against assuming a smaller allowed vocabulary always helps. |
| [Anka, 2025 preprint](https://arxiv.org/html/2512.23214v1) | Reports successful prompt-only use of a new constrained DSL for data pipelines. Its narrow benchmark and two evaluated models do not establish proof-language viability. It supplies a counterexample to the universal claim that new syntax requires training. |
| [Kumar et al., PyLang, 2026](https://arxiv.org/html/2605.15607v2) | Familiar C/JavaScript-like syntax does not eliminate implementation errors. PyLang deliberately removes high-level constructs and the standard library; the comparison therefore changes available abstractions as well as familiarity. Its failures do not isolate a dialect-confusion effect. Training interventions also fail to close the reported gap, so training is not a guaranteed remedy. |
| [Sharma et al., 2026 preprint](https://arxiv.org/html/2606.10933v1) | Agents use generators written in familiar languages to produce unfamiliar esolang programs. Disallowing generators hurts strong agents; executable helper libraries help some weaker agents more than textual strategy advice. These are existing esolangs, with uncertain prior exposure, not newly invented proof dialects. |
| [Sun et al., Clover, 2024](https://theory.stanford.edu/~barrett/pubs/SSP%2B24.pdf) | In textbook Dafny generation tasks, compiler/verifier feedback and repeated attempts improve outcomes. Dafny is an existing language, so this supports testing feedback loops, not assuming they solve unseen-language acquisition. |

Our working hypothesis should be that familiar binding, application, declaration
and proof idioms reduce adaptation effort when the underlying operations remain
available. A competing hypothesis is that familiar notation invites invalid
Lean or Agda assumptions when equality, universes or modalities differ. Both
need measurement. Marking the selected setting explicitly and making errors
explain the missing rule are proposed mitigations, not results established by
the papers.

## Experiments before an importer

These are proposed bounded investigations; none was run for this note.

1. **Audit representation, without translating proofs.** Select a small set of
   declarations from a pinned target library covering dependent identity,
   universe parameters, a pattern match, and any required modality or cubical
   feature. Inspect the corresponding internal declaration and environment.
   Record exactly where each needed rule and assumption survives. Stop with an
   export-field inventory and counterexamples, not a new backend.
2. **Measure superficial translation on paper.** Put the same declarations into
   candidate slean and Agda-like notation. Classify edits as notation,
   elaboration assistance, explicit requirements, or changed mathematics.
   Review denotations before implementing either parser. This can disqualify a
   proposed design without constructing import infrastructure.
3. **Compare authoring surfaces on an existing supported fragment.** Use the
   current embedded interface as the baseline. If a candidate surface has a
   small elaborator into that same fragment, compare matched tasks with equal
   documentation, examples and budgets. Until it does, source-review results
   are only syntax/usability evidence, not checked proof success.
4. **Separate direct generation from assisted generation.** Compare a concise
   language reference, checked demonstrations, compiler feedback, and reusable
   helper code. Hold theorem statements and allowed assumptions fixed. Record
   first-attempt acceptance, eventual acceptance, semantic mistakes, human
   intervention, tokens and elapsed time. Include negative tasks where familiar
   Lean reasoning is unavailable in the selected setting.

The immediate deliverables can therefore be an information-retention table, a
translation-diff corpus, and an authoring comparison. The embedded development
can continue while these expose whether a full Agda importer or a particular
slean surface would repay its cost.
