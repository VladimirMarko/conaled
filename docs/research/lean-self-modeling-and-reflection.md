# Lean self-modeling, denotation, and reflection

Research date: 2026-10-24. This note supports continued development of the
embedded language in Lean. It proposes distinctions and research obligations,
not a replacement implementation or a new architecture decision.

Modeling Lean syntax and typing in Lean is possible. The difficult boundary is
a uniform internal justification that every theorem of the full host theory is
true in its intended interpretation. A commuting-square contract should state
which side of that boundary it needs.

## What the Lean target comprises

Lean's documentation calls the elaborator's destination its **core type
theory**. Kernel checking validates declarations in that theory; compilation
to an executable is a later, separate operation. Our proposed proof-producing
backend targets core declarations, rather than the runtime compiler's
intermediate language. [Lean processing pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)

The implementation type `Lean.Expr` represents expressions used by both the
elaborator and kernel. It also admits metavariables, which must be absent from
kernel input. An expression alone does not supply its constants' definitions,
universe declarations, or typing justification. Consequently a target contract
must account for the environment as well as the emitted expression.
[Lean expression definition](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)

For this project, distinguish these proposed components:

| Component | Required contract |
| --- | --- |
| Target syntax and declarations | Representation of the selected Lean fragment, including its environment and levels. |
| Target judgments | Declarative typing, conversion, and permitted declaration extensions. |
| Target checking algorithm | Acceptance implies the target judgment, with explicit termination or fuel behavior. |
| Target denotation | A mathematical interpretation validating the selected judgments under stated model assumptions. |
| Emission into installed Lean | Correspondence between represented declarations and actual kernel input. |
| Source compilation | Preservation of source meaning by the denotation of the generated target. |

These contracts can be developed separately. Defining an AST does not establish
its denotation. Proving a checker follows typing rules does not establish that
the rules have a model. Kernel acceptance establishes a theorem of the host,
but does not establish that an exporter preserved the intended source statement.

## Existing self-modeling evidence

Carneiro's Lean4Lean paper implements a Lean checker in Lean and separates an
abstract type theory from its implementation. Its published 2024 account reports
partial progress on the metatheory; it is not a completed proof that the entire
Lean implementation proves its own consistency. It also explains why changes
from Lean 3 to Lean 4 matter to an earlier consistency argument. We should reuse
its distinctions and investigate its definitions before designing a second
formalization of Lean's target rules.
[Lean4Lean paper, §§1–3](https://arxiv.org/html/2403.14064v1)

The current Lean4Lean repository separates the checker library, theory, and
verification build targets. Its README also warns that the checker derives from
the C++ implementation and may share implementation bugs. That is evidence for
available infrastructure, not independent validation of every desired theorem.
[Lean4Lean repository](https://github.com/digama0/lean4lean)

The current ConLeche project gives an especially useful example of **relative
semantic soundness**. Its `model_exists` theorem takes a set-theory structure as
an explicit hypothesis and concludes that an accepted environment has a model.
Its rejection theorem for declarations of `False` retains that hypothesis.
Reading the theorem's parameters changes the interpretation of the repository's
short description of a consistency proof.
[ConLeche theorem statements](https://raw.githubusercontent.com/leanprover/con-leche/master/ConLeche/MainTheorem.lean)

The required `SetTheory` interface includes an omega-chain of Grothendieck
universes, together with set-theoretic operations and axioms. The model's
existence is therefore not an assumption-free consequence of implementing the
checker in Lean. The interface is a useful example of how to expose semantic
requirements in a commuting-square backend.
[ConLeche set-theory interface](https://raw.githubusercontent.com/leanprover/con-leche/master/ConLeche/SetTheory/Core.lean)

These are source inspections. This research did not build or audit those
projects, establish their compatibility with this repository's pinned Lean
version, or select either as a dependency. Links to moving repository branches
describe the inspected state, not a versioned compatibility promise.

## The precise Löb boundary

Write `□φ` for the chosen arithmetized assertion that theory `T` proves `φ`.
Assume sufficient coding and diagonalization, and the Hilbert–Bernays–Löb
conditions:

1. If `T ⊢ φ`, then `T ⊢ □φ`.
2. `T ⊢ □(φ → ψ) → (□φ → □ψ)`.
3. `T ⊢ □φ → □□φ`.

Löb's theorem states that `T ⊢ □φ → φ` implies `T ⊢ φ`. With `φ = ⊥`, a
consistent such `T` cannot prove `□⊥ → ⊥`, its corresponding consistency
statement. Applicability depends on the encoded theory and provability
predicate; an arbitrary operation called a modality does not satisfy these
conditions automatically. Bailitis supplies mechanized treatments and discusses
the predicate assumptions explicitly.
[Bailitis, Chapters 5–6](https://www.ps.uni-saarland.de/~bailitis/bachelor/Bailitis_thesis.pdf)

Applied to our design, this rules out requiring a consistent host to prove
unrestricted reflection for its own faithfully encoded full proof theory under
those hypotheses. It does **not** rule out proving a source fragment sound,
proving checker correctness relative to derivability, or proving soundness
conditional on an external model. We have not formalized an arithmetization of
the repository's precise Lean foundation or verified the derivability
conditions for it; this is a design constraint from the general theorem.

A related distinction concerns truth. A full self-applicable truth predicate
with unrestricted disquotation encounters the diagonal obstruction discussed
in the same thesis's treatment of Tarski's theorem. A satisfaction relation for
a specified object language in a specified model has a different scope. Our
denotation interfaces should identify that object language and model explicitly.
[Bailitis, §5.2.1](https://www.ps.uni-saarland.de/~bailitis/bachelor/Bailitis_thesis.pdf)

Nor should we claim that all self-interpreters are impossible. Gross's
dependently typed treatment of Löb explains why representation details matter:
syntax for object types, terms indexed by those types, quotation, and evaluation
place different demands on a system than terms indexed directly by host types.
It discusses the latter distinction in connection with a self-interpreter for
System F-omega. That observation prevents using the word “self-interpreter”
alone as a proof of impossibility or safety.
[Gross, discussion following the first interpreter](https://people.csail.mit.edu/jgross/personal-website/papers/lob-paper/html/lob.html)

## Universe stratification and finite fragments

Lean has `Type u : Type (u + 1)`. Universe parameters are handled at the
declaration level; a universe-polymorphic definition is not a value ranging over
all host universes in one enclosing `Type`. Lean's universes also are not
cumulative. These details matter when arranging an interpreter's object and
host levels.
[Lean universe reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)

Our proposed design consequence is to distinguish three questions:

- Can a particular bounded target fragment be interpreted in a sufficiently
  large host universe?
- Can the same construction be instantiated at each chosen level?
- Can one internal object contain the entire host hierarchy, including the
  interpretation and truth principles needed to justify itself?

The first two do not provide the third. Encoding level expressions as finite
syntax is straightforward in principle; decoding every such code into the
corresponding native host universe with one unrestricted evaluator is a further
claim. A level shift can support a particular interpretation without supplying
unrestricted self-reflection. Conversely, a finite source file is not
automatically a weak fragment: its universe-polymorphic declarations and
accepted axioms must be included in the analysis.

For our embedded language, recording source and model universe requirements
would make finite layers composable without claiming a single universal model
of all layers. Whether a proposed fragment admits such a model remains a
mathematical obligation, especially for impredicative propositions, inductives,
quotients, and the interaction of conversion rules.

## Commuting-square obligations for this repository

The existing shared direction explicitly permits Lean as host and trusted
checker while making mathematical settings parameters. Existing local examples
interpret restricted internal derivations into model mathematics:
`SquareKit/Internal/Graph.lean` applies `sound` in a selected model, and
`SquareKit/GeometricProductRule.lean` applies `GeometricSem.slope_sound`. These
are bounded examples of the desired separation, not models of Lean's full core.
[Language direction](../language-direction.md),
[graph application](../../SquareKit/Internal/Graph.lean),
[geometric product rule](../../SquareKit/GeometricProductRule.lean)

For a proposed target fragment `K`, source `S`, model `M`, and compiler `C`, a
research contract could have the schematic shape

```text
meaningK M (C term) ≈ meaningS M term
```

The relation `≈` must be selected for the intended semantics. This contract
needs meanings for the image of `C` and a correspondence with emitted Lean
declarations. It does not require an unrestricted truth predicate for every
theorem available to the host. A universal model of full Lean would be a much
stronger deliverable than the square itself requires.

The repository already distinguishes exact and relational preservation in
[ADR 0002](../adr/0002-relations-and-synchronization.md). That permits a target
contract to state a logical relation or observation property where equality of
denotations would be inappropriate. Choosing a weaker observation still needs
justification against the source language's intended mathematical distinctions.

The next research deliverable should specify the smallest target fragment
covering existing embedded proofs, its environment assumptions, and the exact
semantic theorem needed for one current square. Compare that specification with
Lean4Lean and ConLeche before committing to infrastructure. Continue the
embedded-language work while this question is investigated.

Two checks should accompany any later extension:

- **Composition:** Which translation preserves the premises needed by the next
  interpretation? Which universe shift or model assumption does it introduce?
- **Return:** Does a result obtained in the target entail the intended source
  proposition? Forward preservation alone supplies no general reflection map.

An interpretation graph may contain many valid finite paths. A cycle of
translations does not by itself certify reflection, conservativity, or the
host's consistency. Those require their own statements and proofs.
