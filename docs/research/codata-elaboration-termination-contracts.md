# Codata, termination certificates and elaboration contracts

Research on 2026-10-25 at repository baseline
`83c1fcb87f10bc2e1c13aba2a85105adc738d994`. This note proposes contracts and
mathematical test cases. It does not add checked theorems or implement a checker.

The owner approved further research and formalization of the finite-prefix
counterexample. Immediate laziness and arbitrary codata are not required.
The architectural requirement is to avoid assumptions that would prevent
supporting them later. The termination/productivity and elaboration contracts
below are approved bounded next steps, independent of a complete lazy runtime.

The project can represent infinite objects without extending Lean's kernel.
It still needs to specify which finite observations can be computed, which
source constructions preserve that property, and which interpretations retain
it. The existing relational-square machinery can express these contracts;
there is no existing general termination/productivity checker or declarative
elaboration specification in the inspected language modules.

## Existing local foundations

[Languages/Machines.lean](../../Applications/Languages/Machines.lean) already
uses a state coalgebra: `Machine.nullable` and `Machine.next` generate observations
of a language. `Machine.unfold` builds a depth-indexed trie by finite recursion.
`Machine.lookup_unfold` relates each sufficiently deep observation to
`Machine.run`; `Machine.run_correct` proves membership correctness for every
finite word. `Machine.intersection_correct` composes machine obligations.
This is a concrete example of infinite behavior presented through all finite
observations. The individual bounded trie is not an infinite materialized tree.

[FRP/Trace.lean](../../Applications/FRP/Trace.lean) models input streams as
`Source → Nat → Message`. Its `eventual_observation` theorem requires both fair
processing of available prefixes and source progress that eventually supplies
a closing prefix. Its safety square alone does not prove either hypothesis.
[FRP/Spec.lean](../../Applications/FRP/Spec.lean) uses total mathematical
behaviors `ℝ → α` and events with finite past support; its comments explicitly
separate those from online realizability.

[Relations.lean](../../SquareKit/Relations.lean) provides preservation,
composition and relation-witness spaces. The indexed membership construction in
[Optimization/Relations.lean](../../Applications/Optimization/Relations.lean)
shows how to retain the input problem while interpreting a successful output
as membership in a set of admissible results. These are reusable foundations
for the contracts below, alongside the
[optimization specification](compositional-optimization.md). None supplies
termination evidence merely because a semantic square commutes.

## What Lean and Agda provide

The pinned Mathlib defines `Stream' α := Nat → α`, with `map`, `zip`, `iterate`
and `corec`. A coalgebra step `S → A × S` therefore gives a stream through
finite iteration. This supplies mathematical infinite streams and executable
observations when the step and initial state are executable. Arbitrary Lean
functions may be noncomputable; the function type alone is not an extraction
or resource guarantee. The representation also does not promise sharing of
successive observations. [Pinned Mathlib stream source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Stream/Defs.lean)

Lean's `coinductive` and `coinductive_fixpoint` support `Prop`-valued predicates,
such as bisimulation, rather than native coinductive data in `Type`.
`partial_fixpoint` constructs fixed points of monotone operations on suitable
orders. Its existence/equational results do not establish termination of a
runtime implementation. In particular, a tail-recursive definition into an
inhabited type may have underspecified values on diverging inputs. Avoid using
that total mathematical value to infer successful runtime evaluation.
[Lean recursive-definition reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)

The versioned reference URL was unavailable during research. The installed
v4.35.0 source confirms that the coinductive fixpoint case rejects non-predicate
results and distinguishes the partial fixpoint mechanism.
[Pinned elaborator source](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean)

Agda 2.8 provides coinductive records and copatterns for streams under
`--guardedness`. Its documentation demonstrates stream operations and a
bisimulation proof. Constructor syntax on a coinductive record does not itself
count as a guard, which matters for superficially similar source translations.
[Agda coinduction](https://agda.readthedocs.io/en/v2.8.0/language/coinduction.html)

Sized types expose observation depth across function boundaries, permitting
compositions that a syntactic guard check misses. Agda's language-tree example
is closely related to our language machines. However, Agda 2.8 explicitly
excludes `--sized-types` from `--safe` because checks against inconsistent uses
are missing. The semantic idea is useful; accepting an imported sized
certificate requires our own justified rules and audit of the source mode.
[Sized types](https://agda.readthedocs.io/en/v2.8.0/language/sized-types.html),
[Safe Agda](https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html)

## Codata under a change of setting

Streams are necessarily infinite sequences. A colist may end after finitely
many outputs; a partial or delayed producer may instead fail to deliver a
next observation. Ending, delaying and diverging require distinct observations
when the intended semantics distinguishes them. Unrestricted filtering can
fail to deliver a first element even when its input is a total infinite stream.
Changing its target to a possibly finite colist alone does not make the end of
a fruitless infinite search decidable.

A geometric inverse image preserves finite limits and, as a left adjoint,
existing colimits. It need not preserve exponentials or countable products.
Therefore a transported coalgebra for `A × -` is not automatically a final
coalgebra. In settings where streams are represented by `A^N`, the comparison
`f*(A^N) → (f*A)^(f*N)` needs a preservation theorem, not just a name for its
source and target. Slice pullback functors enjoy stronger preservation than
arbitrary geometric inverse images, so success in our fixed-slice experiments
cannot discharge this general requirement.
[Van Oosten's topos notes](https://ncatlab.org/nlab/files/vanOosten-ToposTheory.pdf),
[Hemelaer and Rogers, Proposition 3](https://link.springer.com/article/10.1007/s10485-020-09626-6)

Here is a mathematical counterexample specific to streams, not a checked local
formalization. Let `X = {0,1}^N` with the product topology and take the constant
sheaf inverse image `Δ : Set → Sh(X)`. A section of `Δ({0,1}^N)` is a locally
constant map into the set of bit sequences with discrete topology. A section
of the countable product of `Δ{0,1}` is a family of locally constant bit-valued
maps. The coordinate projections on `X` form such a family. Their assembled
map is the identity on the underlying set of `X`, which is not locally constant:
no basic open neighborhood fixes every coordinate. Thus this family is not
in the image of the stream comparison on global sections. Finite products
are preserved, but the full stream object is not. Since `ΔN` is a coproduct
of copies of the terminal object, the product is also the exponential by `ΔN`.

This suggests an early test: prove transport for every finite prefix, then
exhibit the missing condition needed to reconstruct a full transported stream.
Do not silently promote prefix preservation to preservation of finality.
A backend may instead provide a comparison into its own stream object and
prove precisely the observational properties needed by consumers.

## Separate the properties being certified

| Property | Proposed meaning |
|---|---|
| Runtime termination | For a specified input and evaluation strategy, evaluation reaches a value in finitely many steps. |
| Totality on a domain | Every input satisfying a precondition terminates with a related result. |
| Productivity | Every permitted finite observation of a produced object is delivered after finite computation, with any required environmental progress stated. |
| Causality | Agreement on specified input prefixes implies agreement on output prefixes. This does not itself bound runtime or ensure progress. |
| Normalization for conversion | The selected reduction/conversion procedure has the required termination and correctness properties on its specified fragment. |
| Checker termination | The algorithm searching for certificates returns. This is independent of whether the checked program terminates. |

These are proposed distinctions for this project, not claims that all source
languages use those words identically. An infinite stream need never finish
producing. The relevant termination questions concern its finite observations.

For a selected operational semantics, define `Evaluates(p,x,v)` declaratively.
A certifying analysis returns evidence for
`∀ x, Pre x → ∃ v, Evaluates(p,x,v) ∧ Post x v`, or a certificate that a small
checker validates to establish that proposition. Well-founded descent is one
certificate format, not the definition of termination itself. To cover
nondeterministic execution, specify whether all permitted executions must
terminate; existence of one evaluation is weaker.

The analysis result should distinguish `certified evidence`, `unknown`, and
`refuted counterevidence` when supported. Exhausted fuel, failed synthesis or
an unsupported recursive pattern means unknown, not nontermination. A checker
can be total by bounding search without pretending to decide all totality
questions. Completeness claims must name a restricted syntax, certificate
language or supplied-annotation discipline.

For codata, use an observation specification `Obs(p,input,n)` for the first
`n` outputs, and prove finite delivery plus compatibility as `n` increases.
A state-based implementation additionally needs an invariant and an observation
simulation. Bisimulation can prove equality of infinite behaviors; a weak
simulation that permits unlimited silent steps does not alone prove delivery.
Include a decreasing stuttering measure, a finite-step bound, or a separate
progress argument when silent steps are permitted.

The compositional obligation for sequential programs is that the first
component's postcondition supplies the second component's termination domain.
For stream processors, a useful interface gives a finite input-demand function
`d(n)` and a finite computation bound for producing `n` outputs. Demand maps
compose by substitution: a downstream demand `d_g(n)` requires upstream input
`d_f(d_g(n))`. This is a proposed sufficient condition, not a requirement that
all productive processors admit a uniform input-independent bound. Adaptive
processors may need a demand relation depending on observed values.

An optimizer must preserve this operational observation contract when
productivity is required. Equality of abstract streams or equality of returned
values conditional on returning is insufficient. The same issue applies to
termination: an implementation can agree on every result it returns and still
diverge on an input where the original returns. This extends the project's
existing distinction between value preservation and resource preservation.

## A declarative specification of elaboration

A useful semantic output is the set of admissible elaborations of a surface
phrase in its declared environment and context. Propose a relation of the form

```text
Elaborates(Δ, Γ, surface, expectedType?, Δ', core, inferredType, requirements)
```

It must establish well-formed environment extension, scoping, target typing,
and the intended meaning of the source constructs. Typing alone does not prove
that a syntactically valid output represents the intended input. The relation
can retain implicit arguments, coercions and overloaded choices when those
choices affect meaning.

During elaboration, unresolved metavariables and universe variables belong to
an explicit constraint context. An intermediate result specifies the valid
solutions to its constraints; later stages refine this set while preserving
its interpretation. A final accepted declaration supplies a solution and closes
all required obligations. Unsolved constraints must not be quietly replaced
by axioms. Soundness, completeness for a chosen fragment, termination of search,
and diagnostics are separate contracts.

Relational composition expresses admissible intermediate translations without
requiring a unique result. To compose under binders and across dependent
declarations, prove weakening, substitution and environment-extension
compatibility. If two successful elaborations must mean the same thing, prove
coherence under explicit resolution policies. Otherwise retain intentional
ambiguity or reject it. Kernel acceptance alone establishes neither this
coherence nor source fidelity.

Bidirectional typing is a suitable starting discipline: checking against an
expected type and synthesizing a type divide the annotation burden. It does
not guarantee decidability or completeness for every dependent feature.
[Dunfield and Krishnaswami's survey](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/)

Retain generated code and computational witnesses in data-bearing types.
The fact that admissibility is a proposition does not make the elaborated
program, a selected dependent pair witness or a stream state erasable. This is
the same distinction recorded by the project's relation-witness construction.

## Small tests that can change the design

These are proposed experiments, independent of existing application priorities.

1. **Total stream corecursion.** Encode a state step and compare the coalgebra
   interpretation, `Nat → A` observations and an explicit stateful realization.
   Prove compatibility for every finite observation. Add `map`, `zip` and a
   prefix `scan`, carrying termination assumptions for element operations.
2. **Selective output.** Filtering the constant-zero stream for positive
   elements cannot deliver its first output. A total stream-to-stream filter
   therefore needs a hypothesis of sufficiently many matches, a supplied
   executable search certificate, or a partial-output interpretation. Contrast
   it with `filterMap : Stream A → Stream (Option B)`, which emits an observation
   at every input position. Retain those different meanings in the frontend.
3. **Feedback and silent work.** Compare a guarded producer with a loop that
   repeatedly changes internal state but emits nothing. Require the certificate
   interface to reject the inference from state-transition safety to
   productivity. Test that fusion preserves finite delivery as well as values.
4. **Witness-bearing elaboration.** Elaborate a small dependent declaration
   that computes a vector together with its length, then a consumer indexed by
   that length. Check substitution, universe constraints and retained witness
   computation. Include an ambiguous overload and an unresolved implicit
   argument as negative cases. A proof-irrelevant existence theorem alone must
   not count as the executable output.

The first design decision is which observation and evaluation semantics the
next fragment promises. Then implement one certifying analysis and one small
elaborator against these relations. A shared specification can support several
checkers, source syntaxes and targets without demanding that their inference
algorithms agree. Transport to another mathematical setting must separately
preserve the required natural numbers, well-foundedness, coalgebra/fixed-point
structure and observations; the existence of these constructions in Lean's
host mathematics does not supply them in every internal setting.
