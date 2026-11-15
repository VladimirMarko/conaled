# Uniformly tracked multivalued recursion

[#500](https://github.com/VladimirMarko/conaled/issues/500) implements a bounded
realization of the multivalued diagonal argument: relations on represented
partial-recursive computations have fixed points when supplied with a total
computable code transformer realizing the relation. The uniform-family coverage
and diagonal proof are constructed directly. The result does not interpret
Bauer's full synthetic theory in native Lean.

## Primary statement and assumptions

Source: Andrej Bauer, [*On fixed-point theorems in synthetic
computability*](https://math.andrej.com/asset/data/recursion-theorem.pdf),
Theorem 5.2, printed p.10. The inspected 13-page PDF was retained on
2026-11-12, 222,717 bytes, SHA-256
`46d06da0bd44190458a2b9ce74d52546e57cfb048ab1beb36561b6f27b53d9a3`.
This hash identifies the inspected bytes; the public URL is not versioned.

The theorem assumes an internal surjection `e : ℕ → A^ℕ`. A multivalued map
has inhabited fibers. Countable Choice selects `g(n)` in the fiber at
`e(n)(n)`; coverage supplies `k` with `e(k)=g`, yielding a fixed point.
Theorem 5.2 does not directly use Markov or Enumeration. Its applications to
countably generated pointed chain-complete objects obtain coverage from
Theorems 3.2 and 4.2; the latter uses Enumeration and Countable Choice.
Markov enters Proposition 6.1 and the ensuing continuity results. Theorem 5.1
separately requires continuity for leastness. The ambient logic is
intuitionistic higher-order logic, not native classical sets (§§2–6).

## Formal contract and coverage

[TrackedRecursion](../../SquareKit/TrackedRecursion.lean) defines
`Computation = {f : ℕ →. ℕ // Nat.Partrec f}` and `represented c` using Mathlib
program evaluation. `represented_surjective` proves coverage using
`Code.exists_code`; constants zero and one give distinct inhabitants.

For a family `a : ℕ → Computation`, `Uniform a` requires joint partial
recursiveness of `(i,x) ↦ a(i)(x)`. Separate programs for each `i` do not
establish this property. The enumeration

```
row n i = represented ((ofNat Code n).curry i)
```

has uniform rows and covers every uniform family. `uniform_coverage` obtains
one program for the joint computation and uses `eval_curry` to recover every
row entry. It makes no claim to cover all native families.

`selected_diagonal` proves `∃ p, R p p` from a uniform family `g` satisfying
`∀ n, R (row n n) (g n)`. `realized_recursion` supplies this family from a total
computable `F : Code → Code` satisfying
`∀ c, R (represented c) (represented (F c))`. The family is
`g(n) = represented (F ((ofNat Code n).curry n))`. Its uniformity follows from
computable code generation and the partial-recursive evaluator. Coverage, not
Mathlib's fixed-point theorem, finishes this proof.

This is the selected, uniformly tracked form of the source argument. It
replaces unrestricted internal family coverage and choice by proved uniform
coverage and supplied computability data. These are explicit additional
restrictions on the external model. There is no claim that every native serial
relation satisfies them, or that the complete source judgment has been
interpreted. The realizing transformer may inspect source codes; it need not
respect extensional equality of codes. The relation itself is on extensional
computations.

`realized_serial` proves inhabited fibers from code realization and coverage.
`realized_code_exists` supplies an existential code for a fixed computation.
Neither theorem extracts an executable fixed-code selector. The separate
`realized_recursion_mathlib` compares the result with `Code.fixed_point`.
For semantic endomaps, `selected_endomap` connects uniform diagonal coverage
to the existing `DiagonalConstruction.Selected` interface. Its missing
coverage obligation is proved here; no all-function surjection is assumed.

## Prefix clients and classical separator

[TrackedRecursionClients](../../SquareKit/TrackedRecursionClients.lean) builds
`prefixCode b c` directly from native code constructors. It returns `b` at
input zero and runs `c` on `n` at input `n+1`. Its positive primitive-recursion
branch repeats the same partial computation; the checked idempotence lemma
preserves both value and domain. No chosen universal compiler template or
termination decision is hidden in this constructor. `prefixCode_computable`
proves total computability of the code transformation.

One relation permits either prefix zero or prefix one. Both code transformations
realize it, and its two possible outputs differ at coordinate zero for every
input. Applying the direct recursion theorem separately to the branches and
inducting on the coordinate gives two distinct total fixed computations,
constantly zero and constantly one. Prefixing changes some inputs; the public
examples also check that an undefined tail remains undefined while the new
head is defined. These are nonbottom clients, not identity-transformer cases.
The companion `exists_self_code` uses Mathlib's second recursion theorem to
obtain a program returning its encoded code on every input. It is existential
and does not replace the direct diagonal proof.

[TrackedRecursionSeparation](../../SquareKit/TrackedRecursionSeparation.lean)
uses classical equality to send constant zero to constant one and everything
else to constant zero. Its graph has inhabited fibers and no fixed point.
Consequently it has no computable realizing transformer. Its chosen diagonal
family exists as a native function but is not uniform; `row` is not surjective
onto all native families. The existing Boolean no-surjection theorem supplies
a separate general comparison. This distinguishes represented coverage from
an inconsistent assumption of unrestricted classical enumeration.

## Assembly and partial-map interpretation

[TrackedRecursionAssembly](../../SquareKit/TrackedRecursionAssembly.lean)
constructs an assembly of computations, realized by codes for their complete
partial behavior. `uniform_iff_tracked` proves that uniform families are exactly
tracked maps from encoded naturals into this assembly. The converse runs the
tracker to obtain a code, then evaluates it. It uses termination on every input
realizer; merely recording an assembly without proving this equivalence would
not establish the model comparison.

`computationEvaluation` produces a realizer for the result in the existing
`programLift (encoded Nat)`. Its tracker generates a program with the input
fixed; it does not execute that program to decide termination. The underlying
`Option Nat` observation is a noncomputable semantic view.
`computationFunction` uses the existing function assembly and currying.
Evaluation's domain is proved saturated and recursively enumerable, yielding
an actual `Assembly.PartialMap`; `computationEvaluation_classifies` identifies
its classifier with the constructed lifted evaluation.

This reuses the assembly/lifting/partial-map infrastructure of #347/#371. The
[selected certificate solver](internal-selected-certificate-solver.md) retains
stronger selected-state, trace and completeness contracts. The present fixed
point existence theorem supplies no leastness, continuity or selected trace,
and does not replace those contracts. No effective-topos model or validation
of the complete synthetic axiom package is claimed.

## Oracle scope and checked applications

[Examples/TrackedRecursion](../../Examples/TrackedRecursion.lean) consumes the
direct recursion, uniform/tracked equivalence, classifier agreement, positive
prefix clients and classical separator. It also combines prefix semantics with
#498's `toOrdinary_correct`: an oracle program can enter this ordinary code
representation when supplied with an actual ordinary oracle implementation.
That implementation remains an explicit argument.

Arbitrary-oracle recursion remains unimplemented. It needs a relative universal
evaluator and parameterization/self-reference proof; #498's syntax adequacy
alone does not supply those facts. This bounded delivery adopts no general
evidence interface and does not settle #489's production-bridge decision.

Statement review checked joint versus pointwise quantifiers, nonvacuous coverage,
semantic versus code equality, actual transformer computability, undefined
inputs, both distinct branches, tracker termination, and existential versus
effective code selection. Focused builds of all new modules and public examples
passed. Exact integrated build, exhaustive proof audit and independent Standards
and Spec acceptance belong to the enclosing implementation workflow.
