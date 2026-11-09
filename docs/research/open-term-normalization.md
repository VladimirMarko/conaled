# Open-term normalization beyond arithmetic staging

Assessment for [#398](https://github.com/VladimirMarko/conaled/issues/398).
**A useful next target is optional βη equality checking for the existing bounded
dependent-function syntax.** The Cartesian cubical theorem provides a broader
research reference; importing its conclusion would require a calculus and model
construction that conaled has not supplied. The bounded route can answer a
concrete open-equality question without replacing the compiler or requiring all
settings to normalize.

## What #214 already completed

The [arithmetic staging report](arithmetic-staging.md) and
[`Arithmetic.Staging`](../../SquareKit/ArithmeticStaging.lean), inspected at
`78540f8f30ed8cb1afa7dc799a96dac65fec1458`, establish static specialization,
residual syntax, substitution compatibility and compilation correctness.
`specialize_correct` quantifies over arbitrary runtime valuations;
`compile_correct` reuses the existing sound target. The residual term still has
free runtime variables. That does not make this an open-term normalizer:
`specialize` inserts one computed integer into the body, and provides no
canonical representation of every judgmental equality class.

[#214](https://github.com/VladimirMarko/conaled/issues/214) deliberately selected
staging because its stack consumer needed that capability. Its completion is
not a failed normalization attempt, and this proposal does not reopen it.
Likewise the [#410 machine theorem](structural-canonicity-controls.md) concerns
finite reduction of admitted **closed ground** terms under a selected strategy.
It does not decide equality of dependent functions in a variable context.

## Exact external result

The inspected source is [Sterling–Angiuli, *Normalization for Cubical Type
Theory*, 2101.11479v2, 19 April 2021](https://arxiv.org/html/2101.11479v2).
Sections I-D and II give Cartesian Π, Σ, path, glue and circle. **Object
universes are not developed in this paper**; neither are the modifications
for De Morgan cubical type theory. Its use of a universe-rich semantic
metalanguage does not change that object-calculus scope.

Theorems 41–42 give reduction-free normalization, sound and complete for
judgmental equality. Lemma 44 and Corollary 45 give idempotence and unique
normal forms. Theorem 43 gives admissible constructor injectivity, not
injectivity in every semantic model. Corollaries 46–47 obtain a recursive
normalization function and decidable equality of well-typed types/terms in
atomic contexts. Remark 48 handles cofibration assumptions by algorithmic
left inversion. Atomic contexts extend by term and dimension variables;
they are not restricted to closed expressions.

The proof uses gluing, reflection/reification and stabilized neutrals: a neutral
that becomes reducible on a boundary must carry its boundary behavior. It is
not a correctness certificate for the whole implementation of redtt, cooltt or
Cubical Agda. No source here constructs the corresponding Lean algorithm. The universe
construction for the proof's gluing metatheory uses a Boolean background set
theory (section IV-E); the recursive computability conclusion is established
separately in Corollary 46. Neither the abstract normalization map nor a proof
of its existence in Lean `Prop` would itself be executable code.

## A binder-sensitive client already expressible locally

The [dependent function source](../../SquareKit/Internal/DependentFunctions.lean)
has base binders and primitive family fibers indexed by base expressions.
[`DependentFunctionEquality`](../../SquareKit/Internal/DependentFunctionEquality.lean)
already defines `DepEq`/`FuncEq` with β, η, congruence and typed substitution.
For an open `f : Func Γ`, its `FuncEq.eta` proves the source equality

```text
lam (app ((Ren.weaken Γ).funcMap f) (Base.var 0))  ≡  f.
```

`eta_type` checks the dependent result index. That existing theorem is the
native baseline, not work for a new normalizer to reprove for authors. The
new consumer would be a source converter comparing automatically generated
terms after repeated typed substitutions and binder insertion. It must decide
when a chain of such expansions and β-redexes is equal without the caller
selecting the equality derivation. Retaining a variable's identity under a
binder is essential; comparing only evaluations at selected closed inputs
cannot establish this judgment.

A proposed matched fixture starts with `f`, substitutes a nontrivial base
expression into its result family, performs two η-expansions with an intervening
β-application, and compares it with the directly substituted `f`. Exercise
weakening and a second typed substitution. Change one free function variable
or one surviving base index for a rejection control. The exact finite source
terms and expected boundaries must be frozen before implementing a solver.
This fixture is proposed; the report does not claim it has been compiled.

For a future cubical converter the additional discriminator is
`p : Path A a₀ a₁`: `p i` is neutral for generic `i`, but becomes `a₀` under
`i=0`. A solver accepting that endpoint equation unconditionally is unsound.
Conversely, rejecting it on the boundary loses completeness. This example
explains why an untyped tree rewrite cannot supply the cubical service. It is
outside the current dependent-function grammar and outside the proposed first
implementation's acceptance claim.

## Required laws and implementation boundaries

For the bounded converter, first state which **well-typed** instances of
`DepEq` and `FuncEq` it decides. Those relations are defined on raw scoped
terms; their equality constructors alone are not a substitute for the existing
typing premises. Define normal/neutral data with retained context and result
indices. A direct structural normalizer and typed NbE are both eligible.
Choosing NbE would additionally require semantic environments, reflection of
variables, typed reification under a fresh binder, and an interpretation theorem.

| Claim | Required evidence |
|---|---|
| Soundness | Equal returned normal forms produce the existing source equality at the common typed boundary. Preserve the source's family index, not just its host denotation. |
| Completeness | Every admitted `DepEq`/`FuncEq` derivation yields equal normal forms, including the typed-substitution rule. A successful example does not establish this induction. |
| Termination | A total normalizer/checker with a justified recursive definition for the selected grammar. Fuel exhaustion must remain unknown if a bounded search is used instead. |
| Substitution and renaming | Normalization commutes with the appropriate action up to re-normalization, including weakening beneath binders. Normal forms need not remain normal after arbitrary substitution. |
| Model compatibility | Reuse existing function-equality soundness and sheaf interpretation results. Reflection of semantic equality is not a premise licensed by those soundness theorems. |

The named `Normalized*` cubical modules normalize **semantic presentations**
for strict substitution. For example,
[`normalizedIdentity_reindex`](../../SquareKit/Internal/Cubical/NormalizedIdentity.lean)
is a semantic reindexing equality, not a decision procedure on raw cubical
syntax. A full Sterling–Angiuli application would first require matching
Cartesian dimension/cofibration syntax, type and term rules, normal forms and
stabilization, source interpretation, and the gluing metatheory. Our
[universe-free cubical semantics](cubical-model-construction.md) alone does not
meet those requirements. Extending to universes, arbitrary HITs, reflection or
partial recursion needs a new theorem for each changed equality contract.

## Recommendation and rejection conditions

Create one bounded successor under [#36](https://github.com/VladimirMarko/conaled/issues/36)
and [#235](https://github.com/VladimirMarko/conaled/issues/235) for the existing
dependent-function converter, coordinated with the
[authoring assessment](typed-nbe-and-authoring.md). Its deliverable is an
optional executable equality service with the laws above and a caller that
consumes it. It must preserve existing direct proofs and avoid new host axioms.
No normalization requirement is imposed on partial, lazy or noncomputable
settings; they retain their own observation contracts.

Compare against the current βη helpers and typed substitution before claiming
reduced author effort. Reject a productivity claim if the existing helpers
already solve the task with less preparation and repair. Reject a claim of
full equality decision if the implementation only recognizes selected recipes.
A useful sound incomplete converter can be reported as such, with its residual
obligations, but cannot satisfy the proposed completeness milestone. Keep the
full cubical normalizer deferred under #36 until an admitted cubical source
consumer needs its additional operations. No current Lean proof or build was
changed for this assessment.
