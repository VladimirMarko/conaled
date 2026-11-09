# Typed normalization and bidirectional authoring

Assessment for [#399](https://github.com/VladimirMarko/conaled/issues/399).
**Investigate an optional conversion service at an existing author boundary,
and measure it against public helpers before choosing another frontend.**
Typed NbE can answer a judgmental-equality problem; bidirectional checking can
use expected types to avoid some inference. Neither automatically supplies
arbitrary dependent elaboration, a better mathematical setting, or lower total
authoring effort.

## The paired examples, with reproducible source pins

The motivating [18 March 2021 discussion](https://github.com/RedPRL/cooltt/discussions/186)
links two implementations of representation invariance. To avoid moving
`master` references, this assessment inspected each file's last commit before
19 March 2021 UTC:

| Source | Pinned example and observed proof structure |
|---|---|
| RedPRL | [`invariance.prl`, b4c8c2ab9cf736a2913f0cbbe57d3e15b714260e](https://github.com/RedPRL/sml-redprl/blob/b4c8c2ab9cf736a2913f0cbbe57d3e15b714260e/example/invariance.prl). `FunToPairIsEquiv` constructs the Boolean-function/pair equivalence using endpoint extraction, reduction, inversion and branches. `SwapFunEqn` transports pair involutivity and then invokes `coe/eq`, `subtype/eq`, `fun/eqtype` and `path/eqtype` obligations. |
| redtt | [`invariance.red`, 54b035851e8751ea5431127dba365ed656303438](https://github.com/RedPRL/redtt/blob/54b035851e8751ea5431127dba365ed656303438/library/cool/invariance.red). `fun≃pair` uses `pair→fun`, a connection and the explicit `shannon/path` argument. `swap-fun/path` transports the pair involution through `fun≈pair`, with the intermediate `swapcoe` defined under the dimension binder. |

The compared task is the same representation change, `Bool → A` versus
`A × A`, and transport of the swap involution. The proof scripts do visibly
differ in explicit well-formedness work. Sterling's accompanying explanation
attributes this to type-directed automation of contextual equations and notes
that RedPRL can use reflection where redtt uses a path. That is an author report
and source comparison, not a controlled timing experiment. Shorter visible
scripts can also rely on imported lemmas, elaborator engineering and different
judgments. We did not rebuild the historical assistants, measure their authors,
or infer a general productivity ranking.

The [open-normalization report](open-term-normalization.md#exact-external-result)
records the exact Sterling–Angiuli theorem. Its sound/complete conversion
result is narrower than either assistant's entire implemented language.
[Dunfield–Krishnaswami's accepted 2021 survey](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/)
distinguishes checking against an expected type from synthesizing a type;
this split can support constructs for which unrestricted inference is
undecidable. It does not make every omission inferable.

## Local capabilities and the actual missing service

The inspected conaled revision is
`78540f8f30ed8cb1afa7dc799a96dac65fec1458`.

- [#147's elaborator](../../Applications/Elaboration/Elaborator.lean) already
  separates `Resolves`, `Faithful`, constraint equivalence and target typing
  in `Elaborates`. `elaborate_sound` and `elaborate_complete` cover its annotated
  natural/vector fragment and explicit overload policy. `resolve` uses an
  expected sort for an outer literal; bodies are already scoped and typed.
  Assignments are supplied, not found by a general unifier.
- [#214's staging](../../SquareKit/ArithmeticStaging.lean) supplies specialization
  and residual compilation. Its open runtime context does not provide typed
  reification or a judgmental-equality checker.
- [Dependent function βη rules](../../SquareKit/Internal/DependentFunctionEquality.lean)
  already supply `FuncEq.eta`, `DepEq.beta`, substitution and congruence. The
  proposed service in #398 would search/normalize to discharge repeated
  comparisons instead of asking the caller to select these derivations.
- [Reference congruence](../../SquareKit/Internal/DependentJudgments/ReferenceCongruence.lean)
  already supplies typed J branch and motive congruence. A trial must allow
  those helpers wherever applicable. Repackaging their spelling is not evidence
  of a new equality capability, and function conversion does not decide all J
  or higher-boundary comparisons.

The local dependent-function grammar has base-domain functions into primitive
family fibers. It cannot express the full univalent pair/function swap example.
Using that historical example as a source lead is useful; claiming its compiler
or proof imports into this grammar would be false. The immediately matched
local task is the binder/substitution fixture in #398, preserving a changing
result index. The cubical boundary test there remains an explicit later gap.

## Proposed optional interface and separate guarantees

A service can accept an existing scoped term and expected family index, check
formation and conversion, and return either an existing derivation or a
specific unsupported/mismatch result. Synthesis may return a type only where
the chosen grammar determines it. Keep complete source derivations available
for authors and clients outside the service. This is an interface sketch, not
a new exported API or a compulsory stage of every compilation.

Typed evaluation would interpret free variables as neutrals in an environment;
reification would inspect the expected type, extend the context at binders,
and return normal syntax with the same index. In the bounded first-order
dependent-function grammar, a simpler direct algorithm may be enough. Select
between them on proof and maintenance cost rather than the NbE label. A later
cubical version would also need face assumptions and stabilized neutrals; an
unconditional endpoint rewrite is unsound.

| Property | Acceptance condition for the optional service |
|---|---|
| Elaboration soundness | Every success returns a well-typed existing source derivation and the declared source meaning. Preserve the distinction between source fidelity and output typing from #147. |
| Equality soundness/completeness | Prove both directions for the selected βη relation. Completeness of conversion is separate from completeness of elaboration with omitted annotations. |
| Termination | Establish total evaluation/reification and finite checking on the admitted syntax. A heuristic search timeout means unresolved, not inequality or ill-typedness. |
| Elaboration policy | State which annotations are required, which holes are solved, and how ambiguous requests are reported. Prove completeness only relative to that policy. |
| Setting compatibility | Reuse the equality interpretation theorem under its existing model laws. Do not reflect equality of host denotations into source conversion. |

[#260](https://github.com/VladimirMarko/conaled/issues/260) is a conditional
algebraic-subtyping experiment requiring its own semantic algebra and evidence
comparison. Its subject is not the same as βη conversion. This assessment does
not activate it, add global implicit subsumption, or resume the protected
#107/#108 tasks.

## A trial that can reject adoption

Coordinate a single successor with #398 under
[#235](https://github.com/VladimirMarko/conaled/issues/235). Freeze the source
fragment, expected result indices, fixtures, documentation and permissible
helpers before assigning independent authors. Compare:

1. Direct ordinary Lean construction using all existing public βη and
   substitution helpers.
2. The optional conversion/checking service, with the same mathematical
   declarations and model interpretation.

Both authors should complete the same open substitution/η fixture, a repair
changing the result-family index, and a held-out binder variant. Include a
mismatched-variable/index rejection. Do not weaken the baseline by requiring
manual de Bruijn calculations when current helpers already discharge them.
Record model/version, tools, budget, attempts, assistance, diagnostics,
annotations, explicit conversions and successful checking. Account separately
for service development, task preparation, author effort and repair cost.
These proposed observations are not present measurements.

Adopt only if the service preserves the statement and selected observations,
handles the tested recurring conversions, and earns its setup and maintenance
cost for that consumer. Keep the direct route if it is simpler or more capable.
If neither route expresses the frozen task, diagnose the missing source rule
or model capability before blaming elaboration. A failed native encoding is
not a proof that its mathematical setting is unsuitable. The trial can reject
adoption while leaving a sound optional equality engine useful elsewhere.

The follow-up must not add arbitrary recursion to a total conversion procedure
and still advertise its old termination theorem. Partial runtime computation,
noncomputable specification, and lazy demand retain their separate contracts.
No new Lean code, author trial or historical assistant build was performed in
this research change.
