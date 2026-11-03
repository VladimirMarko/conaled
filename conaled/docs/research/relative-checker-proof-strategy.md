# Making the relative checker acceptance proof tractable

Research for [#135](https://github.com/VladimirMarko/conaled/issues/135),
2026-10-25. This is a proposed proof-engineering plan, not an acceptance proof.
It uses Lean v4.35.0 and ConLeche
`8e166ca53cd1f864b63c13cc1d326d38316d00ea`, the existing experiment pins.
No new build or reduction benchmark was run for this note.

The first experiment should compose the existing phase certificates through
small, symbolic equations for monadic sequencing. If that works, reuse the
same method at declaration boundaries. A new kernel or a general trace checker
is not a prerequisite.

## What failed, and what is still unknown

The [checkpoint handoff](../../experiments/relative-graph/checkpoint-135/handoff.md)
records successful proofs of individual And installation phases, but no composed
And positivity root, complete declaration-family acceptance, or resulting model.
Whole-pass attempts exceeded their bounded time limits. Some time was spent
printing enormous failed goals; names and normalized arguments also failed to
match in rewrites. These observations do not isolate kernel checking as the
bottleneck, and do not establish an intrinsic complexity barrier.

There is already a useful success:
[CheckerReduction.depthGo_spec](../../experiments/relative-graph/CheckerReduction.lean)
proves the validity invariant of a memoized depth computation and identifies its
result with structural depth. `depth_eq` then avoids evaluating the hash map in
the concrete proof. Packed expression selector equations also removed a measured
reduction obstacle. Both are proved changes in how we establish an equation;
neither changes the accepted artifact.

The intended result remains an equality for the exact declarations and output:

```lean
checkDeclsPure .verified (fueledOps .verified fuel) pins ds = .ok env
```

ConLeche's [checkDeclsPure](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/CheckDecl.lean#L218)
is a declaration fold. Its [checkDeclsPure_sound_of](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Model/Fold.lean#L221)
already supplies the semantic induction over that fold. Once the concrete
equality is proved, the existing
[reference-model route](../../experiments/relative-graph/checkpoint-135/reference-model-route.md)
constructs the public model with explicit `SetTheory` premises. Rebuilding that
semantic induction would duplicate existing work.

## Ranked options

1. **Compose certificates without normalizing their interiors.** Prove a small
   symbolic sequencing lemma: `a = .ok x` and `k x = .ok y` imply
   `(a >>= k) = .ok y`. Use analogous state-threading and fold lemmas, with named
   intermediate states and explicit equalities at joins. Specialize these lemmas
   to the existing And phase theorems. At declaration boundaries, prove
   `checkDecl ... envᵢ dᵢ = .ok envᵢ₊₁`, then compose the list using the same
   method. The proposed improvement is controlled composition and reuse;
   registering more `cbv_eval` lemmas alone has already been tried.

2. **Prove representation-level simplifications where measurements justify
   them.** Follow the `depth_eq` example for expensive selectors, bookkeeping,
   cache access, or state construction. State each validity invariant and its
   preservation explicitly. An abstract result about arbitrary states can avoid
   repeated conversion of the large concrete state. Keep the raw checker equation
   as the endpoint. This is also a candidate for an upstream ConLeche proof API
   if several clients need it; no upstream change is required merely to test it.

3. **Generate a certificate or derivation and replay it through a proved
   interface.** If symbolic composition still fails, define a bounded trace for
   the troublesome installer or a proof-producing generator that applies the
   phase lemmas. A trace validator must prove that valid replay implies the exact
   checker transition, including the output environment. Its producer may execute
   natively because its output is checked. The validator's own concrete success
   must still be kernel-proved; moving the same large computation into a second
   Boolean function would not solve the problem. Start with And, not a universal
   checker framework.

The third option follows the separation used in
[Chlipala's treatment of proof by reflection](https://adam.chlipala.net/cpdt/html/Reflection):
establish a procedure's correctness once, then reuse it in concrete proofs.
Reflection does not guarantee lower checking cost. Certificate size, sharing,
and the cost of checking the certificate remain experimental questions here.

## Lean facilities and trust boundaries

Lean's `cbv` produces proofs using propositional equations. In the pinned
[v4.35.0 implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Tactic/Cbv/Main.lean#L166),
`handleApp` allows registered `cbv_eval` equations for a `cbv_opaque` constant
while suppressing ordinary unfolding. Its pre/post machinery also matters:
preventing a function from unfolding does not by itself establish that argument
normalization is cheap. If profiling identifies that cost, an explicit symbolic
composition lemma is preferable to normalizing the same state again. A custom
proof-producing pre-simplifier is a later option.

This behavior was checked against the installed v4.35.0 source as well as its
tagged upstream source. The v4.30 release note describes different opacity
precedence, so it should not govern this experiment. The existing checkpoint
already uses both attributes; they are not an untried remedy.

Lean's [proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
distinguishes kernel reduction from native evaluation with an added trust
assumption. Replacing the missing equation with `native_decide`, `#eval`, or
compiled success would violate the current acceptance contract. A native
certificate producer is acceptable only when ordinary kernel checking validates
its output without those extra axioms. Audit the resulting declarations and
their dependencies, not just the tactic name.

## One bounded next experiment

Use the preserved And root as the only initial target. Retain the pinned inputs,
fuel, named phase results, and exact root output. Give proof generation, kernel
checking, and failure rendering separate measurements. Cap diagnostic output;
do not use a timeout dominated by printing as evidence about proof checking.

First prove symbolic bind/state composition in isolation. Then connect the
existing field, guard, crest, and context equalities using that interface. Prove
the small joins, such as array-push notation, separately. Keep expensive state
definitions out of automatic normalization during composition. Audit a successful
root theorem, record proof size and elapsed checking time, and compare with the
retained failed attempt under the same resource bound. If it still fails, save
the smallest failing join and identify its costly phase before another variant.

Only after this succeeds should the worker extend the recipe to Exists, helpers,
and both emitted declarations. Then apply the existing model theorem and finish
the source/native/relative comparison. The exported cached-checker equation
remains a separate obligation unless independently proved; pure-checker soundness
does not imply cached acceptance.

The compositional contract is therefore explicit: operations produce or check
certificates; equations establish exact state transitions; the existing semantic
theorem transports accepted transitions to the model. This preserves the
project's separation of operations, meanings, and laws while allowing several
certificate producers. Incoming `cqueens` work may supply useful performance
techniques later, but this bounded experiment does not depend on it.
