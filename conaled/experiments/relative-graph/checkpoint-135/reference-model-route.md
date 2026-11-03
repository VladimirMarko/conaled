# #135 finite-fuel reference acceptance to the same environment model

Source inspection at ConLeche `8e166ca53cd1f864b63c13cc1d326d38316d00ea`, checkout `/home/vlad/.local/state/conaled-supervision/2026-10-25/128/134/con-leche`. No builds or acceptance probes. The direct route exists and does not require reversing the cached simulation.

## Exact entrypoint and theorem

Import `ConLeche.Model.Fold` and `ConLeche.Model.Denotes` for the semantic route, and explicitly import `ConLeche.Kernel.CheckDecl` / `ConLeche.Kernel.CheckerBase` if needed for exposed checker definitions in the caller's module context.

[Kernel/CheckDecl.lean:218](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/CheckDecl.lean#L218) defines `ConLeche.checkDeclsPure mode ops pins ds` as `ds.foldlM (checkDecl mode ops pins) Env.empty`. Its input is a `List Declaration`, not the cached entrypoint's array.

[Kernel/CheckerBase.lean:55](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/CheckerBase.lean#L55) defines `ConLeche.fueledOps mode F : CheckerOps CheckM`. It calls `inferTypeCore`, `isDefEqCore`, `ensureSortCore`, and `whnf` at exactly `F`. `pureOps mode` instead chooses standard `checkFuel`; a concrete acceptance theorem can choose an arbitrary sufficient finite `F` directly.

[Model/Fold.lean:221](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Model/Fold.lean#L221):

```lean
ConLeche.Model.checkDeclsPure_sound_of
  {V : Type w} [SetTheory V] {μ : CheckMode} {pins : List NatOpPinSet}
  (hμ : μ.isVerified = true) {F : Nat} {ds : List Declaration} {env' : Env}
  (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
  Nonempty (ConLeche.Model.EnvModelM V μ env')
```

The theorem carries the same `env'` produced by the check. Its proof applies `foldPM` from `EnvModelOk.empty`; `foldPM` at line200 carries `EnvModelOk V μ env` through the successful declaration fold, using `declStep_preserves` and `ConLeche.Semantics.checkDeclRun_ofEnvFactsK`. No separate caller-supplied induction/recursor soundness assumption is needed.

[Model/Denotes.lean:330](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Model/Denotes.lean#L330):

```lean
noncomputable def ConLeche.Model.Model.ofEnvModelM
  {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
  (m : ConLeche.Model.EnvModelM V μ env) : ConLeche.Model V env
```

Thus the intended composition is:

```lean
-- h must be independently kernel-proved for the actual encoded ds and output env.
obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of
  (V := V) (μ := .verified) (F := fuel) rfl h
exact ⟨ConLeche.Model.Model.ofEnvModelM m⟩
```

This is a source-derived recipe, not a locally compiled snippet. Main implementer should check exact elaboration and audit the resulting declaration. `fuel` may be bounded and small enough to compute; no equation with standard cached `checkFuel` is required because the soundness theorem is quantified over `F`.

## WF is weaker than the required invariant

`ConLeche.Verify.EnvWF` at [Verify/EnvWF.lean:172](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Verify/EnvWF.lean#L172) only records syntactic well-formedness of stored constants and tables. The direct checker theorem yields the stronger `EnvModelM`, from which `m.base2.wf : EnvWF env` is available. `EnvModelM` also has `type_reads`, `mem_type`, equality and recursor laws. No `EnvWF → Nonempty (Model V env)` theorem was found, and discarding the semantic invariant would lose the evidence used by the model construction. Use the direct `checkDeclsPure_sound_of` route rather than attempting that weaker intermediate statement.

## Trust and acceptance boundaries

The only explicit hypotheses of the composition are `V`, `[SetTheory V]`, verified mode and successful execution of the named pure checker on the exact declaration list and output environment. SetTheory remains a mathematical assumption; this route does not construct its instance. Source inspection found no additional axiom introduced by these two declarations themselves, but it does not certify their complete transitive dependency census. No matching guard for this particular pair was found in the inspected tests, so the candidate must freshly audit `#print axioms` or the repository audit before claiming whitelist compliance.

The proven acceptance would be `checkDeclsPure .verified (fueledOps .verified fuel) pins ds = .ok env`. It would not prove `Cached.checkDecls` acceptance, the compiled checker driver, file parsing, scheduling, runtime correctness, or emitter-to-ds correspondence. Preserve those distinctions in issue status and theorem names. The result can still provide the same public `Model V env` for the exact finite encoded declarations, with source-to-artifact correspondence proved separately.
