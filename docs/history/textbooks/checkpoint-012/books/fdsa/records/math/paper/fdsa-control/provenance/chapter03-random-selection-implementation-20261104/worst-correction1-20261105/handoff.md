# Singleton endpoint proof correction

Finding: `C03-RANDOM-WORST-ELAB-001` (actual compiler/elaboration failure).

Candidate: `96722600aa29636e028751242ce33d562c5a9255`  
Tree: `b472eb84c0bb9861ba11de235ca5efe8d16ed70e`  
Parent: `3c04405d207a7b8c6f7452598da88fa3a7a05ac3`  
Branch: `work/fdsa-ch03-random-selection`  
Commit: `fix(selection): align singleton endpoint occurrence proof (#174)`

The worktree is clean. **This successor is UNCOMPILED.** Root owns the next serial qualified validation after checkpoint0136 is uploaded/exposed.

## Actual failure and exact correction

The first focused pair on the parent closed with actual exit1: owned session6786, terminal `c51a4e`, native/recorder exits1. The entire closed outer log was read in `9d1865`, and the owned/native/recorder reconciliation in `1c129c`. The outer log is13948 bytes/SHA `774df7e1df9d46fecf73211a50d19ddee375d0d2b9262d8e5b9aa71acba1f5fe`; native is13664 bytes/SHA `a92cec41dabc7eeea3f85647312ba43af593c17f3289bcdb0bac5f5382db3d64`. The native body matches the full outer log between its saved prefix and suffix.

The sole reported core error was the singleton proof's `rw [hs]`: its fact used Fin numeral0, while `EndpointTrace` exposed the explicit constructor0. No core or pair pass is inferred from the other core lines reporting no errors; examples were not built.

Only one proof-local line changes:

```lean
-  have hs : (stepRun 0 [x] 0).1 = Sum.inr x := by
+  have hs : (stepRun 0 [x] ⟨0, by simp⟩).1 = Sum.inr x := by
```

The existing proof of the same actual step equation, structural witness and rewrite remain. The explicit constructor has the same actual occurrence0; its bound is proved from singleton length. Proof irrelevance identifies the bound proof with the structural predicate's bound witness. No statement, definition, step semantics or execution law changes.

## Preservation and statement assessment

All **335 headers/contexts,314 public declarations,21 private helpers and26 definitions/abbreviations** are preserved. Every private helper body and all example source/proof bytes remain exact. The other17 source files, including all16 pre-stage09 files, are byte-identical.

Every arbitrary Nodup input and every valid worker rank remain covered by the universal theorem. Actual full/trace factorial probability, singleton termination, triangular W, actual source transport, every-valid-rank range/unbounded family and all duplicate/empty/invalid cases remain unchanged. This correction adds no premise, linter suppression, axiom or probability/cost assumption.

The complete corrected core was read in `bf9288`; the exact delta in `8f0c51`; the changed claim, implicit context, case connections and preservation record in `dcd5bb`. The full stage09 source/case assessment remains immutable and bound. No independent review conclusion is claimed.

Corrected core:10727 bytes, SHA-256 `0e83e44d4e1b2af6b56e09345d248d9af878e8a7d1108458ed8dcee446ec6541`, Git blob `767a9c819b9f52d451b0db403d98c9e4175b6425`.

`Statements314-worst-correction1.lean` is byte-identical to the stage09 input:18231 bytes, SHA-256 `5d4b19d87d87761158e03b322c87834171c9bb7e5fb1e5504399bb1c48a38996`. All314 explicit-@ checks, names/order and six print options are preserved. The separate candidate-binding record identifies this exact successor. No author type execution took place.

## Historical binding boundary

Both prior binding sets were completely verified before the authorized edit. The previous trace395 set remains entirely current/exact. In the stage09/358 set, exactly one intentionally changed live path is `Applications/Resources/RandomSelectionWorst.lean`; all other357 bindings remain current/exact. Its original bytes remain in immutable parent3c04405d with blob `03b683c8040bdcc7b92ac6898f1464a77c61d360`. The old stage09 hold and every historical record remain untouched. The current hold explicitly binds the corrected source and preserves the union of historical record paths.

All304 earlier own records and14 actual failed-run records remain exact. No historical process identifier was polled. The native/transport distinctions of previous attempts and original Karp1994 access limitation remain unchanged.

## Validation and hold

The staged whitespace check returned actual exit0 (`cef083`), and the local commit returned actual exit0 (`b4d9d5`). These are not Lean validation. No compiler, environment, dependency, cache, output, profile, integration ref or GitHub operation was performed.

Requested root targets remain `Applications.Resources.RandomSelectionWorst` and `Examples.RandomSelectionWorst`. Actual successor focus, types, full immutable candidate validation/audit and both independent axes are still required. No whole-Chapter3 acceptance is claimed. **All source and provenance writes are held after the final author-hold record, including throughout checkpoint0136 capture/upload.**
