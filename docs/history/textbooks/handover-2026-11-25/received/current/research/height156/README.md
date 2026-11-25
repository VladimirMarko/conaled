# Actual source-path InternalHeight

**Status: uncompiled external implementation draft.** Root owns all compilers, products, integration, checkpoints, and the existing independent review loop. This work is not a Standards/Spec approval or a target-space theorem. No project source, product, resource setting, or earlier frozen research file was changed.

`EXPECTATIONS.md` was written and frozen before the Lean proof text, with SHA256 `33eb8454918f38a201e77b36c93eda67709b38ea5a25c6343e135ff88e105f41` (6655 bytes). Its literal positive and negative cases are retained. The six normal-dispatch research files remain unchanged and are not imported or assumed by this increment.

## Source identity and reads

The requested source candidate C155 is `a5a917db8717977371b8d76d93f166389c9eec9b`, tree `394733a450268e8943048ea146440dcb75c7ceea`. The candidate object and tree were resolved read-only. The actual read owner/example/guidance files were compared with the candidate's Git blobs; the manifest records the exact paths and hashes. The checkout HEAD is a different base, so no HEAD-tree identity or whole-working-tree comparison is substituted for those per-file bindings.

The source comparison used native `TM2.stepAux` and the grouped `stRun`, `stVar`, `stWrite`, and `stmtStRec` operations, plus existing `actionBound`, `actionBound_run`, `stWrite_length_le`, and `tailSteps_le_reserved`. Current concrete fixtures were read directly. Prior full guidance readings were reused only after their bytes were checked unchanged; AGENTS/task/formal were also read again. All native/toolchain inputs remain root-owned.

## Definition and actual-path contract

`Resources.TuringSimulation.StackToTape.InternalHeight q v S H` follows the seven native TM2 constructors. At push, peek, and pop it requires both the old and new selected stack length to be at most H, then recurses with exactly the source register and stack update. Loads use the changed register; branches choose only the arm selected by the current register. Goto and halt end inspection of this finite statement body.

The predicate does not follow a goto into another program body. A whole source run would need its hypothesis at each actually executed body. The generic type retains arbitrary dependent alphabet family `Γ : K → Type*` and the native stack-index `DecidableEq`; it adds no finite-index, inhabited-register/main, or decidable alphabet/control premise.

H is a natural selected-path height. There is no TM1/TM0 configuration, head position, interval, visited set, target witness, or desired space inequality in the definition. It is deliberately weaker than a bound on the whole initial family. The callback results and actual register-dependent branch choices are part of its meaning, not freely supplied witnesses.

## Generic claims and derivations

| Public claim | Mathematical content and proof route |
|---|---|
| `internalHeight_stRun` | A grouped equation using the native `stWrite`, `stVar`, and `Function.update`. Cases on the native action recover the explicit constructor equations; peek uses `Function.update_eq_self`. |
| `InternalHeight.mono` | For the same q, v, and S, widening H preserves the predicate. Structural induction keeps the actual source path and transports each selected-length inequality. |
| `internalHeight_of_reserve` | The whole-family condition `∀ j, length (S j) + actionBound q ≤ H` implies the actual-path predicate. In an action case, the existing `stWrite_length_le` pays for at most one new cell while one action is removed from the reserve. The updated selected stack and unchanged other indices both retain the remaining reserve. Loads and branches follow actual source values. |
| `internalHeight_of_uniform_bound` | Starting lengths at most B and a supplied syntax bound `actionBound q ≤ A` imply `InternalHeight q v S (B + A)`, by the reserve theorem and addition monotonicity. |

The reserve induction follows the already established update argument in `tailSteps_le_reserved`; it does not use that theorem's numeric time conclusion as a substitute for intermediate-state reasoning. The recursive height hypothesis is derived after proving the actual updated-family reserve. The branch reserve may use the syntax maximum to discharge a sufficient premise, while the predicate itself still inspects only the executed arm.

The uniform theorem is per supplied q, v, S, B, and A. A caller claiming a single program-wide A must still establish the required bound uniformly. No input-dependent choice is silently promoted to that stronger quantifier order.

## Connected cases

The examples live in `Examples.TuringSimulation.InternalHeightCases` and reuse the existing source fixtures. Two small body definitions append halt to the retained empty-peek/pop actions; they do not define a new operational machine.

| Connected result | Retained meaning |
|---|---|
| `empty_peek_height_zero` | Empty selected track permits H=0 through the grouped action equation, while the unrelated track's actual length is 4. |
| `empty_pop_height_zero` | Empty pop likewise permits H=0 and retains the unrelated length-four observation. |
| `empty_peek_not_reserved` | At the unrelated index, the whole-family reserve at zero would require 4+1≤0. Thus the sufficient reserve is not necessary for the preceding valid predicate. |
| `pushPop_height_and_empty_endpoints` | The actual path 0→1→0 satisfies H=1 and rejects H=0. The same theorem retains the existing exact native source-step equality with empty initial and final families. |
| `pushPop_uniform_and_widening` | The uniform corollary supplies the safe coarser H=2 from B=0 and A=2. Monotonicity separately widens the independently established H=1 to every H≥1. |
| `loaded_true_height_three_not_two` | Supplied false is loaded to true and selects push, so the selected path 2→3 satisfies H=3 and rejects H=2. The unselected stack remains length 4. |
| `loaded_false_height_zero` | Supplied true is loaded to false and selects halt, so H=0 holds even with nonempty starting stacks. This does not change any default. |

The literal source reductions in the case proofs expose the independently calculated numeric guards. The cases use public predicate/equation statements; the reserve and monotonicity cases explicitly consume the new generic lemmas. No existing TM1 or TM0 clock is changed or inferred from these source heights.

## Occupancy and future geometry remain separate

The empty-selected/other-four example is intentional. H=0 does not bound all source stack lengths or the encoded tape's complete occupied region. Even a later head-visit theorem would need a separate premise to cover an initial input interval or arbitrary initially occupied cells. A whole-family reserve can supply stronger initial bounds when its premise is available; those bounds must not be read back into the weaker predicate.

This increment supplies source-side hypotheses for the later primitive geometry proof. It does not prove that the native head stays in `[-1,H]`, that the visited span is `H+2`, or that all primitive internal moves have been accounted for. The existing time-derived visited-space bound, initialized empty-peek live-five/none-six distinction, marker/all-track obligations, finite-control transport, and ordinary/conventional geometry remain unchanged and separate.

## Files, prospective placement, and checking

`InternalHeight.lean` is one complete external draft using normal imports of the current StackToTape and Examples owners. It is independent of the uncompiled normal-dispatch work. On eventual integration, the generic namespace block belongs in `StackToTape.lean`, after the existing action-bound/growth machinery; the example block belongs in the existing Examples owner. The production generic owner must not acquire an Examples import. No new production module or entrypoint import is proposed.

`InternalHeightStatements.lean` has normal production imports and exactly fourteen each of `#check`, `#print`, and `#print axioms`, with `pp.all` true. It covers the predicate, four generic lemmas, two body definitions, and seven connected case claims. Unchanged C155 owners do not yet export these new names. Root may append only the query block to a separately bound local draft-check copy for the first reading; a later normal-import check must query the actual installed owner exports. These are distinct evidence scopes.

`MANIFEST.json` binds the source reads, ordering of the expectation freeze, all new artifacts, unchanged normal-dispatch artifacts, and explicit compiler status. Root must obtain an actual compiler result, read the full expanded statements and relevant definitions/proofs, inspect axiom outputs, record any printer elisions, and apply the existing integration/review/build/audit requirements. No source, query, or file hash is a substitute for those checks.

Remaining elaboration risks include the native recursor's dependent hypotheses, the grouped peek update simplification, and the concrete `change` reductions through native functional updates. Any repair must retain the independently fixed path heights and supplied register choices. There are no admissions or resource/transparency/linter overrides in the proposed proof text, and no claim that a compiler has checked it.
