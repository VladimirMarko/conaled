# Normal dispatch: expectations fixed before proof implementation

Status: uncompiled implementation research, fixed on 2026-11-25 before writing the next Lean files or receiving compiler feedback about them. This is one stationary dispatch segment, not the general height theorem. Earlier trace-concatenation files and expectations stay frozen. Root reported their first check failed on a concrete calc elaboration; root owns that repair and all compilers.

## Current source basis

Read the restored `TapeToPrimitive.lean` completely, `StackToTape.lean` statement-tail/normal-dispatch section, pinned Mathlib `TM2to1.trNormal`, `stmtStRec`, `trNormal_run`, `TM1to0.trAux`, and the current empty-peek and load/branch fixtures. The source identity remains root-reported commit `0959a1c9d59660eec33ca4c9d971d74a8bc54378`, tree `655ddb1ee2a730d73a7b0fb5eda5a3e3c40eb669`.

The relevant literal native definitions are: source push/peek/pop becomes a goto of a go control; source load updates the register before translating the continuation; source branch follows that actual register; source goto and halt remain goto and halt. Native TM1to0 translation folds loads/branches and emits a write of the current symbol for goto/halt. None of these normal-body leaves emits a movement.

## Generic intended contract

For any source statement `q`, register `v`, and actual current symbol `a`, translating `trNormal q` under a supplied target program `P` must emit a native command whose action is exactly `TM0.Stmt.write a`. Its next control must remain the actual `trAux` result, retaining any register changes and branch choice; it must not be replaced by an arbitrary witness.

The existing positivity, syntax-bound, and exact-statement theorems imply that `primitiveSteps (trNormal q) v T = 1` and that after that one actual native step the full endpoint is

```lean
TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal q) v T)
```

The desired prefix result will retain the whole selected command, this full optional endpoint, unchanged complete tape, and unchanged supplied integer coordinate. The displacement must be justified from the actual self-write command. Tape equality alone is insufficient to justify stationarity, since a move on an all-blank tape may preserve its contents.

Specialize this to the actual simulator program `P = TM2to1.tr M` and actual normal control `l`. No encoding-image, bottom-marker, finite-support, stack-height, or decidable alphabet/control equality premise is needed for this local dispatch. The actual source register, main/default instances, and translated blank remain supplied natively. The `DecidableEq` needed to construct the actual stack simulator is retained in its specialization.

The minimal continuation decomposition, consuming the prior concatenation interface, must say that for every suffix length `k`:

```lean
cfgAt primitive start (1 + k) = cfgAt primitive finish k
commandAt primitive start (1 + k) = commandAt primitive finish k
headPosition primitive start origin (1 + k) =
  headPosition primitive finish origin k
```

Here start and finish are the exact configurations above; the same origin on both sides follows from the newly justified stationary first command. Zero suffix and suffixes through outer none are included. This is not a freely assumed simulation or timing interface. The continuation file may depend on the earlier new trace lemmas and this new prefix result; that dependency must be stated honestly until root installs or assembles them for checking.

## Fixed connected calculations

### Existing genuinely initialized empty peek

Reuse `Examples.TuringSimulation.VisitedSpace.peekMachine`, `peekStart`, `peekGo`, and their existing defaults. Source main is Unit.unit; the initialized register is false; the marked raw input is empty, not present false.

At prefix zero the actual command is `some (peekGo.q, TM0.Stmt.write peekTape.head)`. One native step reaches the complete `peekGo` configuration, with false register, unchanged tape, and coordinate zero. This is just the stationary dispatch before the already fixed left excursion. The whole fixture remains live five / outer-none six; those existing clocks are unchanged.

The connected continuation result must specialize the generic one-step decomposition to `peekStart` and `peekGo` for every suffix length, with the same origin zero. In particular the first suffix step moves left and the full prefix-two coordinate is minus one. The continuation result must use the new decomposition, not merely re-prove the old position list.

### Existing load-Bool.not branch, supplied register false

Reuse `StatementCases.branchProgram` and `Cases.columns`. The input tape encodes selected stack `[true, false]` and unrelated stack `[true, false, true, true]`, with the existing marker at zero. This is a supplied encoded configuration; do not relabel it as fresh native list initialization.

The source body is `.load Bool.not (.branch id (.push false (fun _ => false) .halt) .halt)`. From false, the load produces true; the branch selects the push. Normal dispatch only selects the go control and does not perform the push yet.

After exactly one native transition the full endpoint is the primitive translation of tape configuration `⟨some (.go false Cases.pushFalse .halt), true, T⟩`. The selected command writes the unchanged current head symbol, and its next control is exactly that endpoint's control. The entire tape remains T, including both tracks. With supplied coordinate origin seven, the coordinate remains seven.

The existing whole-statement TM1 count eight is not asserted to be a primitive TM0 count. This new case concerns only its first stationary primitive dispatch.

### Same load/branch, supplied register true

From true, the load produces false; the branch selects halt. After exactly one native transition the full endpoint is `⟨(none, false), T⟩`. The actual selected command writes the original head symbol. With supplied origin seven the coordinate is seven, and the complete tape is unchanged. The following separate second transition is outer none.

This uses a deliberately supplied true register, not a changed native default. It separates actual loaded branch selection from choosing a branch using the pre-load register. It does not change any existing fixture or empty-peek clock.

## Boundaries

No `InternalHeight` implementation, source-run height assumption, outward scan, action/return interval, general `[-1, H]` bound, or `H + 2` span is proved by these expectations. No conclusion about all other-track occupancy, conventional machine space, NP, whole-library acceptance, or textbook qualification follows. Every future declared proof remains uncompiled until root obtains and reads the actual checker result; frozen expectations must not change merely to obtain a passing elaboration.
