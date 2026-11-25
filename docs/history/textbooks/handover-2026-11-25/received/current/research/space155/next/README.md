# Stationary normal dispatch and its actual suffix

**Status:** admission-free external proof text, statically assessed by the implementer, **uncompiled**. This is the next small implementation increment, not independent Standards/Spec review, acceptance, or the height theorem. Root owns every compiler, source installation, product, checkpoint, and review decision. This agent has not changed project source, toolchain/cache/resource settings, or any earlier frozen artifact.

The fixed calculations were written first in `EXPECTATIONS.md` (6862 bytes, SHA256 `bb908a5d8ab2c86303dd760285a80ab45dc9708749768bf95183ec9f579a6015`). The subsequent Lean files preserve those expectations. Root reported that the earlier concatenation draft's first check failed on a concrete calc type-inference issue; root owns its immutable repair. No successful overall result for that earlier increment is assumed here.

## Files and dependencies

- `NormalDispatch.lean` is a complete combined generic/case draft importing only the current normal production owners. It does not depend on the three new concatenation declarations. Root can check this file against the existing owner outputs without installing the earlier increment.
- `NormalDispatchContinuation.lean` contains the minimal all-suffix decomposition and its connected empty-peek case. It uses this draft's `normal_control_prefix` and the earlier proposed `cfgAt_add_of_live`, `commandAt_add_of_live`, and `headPosition_add_of_live`. These are not exports of the unchanged recovery154 owners. Root must first install/build matching checked declarations or assemble a separately named and hash-bound check copy from the selected prior increment and these bodies. Do not infer a mathematical failure from missing imports against unchanged owners.
- `NormalDispatchStatements.lean` has normal owner imports and exactly nine each of `#check`, `#print`, and `#print axioms`, with `pp.all` true. It declares no substitute theorem. It can query integrated exports; for local draft reading root may append only its query block to a separately bound combined check copy, keeping all imports at the top.
- `MANIFEST.json` binds the new files, current source reads, fixed expectations, and explicit uncompiled/dependency status.

All root-created check copies should retain exact source maps and actual results. Earlier frozen sources and expectations must remain unchanged. The independent review loop and existing broader gates are not replaced by any of these files.

## Reusable mathematics

All five generic declarations use the namespace `Resources.TuringSimulation.TapeToPrimitive`.

| Declaration | Precise contribution |
|---|---|
| `primitiveSteps_trNormal` | Existing positivity plus `primitiveBound_trNormal = 1` yields exact native count one for the complete translated normal body. It does not infer a count from endpoint equality. |
| `trAux_trNormal_command` | Induction through the source's `stmtStRec` proves the actual `trAux` action component is exactly `write a`. Stack-action cases become gotos; loads update the register before applying the induction hypothesis; branches follow that updated value. This command-level lemma is placed outside the inhabited-label/register section because its raw operation does not use defaults. |
| `trNormal_prefix` | For a supplied target program P, source body q, register v, complete tape T, and integer origin, retain the full selected command, actual cfgAt-one endpoint `trCfg P (TM1.stepAux (trNormal q) v T)`, unchanged coordinate, and complete unchanged tape. The next control is the actual `trAux` first projection, not an arbitrary witness. |
| `normal_control_prefix` | Specialize the preceding result to `P = TM2to1.tr M` and the actual translated normal control l, preserving the source main/register instances and actual source body `M l`. |
| `normal_control_resume` | Use that actual one-step prefix and the earlier concatenation laws to identify every suffix configuration and full command at `1 + k`, with the same original coordinate origin. The source continuation is the actual TM1.stepAux result, including folded load/branch effects. |

The proof of full tape preservation in `trNormal_prefix` reduces the actual native step using the proved self-write command, applies `Tape.write_self`, and compares complete successor configurations with the existing exact-statement result. The coordinate proof separately uses that actual command inside `commandOffset`. Therefore movement is never inferred from tape equality. This matters even for a uniform blank tape, whose contents can survive a movement unchanged.

The generic prefix is local to the translator. It needs no bottom-marker or encoding-image premise, no height premise, no finite support, and no decidable alphabet/control equality. The actual simulator specialization retains the stack-index `DecidableEq` needed to construct `TM2to1.tr`. Native inhabited assumptions are retained where the machine API uses them. Arbitrary source goto loops are allowed; reaching the same cfg again would still be the recorded one primitive step, not zero steps.

The resulting primitive endpoint is inside `some`, even if its control has become `(none, v')`. The later outer-none transition remains separate. The all-suffix theorem permits that later observation and longer absent suffixes without treating bookkeeping coordinates as new visits.

## Connected calculations and source defaults

The cases use `Examples.TuringSimulation.NormalDispatch`.

`empty_peek_dispatch` applies the actual normal-control specialization to the existing genuinely initialized empty-peek machine. It retains the complete command writing `peekTape.head`, endpoint `peekGo`, zero coordinate, and exact initial tape. The explicit local Pi and control instances match the existing fixture; its raw cell is none, its source register starts false, and its whole run remains live five / outer none six.

The two branch cases reuse `StatementCases.branchProgram` and `Cases.columns`; the additional definitions merely name that existing program's native translations and supplied configurations. From false, Bool.not produces true and the dispatch selects the push-go continuation with true register. From true, Bool.not produces false and the dispatch selects live halt with false register, followed by outer none at step two. Both first commands self-write, preserve the complete tape, and retain coordinate seven. These are supplied encoded starts, not new claims about native initialization. In particular the true start is not a changed default. The unrelated four-cell track is preserved with the entire tape.

`empty_peek_resume` consumes `normal_control_resume`, identifies every suffix after the genuine initialized dispatch with the actual `peekGo` suffix, and uses its first left move to obtain global prefix-two position minus one. It does not substitute an independent re-proof of the old whole-position list for the new connection.

There are no changed clock expectations. The existing full branch TM1 count eight is not presented as a TM0 primitive count. Only its one-step primitive dispatch is treated here.

## Prospective owner placement

The generic declarations and suffix theorem fit the existing `TapeToPrimitive.lean` owner. Its geometry declarations would add the existing `VisitedSpace` module as an import; the inspected VisitedSpace owner imports only Mathlib modules, so this direction introduces no reverse project dependency in the examined owners. Keep the external draft's Examples import out of the production library owner.

Append the connected example namespace blocks to the existing Examples owner, after their referenced fixtures. The earlier three concatenation lemmas retain their separately proposed VisitedSpace owner. No new operational model, maximal interface record, alternative tape representation, or production module is proposed. Root and the existing reviewers own final placement and all normal build/audit checks.

## Static assessment and remaining actual checks

The source-level statement assessment found no intended reliance on a desired target bound or invented cost. Each one-step equation follows the literal native optional iterate, the complete endpoint follows existing `statement_exact`, and the stationary geometry follows the actual emitted action. The branch cases exercise register updates before control selection, while the empty-peek case separates stationary dispatch from a later genuine movement.

All new proof text remains uncompiled. Actual elaboration must confirm the raw trAux lemma's instance requirements, stmtStRec induction elaboration, native function-valued alphabet defaults, complete pair/control types, hidden machine instances, and the exact reductions used by the concrete specializations. The carrier intentionally prints all nine public claim types and bodies; root must record any printer elisions or unread ranges and inspect the actual transitive axiom outputs. Preserve every failing source/log if repair is needed, without changing fixed expectations merely to obtain a pass. No admissions or resource/transparency/linter changes are proposed.

This increment supplies the stationary leading segment needed before the action/shuttle case of a future InternalHeight induction. It does not show that arbitrary go or ret controls are stationary: empty peek's go actually moves left, and a ret above the marker moves left. A later marker-guarded ret activation can reuse the arbitrary-body trNormal helper only after proving the actual branch selection.

Still open: InternalHeight itself; selected old/new stack-height hypotheses; outward, action, and return primitive-prefix intervals; the full `[-1, H]` and `H + 2` claims; finite-control command/position transport; ordinary/reflected and combined print/move geometry; and all unrelated acceptance, NP, and textbook qualification obligations. The time-derived visited-space result remains unchanged.
