# Prospective integration and statement-query plan

**Status:** uncompiled preparation only. The root-reported recovery154 source remains unchanged. The new query and this map do not install declarations, run a compiler, certify a candidate, or start another review axis. Existing task acceptance requirements and unresolved findings remain with root and the same review loop.

## Immutable inputs

The proposed proof input is `../TraceConcatenation.lean`, SHA256 `a9639107bc211e0ee999e6d30422e4429d298ab7b5c4ec418480e0dfceec0bcf`, 7191 bytes, 156 lines. The fixed mathematical expectations are `../EXPECTATIONS.md`, SHA256 `d8ffae1a7d60fbe91b86f47e0beca5da8c1d80b9384cf098c6a3f72c65e31669`, 6816 bytes. The original README and MANIFEST remain unchanged; the latter binds the source and guidance that were read.

The baseline source identity supplied by root is commit `0959a1c9d59660eec33ca4c9d971d74a8bc54378`, tree `655ddb1ee2a730d73a7b0fb5eda5a3e3c40eb669`, restored under `work/conaled154`. Root reports its owner and query checks passed. Those existing results do not validate the new draft.

## Two distinct statement-reading routes

`TraceConcatenationStatements.lean` is a **normal-import carrier**. It imports `Applications.Resources.TuringSimulation.VisitedSpace` and `Examples.TuringSimulation`, then performs exactly seven `#check`, seven `#print`, and seven `#print axioms` commands. `pp.all` is true for every query. It declares no alternate theorem, supplies no namespace alias, and uses no custom dependency path or generated project object.

The unchanged recovery154 owners do not yet export the seven new names. Therefore this carrier is intended to run after root integrates the checked declarations and the ordinary Lake build produces their owner outputs. Running it now against the unchanged imports would report missing declarations; that is not a mathematical test of the draft.

For the **first pre-integration check**, root can check the complete frozen external draft through the existing normal environment. To read the same expanded statements in that local declaration environment, root may create a separately named, separately hash-bound derived copy containing the complete frozen draft followed by the query commands starting at `set_option pp.all true` in the carrier. The import header must remain at the top from the original draft; do not append a second import header after declarations. Preserve the frozen draft and every actual attempt. This reads locally checked draft declarations; it does not replace the later normal-import query against the installed owner exports. No compiler command or derived check copy has been created by this agent.

## Exact public query inventory

The carrier queries these seven names in this order for each of its three command groups:

1. `Resources.TuringSimulation.VisitedSpace.cfgAt_add_of_live`
2. `Resources.TuringSimulation.VisitedSpace.commandAt_add_of_live`
3. `Resources.TuringSimulation.VisitedSpace.headPosition_add_of_live`
4. `Examples.TuringSimulation.VisitedSpace.TraceConcatenation.peek_resume_trace`
5. `Examples.TuringSimulation.VisitedSpace.TraceConcatenation.peek_split_selected_command`
6. `Examples.TuringSimulation.VisitedSpace.TraceConcatenation.peek_split_completion`
7. `Examples.TuringSimulation.VisitedSpace.TraceConcatenation.peek_resume_shifted`

The private `peek_left_prefixes` helper is used by the completion result. Its actual generated private name can change with the module name on integration. No promise of a stable public name for that helper is made. The seven transitive axiom queries are useful focused evidence; they do not replace the repository's exhaustive applicable audit, including private and generated declarations.

## Source integration map

| Frozen draft segment | Prospective production owner | Placement and preservation |
|---|---|---|
| Lines 26–55: three generic doc comments and theorem declarations | `Applications/Resources/TuringSimulation/VisitedSpace.lean` | Insert inside its existing `NativeRun` section, immediately after `cfgAt_add_of_none` and before `visitedCells_add_of_none`. The existing section already supplies `Γ`, `Q`, native inhabited instances, and the required observer definitions. Do not duplicate the draft's imports, namespace wrapper, variable command, or options. Preserve names, argument order, statements, and proofs unless actual compiler diagnostics require a recorded repair. |
| Lines 59–156: complete example namespace block | `Examples/TuringSimulation.lean` | Place after the existing `end Examples.TuringSimulation.VisitedSpace`, before `OrdinaryPackageCases`. Keep the `TraceConcatenation` namespace, both explicit local instances, all four public results, and private suffix helper. Reuse the existing initialized fixture and step lemmas unchanged. |
| No production source insertion | This query carrier and handoff files | Keep queries/evidence outside the source diff. The generic owner must not acquire an import from Examples. The existing Examples owner already imports VisitedSpace, so no new production module or entrypoint import is proposed. |

This is a map, not an instruction to bypass root's current capture or review boundaries. Root may choose a separately staged candidate and record any mechanically different placement. Old acceptance scope, baseline, affected clients, quarantines, and whole-library obligations remain in force.

## Expectation and evidence gates for this increment

### 1. Preserve the actual source premise and semantic observations

Inspect the actual elaborated types, not only their short printed names. The execution premise must be the literal `cfgAt M start n = some finish` for the same supplied native machine and complete configurations. The conclusion must quantify over arbitrary suffix length. The command conclusion must retain the whole `Option (Q × TM0.Stmt Γ)`, including next control. The position conclusion must carry `headPosition M start origin n` into the suffix origin and use actual command offsets in its derivation.

Retain arbitrary integer origin, both native inhabited instances, zero-length segments, and suffixes after outer none. Do not add a desired position bound, replacement execution witness, finite-type premise, decidable-control equality, or default-reset condition. The source observer already uses qualified `Bind.bind`; no alternate resource bind or optional-iteration semantics is proposed.

### 2. Preserve the fixed literal fixture

- The existing source main is Unit.unit; the initialized register remains false. The local control default remains `(some (peekTapeProgram (.normal ())), false)`, and the function-valued alphabet uses the existing Pi default.
- Raw input is empty (`none`), distinct from present false. Its marker remains true at the initialized head. Do not alter the supplied `peekStart`, any fixture definition, or the native translated alphabet blank.
- Prefix two is the actual `peekLeft` configuration at origin-zero coordinate minus one. Its full next command is `some ((some peekGotoRet, true), TM0.Stmt.move Dir.right)`, offset one.
- From that split, suffix lengths one/two/three reach the complete `peekBack`/`peekRet`/`peekHalt` configurations; suffix four is outer none. Composition must retain global live five, global outer none six, both coordinates zero, absent command at outer none, true final register, and exact initial tape at live halt.
- Origin seven gives split coordinate six; its next move returns to seven. The same machine, tape, source defaults, and clocks are used.
- All connected conclusions must continue to consume the new public concatenation results. Replacing those connections by independent reductions alone would leave the new interface unexercised.

### 3. Record actual checks and reading boundaries

Root owns the first actual compiler after the recovery backup, through the normal environment without resource/transparency/linter overrides or admissions. Preserve actual exit status, exact checked source, relevant input binding, and complete stdout/stderr for each attempt. A header or a planned check is not a passing result.

After a successful draft check, read the expanded seven `#check` types, seven `#print` outputs, and seven axiom outputs. Record any printer elision or unread range rather than claiming an unqualified full reading. Pay particular attention to hidden native instances and the complete optional endpoints. A successful local draft check does not certify the later installed bodies; after source integration and the applicable ordinary owner build, run the normal-import carrier and bind its evidence to that candidate's owner outputs.

Any proof repair must retain the old failing source and diagnostics and leave EXPECTATIONS unchanged unless a separately stated mathematical reason warrants correction. No such correction is currently proposed. Root's existing independent Standards and Spec process, applicable build, exhaustive audit, and final source comparison remain separate from this implementer handoff.

### 4. Keep the bounded claim

The increment supplies actual trace concatenation and one connected initialized fixture. It does not prove `InternalHeight`, the head interval `[-1, H]`, the `H + 2` visited span, a bound on all other-track occupancy, ordinary/reflected or combined print/move coordinate transport, a new NP result, textbook qualification, or whole-project acceptance. The already proved time-derived visited-space bound is unchanged. Coordinates retained after outer none remain bookkeeping, not additional visits.
