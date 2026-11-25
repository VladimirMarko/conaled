# Native trace concatenation: small external draft

**Status:** complete admission-free proof text, statically assessed by its implementer, **not compiled or accepted**. This is implementation assistance in the existing review loop. Root owns the compiler, normal dependency environment, installation, build/audit, independent Standards and Spec review, and checkpoints. No project source, Git objects, project outputs, cache, toolchain, resource settings, or existing frozen research files were changed by this task.

## Files and order

- `EXPECTATIONS.md` was written and frozen before the proof draft and before any compiler feedback. Its SHA256 is `d8ffae1a7d60fbe91b86f47e0beca5da8c1d80b9384cf098c6a3f72c65e31669` (6816 bytes).
- `TraceConcatenation.lean` is one complete external file. It imports the existing generic owner and existing examples so root can check the whole increment without inventing an external module dependency or installing author-generated objects.
- `MANIFEST.json` binds the exact deliverable bytes, current relevant source/guidance bytes, read ranges, source identity supplied by root, and uncompiled status. This README is an implementation handoff, not an independent review record.

For integration, the three reusable lemmas belong in `Applications/Resources/TuringSimulation/VisitedSpace.lean`; the connected declarations belong with `Examples/TuringSimulation.lean`. The external file's import of Examples is only for its combined draft and is not a proposed library-to-Examples dependency.

## Public contract and mathematical argument

The reusable declarations are in `Resources.TuringSimulation.VisitedSpace`:

| Declaration | Premise and conclusion | Proof route |
|---|---|---|
| `cfgAt_add_of_live` | Given the actual equality `cfgAt M start n = some finish`, every suffix has `cfgAt M start (n + k) = cfgAt M finish k`. | Induct on `k` using the existing native optional-iterate successor equation. Retain the entire configurations. |
| `commandAt_add_of_live` | The same premise gives equality of the entire commands at `n + k` and suffix `k`. | Rewrite the actual configuration in the existing command observer. This keeps next control, move direction or written symbol, and absence. |
| `headPosition_add_of_live` | The same premise gives `headPosition M start origin (n + k) = headPosition M finish (headPosition M start origin n) k`. | Induct on `k`; use the preceding full-command equality inside the actual `commandOffset` recurrence. |

Quantification retains arbitrary alphabet/control types with the native inhabited instances, an arbitrary supplied machine and complete start/finish configurations, arbitrary integer origin, and arbitrary natural split/suffix lengths. No finite-type, decidable-equality, support, initial-list, normalization, or height premise is added. The live split premise is directly supplied by an actual native prefix; it is not a desired geometry premise.

Both zero-length cases are included. Suffixes can reach and extend beyond outer none. The configuration/command equalities then retain `none`, while the head observer retains its last coordinate as bookkeeping. That bookkeeping coordinate is not a new visit: the existing `visitedCells` definition excludes absent prefixes, and its separate terminal lemmas remain unchanged.

The key distinction remains: equality of tape contents does not determine displacement. In particular a blank tape can be invariant under movement. The position theorem depends on the actual emitted commands, not solely on equality of tape/configuration endpoints or on an assigned source-event tariff.

## Connected existing fixture

The examples are in `Examples.TuringSimulation.VisitedSpace.TraceConcatenation`. They reuse the existing genuine initialized empty-peek fixture rather than define a new machine:

- `peek_resume_trace k` consumes all three generic lemmas at actual prefix two, where the full configuration is `peekLeft` and the global origin-zero coordinate is minus one. Its equality covers every suffix `k`, including zero and suffixes after termination.
- `peek_split_selected_command` consumes command concatenation to recover `some ((some peekGotoRet, true), TM0.Stmt.move Dir.right)` and then its actual offset one.
- `peek_split_completion` derives the local suffix from the existing `peek_step2` through `peek_step5` equations, then consumes the generic equalities to recover full initialized live-five and outer-none-six endpoints, both coordinates zero, and the absent command at outer none. It also retains the true register and exact initial tape at the live endpoint.
- `peek_resume_shifted` applies coordinate concatenation to the same machine/configuration with supplied origin seven. The split coordinate is six and the first suffix move returns to seven.

The private `peek_left_prefixes` helper establishes actual suffix configurations; it does not assume the composed full-run conclusion. Small coordinate reductions use `decide`, as the existing fixture does, after the literal outcomes were fixed in EXPECTATIONS. The connected conclusions explicitly invoke the new public lemmas; they are not merely independent re-proofs of the old list of positions.

The two local instance commands intentionally match the existing fixture: `Pi.instInhabited` for `Unit → Option Bool`, and control default `(some (peekTapeProgram (.normal ())), false)`. The supplied initialized tape, raw `none`, marker, source main, register, and clocks remain unchanged. Reopening a namespace does not reopen its previous local instance commands, which is why these explicit selections are retained here.

## Static statement assessment and pending checks

The implementer compared all proposed statements and their derivations against the current native definitions and retained literal calculations. The generic premise is satisfiable in the fixture through `peek_actual_prefixes.2.1`. The full command is preserved before its offset is used. The live endpoint and later outer-none observation are separate; the cases never infer the clock from endpoint equality.

No compiler or checker has run on these declarations. Root must check the complete external file in the ordinary environment, read the actual elaborated generic and connected statements, inspect proof dependencies, and route any integration through the existing review loop. In particular the local defaults, hidden native instances, function-valued alphabet, complete optional cfg endpoints, full command type, integer origin, and conjunction indexing should be confirmed from actual output. Any elaboration repair must preserve the fixed expectations. No resource/transparency/linter override or admission is proposed.

## Remaining scope

This increment supplies a reusable split operation needed by the next height argument. It supplies no `InternalHeight` predicate/proof, no primitive internal-action interval proof, no `[-1, H]` theorem, and no `H + 2` visited-span theorem. The already proved time-derived bound remains separate. No occupancy bound follows for arbitrary other tracks. Finite-control command transport, ordinary/reflected wrapper coordinates, and conventional combined print/move geometry remain their distinct later obligations. There is no new NP, conventional-machine integration, whole-library acceptance, or textbook-completion claim.

The earlier reconstructed plan is retained separately at `work/space154/PLAN.md`; it is not promoted to a proved result by this draft.
