# #358 independent trial statement preflight

Reviewer: `/root/361_acceptance`. I did not prepare or review the #358 fixtures, freeze, tasks or author submissions before exposure. Earlier exposure was the generic integration preflight and full #358 issue requirements. I contributed to #359 and remain ineligible to review that implementation. This review supplies no author hints or repairs and changes no author artifact.

Freeze: `2838b20125fc4253f55eb1feb45f069f604175df`. Requirements: complete `358.json`, frozen `experiments/dependent-operation-scaling/protocol.md` and `task.md`, independent `Examples.DependentOperationTrialSpec`, and each arm's allowed support. I inspected the native completed snapshots first. Shared snapshots were inspected only after root reported its completed, frozen repair submission. No Lean replay was run; root coordinates replay and declaration/axiom checks.

**Statement assessment: all four frozen stages are met by each arm; zero identified semantic findings.** This is a preparatory trial assessment, not final #358 Spec approval. Exact replay, evidence/report integration and the final whole-issue candidate remain outside this result. Failures and incomplete outcomes would remain legitimate empirical evidence; none is repaired or retroactively credited here.

## Exact submissions

Paths below are relative to `/tmp/conaled-362-orchestration/trial358/`.

| Arm/stage | Snapshot | SHA-256 |
|---|---|---|
| Native A | native/attempts/Attempt02.lean | `4a27c255e82dc6d63db9f4d8e7bf46504f23c89e5ca7b1abcc12738652745f58` |
| Native B | native/attempts/Attempt03.lean | `ea47db12ef73292655965246eaeea4b65dc80318fc3e29d65705091a05a67aa8` |
| Native C | native/attempts/Attempt07.lean | `d2e107e6436e96a4102b8bf43924bbdd73937cffb139e9c3cdf510d89f5190ff` |
| Native repair | native/attempts/Attempt08.lean | `99d5436e97a3c324384342e7c6928971dd89c80ed68d81e1f3b875673ec73a06` |
| Shared A | shared/attempts/Attempt03.lean | `a17e87345f5ca755680641e0c6fe52d918fead6f971ada25c4bc8772dfdc95f5` |
| Shared B | shared/attempts/Attempt04.lean | `6d4e4d6e099feeb0f704fff00aae9a458e4e436bbbb5d175c6df6b8b05d697f3` |
| Shared C | shared/attempts/Attempt06.lean | `d682da50727f5dc4aa90357e2c81468ef4ae2c23c18e7c30baaac50dc59dd083` |
| Shared repair | shared/attempts/Attempt07.lean | `323653e8c1b28c90e1800d783a5c1f91b79cf8c19282446804658f24d59fec79` |

For all 15 attempts, each live attempt file equals its archived `checks/AttemptNN/Source.lean`, and the computed SHA-256 equals the recorded source hash. Checkpoint wrapper receipts report Lean exit 0. Their statuses explicitly leave declaration/statement/axiom acceptance pending. This inspection does not replace replay.

## Acceptance matrix

| Frozen obligation | Native exact evidence | Shared exact evidence | Assessment |
|---|---|---|---|
| A: locally admitted rotation and actual source typing | `Prim.rotate`, dependent `meaning`, `Term Prim V n`, `stageOne` | `Op.rotate`, dependent `operate`, `Term Op V n`, `stageOne` | Met in A; intrinsic source indices are substantive typing, not a True predicate. |
| A: universal selected execution including variables | `localT`, generic `preservation`, `all_total`, `variable_case` | `total_local`, `total_sound` through `emit_sound`, `empty_result` | Met in A for arbitrary typed terms and variable environments. Primitive hypotheses are proved, not supplied as final program equations. |
| A: two real compilation passes and exact quotation | `macros`, `expand`, `word`, generic `quotation` | `instructions`, `lower`, `bytecode`, `quotation` through `emit_lower` | Met in A. Macro emission followed by flatMap expansion produces executable instruction data; padding expands to distinct left/right words. The task permits these passes without a second indexed target tree. |
| A: oracle and boundary | `stageOne_meaning`, `stageOne_quote`, `stageOne_result`, `wraparound` | Same roles plus `empty_result` | Met: bound4/input3 produces selected4; last position wraps to zero, including n=0. |
| B: halving and independent distance realization | `Prim.half`, `runD`, `localD`, `all_distances` | `Op.half`, `runDistances`, `distances_local`, `distances_sound` | Met in B. Distance algorithms use their own coordinates; no total executor or source interpreter call. Full bound/position observation retained. |
| B: four-step exact client and failed interaction | `stageTwo_*`, `rotate_half_noncommute` at input4 | `stageTwo_*`, `rotate_half_do_not_commute` at input0 | Met in B: bound5/input4 gives position1. Both are inhabited counterexamples to commuting, not a claim that local correctness implies interaction. |
| C: noninvertible dependent compression | `Prim.compress : Prim n (n/2)`, all three local laws | `Op.compress : Op n (n/2)`, all three local laws | Met in C; changed result index is retained by intrinsic typing and result encoding. |
| C: third independent executor and full lists | `runU`, `localU`, `all_unary` | `runUnary`, `unary_local`, `unary_sound` | Met in C. Algorithms use list operations/lengths/replication, not previous machines or Spec. Equalities compare entire list pairs, not only lengths. |
| C: nine-step source and exact ten-instruction quotation | `stageThree`, `stageThree_meaning`, `stageThree_quote`, `stageThree_results` | `stageThree`, `stageThree_meaning`, `stageThree_quote`, separate three-backend result theorems | Met in C: original bound8/input6 yields bound7/position3; padding contributes two actual instructions. |
| C: actual typed substitutions and general two-stage theorem | `reflectSub`, `resetSub`, genuine `graft`, `eval_sub`, backend-parametric `two_substitution`; concrete total/distance/unary outcomes | `reflectVars`, `resetVars`, genuine `graft`; `total_twice`, `distances_twice`, `unary_twice` through `eval_twice`; concrete source/total outcomes | Met in C for arbitrary typed substitutions. Concrete reflection then resetting inner variables yields position2 then1. Shared general backend theorems cover those same concrete substitutions even without separate named numerical distance/unary corollaries. |
| C: selected dependent tail | `selectedTail`, partial checked `observeTail`, three `compiled_tail*` theorems | `Tail`, `selectedTail`, `recover_position`, three backend tail theorems | Met at the frozen chosen-last contract: the preserved selected position determines `Fin(i.val+1)` and its selected last member. Neither claims preservation of arbitrary incoming tail data. |
| C: reject same-bound wrong position and recover old clients | `wrong_position`, `liftOld_meaning`, `native_selector_recovered`, old interaction controls | `stageThree_wrong`, actual `includeOld` compiler/local meaning, `recovered_selector`, old interaction controls | Met in C. Shared rejection is on selected source meaning and transfers through universal executable preservation. Existing regression modules remain the eventual integration build's responsibility. |
| Repair: source/three executors changed together | `meaning` now `Spec.backward`, changed `runT/runD/runU`, local laws and unchanged generic preservation | `operate` now `Spec.backward`, changed three executors, local laws and unchanged generic preservation | Met. Runtime algorithms change independently; source constructor and bytecode syntax remain unchanged. |
| Repair: independent recomputed clients and interactions | `repairStageOne/Two/Three`, `repair_oracles`, changed concrete results; counterexample moves to input0 | `repairedStageOne/Two/Three`, `repaired_oracles`, changed concrete results; retained input0 rejection plus `repaired_interaction_values` | Met: A2, B0, C4, reflected3, twice5. Backward zero wraps to last. Explicit stage meaning equations and universal executor/substitution laws connect repaired oracles to actual compiled clients. |

## Semantic boundaries and evidence interpretation

Both arms give arbitrary-term theorems over indexed source contexts. Runtime instructions contain operation tags rather than derivation trees, correctness proofs or precomputed answers. Spec functions occur in source meaning, where they are the independent oracle; runtime algorithms do not call them. The two passes are executable macro emission and word expansion. Do not describe either submission as adding a second typed target calculus. This is within the frozen alternative allowed by the task.

For dependent tails, native reconstruction rejects invalid machine states with `none`, while shared reconstruction clamps a supplied index to the known bound. Neither convention hides an error on the advertised domain: each universal executor theorem already proves the exact valid encoding before the tail reconstruction theorem applies. The chosen last tail member is determined by the preserved position. This is precisely the bounded requested tail and does not test arbitrary fiber values or a general dependent-context frontend.

The native arm independently wrote structural preservation and quotation proofs once in A and reused native graft semantics in C. The shared arm reused prepared `emit_sound`, `emit_lower`, `eval_twice` and `compile_meaning`; it still supplied primitive/backend laws. These are different support costs, not a proof that the shared architecture universally removes obligations. Both reuse their global machinery during repair.

No snapshot requires equivalence of compression, erases the selected result to mere bounds, or asks for its desired whole-program conclusion as a primitive law. The old-source inclusion is semantic recovery of arbitrary old terms, with concrete positive/negative interaction controls retained. The tasks do not establish the missing full dependent source/model admission from #366.

## Failures retained and not retroactively repaired

Native attempts: 01 failed (namespace-alias syntax and quotation proof goals); 02 passed A; 03 passed B; 04 failed (unary match syntax and resulting obligations); 05 passed an intermediate C draft; 06 failed (old-term proof rewrite/transparency); 07 passed C; 08 passed repair. The intermediate 05 is not credited with later C additions. Final native C/repair retain an unused-tactic warning, not a logical hole. The A activity record also retains a pre-check missing-python environment failure and rejected missing-file wrapper invocation, with no Lean run attributed to the latter.

Shared attempts: 01 failed (namespace-alias syntax and dependent unknown names); 02 failed (old reflection local proof); 03 passed A; 04 passed B; 05 failed (unary arithmetic proof and a syntax delimiter); 06 passed C; 07 passed repair. Exact failed snapshots and diagnostics remain under each arm's checks directory. Error-recovery `sorry` warnings in failed checks do not make those attempts accepted.

No author source was edited and no later proof was credited to an earlier stage. Both arms disclosed full cumulative task exposure, so anticipatory work can affect stage comparisons. Timing, memory, exposure, wrapper integrity and assistance claims require the coordinator's retained measurement/protocol evidence; this mathematical preflight does not independently certify all activity accounting. The final report must preserve setup cost and unavailable metadata rather than infer a broad or asymptotic productivity advantage.

## Remaining final acceptance work

Root should replay the exact eight checkpoint snapshots against their frozen input closure, retain declaration/axiom checks and complete measurement/status reconciliation. Then review the final #358 candidate across its implementation, freeze, trials, all failures and report against the whole issue. This assessment can supply the statement-review evidence for those exact snapshots; it does not approve unexamined report claims, changed snapshots or the final issue candidate.
