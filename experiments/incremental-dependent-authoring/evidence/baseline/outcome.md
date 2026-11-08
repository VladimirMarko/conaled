# Native author outcome

Final submission: `attempts/Attempt05.lean` (namespace `IncrementalNative`). Archived exact bytes: `attempts/checks/Attempt05/Source.lean`. SHA-256: `a70ad60ebd81ea6ca54861aa9a22d1be2d26adcca2f74002415f6e86326c2786`. Size: 248 lines, 11,329 bytes.

Wrapper check passed at 2026-11-08 08:09:18.395047 UTC, with no Lean diagnostics. Frozen public inputs verified before and after. Five archived checks: Attempt01–03 failed, Attempt04–05 passed. One additional wrapper invocation rejected a missing Attempt02 file before creating an archive, after Python was initially invoked without direnv; no Lean ran on that invocation. All Lean checks used the unchanged wrapper.

## Requirement coverage

1. `Ix`, `generate`, and `Ix.quote` construct the schedule expression. `raw` is the actual snd/pair quotation with s(index) and t(index). `Ix.typed`, `familyTyped`, and `rawTyped` construct native typing derivations in Γn, including the firstBeta/familyCong conversion to `resultType = B(s(index))`. `afterF`, `afterG`, and `twoStage` supply the retained inclusion/fullG path. `TargetCode.quote` uses the actual Elimination.second dependent-split template and Elimination.pack; `quotation` identifies it with G applied to the actual source quotation.

2. `SourcePair`/`SourceCode` and `TargetPair`/`TargetCode` are executable carriers independent of derivations. `Ix.eval` computes arithmetic; the pair executors construct the dependent pair; the source observer projects it and the target observer eliminates it. Their implementation calls neither Spec.run nor Spec.selected. `execution` connects the two executions, and `selected` proves the arbitrary-schedule selected packet, including both index and component. The bounded interpretation is stated beside these definitions.

3. `generate_append` proves code concatenation for arbitrary lists and base expression. `eval_append` and `selected_append` give execution and final selected-output consequences. The second program receives the completed first index, with the dependent pair constructed after the complete arithmetic schedule. `empty_selected` specializes the general selected theorem, and `twoStage` retains F/G proof translation.

4. `envTyped` proves the native typed substitution for any index replacement. `sigmaIndex` and `tauIndex` have raw images s(var m) and d(var m); each telescope uses the same SingleV representation, with its sole variable understood as n, k, then m at successive stages. `firstSubstituted` and `twiceSubstituted` apply the actual native substitution admissibility theorem. `twice_raw` and `twice_type` identify the resulting raw term and dependent type with the executable program on `twiceIndex`. `twice_target_quote` connects the translated substituted term to that target quotation. `twice_selected` proves the required selected output at sigma(tau(n)) for arbitrary schedules and input.

5. `demo_value` uses `selected`; `substituted_value` uses `twice_selected`; `reject_wrong` uses `substituted_value`. These recover the two supplied oracles and reject the alternative component at the same dependency index.

No known requirement gaps after local statement review. Coordinator replay, elaborated-statement review and axiom acceptance remain pending; the author wrapper result is not a substitute for those checks. No assumptions, sorry/admit, or added axioms were introduced. No proof assistance or environment assistance was requested. No interruptions occurred.

Stopping reason: complete passing submission within both budgets. Author work stops with this outcome record at approximately 2026-11-08 08:09:40 UTC, from the 08:05:00 UTC dispatch (approximately 4 minutes 40 seconds including reading, editing and reporting). No further proof work will be performed.
