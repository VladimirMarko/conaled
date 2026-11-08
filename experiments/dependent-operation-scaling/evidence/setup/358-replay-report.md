# #358 checkpoint replay and evidence assessment

All eight exact checkpoint replays passed. Separate exhaustive current-module axiom audits also passed for all eight checkpoints. This is bounded replay and evidence assessment, not whole-task acceptance or the independent semantic statement review.

The frozen candidate is `2838b20125fc4253f55eb1feb45f069f604175df`. The unchanged handoffs are `trial358/native` and `trial358/shared`; originals remain in `trial358/evidence/{native,shared}`. No original submission, failed attempt, public file, runner or checker was edited. Every original evidence file was hashed before replay and checked again after replay and audits; all bytes match.

| Arm | Stage | Exact checkpoint | Bytes | Replay exit | Audited logical declarations |
|---|---|---|---:|---:|---:|
| Native | A | Attempt02 | 3376 | 0 | 129 |
| Native | B | Attempt03 | 5335 | 0 | 172 |
| Native | C | Attempt07 | 13182 | 0 | 268 |
| Native | Repair | Attempt08 | 13990 | 0 | 272 |
| Shared | A | Attempt03 | 3449 | 0 | 128 |
| Shared | B | Attempt04 | 6456 | 0 | 173 |
| Shared | C | Attempt06 | 15596 | 0 | 267 |
| Shared | Repair | Attempt07 | 16943 | 0 | 272 |

Replay sources were byte-identical copies named ReplayA, ReplayB, ReplayC and ReplayRepair. Each ran through `direnv exec . python3 /tmp/conaled-362-orchestration/run_attempt.py attempts/Replay<stage>.lean` from its handoff. The invoked runner is byte-identical to each handoff's frozen runner. Its internal lock serialized checking; no outer lock was used. Wrapper records verify the frozen public files before and after every attempt. Independent whole-handoff checks also passed before/after each batch and at final inspection.

Native manifest SHA-256 remains `08faf6b4cac1ce522fa7f81198f5f6e0c418f1fa9d56d0466ec9ea99718add65`; shared remains `de11f396b5fee2be8a264cde2e2c0cdb6856dcb6b7571156f2e44b7bea76eafd`. These match the dispatch/setup gate. Sources, wrapper archives, timing receipts and replay stdout are under `trial358/setup/replay-native` and `trial358/setup/replay-shared`. Replay artifacts were removed from author attempt directories after archiving. `358-replay-receipts.json` records checkpoint hashes, results, runner/wrapper hashes, timing and the complete original-evidence hash inventory.

The checker explicitly leaves axiom checks to the coordinator. Accordingly the independent Audit2A/B/C/Repair sources add only core Lean audit imports before the exact original bytes and a current-module audit command afterwards. This command enumerates current-module constants through `foldStage2`, including helper definitions, private declarations and generated auxiliaries; it rejects source unsafe declarations and checks every kernel-safe root's transitive `Lean.collectAxioms` result against propext, Classical.choice and Quot.sound. Every checkpoint passed, with zero unsafe runtime exclusions. The logs list each root and its axioms. No inference was made from integrated ProofAudit coverage of these otherwise unimported experiment files. Audit receipts are in `358-audit2-receipts.json`; complete audit sources and diagnostics are beside the replay archives.

## Original attempt and timing evidence

Every archived original source matches its corresponding AttemptNN file. Every hash in each original result's evidence inventory matches, every wrapper result verified public inputs before/after, and wrapper/runner exit codes agree. The 15 original checks include six failures, all retained. Native failures are Attempt01 (syntax, identifier and proof errors), Attempt04 (unary executor syntax/proof errors), and Attempt06 (rewriting under transparency). Shared failures are Attempt01 (namespace/identifier syntax), Attempt02 (old operation reduction), and Attempt05 (arithmetic proof and syntax). Elaborator-generated sorry warnings on failed files do not constitute accepted results. Native C and repair retain an unused-tactic warning; their replay and axiom audit succeed.

| Arm | Stage | Checks | Failed checks | Wrapper checking seconds | Lock wait seconds | Reported active seconds |
|---|---|---:|---:|---:|---:|---:|
| Native | A | 2 | 1 | 3.886356 | 5.150759 | 64.849241 |
| Native | B | 1 | 0 | 1.897405 | 0.000084 | 44.999916 |
| Native | C | 4 | 2 | 8.497129 | 0.000429 | 133.999571 |
| Native | Repair | 1 | 0 | 2.113145 | 0.000115 | 84.827181 |
| Shared | A | 3 | 2 | 5.307522 | 0.000323 | 110.766556 |
| Shared | B | 1 | 0 | 2.046151 | 0.000121 | 49.276469 |
| Shared | C | 2 | 1 | 4.218723 | 0.000217 | 124.919483 |
| Shared | Repair | 1 | 0 | 2.219313 | 0.000120 | 76.897853 |

`358-original-evidence-audit.json` preserves the per-attempt data behind these totals, including RSS and timestamps. Stage boundaries are contiguous within each author's record and enclose the associated runner checks. Reported active time equals reported wall time less recorded lock waiting, within rounding. Every stage is below its 20/20/35/15-minute and 15/15/25/10-check cap. Native has eight original checks; shared has seven. Both report stopping after successful checkpoints, pending external acceptance. An earlier successful partial file is not substituted for a later checkpoint.

The author clock is not a complete independently instrumented activity clock. Native starts at its reported 16:42:07Z; shared charges an estimated 30 seconds of initial reading before its first recorded 16:43:52Z timestamp, giving 16:43:22Z. These limitations are already disclosed in dispatch and author records. Final-summary/report preparation after the last recorded endpoint is not independently timed. Do not report the resulting active seconds as exact total labor or infer precise small productivity differences. Reading/editing/reporting costs inside the reported stage intervals are included; no thermal suspension was reported. Staggered dispatch and the native first-check lock wait remain visible. Peak memory is Linux RUSAGE_CHILDREN high-water RSS for each runner invocation, not simultaneous aggregate memory; all raw values are retained.

Both authors report a failed shell edit outside direnv and a subsequent missing-file runner rejection before Lean was launched. These incidents are preserved in their activity/checkpoint records, but no wrapper archive exists because invocation validation failed before archive creation. They are not additional archived Lean checks; their time remains within the reported stage wall interval. Available evidence does not provide independent shell-level receipts for those author-reported events.

Dispatch records identify fresh fork-none authors, no model/reasoning override, and no prior task/fixture/solution exposure. Exact model/reasoning telemetry is unavailable and remains marked unavailable. Both report no substantive assistance or cross-arm exposure. I assessed consistency of these records; the access contract is not an OS sandbox and these records do not prove absence of undisclosed access. Both authors saw the cumulative task initially and explicitly acknowledge anticipation of later stages. Prepared closure/framework costs remain separate treatment/setup costs, with earlier uninstrumented effort unknown.

## Coordinator costs and discrepancies

There were eight successful exact replays and sixteen coordinator audit checks: eight failed AuditA/B/C/Repair harness checks and eight successful Audit2 checks. The first audit harness omitted Nat type annotations on its counters, causing Lean to infer MessageData from logging. All failures are archived, with timing, in the replay setup directories and `358-audit-receipts.json`. Only the coordinator audit harness changed; original source bytes and public inputs did not. These sixteen checks do not belong to author counts.

After the first successful native ReplayA, moving its read-only archive failed with a permission error. A byte-identical copied archive was verified, and only that new replay directory's permissions were adjusted to complete archival. ReplayA was not rerun. An attempted coordinator-script edit then failed because python3 was invoked outside direnv, and a script restart encountered the existing replay directory. Those failures ran no Lean check. The resumed orchestration retained the first successful receipt and completed the remaining seven checks. These are post-trial coordinator costs, not author assistance or changes to results.

No source-byte, manifest, checkpoint-selection, exit-status or cap discrepancy was found. The clock precision, unavailable model telemetry and unarchived pre-Lean invocation mistakes above remain evidence limitations. Semantic validity and obligation coverage belong to the separately assigned statement assessment; final issue acceptance and durable integration remain with the coordinator.
