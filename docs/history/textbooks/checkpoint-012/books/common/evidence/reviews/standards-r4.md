# Standards review — textbook integration, round 4

**Source/handoff outcome: Passed.** The frozen candidate and inspected handoff are ready for source delivery under the user's delegated-validation instruction. Source analysis is complete; **new Standards findings: 0; unresolved new source/handoff findings: 0**.

**Final acceptance status: Pending receiving validation; no final approval.** `INT-SP-001` remains **open-delegated-receiving-gate**, owned by the receiving integrator through `INT-090`. Full guarded build, exhaustive audit, both final review approvals, immediate verification and final snapshot comparison remain required. This assessment does not make a missing local full pass a prerequisite for authorized mathematical work or source checkpointing.

Review cut: 2026-11-14T20:44:55.067757+00:00. Reviewer: `/root/recovery_review/standards_r4`, replacement independent Standards reviewer in the existing ordinary integration loop. The prior reports remain immutable; the Spec axis owns its own findings and outcome. This reviewer performed only read-only source/evidence inspection and wrote this report pair. No compiler, checker, audit, setup, installation, process-control, source/index/ref/checkpoint mutation, network, GitHub or Library operation ran.

## 1. Immutable inputs and full original-base scope

| Input | Identity |
|---|---|
| Original full-spec base and actual merge base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |
| Prior R3 candidate | `16440863ddb14d95c402ce65498e22497e246e72` |
| Current candidate | `18235331da1fe343d09080ca4c41173f9b4d9963` |
| Current tree | `63205d8a3ff27deb3680c613b70085163f289b83` |
| Incorporated upstream | `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` |
| Requirements version | `2026-11-14-evening-probability-and-delegated-validation` |
| Requirements SHA-256 | `a60dd5a4aa4ef46ff8463e47f536961a7f374c5ade74f012c609470e59f6b29c` |
| Scope identity | `04aaeba64ef993665ce417ac3441139f22ca88b53f8865ca6423525f21f2c309` |
| Candidate content identity | `f3d62399fb025c399790a4fd6a9808c9110ebf44d130c984474e9dcb4328cde4` |

The review comparison is `git diff 9175737c2b14ef738cfb6c2cdc68d885c0805ddd...18235331da1fe343d09080ca4c41173f9b4d9963`. Independent Git-object inspection confirms **381 changed paths, including 347 Lean paths, and 322 commits**. The complete manifest has **490 paths**, `entries: {}`, `exclude: []`, and no changed path outside its scope. Both evening helper receipts parse completely, report `ok`, retain integration mode and the original base, and have the dispatched hashes. Their live retention refs resolve to the stated objects. The candidate receipt's **9,178 mode/object entries exactly equal the full candidate tree**, and all 490 scoped live descriptors match the receipt. The reviewed checkout is clean at the candidate and tree above.

The original full-spec base remains fixed. The current candidate has R3 and the new upstream as its two parents; all three nominated VFA/FDSA/PFDS tips remain ancestors. Its nine-path delta is three new probability Lean modules, their public import, three probability/progress documents, the mathematical-suppression research note, and the integration correspondence. **372 of the prior 374 full-scope changed paths retain exactly their R3 mode/blob identity**. The complete commit/path lists remain reproducible from the pinned range; no duplicate broad inventory is needed for this report.

All seven upstream non-entrypoint blobs are exact to the new pin. The public entrypoint retains every import from both parents: 920 current import lines, compared with 919 at R3 and 761 at upstream. This is a source preservation check; the receiving checker still owns full parsed coverage and compilation.

## 2. Applicable standards and justified reuse

I read the actual candidate `AGENTS.md`, implementation and code-review skills, review heuristics, shared review-loop, architectural-quality and domain guidance, glossary, ADR index and ADRs 0001, 0002 and 0010. Statement review follows example-driven-development and its worked example. The evolution/specialization and author-capability criteria in `docs/language-direction.md`, together with the probability and preservation-contract inventory, supply the relevant architectural boundaries.

The user's current requirements control the local issue/spec tracker, optional Nix with exact mandatory pins, and assignment of the final full gate to the receiving integrator. These exceptions leave proof policy, current-candidate identity, independent axes, fixed-base continuity and durability obligations intact. The source/handoff decision is intentionally separate from final library acceptance.

The actual source comparison leaves guidance, skills, checker, audit, snapshot helper, toolchain and dependency pins unchanged against the original base. README's sole original-base change remains the earlier textbook-workstream link; its environment/build/audit sections are unchanged. R4 adds no new fresh-validation trigger through tooling or pin changes. Separately established integrity concerns remain governed by the actual README/runbook.

The R1/R2/R3 Standards source analyses and both R3 navigation addenda are retained at their recorded fingerprints. Their former Blocked outcomes remain historical. Reuse here is supported by the complete unchanged-blob comparison and inspection of the actual affected dependencies; it transfers semantic analysis, not past approvals or compiler results. The new producer does not alter the earlier map, potential, sorting, sequence, physical-container, suspension or persistence implementations. All textbook implementation blobs named in the evening accounting evidence remain exact at R4. The donor-disposition, process and canonical PFDS-register fingerprints still match those reviewed at R3.

The retained full-scope assessment preserves these contracts: ordered occurrence-sensitive sorting and summaries; arbitrary matching initial states and optional failures; actual execution with explicit charge carriers/invariants; valid raw-state restrictions and independent map observations; physical identity separately from value equality; successful cache writes separately from body entries; persistent-history and signed-potential hypotheses; and actual finite occurrence-pivot PMF runs. Neither source preservation nor the new sampler permits inference of equal cost, sharing, runtime, independent successive states, or additional whole-book coverage.

## 3. New source: architecture and statement review

### One resumable execution through existing owners

`Applications/Probability/TableProducer.lean` reuses `PreparedRow.State`, `PreparedRow.step`, `Progress.Producer`, `Progress.Evaluates` and `Progress.Delivers`. State retains the semantic value plus cursor, remaining block width and accumulated code. Silent steps continue that row. A completed row emits its result and initializes the next row at the actual returned cursor, including a self-transition.

`evaluates_of_row` and `row_of_evaluates` relate next-output evaluation to row evaluation in both directions for arbitrary partial row states, retaining the same step count and the exact restarted residual state. They do not assume that an arbitrary partial state has the initialized row's probability law. The later distribution claims explicitly start from `start`.

`delivers_of_trace` and `trace_of_delivers` connect finite delivery to the existing `RowChain.Trace`, preserving the entire ordered output list, final semantic state and cursor. I checked the actual `Trace.zero`, `Trace.next`, `trace_work`, `Delivers.nil/cons`, evaluation uniqueness and silent-evaluation impossibility. The empty chain has one administrative return and zero producer deliveries; positivity of a trace's count justifies subtraction. `delivers_work` derives the initialized producer's cursor equation from this bridge. Its count is inspected bits in this machine, with no arithmetic, lookup, entropy-adapter or host-time tariff implied.

The new measurable-step proof observes the single tape bit at the stored cursor. `prefix_eq` and `endpoint_eq` identify events of actual deliveries with the existing row-chain events. `prefix_mass` and `endpoint_mass` consume those bridges and existing table laws. Explicit finite enumeration, rational row validity, finite carrier and decidable-equality premises remain at their actual scopes; arbitrary-state operational equivalence does not silently widen the initialized distribution law.

### Almost-sure productivity and actual joint blocks

`almostSureProductive` derives each requested finite delivery from `RowChain.table_ae_terminates`. The existing `ProbabilityProgress.ae_coherent_prefixes` then combines the countable family on one conull set and uses deterministic delivery coherence. The quantifier order preserves one tape and one initialized producer for all prefixes. No infinite execution is claimed to halt, and no pathwise universal productivity or finite deadline follows.

`TableProducerStationarity.blockEvent` hides a finite prefix by taking an actual longer delivery of the same producer and dropping exactly the specified number of emissions. `block_succ` retains the first row's returned cursor. `block_succ_mass` uses the existing `PreparedRow.stopped_mass`, whose actual definition/proof retains return value, cursor and work before factoring a measurable suffix event. This is the relevant stopped-cursor argument; fixed-cut independence alone is not substituted for it. Event disjointness uses deterministic result uniqueness.

The generic `stationary_blocks` is an equality of mixtures under the displayed stationary equation for weights `π : α → ℝ≥0∞`; it does **not** require normalized weights. `FiniteMH.producer_stationary_blocks` specializes it to the established target, with nonempty finite state space, positive target weights, normalization and stationarity supplied by the existing MH owner. The explicit mixture keeps initial target selection independent of the fair tape. The conclusion preserves whole ordered finite-block probabilities, including correlations. It supplies no mixing, convergence or empirical-accuracy claim.

### Connected cases and counterexamples

I read all of `Examples/TableProducer.lean` and its concrete MH/table preparation dependencies. The examples connect to public source results: actual `step`/`search` for partial-state resumption and rejection retry; `search_sound` and `Delivers.cons` for consecutive/self emissions; `Table.compile_eq` and `almostSureProductive`; `prefix_mass` for `[false,true]` at mass `1/3`; `endpoint_mass` for the two-step `true` endpoint at `7/9`; and `FiniteMH.producer_stationary_blocks` for the target-initialized pair at `1/4` after every finite shift.

The singleton cases distinguish the relevant negative observations. `changes_not_productive` suppresses all completed outputs on a subsingleton semantic space using the existing silent-evaluation impossibility. `exceptional_not_productive` follows the actual singleton sampler on the all-true tape and rules out any accepted one-bit block. The ordinary singleton producer remains almost surely productive in the positive case. The source also demonstrates that an unchanged MH state can be an accepted self-proposal: filtering unchanged states is not an observation of an acceptance flag.

These are substantive retained source fixtures, with no new compiler or elaborated-type run claimed for R4. Their inclusion under the public entrypoint makes them part of the receiving validation scope. No source-level architectural or statement-methodology defect was found.

## 4. Documentation, textbook scope and ownership

The received probability/progress prose follows the actual source distinctions above. The 470-line mathematical-suppression document explicitly remains a research note: derived views, recoverability, lossy preservation, proposed experiments and no chosen library interface. Its factorization preorder keeps its direction, and descent of an observation is scoped to the image/fibers; no arbitrary out-of-image reconstruction or formal Lean result is asserted. It does not weaken implementation, statement review or validation policy. External literature was not refetched during this read-only review.

The changed textbook correspondence identifies the new upstream and its prospective finite row/stopped-suffix owners. The existing `RandomSelectionRun` and `RandomQuickSortMean` retain occurrence-index PMF recursion and explicit exclusions for random-bit sampling costs. `INT-033` owns a future bridge preserving ranks, duplicates, shrinking domains, actual trace/cost observations and returned-cursor freshness. The record appropriately does not impose stationarity or an infinite stream on terminating algorithms.

I read the full current `COVERAGE.md`, `STATUS.md`, `README.md`, `VALIDATION-HANDOFF.md`, local issue record and source identity records. Coverage keeps three distinct source cuts: detailed historical C2 accounting, the R3 map recovery, and the R4 upstream receipt that changes no textbook proof files. The evening compact account is bound to R3, with the merge receipt supplying the separate R4 preservation binding. It is not represented as a new R4 compiler pass or an exhaustive latest-master manuscript comparison.

The denominators and validation qualifications remain sound: FDSA historical Chapters 1–3, with 112/112 Chapter 2 and 83/83 Chapter 3 obligations; VFA's 30-record/four-exercise Perm mapping and five historically focused-checked staging developments; PFDS Chapter 2's six exercise headings and 35 cited source paths, eight mathematical scopes, and Chapter 1's introductory accounting-only acceptance. The chapter, exercise, lexical-record and mixed-ledger counts are not treated as interchangeable proof percentages. The five preserved VFA staging hashes match the evening evidence.

The selected table/AList/validity slice remains partial. `INT-020`, `INT-021` and `INT-032` keep the generic total-table contract, deletion/Modify/set-delete/valid-graph capabilities, other staging drafts and remaining donor families owned. The canonical PFDS register preserves every historical boundary and validation ID. This review reuses the prior detailed accounting provenance; it does not perform a fresh manuscript audit or independently remap every source row to the expanded library.

## 5. Receiving handoff, source export and resource precision

The handoff binds the exact candidate, tree, upstream, requirements and snapshot. Its procedure retains a clean isolated receiving checkout, exact dependencies/compiler/configuration, the full guarded checker and exhaustive three-axiom audit, a matching `.lake/verification.json`, final independent approvals, immediate `--verify-candidate HEAD`, and helper comparison against the actual accepted input. User delegation assigns execution and troubleshooting; it does not close `INT-SP-001`.

The corrected handoff explicitly explains that applying a standalone patch and committing produces a **new receiving SHA even when the tree is identical**. That receiving commit must be recorded, reviewed under permitted reuse, and validated. The full bundle retains the exact delivered commit and history. Neither patch application nor a matching tree is represented as a compiler/audit result.

Independent read-only regeneration of `git diff --binary --full-index` from upstream to candidate yields **3,544,383 bytes**, SHA-256 `955c71b607aab9e217f1b0e4b9c1ef476f16a4596e9d47192052acc8f8a88498`, matching `patch-export-009.json`. The retained private-index receipt records the exact reconstructed tree; I did not reapply the patch. The catalog has **155 stored refs**, all matching the bundle's advertised OIDs; the bundle advertises **156 including HEAD**. Its 98,957,987-byte hash matches `source/integration.json`. The 149 catalog entries preceding the six new capture aliases match the restored work repository, and the new aliases are present in the exported bundle. No external archive dependency is listed. This establishes the inspected source bindings, while root owns recovery/pack verification and durable upload.

Root's later `intake/integration-handoff-compare-r4.json` reports `ok` for candidate and accepted commit `18235331da1fe343d09080ca4c41173f9b4d9963` with the reviewed scope identity. I inspected its complete 394-byte receipt, SHA-256 `4077c7172c802bbc8070b0bdb8353136143fb8a738f074dd2b95c91cc9a6932c`. It is a handoff content comparison, with final acceptance verification still required later.

Resource prose correctly distinguishes the native launcher's `LEAN_NUM_THREADS` from Lean CLI `-j` and from a universal child-process/core cap. I inspected the frozen launcher/environment/run path and unchanged project configuration; the runtime/CLI behavior is attributed to the retained assessment's explicit primary-source locations at pinned Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. I performed no new upstream fetch, host measurement or benchmark. The record retains visible resource observations without claiming verified quotas, downscaling, diagnosed interruption cause, linear speedup or a defensible current full-build ETA. The normal run path supplies no wall-time timeout; fresh-mode `--jobs` remains distinct from normal Lake scheduling.

The resource note's current Evidence links resolve to the actual archived JSON names. Its final inspected hash is `033b62d94235567565823528a02f0903f048c33ad07e05830b1f16ab93f208b3`. The coordinator's earlier navigation question was resolved before this reviewer opened any finding; no new ID is needed.

## 6. Finding continuity

| Finding/register | Current Standards disposition |
|---|---|
| `INT-ST-001` — Low | **Fixed, retained.** Actual source catalog remains PFDS S9, VFA S10, FDSA S11; the prior correction is unchanged. |
| `INT-ST-002` — Low | **Fixed, retained.** The exact 1,426-byte R3 start observation, SHA-256 `33951558afb5c06a6d3c33141d6279470eed3263bc5d74dcd87e0c5c92a6c28b`, remains retained and explicitly mapped by README. |
| `INT-SP-001` | **Open delegated receiving gate.** The Spec-owned identity and history are preserved; this Standards report does not close or rerank it. |
| VFA `ST-002` / `SP-VAL-001`, prior `ST-006` repair | Retain validation/incident history and original source-fix evidence. No conversion of output-creation failure into a proof failure or current success. |
| FDSA `XT03-CP01` / `XT03-DOC01` | Retain source correction/recheck and receiving/compiler boundary, original base `64c6b777d828ecfe83234fc2aed94600a1f24297`, donor and seven-path/88-name scope. Chapter 4 keeps its original base, three streams, 76 obligations and 11 exercises. |
| PFDS canonical 39 IDs / eight aliases | All dispositions remain in section 5 of `books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md`: 23 repair/static/development closures, two boundaries and 14 distinct open validation IDs. No renamed duplicates or retrospective closures. |

The eight PFDS Standards/shared validation IDs remain `IMPORT-VAL-004`, `CH02-PRE-005`, `SUSP-STD-VAL-001`, `PURE-STD-VAL-001`, `COUNT-STD-VAL-001`, `PERSIST-ACC-STD-VAL-001`, `BODY-COUNT-STD-VAL-001` and `SIGNED-POT-STD-VAL-001`. Paired Spec findings remain independently owned. `SUSP-STAT-001` retains its effectful cached-reference type/result counterexample, and `PREP-10019-02` retains the pure-interpretation/cache-write ownership boundary.

**No new Standards ID was opened; INT-ST-003 remains unused.** No heuristic pattern was promoted to a defect without an applicable rule, concrete consequence and suitable remedy.

## 7. Actual validation and completion boundary

The preserved R3 focused map receipt/log shows exit 0 for its three stated roots and candidate. The actual public-type inspection remains R3 evidence. These unchanged-source records are useful development provenance, with no transfer of whole-candidate validation to R4.

The historical R3 full check has a retained running start, a later nonterminal progress observation, and then lost execution state without a terminal exit or verification record. Current docs correctly describe it as incomplete historical evidence. C1 is separately interrupted. No record establishes a proof failure, timeout, memory/disk exhaustion or host incapacity for either missing terminal outcome. No R4 compiler run or final success record was supplied or created.

The current authorization permits the source/handoff decision recorded here and continued focused mathematical work. The receiving integrator must still complete the exact accepted candidate's full guarded build and exhaustive audit, preserve genuine terminal/verification evidence, obtain both final axes, immediately verify that candidate and compare the accepted input. Any later source change or receiving conflict resolution needs the same loop's applicable recapture, review and validation. Source handoff does not grant final merge approval or whole-book completion.

Root owns canonical REVIEW/ISSUES reconciliation, final source compare/export, recovery checks and the next durable checkpoint upload. The present REVIEW/ISSUES fingerprints describe their pending-review state at this cut; a later mechanical reconciliation should be recorded as such. This reviewer makes no upload claim.

## 8. External evidence fingerprints

These files lie outside the candidate Git tree. The companion JSON records the complete set actually read or fingerprint-checked and distinguishes partial/retained-analysis inspection. Paths below are relative to the checkpoint root unless marked `intake/`.

| Record | SHA-256 |
|---|---|
| `books/common/REQUIREMENTS.md` | `a60dd5a4aa4ef46ff8463e47f536961a7f374c5ade74f012c609470e59f6b29c` |
| `books/common/VALIDATION-HANDOFF.md` | `c17d8ba02e66abbf8d3455facb0605cad285d854035685df08c70c1f5f41ebb2` |
| `books/common/STATUS.md` | `258bc92560460ea8ab369f569e04b22cd79649b89b6a5daef6ac1eb21d9453bf` |
| `books/common/COVERAGE.md` | `779c1701392c921b81d6c193c9e149c29adf99cc881a0a0fd03650f5b229a59b` |
| `books/common/README.md` | `041e837c443fb2ada2e0a8a88899950b2b3ea9c4f8f82fb25d40e84f3288c758` |
| `books/common/REVIEW.json` | `2350a066c50a62086cb9bbf4185d0d9f291e6f8a71d27a66ac9983b1292384de` |
| `books/common/ISSUES.json` | `d9160998531f10a50c6cfba551683b355aa2036cba4c2eb57213c5452bcf7c47` |
| `source/integration.json` | `558afc496c69f28f09f4289cab6c9dda149ec9a111ff7c6bc02405fb01deeede` |
| `source/refs.json` | `f08f0fd29934c4d4311d8980a2422de7f3db23d8166ec676743a2644447fd254` |
| `books/common/evidence/integration-baseline-20261114-evening.json` | `5552685f5e8e87d51ee0f831346b73533c101706c95d1f0d91c712128565c99c` |
| `books/common/evidence/integration-candidate-r4.json` | `01e15d6d360c81e2d5e06187b35cb7a7fd8f1b2efcdec90b8b4f94a38e73e667` |
| `books/common/evidence/integration-scope-20261114-evening.json` | `d9cdf67714389042e0f1c252267506cf42e97fcb7aef606fafb7d850e0c2b773` |
| `books/common/analysis/upstream-probability-04514fc1.md` | `89cc324fa70321e5c5914d02b157b3e8de0b57dcda6efe15b2415be921509f12` |
| `books/common/analysis/build-resources-20261114.md` | `033b62d94235567565823528a02f0903f048c33ad07e05830b1f16ab93f208b3` |
| `books/common/evidence/patch-export-009.json` | `620751b5c1bf85ef97937cf293fddf940009f0bee17644092f2975ad10dd9a10` |
| `books/common/analysis/donor-dispositions.json` | `3437ebcd64d5a4f1b9564698a79bd83ee6116f2073b47a2d4619b14115641e6b` |
| `books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md` | `07fb1b0ea46e06a721ea603dbb99865597d844824f21d01b144659eb3ae1c6d6` |

**Final Standards accounting:** original base retained; current candidate `18235331da1fe343d09080ca4c41173f9b4d9963`; source/handoff **Passed**; new findings 0; unresolved new source/handoff findings 0; `INT-ST-001` and `INT-ST-002` fixed; historical gates retained; **final acceptance pending, with no final approval**.
