# Textbook integration — independent Spec source/handoff review, round 4

**Source handoff outcome: Passed. Final library acceptance: Blocked.** No new source, mathematical-statement, coverage-accounting or receiving-handoff defect was identified. **INT-SP-001 remains open as the receiving integrator's required final-validation gate.** This source/handoff pass permits the authorized continuation and checkpointed delivery; it supplies no whole-library compilation, exhaustive-audit result, final Spec approval or merge acceptance.

Reviewer: `/root/recovery_review/spec_r4`, replacement independent Spec reviewer in the existing ordinary integration loop. The previous reviewer is unavailable; its complete immutable reports remain authoritative retained analysis at their stated scope. This is not a replacement of the loop, a reset of the original base, or a new source of historical approval. The independent Standards axis is separately assigned. Review cut: **2026-11-14T20:45:50.244496+00:00**.

## 1. Immutable scope and governing requirements

| Input | Reviewed identity |
|---|---|
| Original full-spec base and actual merge base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |
| Frozen candidate | `18235331da1fe343d09080ca4c41173f9b4d9963` |
| Candidate tree | `63205d8a3ff27deb3680c613b70085163f289b83` |
| Previous R3 candidate | `16440863ddb14d95c402ce65498e22497e246e72` |
| Incorporated upstream | `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` |
| Requirements version | `2026-11-14-evening-probability-and-delegated-validation` |
| Requirements SHA-256 | `a60dd5a4aa4ef46ff8463e47f536961a7f374c5ade74f012c609470e59f6b29c` |
| Candidate receipt SHA-256 | `01e15d6d360c81e2d5e06187b35cb7a7fd8f1b2efcdec90b8b4f94a38e73e667` |
| Scope identity | `04aaeba64ef993665ce417ac3441139f22ca88b53f8865ca6423525f21f2c309` |
| Candidate content identity | `f3d62399fb025c399790a4fd6a9808c9110ebf44d130c984474e9dcb4328cde4` |

The full comparison is `git diff 9175737c2b14ef738cfb6c2cdc68d885c0805ddd...18235331da1fe343d09080ca4c41173f9b4d9963`: **381 changed paths, 347 Lean paths, 322 commits**. The manifest has **490 paths, `entries: {}`, `exclude: []`**. Both continuation receipts are complete JSON, status `ok`, mode `integration`, retaining the original base. Every full-diff changed path is declared. I independently matched the receipt's entire mode/blob entry map to the candidate Git tree, resolved the live retention refs and observed a clean worktree at the frozen HEAD. The receipt's ordinary outside-scope inventory is not an exclusion of task work.

The three new upstream commits and the integration merge add four commits after R3. R3-to-R4 changes exactly nine paths: the two TableProducer modules, their example, the public root, three probability/progress documents, the suppression research note and the textbook correspondence document. All seven upstream paths other than the unioned public root have exact upstream blobs. The public import set grows from 919 to 920 lines, retaining both parents' imports and adding `Examples.TableProducer`.

The complete requirements, actual AGENTS, implement/code-review skills and heuristics, shared review loop, architectural/domain guidance, glossary, ADRs 0001/0002/0010, example-driven statement review and worked example, relevant language-direction criteria and README acceptance rules were inspected. Library coherence precedes preservation. The user's local-tracker and optional-Nix exceptions retain exact pins. The new explicit delegation changes the execution owner and source-progress prerequisite; it does not waive full validation, proof policy, either final review axis, immediate verification or final comparison.

## 2. Full-original-base continuity and preserved mathematics

The complete prior Spec R1/R2/R3 reports, R3 Standards/coordinator Markdown and JSON, both navigation addenda and the current review record were read. Their historical outcomes remain **Blocked**. No previous approval is transferred because none was available for those full candidates.

Independent Git comparison establishes that **372 of the 374 R3 full-scope changed paths are unchanged in bytes and mode**. The only changed members of that prior scope are `SquareApplications.lean` and `docs/research/textbook-integration.md`. Every previously existing Lean blob other than the public import root is unchanged. The source-text local import closure of TextbookSorting, TextbookSequences, TextbookMaps and MappedPotentialAccounting has 44 paths, none changed by R4. This is a context comparison, not a substitute for the pinned Lean parser or compilation.

These observations retain the prior mathematical analysis of the original full integration: mapped/invariant/signed potential through the actual executor; occurrence-sensitive sorting and synchronized implementations; relational stack/difference-list clients; finite random-selection/quicksort models and explicit tariffs; OrderedMap validity, independent partial meaning, AList/list/function/tree realizations and arbitrary initial-state clients; physical sharing; suspension semantics; pure forcing; distinct successful-write/body-entry counts; and persistent debit histories. The exact statements, assumptions and connected cases of those families were not altered by this intake. This report does not claim a fresh manual rereading of every inherited proof line or every manuscript page.

In particular, the retained map assessment still distinguishes absence from a stored optional `none`, default-valued lookup from full partial meaning, raw first-match lists from chronological last-write updates, valid trees from malformed raw trees, and ordinary independent universes from the existing common-universe Square adapter. The retained sorting, sequence and map relationships do not imply equal costs, representations or physical sharing. The potential assessment retains actual successor states, initial credit, stated final nonnegativity and noncommutative order where claimed.

I re-resolved all **167** catalog identity checks: 65 selected additional FDSA paths, 81 variants at 36 existing paths, five VFA staging-file hashes and 16 research donor objects. There are **zero mismatches**. The donor-disposition JSON remains byte-identical to the R3-reviewed record. INT-020/021 retain remaining source-specific work; INT-032 remains a bounded binding/validity/observation recovery. The weaker generic total-table contract, six-law deletion interface, Modify round trips, set deletion, generic valid-graph composition, remaining VFA drafts and later FDSA/PFDS work stay preserved with owners. Their absence at an old filename is not relabeled as capability loss or a requirement for a duplicate active framework.

## 3. Independent statement review of the new probability intake

### One operational producer and exact observations

`Applications/Probability/TableProducer.lean:15–59` uses the existing prepared-row machine and Progress producer semantics. A state is the semantic value together with the sampler's actual cursor, remaining block width and accumulated code. A row return emits its value and starts that value's next row at the returned cursor. A silent transition retains the semantic value and advances the same incomplete row. Self-transitions emit; rejected sampler blocks do not.

The next-emission bridges apply to **arbitrary partial row states**. Their conclusion retains the emitted value, exact continuation state and same transition count. The reverse bridge obtains the actual returned cursor, rather than assuming a restarted sampler or merely matching an output distribution. These hypotheses are appropriate for resumption and do not assert arbitrary-state almost-sure termination.

`delivers_of_trace`, `trace_of_delivers` and `delivers_work` (lines 61–98) connect delivery from an initialized producer to the actual RowChain trace. The trace has one final administrative return; the producer has none. The positive-trace argument justifies natural subtraction in `k - 1`, and the reverse direction adds exactly one. Empty delivery has zero producer work and leaves the initialized state unchanged. The endpoint cursor equation `z.2.1 = s + k` counts bit inspections. It gives no bound on arithmetic, row preparation, storage, physical entropy or host time.

I inspected the unchanged `PreparedRow` representation and start/step, BoundedUniform width/state/bit-step definition, RowChain Trace/work/path/termination laws, Progress Delivers/Productive/coherence definitions and the productivity API. The operational bridges use these existing owners. They do not introduce a parallel transition relation with an assumed correspondence.

### Probability, domains and simultaneous prefixes

`prefixEvent` and `endpointEvent` observe actual finite deliveries. Their equations with RowChain events retain the full ordered path or its stated endpoint projection. `prefix_mass` and `endpoint_mass` use a finite carrier, decidable equality, an explicit `Fin m ≃ α`, rational table rows and the existing fair-tape law. They do not identify probability tables with partial dictionaries.

`almostSureProductive` uses the existing finite-chain termination theorem for each requested length. `ae_coherent_prefixes` then invokes the existing countable almost-sure productivity/coherence result to obtain **one conull set of coherent finite prefixes of this same producer on the same tape**. The quantifier order is correct for that claim. It does not prove termination of an infinite stream, a uniform finite deadline, or productivity on every tape. A meaningful finite MH instance and the singleton instance supply positive uses, so the usability claim is not supported solely by impossible premises.

### Joint block stationarity and its premise

`TableProducerStationarity.lean:10–75` defines a block by hiding an initial number of emissions from one longer actual delivery. `block_succ` retains the first row's actual cursor and then resumes there. `block_shift` relates tape suffixes, and `block_succ_mass` applies the existing **stopped-mass** theorem to measurable continuation events. Disjointness comes from deterministic row evaluation. Fixed-cut independence is not substituted for a random-return-cursor argument.

`stationary_blocks` (lines 77–91) proves an ordered finite-block identity under the displayed stationary equation for `π : α → ℝ≥0∞`. It deliberately does **not** require `π` to have total mass one. The intake assessment records this general weighted scope; the result should not be read as normalization of arbitrary weights. `FiniteMH.producer_stationary_blocks` (lines 99–108) specializes to the existing normalized target using target nonnegativity and its established stationary equation. Its displayed weighted sum expresses an initialization independent of the fair tape. Neither theorem asserts independent successive states, convergence, mixing, burn-in, confidence bounds or empirical accuracy.

### Cases and observation-policy boundaries

The complete new example file exercises one unfinished block, resumption at that exact state, a rejected block followed by a successful retry, two consecutive emissions without a terminal administrative step, an emitted self-transition, the prefix mass `1/3`, the two-step endpoint mass `7/9`, simultaneous coherent prefixes and stationary pair `(false,true)` of mass `1/4` after every finite emission shift. The probability examples consume the new public laws, rather than recomputing an unrelated specification. The compiled-row productivity case uses `Table.compile_eq` to connect its actual executable rows to the prepared-row theorem.

The positive singleton producer and its all-true exceptional tape separate almost-sure productivity from total productivity. `changes_not_productive` is an actual separating construction on a singleton semantic space: suppressing completed unchanged outputs removes every possible emission. Its source and examples correctly distinguish that policy from filtering MH acceptance flags. The endpoint transition table combines accepted self-proposals with rejection mass and exposes no such flag.

All these are source/statement assessments. The three received upstream Lean modules have **no new local compiler result in this restored environment**. Their upstream origin and `decide +kernel` proof text are not treated as executed validation.

### Textbook relevance and research scope

The proposed INT-033 connection is appropriately narrower than the new stream API: relate the existing FDSA occurrence-index PMF runs to finite row/tape execution, preserving shrinking domains, ranks, duplicate occurrences, joint source-cost observations and returned-suffix freshness. I inspected RandomSelectionRun's actual recursive PMF and source bridge and RandomQuickSortMean's declared observations. They explicitly exclude random-bit implementation/pivot sampling costs. Receiving the producer does not discharge that correspondence, turn one global permutation into fresh independent pivots, or create a sampling-cost theorem.

The suppression note is explicitly paper research about derived views and discovery, with different recoverability, approximation and preservation contracts. It selects no new Lean abstraction or validation policy. Its warning that discarded observations need explicit recovery/preservation is consistent with this integration; it does not justify equating unrelated textbook interfaces. No new external literature audit is claimed by this offline source review.

## 4. Coverage and historical finding continuity

The complete maintained COVERAGE, STATUS, README and issue records distinguish the **current source identity `18235331`** from the detailed C2 account, exact R3 map recovery and evening accounting evidence at `16440863`. They expressly give no extra textbook credit to the three new probability modules. This avoids attributing earlier mathematical coverage or focused evidence to an unvalidated R4 execution.

The account retains historical FDSA Chapters 1–3 acceptance, the separate 112/112 Chapter 2 and 83/83 Chapter 3 denominators, and Chapter 4's 76 obligations/11 exercises and three unfinished streams. VFA retains its implemented Perm correspondence and all five historically focused-checked staging developments without claiming a completed chapter; table recovery is explicitly partial. PFDS retains the six Chapter 2 exercise headings and substantive later foundations, while Chapter 1 acceptance remains introductory accounting and all 16 forward costs remain open. Its 77 later exercise headings and mixed 135-row ledger are not converted into invented completion percentages. No fresh exhaustive manuscript audit is asserted.

INT-ST-001/002 remain **Fixed** with their existing Standards-owned evidence. I read both navigation addenda and the exact retained nonterminal start observation; no duplicate Spec finding is created. VFA ST-002/SP-VAL-001 and ST-006's correction, FDSA XT03-CP01/XT03-DOC01 and their original bases/donor boundaries, and all PFDS historical identities persist.

The PFDS canonical register remains `books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md`, **section 5**. Its **39 IDs** comprise 23 repair/static/development dispositions, two source/ownership boundaries and 14 current-validation identities. They are not 39 missing theorems. The eight Spec/shared validation IDs remain IMPORT-VAL-004, CH02-PRE-005, SUSP-SPEC-VAL-001, PURE-SPEC-VAL-001, COUNT-SPEC-VAL-001, PERSIST-ACC-SPEC-VAL-001, BODY-COUNT-SPEC-VAL-001 and SIGNED-POT-SPEC-VAL-001. SUSP-STAT-001 and PREP-10019-02 keep their exact mathematical and ownership meanings. This report neither closes paired Standards findings nor retroactively accepts historical chapters.

## 5. Receiving handoff, evidence limits and the open gate

The full current `VALIDATION-HANDOFF.md` was inspected at SHA-256 `c17d8ba02e66abbf8d3455facb0605cad285d854035685df08c70c1f5f41ebb2`. It correctly binds the original base, upstream, candidate, tree, manifest and receipt, and gives the normal full guarded check, applicable fresh-mode triggers, exhaustive audit, both independent final reviews, immediate verification and final snapshot comparison. The local setup/tracker exceptions remain separate from proof acceptance.

The final patch clarification is correct: a separately applied patch followed by a new commit produces a **new receiving candidate SHA**, even if its tree is identical. The actual receiving commit needs its own identity and applicable validation/review reconciliation. Complete checkpoint restoration retains the exact delivered commit and history. The patch record reports 3,544,383 bytes, SHA-256 `955c71b607aab9e217f1b0e4b9c1ef476f16a4596e9d47192052acc8f8a88498`, and private-index application against `04514fc1` reproducing tree `63205d8a`. I assessed that retained evidence, without rerunning application. The patch is regenerable from recorded Git objects and is not an external archive dependency.

I independently read the source catalog and bundle advertisement: **155 stored catalog refs plus HEAD = 156 advertised refs**, with all catalog object IDs matching. All **149 restored input refs** remain exact. The six new capture entries are present in the bundle and their original live refs resolve correctly; export-specific stored names need not already be installed in the working repository. The bundle's 98,957,987 bytes and SHA-256 `a508155107a17a63baa01801a89ef2e0d86e9d079eb41ddd0b6bd50c4f1f9a73` match `source/integration.json`. These are source-identity observations, not a new restore or proof-validation claim.

Root's `intake/integration-handoff-compare-r4.json` is an actual successful comparison of the exact frozen source and reviewed scope. Its `accepted` field identifies the compared Git input; it does not assert final mathematical acceptance. The receiving procedure still requires a fresh immediate comparison at final acceptance. Root owns comparison/export operations and durable upload; this reviewer executed none of those operations.

The old C1 and R3 full runs retain **no terminal success**. The exact R3 start and progress observations remain historical. The later interruption record reports lost handles, available locks and no verification record, without diagnosing exit code, memory failure, timeout, proof failure or host incapacity. R4 has no new compiler run. The R3 focused map receipt and actual public-type output remain useful evidence at their original exact scope; they do not become R4 full-check evidence.

The corrected resource note keeps `LEAN_NUM_THREADS`/Lake runtime scheduling distinct from the Lean CLI's separate `-j` setting and compiler-child behavior. The local launcher excerpts show the environment variable and no normal-run timeout; the pinned-source assessment supplies the CLI distinction. Ordinary `--jobs` remains rejected outside fresh mode. Visible resources and a few old module times do not establish a current full-build ETA or downscaling. No new benchmark or hardware diagnosis was performed here.

### INT-SP-001 — Blocking for final acceptance; open delegated receiving gate

**Requirement:** Current REQUIREMENTS, explicit delegated-validation exception and completion boundary; VALIDATION-HANDOFF; pinned code-review/review-loop and README/ADR 0010 acceptance policy. The receiving integrator must provide the final exact candidate's guarded complete build, exhaustive axiom audit and matching success evidence before final acceptance.

**Evidence:** Candidate `18235331` is source-bound, but no successful terminal whole-candidate check/audit or matching `.lake/verification.json` has been supplied. The predecessor's partial runs have no terminal result, and earlier focused success, source comparison, patch reconstruction and bundle preservation have narrower meanings.

**Consequence:** Final acceptance remains **Blocked** and this finding remains **open**. Under the user's express instruction, its missing local full pass does **not** block continued bounded mathematics or an honest reviewed source handoff. The historical R1–R3 Blocked reports remain unchanged. No false-theorem or machine-capacity conclusion follows from this missing gate.

**Remedy and owner:** The **receiving integrator** runs the actual receiving candidate in its normal pinned environment, retains terminal log/coverage/integrity/audit and verification evidence, and returns corrections through this same loop. Independent Standards and Spec reviewers reconcile the exact current candidate and versioned requirements, retaining all original IDs. Immediately before acceptance, the responsible integrator performs successful `--verify-candidate` and snapshot comparison. Reconcile INT-SP-001 only on actual evidence; delegation alone never closes it.

## 6. Outside-Git fingerprints and delivery boundary

Candidate SHA does not cover checkpoint prose, ledgers or evidence. The companion JSON fingerprints every external record actually inspected, distinguishes excerpt/identity-only inspection where relevant, and records inherited analysis separately from executed validation. Selected current inputs are below; paths are relative to the checkpoint root.

| Record | SHA-256 |
|---|---|
| `books/common/REQUIREMENTS.md` | `a60dd5a4aa4ef46ff8463e47f536961a7f374c5ade74f012c609470e59f6b29c` |
| `books/common/VALIDATION-HANDOFF.md` | `c17d8ba02e66abbf8d3455facb0605cad285d854035685df08c70c1f5f41ebb2` |
| `books/common/STATUS.md` | `258bc92560460ea8ab369f569e04b22cd79649b89b6a5daef6ac1eb21d9453bf` |
| `books/common/COVERAGE.md` | `779c1701392c921b81d6c193c9e149c29adf99cc881a0a0fd03650f5b229a59b` |
| `books/common/README.md` | `041e837c443fb2ada2e0a8a88899950b2b3ea9c4f8f82fb25d40e84f3288c758` |
| `books/common/REVIEW.json` | `2350a066c50a62086cb9bbf4185d0d9f291e6f8a71d27a66ac9983b1292384de` |
| `books/common/ISSUES.json` | `d9160998531f10a50c6cfba551683b355aa2036cba4c2eb57213c5452bcf7c47` |
| `books/common/analysis/donor-dispositions.json` | `3437ebcd64d5a4f1b9564698a79bd83ee6116f2073b47a2d4619b14115641e6b` |
| `books/common/analysis/upstream-probability-04514fc1.md` | `89cc324fa70321e5c5914d02b157b3e8de0b57dcda6efe15b2415be921509f12` |
| `books/common/analysis/build-resources-20261114.md` | `033b62d94235567565823528a02f0903f048c33ad07e05830b1f16ab93f208b3` |
| `source/integration.json` | `558afc496c69f28f09f4289cab6c9dda149ec9a111ff7c6bc02405fb01deeede` |
| `source/refs.json` | `f08f0fd29934c4d4311d8980a2422de7f3db23d8166ec676743a2644447fd254` |
| `books/common/evidence/integration-baseline-20261114-evening.json` | `5552685f5e8e87d51ee0f831346b73533c101706c95d1f0d91c712128565c99c` |
| `books/common/evidence/integration-candidate-r4.json` | `01e15d6d360c81e2d5e06187b35cb7a7fd8f1b2efcdec90b8b4f94a38e73e667` |
| `books/common/evidence/integration-scope-20261114-evening.json` | `d9cdf67714389042e0f1c252267506cf42e97fcb7aef606fafb7d850e0c2b773` |
| `books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md` | `07fb1b0ea46e06a721ea603dbb99865597d844824f21d01b144659eb3ae1c6d6` |

No compiler/checker/audit, installation, setup, process control, source/index/ref change, checkpoint mutation, network call, GitHub/Library operation, patch reapplication or acceptance command was performed. Writes are confined to this immutable report and its JSON companion. Root must include the pair in the next verified durable checkpoint; no upload or delivery success is asserted here.

**Full base:** `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. **Candidate:** `18235331da1fe343d09080ca4c41173f9b4d9963`. **New Spec source/handoff findings:** 0. **Source handoff outcome:** Passed. **Final acceptance status:** Blocked by open INT-SP-001, with inherited validation identities retained. **Final approval granted:** none.
