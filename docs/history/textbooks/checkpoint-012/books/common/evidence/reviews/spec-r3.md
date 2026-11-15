# Textbook integration — independent Spec source continuation, round 3

**Outcome: Blocked. Source analysis identifies no new source defect. INT-SP-001 remains blocking because successful terminal full-check and exhaustive-audit evidence for the exact current candidate has not been presented.** The focused map success and candidate snapshot are useful evidence within their scopes; neither constitutes full validation or approval.

Reviewer: `/root/recovery_review/spec`. This is the independent Spec axis in the existing ordinary integration loop. The earlier R1/R2 reports remain immutable. This reviewer ran no compiler, checker, audit, setup, process-control or acceptance command, and changed no source, index, refs, dependencies, checkpoint records or remote data. Writes are limited to this report and its JSON companion. Root owns compilation, canonical status, durable saving and final acceptance.

## Immutable inputs and full scope

| Input | Identity |
|---|---|
| Original full-spec base and merge-base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |
| Current candidate | `16440863ddb14d95c402ce65498e22497e246e72` |
| Current tree | `33d087744fc2435c29d60981ca0d79af629b8c8d` |
| Prior C2 | `f52a47b9e240b3937533f48befb8622527b7f6db` |
| Authorized upstream pin | `983d0b6b602b71541f182737011621a8805be27b` |
| Requirements | `books/common/REQUIREMENTS.md`, version `2026-11-14-upstream-recovery-and-coverage` |
| Requirements SHA-256 | `5d48738af724152b67daf993fa0f3d2abd7c2eeb7a47b7e080aa7740de1e07ac` |
| Complete candidate receipt | `intake/integration-candidate-r3.json`, status `ok`, mode `integration` |
| Receipt SHA-256 | `9735a260a6d1ab62b5d0b132f87c226f053052526a877fc7047266ec18fca47c` |
| Scope identity | `2af6c974c630c10dd6d32dd3fc585dfcd5f9b9fc54ce85a349289296cf92030a` |
| Content identity | `77e32c504c74e498c9a013c7fb269944dfcbb0c1f8c96cd8eb15e6e531755854` |

The review comparison remains `git diff 9175737c2b14ef738cfb6c2cdc68d885c0805ddd...16440863ddb14d95c402ce65498e22497e246e72`. I independently checked the receipt hash, requirements hash, candidate HEAD, clean frozen worktree and merge-base. The full comparison contains **374 changed paths, 344 Lean files and 318 commits**; the manifest declares 483 paths, without projections or explicit exclusions. The coordinator's complete path and commit lists are `round3-changed-paths.txt` and `round3-commits.txt` beside this report. The snapshot's ordinary outside-scope inventory is not an extra list of task exclusions.

The complete current requirements govern, including library coherence before preservation, active recovery through actual owners, the new upstream assessment and accurate book coverage. The user permits useful unfinished work to remain explicitly owned. Local tracking and exact-pin native setup are authorized exceptions; they do not waive either review axis, full validation, axiom policy, original-base continuity or durable delivery.

### Reuse of prior analysis

I read the complete prior independent Spec reports at `intake/review/spec-r1.md` and `spec-r2.md`. Both were Blocked, not approvals. Their assessment covers the incoming FDSA/PFDS/VFA families, preservation beyond the three tips, mapped and signed potential reconciliation, sorting and sequence interoperability, physical sharing, suspension semantics, persistent accounting, actual cost models and remaining scope. Those analyses are retained, with their explicit limits; this continuation does not pretend to reread every inherited proof line or manuscript page.

Independent Git comparison found **352 of the prior 356 changed paths byte-identical**. The four changed prior paths are `OrderedMap/Interface.lean`, `OrderedMap/Basic.lean`, `SquareApplications.lean` and the textbook correspondence document. The C2-to-current delta is 22 paths, 3,044 insertions and 66 deletions. The other changed path from upstream, `UniformThreeLaw.lean`, was already in the original master and is now included in the full original-base review.

The prior shared Potential, Growth, Workload, Measured, both relevant ListFusion/TreeFlattening owners, TextbookSorting, TextbookSequences and MappedPotentialAccounting remain unchanged. The old OrderedMap clients and physical `SharedTree/Map.lean` also remain unchanged. The actual `Squares.vertical`, `Rep.after`, `synchronized`, `synchronize` and `synchronize_agrees` definitions were inspected; their blobs are unchanged. Their common-universe foundation is not silently generalized by the map work.

All prior public imports and all new upstream public imports are retained; `Examples.TextbookMaps` is added. I independently re-resolved all 65 selected missing-path FDSA donor objects and all five VFA draft hashes, with zero mismatches. The prior wider 167-object donor/draft/research reconciliation remains supporting evidence; I did not reperform every older variant check. Deferred source is retained rather than resurrected as redundant active interfaces.

## Map recovery: mathematical assessment

I read all six current map files, the original VFA `TableObservations.lean`, the exact XA01 `Map`, `AList`, `Modify` and `ValidGraphs` donor files at `20a5b5537a704be016d09e4eb31db0dad8a12d61`, the implementation handoff and both correction records. I also inspected the actual current public-type output, existing OrderedMap/SharedTreeMap clients and their relevant definitions. The following assessment concerns intended mathematics, hypotheses, domains and useful consumers, separately from the missing full validation.

**One existing contract and ordinary clients.** `OrderedMap/Interface.lean:18–74` retains separate operations, full partial-function meaning and laws. `bindAll` and `writeAll` execute in chronological order, so later equal keys win. `Laws.bindAll_observation_agrees` quantifies every shared binding list and arbitrary corresponding initial states in potentially different carrier universes. It concludes equality of complete partial functions. It neither assumes equal concrete representations nor requires every representation to realize every abstract function. The retained `bindAll_correct` supplies its induction, rather than introducing another executor.

The actual elaborated output confirms independent key, value and carrier universes for ordinary Ops/Laws and four universe parameters for cross-realization agreement. The Square adapters explicitly retain their existing common universe. The type-valued Bool-key client exercises the ordinary interface without payload equality/order. Empty payloads remain permitted in the ordinary partial-function realization; a default is required only by the separate default-valued observation.

**Validity and the independent tree meaning.** `Invariant.lean:27–67` constructs restricted operations from actual raw computation and explicit initial/step closure. `Laws.restrict_iff` is a real equivalence with the raw observation equations on valid inputs. The explicit valid empty state prevents the vacuous empty-domain interpretation. Lookup correctness is included, rather than defining all observation from directed lookup and thereby hiding the tree invariant.

`Basic.lean:176–193` applies this adapter to the existing raw trees. The raw bind, directed lookup, whole-tree observe, `OrderedBy`, their proof bodies and the tree finite-domain result are retained. The adapter adds no assertion about invalid trees. `invalid_tree_boundary` supplies a concrete malformed tree whose directed search misses a binding found by whole-tree observation; the contradiction uses the public `lookup_correct` theorem. The independently expected two lookup results and invalidity proposition were unchanged by the compiler corrections.

This is a coherent recovery of selected XA01 validity/observation capabilities, not a theorem that its whole six-law update/delete interface has been recovered. The original donor's pointwise contract needs no key decision; the current common `write`-based law presentation states its `DecidableEq` requirement explicitly. The original more general contract and deletion/Modify/valid-graph capabilities remain preserved pending, so this slice does not erase them or claim full parity.

**Information retained by observations.** `Observations.lean:27–114` keeps `Option` absence separate from a stored payload, including optional `none`. `binding_iff` and `meaning_eq_iff` reconstruct partial meaning jointly from presence and lookup with an explicit default. Neither claims that default lookup alone reflects equality. `forget_default_not_injective` constructs its two distinct functions using an explicit key and default, so it makes no hidden nonempty-key or inhabited-payload claim.

The `Function.update` and chronological-fold equations preserve update order. `defaultBindAllSquare` uses the existing vertical-pasting construction; it is a one-way change of observation. `default_client` consumes that square's commuting equation to establish the independently expected total table, true exactly at key three. An arbitrary total-table realization need not expose presence information, so the original generic VFA Table Ops/Laws and its general transport remain a genuinely weaker pending capability. The recovery ledger says this explicitly.

**Real implementations and precedence.** `AssociationList.lean:60–132` supplies ordinary partial functions, raw shadowing lists and the actual Mathlib `AList.insert`/`lookup` operations as realizations of the shared contract. No finite-support requirement is imposed on arbitrary partial functions. AList uniqueness belongs to its concrete carrier; raw lists retain duplicates. `bindAll_lists` proves that chronological writes give `bindings.reverse ++ entries` for every initial suffix. `listObserve_reverse_append` transports that actual computation to meaning. The repeated-key case separates chronological last-write behavior from first-match raw-list interpretation; the shadowed-member case correctly rejects using arbitrary entry membership as the current binding.

`TextbookMaps.lean:33–81` uses the public arbitrary-initial-state agreement law, `synchronize` and `synchronize_agrees` with actual list/tree implementations. AList/tree agreement is composed through those bridges. These are useful consumer relationships, not pairs of unrelated certificates. The optional-payload fixture obtains its absent/stored-none/last-write expectations through `lookup_bindAll`; presence distinguishes two queries that default to the same value. The existing physical-tree examples continue to retain actual old roots, child addresses, allocation and comparison observations. None of the new lookup equalities claims equality of costs, callbacks, physical sharing or concrete states.

The source contains no inferred chapter closure. `INT-020`, `INT-021` and `INT-032` preserve named ownership of the remaining six-law deletion interface, Modify round trips, set deletion, general valid-graph composition, generic total-table contract and the other four VFA drafts. The donor disposition records correctly mark partial capability recovery rather than complete donor integration.

## New upstream delta and relevance

The 14 substantive upstream module blobs exactly match authorized pin `983d0b6b…`; the public root unions both parents. I read the new binary-block, bounded-uniform, rational-row, sequential-machine, row-sampling/composition/iteration, finite-MH and tariff modules and their two example files. I inspected the full `UniformThreeLaw` correction: the fixed-cut suffix facts delegate to the new common owner with the same public statements. The old special sampler also has a new proved correspondence preserving all finite fuel observations, actual cursor and bit-reading work.

The bounded sampler uses a positive bit width, accepts below the bound and retries otherwise. Positive-bound assumptions are explicit for termination. Bound one deliberately can reject bits despite having only one possible output. The exact finite-fuel tail counts complete blocks; timeout is not equated with divergence. Random-cursor independence is derived from the actual consumed-prefix events and disjoint terminal atoms, rather than assumed for an arbitrary stopping rule.

Prepared rational rows use an explicit finite enumeration, natural multiplicities and positive total. Zero weights and non-dyadic probabilities have connected cases. Sequential sampling feeds the actual returned cursor into a row that may depend on the first result. Finite chains retain the whole output path and the stated extra administrative return transition; the recurrence is connected to existing table/kernel composition. The deliberate same-cursor reuse case separates its joint law from proper sequential sampling. MH stationarity is transported to the actual finite-chain final law; no mixing rate or convergence claim is introduced.

The work model explicitly prices source operations, preparation, bit steps, selection and output interpretation. Meter erasure and charged execution share the actual transition path. Its natural-number tariff does not imply wall-clock or operand-bit-complexity bounds. The new probability Table describes stochastic kernels, whereas OrderedMap describes partial dictionaries; their shared word “table” is not an architectural identification.

These new owners are relevant to later FDSA randomized/permutation work, but current docs correctly require a proved correspondence before granting that work source-coverage credit. No theorem here silently converts one global input permutation into fresh independent pivots or grants a cost-model equivalence. The instruction, checker and pin comparison receipt records no policy/toolchain change. Required full validation remains the way to establish the combined import/build/audit result.

## Coverage accounting and outside-Git evidence

The coverage and disposition files are outside the candidate Git tree. Their identities therefore form separate review inputs, rather than inheriting the candidate SHA:

| Record, relative to checkpoint root | SHA-256 |
|---|---|
| `books/common/COVERAGE.md` | `3a643997082f7db88d92395e1239cbbc1c86af78dbe7d21c3a8adffaeb53cafa` |
| `books/common/analysis/donor-dispositions.json` | `3437ebcd64d5a4f1b9564698a79bd83ee6116f2073b47a2d4619b14115641e6b` |
| `books/common/evidence/coverage-20261114.json` | `d6c08c878f63c581fcadfe3460eb4aafafeb0b37679540ceffc6b8eaa4b58cbe` |
| `books/common/ISSUES.json` | `1bc33b69ec1bee3868adcb049b31b99a9e7da4563c0a88ca2e0614ff30acdf13` |

The JSON companion also records the four detailed intake accounting-report identities. I read the maintained coverage account, its dated current-candidate map delta and the selected current donor dispositions. I checked their denominators and historical boundaries against retained source inventories, acceptance receipts and staging review records. This is not a new exhaustive manuscript audit or a comparison of every later source obligation with every theorem now in conaled.

**FDSA:** The five cited historical acceptance commits are ancestors of the current candidate. The receipts distinguish Chapters 1–3 from XT01/XT02 prerequisites; Chapter 2 records 112 obligations, Chapter 3 records 83, and both shared-unit records leave Chapter 4 unaccepted. All 27 chapter-inventory hashes match the detailed accounting evidence. Chapter 4's 76 obligations, 11 exercises and three draft streams remain open. The 2,696 numbered chapter/appendix inventory rows are heterogeneous and are not used as a theorem count or book-completion percentage. Recovery of selected XA01 observations and mapped potential is not credited as a completed later chapter.

**VFA:** The canonical inventory supports the Preface plus 16 substantive chapters, 811 lexical records and 182 exercise markers. The Perm mapping/frontier and historical focused-success/full-validation-failure distinction are retained; no chapter is accepted. All five staging source hashes match. Their retained focused/bounded-review evidence supports calling them historically checked, including the final resource-adapter follow-up and the SS-1/TS-1 resolutions. The dated map delta correctly supersedes only the old C2 claim that the table draft was wholly unintegrated; its generic total-table capability and full Maps/ADT/SearchTree scope remain open.

**PFDS:** The original Chapter 1 integration receipt expressly accepts only introductory source accounting/documentation and excludes forward costs. The current account preserves that limit and all 16 open forward contracts. The chapter exercise counts sum to 83; Chapter 2's six exercise headings and both 2.5 constructions retain their formal/focused status, while 77 later headings remain unproved in the retained ledger. The eight mathematical scopes plus one import-maintenance scope and the 39 historical IDs are not presented as a count of proved chapters or unproved theorems. The mixed 135-row ledger is expressly non-exhaustive, and the later signed-potential focused receipt is distinguished from its stale running field. Related suspension/persistence foundations are not credited as every later source algorithm.

No new accounting correction is requested. The maintained account identifies substantial formal mathematics without treating file counts, lexical records, generic prerequisites or focused builds as whole-book acceptance.

## Validation evidence and complete finding

The two failed development runs remain identified at `7d6c8dc…` and `d59b8053…`, each with terminal exit 1. The correction notes preserve the intended claims: explicit arguments for vertical pasting, current conditional rewrite names, and a theorem-connected proof of the malformed-tree boundary. There was no weakening of examples, validity obligations or proof policy.

`intake/maps-focused-r3.json` records terminal exit 0 on the exact current candidate, 7.578451 seconds and 732 jobs for `Examples.TextbookMaps`, `Examples.OrderedMap` and `Examples.SharedTreeMap`. Its log hash is `8dc2b3ac56841e6043f27fb2254d15ee2d4302952368d05d18bcd818c556a8cd`; I independently matched the bytes and read the terminal result. The actual public-type log hash is `98070df4a9c4b8cbf1b992ff3d5eebc7388974766ee632289fb98a5c35e0dd0a`. Neither run is the exhaustive project audit.

Root started `./check.sh --candidate HEAD` through the pinned native route on this candidate at **2026-11-14T03:29:12.689406Z**. At this review's evidence cut, `intake/full-validation-r3.json` says running, `terminal_observed: false`, and no terminal success has been supplied. This report does not follow or control the process.

### INT-SP-001 — Blocking — exact-current-candidate full validation pending

**Requirement:** Current `REQUIREMENTS.md`, governing workflow and completion boundary; pinned code-review §3/§5, review-loop and ADR 0010. Passing either review axis requires applicable full-build and exhaustive-audit evidence with matching immutable inputs. Immediate verification and snapshot comparison remain acceptance gates.

**Evidence:** The exact current full run has started but has no observed terminal outcome in the supplied record. Focused success, public-type inspection, patch reconstruction and a complete candidate snapshot do not discharge this gate. Earlier interrupted C1 validation likewise has no terminal result or verification record.

**Consequence:** Spec remains **Blocked**, with no approval and no ready-to-accept conclusion. This blocker alone is not evidence of a false theorem, an impossible build or host incapacity.

**Remedy:** Root supplies genuine successful terminal full-check/audit evidence and matching candidate/runtime/dependency/coverage/verification records. This same axis then reconciles them with this source analysis and any exact correction delta. A source correction needs a new snapshot and applicable validation without resetting the original base or stable findings. After both independent axes pass the same candidate, root performs immediate candidate verification and final snapshot comparison before acceptance.

The interruption evidence at `intake/validation-interruption-20261114.json` records 630 observed completions of 3,278 cold targets, no recorded error lines, no terminal outcome and no verification record. Some long module times show a large cold build; they do not establish that this host cannot finish. Its old candidate and nonterminal state are not relabelled as current success. No environment diagnosis or setup retry is needed for this source review.

## Inherited findings, remaining work and handoff

INT-ST-001's C2 source-register fix is retained; Standards owns its disposition. VFA ST-002/SP-VAL-001 retain the current-validation boundary and ST-006's old correction. FDSA XT03-CP01/XT03-DOC01 retain their source corrections and outstanding receiving/compiler gate, with original XT03 base `64c6b777d828ecfe83234fc2aed94600a1f24297` and donor `b0fce71fa00b2ff6250b09002176bdc75baf1f46`. Chapter 4 retains its original base `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, three streams and complete obligation scope.

The complete PFDS **39-ID** register remains at `books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md`, section 5 (SHA-256 `07fb1b0ea46e06a721ea603dbb99865597d844824f21d01b144659eb3ae1c6d6`). Its 23 repair/development dispositions retain their supporting source scope; SUSP-STAT-001 and PREP-10019-02 remain explicit mathematical/ownership boundaries. All 14 current-validation IDs remain pending. The eight Spec/shared IDs are IMPORT-VAL-004, CH02-PRE-005, SUSP-SPEC-VAL-001, PURE-SPEC-VAL-001, COUNT-SPEC-VAL-001, PERSIST-ACC-SPEC-VAL-001, BODY-COUNT-SPEC-VAL-001 and SIGNED-POT-SPEC-VAL-001. The six paired Standards IDs remain separately owned. This report does not duplicate or erase that register.

The coordinator reports checkpoint 007 durably complete for this candidate and pre-review evidence. That is root's delivery observation, not an upload performed or independently authenticated by this reviewer. These new review reports must join root's next verified checkpoint. Missing recovery material after a wipe still requires an explicit request for the latest archive before resuming. A failed or uncertain upload still requires prompt notification and a stop; local report files alone are not durable delivery.

**Base:** `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. **Candidate:** `16440863ddb14d95c402ce65498e22497e246e72`. **New source findings:** 0; worst source issue: none identified. **Current required-evidence blockers:** 1, INT-SP-001 (Blocking), with inherited validation identities retained. **Spec outcome: Blocked.**
