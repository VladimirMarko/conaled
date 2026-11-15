# Standards review — textbook integration, round 3

**Outcome: Blocked. Source analysis is complete, with zero new Standards findings and zero unresolved new integration source findings.** `INT-ST-001` remains fixed. Required current-candidate full validation is still nonterminal, so this is not approval or acceptance.

Review cut: 2026-11-14T03:34:47.824088+00:00. This report continues the existing ordinary implementation/review loop as its independent Standards axis. The Spec axis remains independent. No compiler, setup, source edit, index/ref mutation, checkpoint mutation or remote operation was performed by this reviewer. Only this report and its companion JSON were written.

## 1. Immutable candidate and full acceptance scope

| Input | Identity |
|---|---|
| Original full-spec base and actual merge base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |
| Prior reviewed C2 | `f52a47b9e240b3937533f48befb8622527b7f6db` |
| New incorporated upstream pin | `983d0b6b602b71541f182737011621a8805be27b` |
| Current candidate | `16440863ddb14d95c402ce65498e22497e246e72` |
| Current tree | `33d087744fc2435c29d60981ca0d79af629b8c8d` |
| Requirements | `2026-11-14-upstream-recovery-and-coverage`; SHA-256 `5d48738af724152b67daf993fa0f3d2abd7c2eeb7a47b7e080aa7740de1e07ac` |
| Complete helper receipt | `intake/integration-candidate-r3.json`; SHA-256 `9735a260a6d1ab62b5d0b132f87c226f053052526a877fc7047266ec18fca47c` |
| Scope identity | `2af6c974c630c10dd6d32dd3fc585dfcd5f9b9fc54ce85a349289296cf92030a` |
| Content identity | `77e32c504c74e498c9a013c7fb269944dfcbb0c1f8c96cd8eb15e6e531755854` |

The receipt is complete and `ok`, mode `integration`, with **483 declared paths**, no projections and no explicit exclusions. I independently checked its hash, requirements hash, candidate/tree, clean source checkout, merge base and changed-path coverage. The three-dot comparison is `git diff 9175737c2b14ef738cfb6c2cdc68d885c0805ddd...16440863ddb14d95c402ce65498e22497e246e72`. It contains **374 changed paths, including 344 Lean paths**, and the full range contains 318 commits. No changed path lies outside the manifest. The receipt's ordinary outside-scope inventory is not an exclusion of part of the requested integration.

The updated upstream pin does not replace the original review base. Full-scope prior analyses remain relevant, but no old outcome or focused result is transferred as approval to this candidate.

## 2. Governing standards and methodology

I applied the candidate's `AGENTS.md`, implementation skill, code-review skill and subordinate heuristics, shared review-loop procedure, architectural-quality/domain guidance, root glossary, ADR index and ADRs 0001, 0002 and 0010. Formal statement review follows example-driven-development and its worked example. I also read the applicable evolution/specialization criteria in `docs/language-direction.md` and the relevant preservation-contract inventory, including probability's distinction between mass, correlation, stationarity and progress.

The user's explicit exceptions remain controlling: issue/spec tracking is local and checkpointed; Nix is optional while the pinned inputs remain mandatory. Library coherence precedes preservation of useful mathematics; deferred capabilities must retain exact sources, ownership and concrete integration boundaries. Neither exception waives validation, independent review or durability.

The actual source change against the original base leaves agent instructions, skills, toolchain/dependency configuration, checker and proof audit unchanged. README has only the already-reviewed added textbook-workstream link; its environment and validation sections are unchanged. Routine full candidate validation and the README's actual fresh-mode triggers therefore remain in force. No new setup experiment, proof-policy change or narrowed public coverage is justified by this review.

## 3. Full-scope continuation of the earlier source analysis

The R1/R2 reports under `intake/review/` remain part of this complete Standards report by reference, at the fingerprints below. The current candidate changes **22 paths since C2**. Of the 374 full-scope changed paths, **352 retain exactly their C2 content**. I inspected all 22 changed paths, their relevant unchanged definitions and consumers, and the new dependency contexts. This is a full-original-base review with retained analysis, not a review restricted to six map files.

The retained R1 analysis covers the three source imports and merge decisions, occurrence-sensitive sorting, stack/difference-list clients, generic and mapped/signed potential accounting, ordered/physical containers, suspension source semantics and pure forcing, successful cache-write versus body-entry accounting, persistent histories, finite probability/selection statements, and source/provenance documentation. Their substantive boundaries remain applicable:

- Sorting permutation, stable equal-key order and value uniqueness require their respective contracts; output agreement supplies no cost agreement.
- Sequence clients retain arbitrary starting states/tails, sufficient fuel, failure distinctions and ordered noncommutative observations.
- Potential accounting retains actual execution, separate raw/charge carriers, invariant conditions, signed credit and its stated final nonnegativity requirements.
- Stored tree/list guarantees retain actual representation witnesses, optional failure layers and physical sharing/cost claims where separately proved.
- Suspension and persistence results retain their source domains, reentry/error behavior, successful-write/body-attempt distinction and explicitly conditional cost conclusions.
- Finite randomized selection statements concern the actual stated occurrence/pivot process, not an assumed independent replacement process.

No active competing collection framework was introduced in this round. Deferred FDSA/VFA families are still owned by `INT-020`/`INT-021`; current selected map recovery is owned by `INT-032`. Historical chapter bases, all PFDS finding dispositions and the previous true validation failures remain preserved.

## 4. Map recovery: architecture and statement assessment

### Existing owner and usable laws

`Applications/Search/OrderedMap/Interface.lean` keeps the existing `Ops`, `Meaning`, `Laws`, `bindAll` and `writeAll`. Operations contain computation, while laws separately connect an independent observation to the complete partial function. `Laws.bindAll_observation_agrees` follows from the existing arbitrary-list correctness theorem and quantifies over arbitrary corresponding starting states and arbitrary chronological binding lists, including repeated keys. It does not require equal concrete states, every abstract meaning to be representable, or finite support of all meanings.

Keys, payloads and concrete carriers now have independent universes in the ordinary algebra. The actual public-type log confirms four universe levels for the two-realization agreement theorem and independent key/value/carrier levels for the validity bridge. The existing Square framework remains explicitly a common-universe specialization. No payload equality/order/default was added to the core; the new `Empty` and type-valued payload clients exercise that distinction.

### Validity remains an actual invariant

`OrderedMap.Invariant` restricts the existing operations to valid subtypes. `Ops.restrict` requires empty validity and closure of actual binding results. `Laws.restrict_iff` is an equivalence with the raw observation laws on valid inputs, not an assertion on every raw value. The empty-validity witness prevents a vacuous usable-start claim; subsequent intermediate validity is retained in subtype results.

`Basic.rawTrees`, `trees` and `trees_laws` make the pre-existing ordered-tree implementation an actual consumer of this adapter. The raw binding, directed lookup, independent whole-tree observation, ordering predicate and substantive tree proofs remain unchanged. `Examples.OrderedMap`, `Applications/Search/SharedTree/Map` and `Examples.SharedTreeMap` retain their previous observation, optional-value, allocation and sharing contracts. The new malformed-tree example proves that directed lookup can disagree with whole-tree observation and then uses `lookup_correct` to reject orderedness. It does not prove an invalid tree lawful by choosing its own lookup as observation.

### Observation changes preserve their direction

`OrderedMap.Observations` recovers the VFA draft's `withDefault`, `hasBinding`, `binding_iff` and noninjectivity boundary. `meaning_eq_iff` reflects equality from the joint presence/default observation, with an explicitly supplied default. Default lookup alone is deliberately weaker; the noninjectivity theorem also supplies an explicit key, avoiding a hidden nonempty-key assumption.

`write_eq_update`, `withDefault_writeAll` and `defaultWriteSquare` connect the existing chronological executor to ordinary function updates. `Laws.defaultBindAllSquare` uses the actual `Squares.vertical` construction, with the intermediate computation agreement explicit. `Examples.TextbookMaps.default_client` consumes that pasted square's commuting law. No inverse from total lookup to presence, generic total-table equivalence, or cost preservation is asserted.

### Real implementations and discriminating clients

`OrderedMap.AssociationList` uses actual Mathlib `AList.insert`/`lookup`; raw shadowing lists have a separate first-match observation, and ordinary partial functions provide another lawful realization. `bindAll_lists` and `listObserve_reverse_append` explicitly establish reverse-prepending for chronological writes, including an arbitrary original suffix. AList's unique-key representation is not equated with raw lists retaining shadowed entries. The full partial-function model deliberately has no finite-support requirement.

`Examples.TextbookMaps` connects AList/list/function executions through the public generic agreement law, and raw lists/ordered trees through existing `synchronize`/`synchronize_agrees`. Its AList/tree client composes these relationships. Connected cases retain last-write precedence, outer absence versus `some none`, loss of presence when defaulting, shadowed raw membership, empty payloads, different universes and malformed raw trees. The general synchronized client covers arbitrary matching initial meanings; the AList/tree-from-empty specialization does not narrow that general theorem.

The initial handoff and both correction notes identify the intended claims and retain genuine failed attempts. R1 corrected elaboration arguments and deprecated lemma names without changing the mathematics. R2 changed only the malformed-tree proof to consume the public correctness theorem; its three intended conclusions remained fixed. Current public types and focused success support this source assessment at their actual scope.

### Donor preservation boundary

I inspected the exact FDSA-XA01 donor `20a5b5537a704be016d09e4eb31db0dad8a12d61` Map/AList source and the retained VFA table draft (SHA-256 `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57`). The adapted source notice remains in the receiving source. The new code recovers the selected binding/observation/validity capabilities; it does not claim to replace the six-law deletion contract, modification round trips, set deletion, generic valid-graph composition, or the weaker generic total-table contract. Their exact sources and pending owners remain in the maintained donor and issue records. This partial recovery is consistent with the current bounded requirements and does not close a chapter.

## 5. Incorporated upstream probability source

The two upstream commits change 15 paths. I independently checked that all 14 non-entrypoint received blobs equal the newly pinned master, and that the candidate public entrypoint retains every import from both C2 and the new master. I read the full new source and examples, plus the changed UniformThree law and its surrounding dependencies.

- `BinaryBlock`, `CoinSuffix` and `BoundedUniform` separate finite decoding, fixed-cut independence and actual bit-consuming execution. Positive block width is explicit, including the bound-one behavior. Finite fuel exhaustion remains distinct from divergence. The operational inversion retains returned cursor, retry count and transition count.
- `BoundedUniformLaw` proves stopping-event prefix dependence before applying suffix independence. Exact atomic/geometric masses and almost-sure termination retain their positive-bound hypotheses. The selected-suffix construction keeps result/work information at the random returned cursor. It does not silently substitute fixed-cursor independence for the stopping argument.
- `UniformThreeLaw` delegates its existing fixed-cut lemmas to the shared owner. Its statements remain compatible. `Examples.BoundedUniform` proves agreement with the existing three-outcome machine for actual accepted prefixes, full return/cursor/work derivations and every finite fuel observation; it includes bound-one, non-power-of-two and partial-block cases.
- `RationalRow` prepares finite rational rows through an explicit enumeration and nonnegative natural multiplicities with a positive total. Interval selection is connected to those weights. It does not choose an arbitrary executable enumeration by classical choice.
- `TableSampler` interprets the bounded machine's actual returns through the prepared selector, and connects finite-space event probabilities to the existing table kernel. One-block subprobability and uncapped return laws remain distinct.
- `Progress.Sequential` proves inversion and return/family transport for the existing machine semantics. `TableSamplerComposition` consumes the actual first returned cursor, retains both results and work, and proves full joint/atom relationships. Its deliberate tape-reuse control has an off-diagonal impossibility result; examples distinguish it from sequential fresh-suffix sampling.
- `TableSamplerIteration` realizes each finite chain on one tape, retains the complete ordered path and derives existing iterated-table/kernel meaning. The zero-draw administrative return is distinguished from a bit read. `FiniteMHSampler` reuses stationarity under its real hypotheses and connects it to operational final-state probabilities; it makes no mixing/convergence claim.
- `SamplerWork` states an explicit nonnegative tariff model and proves its instrumented algorithms' erasure and bounds. The actual acceptance branch invokes its measured selector once. Preparation, initialization, bit transitions, arithmetic, lookup and interpretation have declared accounting boundaries. Its operational machine instrumentation is distinct from the existing `Resources.Measured` value/writer pairs; no automatic host-runtime or arithmetic bit-complexity guarantee is asserted.

These components extend the pinned library's existing probability and progress owners. Their potential relevance to later textbook random algorithms is documented without crediting any unproved textbook model correspondence. Probability tables and partial dictionary maps retain their different meanings.

## 6. Coverage and maintained records outside Git

The candidate SHA does not identify checkpoint-maintained prose/JSON. I assessed the current `COVERAGE.md`, selected current donor dispositions, local issue ownership and retained process/finding records at the fingerprints below. The coverage account explicitly dates its detailed C2 cut and adds a separate exact-R3 map delta; it does not silently rewrite historical acceptances.

The accounting keeps defensible denominators: VFA's 16 substantive chapters, 811 heterogeneous lexical records and 182 exercise markers; FDSA's 27 chapters and appendices, with heterogeneous numbered obligations rather than a mathematical percentage; PFDS's 11 chapters plus appendix, 83 exercise headings and 12 numbered theorem/lemma results. Known accepted FDSA Chapters 1–3, the exact 112/112 and 83/83 obligation scopes, VFA Perm's 30-record/four-exercise implementation, and PFDS Chapter 2's six exercise headings retain their different validation meanings. PFDS Chapter 1 acceptance remains introductory accounting only.

All five VFA staging developments retain their historical focused-success evidence. The current table recovery is identified as partial; four other drafts and the generic total-table capability remain pending. FDSA's selected XA01 recovery and mapped-potential progress do not close Chapters 6 or 19. The Chapter 4 streams and their original base, 76 obligations and 11 exercises remain explicit. The PFDS 39-ID register is preserved by reference rather than treated as 39 missing theorems or copied into another inventory.

This Standards assessment checks the account's scope, evidence distinctions and consistency with the integrated source. It is not a new manuscript reading or an exhaustive independent remapping of all source rows to the latest master. The dedicated coverage audits and their original evidence pointers remain the substantive accounting provenance.

## 7. Finding history and dispositions

**New Standards findings: 0. New required source corrections: 0.** No heuristic pattern was promoted to a finding without a concrete consequence and applicable rule.

| Finding or retained register | Round-3 disposition |
|---|---|
| `INT-ST-001` — Low, duplicated source identifier | **Fixed, retained.** Current `docs/SOURCES.md` has PFDS S9, VFA S10 and FDSA S11. The R2 correction and reference assessment still apply; the current source preserves the fix. |
| `INT-SP-001` | Preserve the independent Spec-owned required-validation blocker; this Standards review does not close or rename it. |
| VFA `ST-002` / `SP-VAL-001`, historical `ST-006` fix | Retain the open required-validation findings and the actual source-fix evidence. The old output-creation failure is not reclassified as a proof failure. |
| FDSA `XT03-CP01` / `XT03-DOC01` | Retain source correction/recheck disposition and pending compiler/receiving gates; preserve original base `64c6b777d828ecfe83234fc2aed94600a1f24297`, donor identity and seven-path/88-name scope. |
| PFDS canonical 39 IDs and eight aliases | All dispositions in the canonical register, section 5, are retained. There are 23 repair/static/development closures, two boundaries and 14 distinct validation IDs. No historical scope or severity is erased or reranked. |

The PFDS Standards/shared open validation IDs remain `IMPORT-VAL-004`, `CH02-PRE-005`, `SUSP-STD-VAL-001`, `PURE-STD-VAL-001`, `COUNT-STD-VAL-001`, `PERSIST-ACC-STD-VAL-001`, `BODY-COUNT-STD-VAL-001` and `SIGNED-POT-STD-VAL-001`. Paired Spec findings remain independently owned. `SUSP-STAT-001` retains the effectful cached-reference type/result boundary; `PREP-10019-02` retains the pure-interpretation versus general cache-write ownership boundary.

These unresolved validation obligations coexist with satisfactory source corrections. Zero new source findings does not mean zero outstanding acceptance conditions.

## 8. Actual validation state and required continuation

The exact-R3 focused command was `lake build Examples.TextbookMaps Examples.OrderedMap Examples.SharedTreeMap`, through the authorized pinned native route with the documented one-thread setting. Its actual log ends with successful completion, 732 jobs, exit 0; the wrapper receipt records 7.578451 seconds. The log hash matches `8dc2b3ac56841e6043f27fb2254d15ee2d4302952368d05d18bcd818c556a8cd`. The receipt binds candidate/tree and toolchain/dependency pin hashes, and the public-type log confirms the reviewed universe boundary. This is focused development evidence, not the whole-library source-policy/coverage check and exhaustive audit.

Root's current full `./check.sh --candidate HEAD` began at **2026-11-14T03:29:12.689406+00:00** on this candidate. At the review cut, `intake/full-validation-r3.json` says **running; no terminal outcome yet**, `terminal_observed: false`. No current full success/verification record has been presented. The latest full record's fingerprint below identifies the running observation only and will differ if root later records a genuine terminal result. A later immutable continuation must assess that new evidence; this report does not predict it.

The older C1 cold run is separately recorded as interrupted: 3,278 targets, 630 observed completions, no recorded error line, unknown exit, no success record. Some modules taking several minutes does not establish host incapacity. That run supplies neither R3 validation nor a new mathematical defect.

Standards therefore remains **Blocked by required exact-candidate validation**. Necessary continuation is actual successful full build/coverage/policy checking and exhaustive audit with the matching `.lake/verification.json`, independent current-candidate outcomes on both axes, immediate `./check.sh --verify-candidate HEAD`, and final helper comparison to the approved receipt. Root owns those operations, canonical records and durable saving. The coordinator reports checkpoint 007 has been durably saved; archive/patch reconstruction establishes recoverability/content, not proof approval. No source, compiler or upload operation was delegated to this reviewer.

## 9. Evidence fingerprints

Paths here are relative to the integration workspace root. They identify the outside-source bytes used by this review, including maintained accounting records. No recursive inventory is reproduced.

| Record | SHA-256 |
|---|---|
| `checkpoint/conaled-textbooks/books/common/REQUIREMENTS.md` | `5d48738af724152b67daf993fa0f3d2abd7c2eeb7a47b7e080aa7740de1e07ac` |
| `checkpoint/conaled-textbooks/books/common/COVERAGE.md` | `3a643997082f7db88d92395e1239cbbc1c86af78dbe7d21c3a8adffaeb53cafa` |
| `checkpoint/conaled-textbooks/books/common/analysis/donor-dispositions.json` | `3437ebcd64d5a4f1b9564698a79bd83ee6116f2073b47a2d4619b14115641e6b` |
| `checkpoint/conaled-textbooks/books/common/ISSUES.json` | `1bc33b69ec1bee3868adcb049b31b99a9e7da4563c0a88ca2e0614ff30acdf13` |
| `checkpoint/conaled-textbooks/books/common/analysis/process.md` | `664faf609487139931459ee2b9d6cf9b72a39b0b6390ee87eded5a012b6635a3` |
| `checkpoint/conaled-textbooks/books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md` | `07fb1b0ea46e06a721ea603dbb99865597d844824f21d01b144659eb3ae1c6d6` |
| `intake/review/standards-r1.md` | `614928110c89288ab7296496dd65b46d16a4dd18817edc2d81a2274af0902b1b` |
| `intake/review/standards-r2.md` | `0757de767d72f39de79a029f33908f17db13c459717c24a21bb530440de04863` |
| `intake/map-recovery-handoff-20261114.md` | `cde82596e493d3d4dd13e2b570022226b0446843dc3e219d4c9eed13215eb688` |
| `intake/map-recovery-correction-r1.md` | `45ba98425dc533860c22875b4b828a61962a655d14c563fd399a871b913647c9` |
| `intake/map-recovery-correction-r2.md` | `9c532acee16bfb552a0ff91ea2abcd0dfb6488a38255c0298195e9d92074aaef` |
| `checkpoint/conaled-textbooks/books/common/evidence/map-public-types-20261114.log` | `98070df4a9c4b8cbf1b992ff3d5eebc7388974766ee632289fb98a5c35e0dd0a` |
| `intake/maps-focused-r3.json` | `eb10b219e860dc3cf8248a7e303446a372038d0d8bb011ed7be91fd7d56feb42` |
| `intake/validation-interruption-20261114.json` | `ac0649ae1ee7f69a0507a28a2b2fe00cd1a1329b2224385e8423d4d16727ac41` |
| `intake/full-validation-r3.json` | `33951558afb5c06a6d3c33141d6279470eed3263bc5d74dcd87e0c5c92a6c28b` |
| `intake/integration-candidate-r3.json` | `9735a260a6d1ab62b5d0b132f87c226f053052526a877fc7047266ec18fca47c` |

**Final Standards state:** base `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`; candidate `16440863ddb14d95c402ce65498e22497e246e72`; new findings 0; unresolved new integration source findings 0; `INT-ST-001` fixed; inherited validation findings retained; worst outstanding condition is required full validation; **Blocked**.
