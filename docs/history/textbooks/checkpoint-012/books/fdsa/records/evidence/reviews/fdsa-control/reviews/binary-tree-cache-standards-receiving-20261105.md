# FDSA-XT01 — Standards review of the receiving candidate

## Current outcome and unchanged scope

**Overall outcome: Passed.** The complete original source scope, all 115 actual public statements and matching full candidate validation have been assessed with **zero concrete Standards findings and zero unresolved findings**. This is the continuation of the existing XT01 review axis. It is not a new review scope, a third axis, or an acceptance action.

The immutable candidate is `90469ce4ba3fc49397d369a5db7d58aec7014f58`, tree `18bf4bc9df979d4ee6ac76182f58faed235a0714`. The incorporated integration base is accepted Chapter 3 `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`. The original unit base `a14977b9e316cc484ffad8a470d26b15615956c0`, original donor `64c6b777d828ecfe83234fc2aed94600a1f24297`, seven-path scope and every XT01-01–07 requirement remain in this same review history. The requirements retain SHA-256 `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`.

The complete prior Standards source assessment, SHA-256 `a24df99f02fd70300f25b982b53293d2f0d8485f053b8891829fe81c37043c97`, remains unchanged. Its source-only conclusions and exact input identities are retained; its Blocked outcome is not reused as approval. The current review freshly read the four complete formal modules, all receiving changes, both complete correction patches, the complete current source note, relevant unchanged definitions and pinned APIs, all 115 actual public types, and the closed focused/type evidence. The accepted root and map are preserved by exact byte comparison, excluding the one new public import and appended XT01 section. Their unrelated accepted content is not rereviewed as if it were new XT01 work.

Reviewer: `/root/tree_cache_standards`, independent of implementation. Root alone runs the compiler. This reviewer has run no Lean, Lake, checker or audit, polled no execution session, changed no project source/index/ref/cache, and taken no integration or upload action.

## Source, architecture and statement assessment

| Scope | Standards assessment |
|---|---|
| XT01-01: ordinary fold | The existing node-labelled `BinaryTree` is reused with explicit empty and ternary node operations. Payload and summary universes are independent. Constructor laws, arbitrary label-map transport and fusion require exactly the stated operation compatibility. The actual types contain no default-payload, equality-decision, ordering, monoid or balance premise. Canonical count and height are reused. |
| XT01-02: inorder and shape | Inorder retains left/root/right occurrence order and duplicates. Its length is canonical node count; arbitrary maps preserve inorder and shape. The leaf-count proof uses the pinned node/leaf identity. Value-level append equality is not called a cost identity. |
| XT01-03: cached product labels | Erasure is `map Prod.fst`, while the reader inspects only the root. `Valid` requires both recursively valid children and the stored local equation. `smartNode_valid_iff` does not repair descendants; `read_eq_fold` has the independent erased-tree fold on its right. Erasure/shape laws have no validity premise. |
| XT01-04: actual annotation | Annotation is an ordinary fold using the smart constructor. The separate erasure, recursive-validity and reader theorems apply to every input and are connected to those public operations. No full-annotation cost claim is added. |
| XT01-05: measured local execution | The existing measured pair, bind, pure and tick are reused. The implementation performs two actual reads and calls the supplied callback on those values. Value refinement requires its reached-argument equality; validity separately requires valid children. The actual cost statement is unconditional callback cost plus three; the bound adds only the reached cost premise. Nat cost does not constrain payload/summary universes. No physical-runtime or arbitrary-callback constant bound is inferred. |
| XT01-06: checked uses | Size/height readers, both pair projections, ordered-summary composition, a noncommutative word, asymmetric/repeated-label/Empty cases, corrupt descendants, and measured append/chain clients retain their intended public connections. Actual type review confirms their assumptions and conclusions. The valid chain supplies cost `n + 4`, actual next annotation and validity, and exceeds every fixed `K` at `n = K + 1`. Preparation of the input cache is not charged by that local theorem. |
| XT01-07: integration and provenance | One import reaches all four new modules. All accepted map bytes are a prefix of the receiving map; no old map replaces later accepted work. The dated source note separates original development status and receiving proof repairs. Exact source/representation/tariff boundaries and all later chapter obligations remain. The complete normal candidate check is now established below; the other ordinary review axis and caller acceptance duties remain distinct. |

The actual 115-name surface has 25 definitions and 90 theorems, with per-module totals 15/24/8/68. No authored private declaration, new instance or anonymous example is introduced. All exact original source headers and ordered names remain unchanged, including the four equation-style headers. Source-header identity is separate from actual exported-type review; both have now been checked for this candidate.

The noncommutative composition assumes only `Monoid M` and preserves `(left * measure label) * right`. The FreeMonoid case uses the concatenative instance and the expected ordered word. The empty-label examples have explicit summary bases and no hidden inhabitance assumption. The malformed four-node case simultaneously has a correct root count and local root equation but fails recursive validity. The invariant is satisfiable through actual annotation, and the unbounded measured family uses valid prepared children. These cases establish the intended connections without turning examples into substitutes for universal proofs.

The corrections leave every definition, theorem statement, hypothesis, example expectation, callback and tariff unchanged. Correction 1 unfolds the existing smart constructor after applying the reached-value equation and uses `omega` after explicit operation unfolding to normalize Nat addition. Correction 2 makes the existing generic fold/erasure chain explicit for size and height, closes the FreeMonoid calculation by reduction, uses the public empty-fold equation and removes a redundant tactic combinator. No linter option, mathematical premise, proof restriction or dependency was relaxed. The two failed attempts remain actual failures; later success does not reinterpret them.

## Current inputs and applicable standards

All 22 pre-existing files in the 26-file local import closure match the original draft and accepted Chapter 3. The later potential-accounting draft is not incorporated. All ten configuration/checker inputs and all 17 retained instruction identities match. Current relevant instructions were freshly read; unchanged complete prior readings of the remaining architecture/implementation guidance and three preflights are retained by exact identity. No `CODING_STANDARDS.md` or `CONTRIBUTING.md` exists at the candidate. Applicable ADRs 0001 and 0010 preserve the module layout, native Lean clients, exact pins, public coverage and exhaustive audit.

Fresh readings of `Measured`, `CallCount`, `ListReversal`, `TreeFlattening/Core` and `OrderedSummary` establish the actual sequencing, tick, recursive append and ordered summary interfaces used here. The complete pinned Mathlib `Data/Tree/Basic.lean` and the recorded FreeMonoid ranges were read and matched the immutable revision. No unvisited dependency file is claimed as a fresh semantic reading merely because it appears in an identity inventory.

The user waived only Nix. Official Lean/Lake 4.35.0, nine dependency pins and the disclosed native adapter/profile remain unchanged. The source-only delta does not create a fresh-check trigger under README; the accepted Chapter 1 fresh baseline remains authoritative. The current required gate is the complete normal `./check.sh --candidate HEAD`, including source policy, entrypoint coverage, output-integrity guards, full build and exhaustive permitted-axiom audit. Focused builds and type-printing cannot replace it.

## Actual validation and type qualification

| Recorded run | Candidate | Actual result | Reviewed evidence |
|---|---|---|---|
| Focused attempt 1 | `f0fd3faa84d57ab7583f877039da2c703431f0ce` | Exit 1 | Observations/Cached built; resource proof obligations and unused simp arguments failed. Complete 6,789-byte closed log and actual/native terminal records retained. |
| Focused attempt 2 | `bd7e379b742103767ee4620b14057ee86da8845c` | Exit 1 | Resource module built; five example proof/tactic obligations failed. Complete 6,209-byte closed log and actual/native terminal records retained. |
| Focused attempt 3 | `90469ce4ba3fc49397d369a5db7d58aec7014f58` | Exit 0 | All four targets completed. Complete 3,137-byte closed log; actual terminal `049454`; native and recorder exits agree. |
| Actual 115 statements | Same `90469ce` | Exit 0 | Actual terminal `44cda7`; 46,032-byte native output, 656 lines and all 115 ordered blocks read completely. |
| Full candidate check | Same `90469ce` | Exit 0 | Actual terminal `4e4f6d`, owned session 58948 CLOSED; the complete 325,963-byte log, native/recorder exits, all 1,111 audit rows and exact candidate verification are reconciled below. |

The actual type-output SHA-256 is `ea8ebef082abef7de66e7ce3f269771290073bc96a287ff864d49813c90d052b`; the complete block index is `1a44bd06217f4d6ef66c1fb3effd5e06427a627f023adcb97017cb9a3b517bbb`. The four untruncated read receipts cover ordinals 1–39 / lines 1–172 (`0e4158`), 40–70 / 173–330 (`25a597`), 71–95 / 331–516 (`b528f0`), and 96–115 / 517–656 (`0f5ef6`). Every block was assessed against its source definition, hypotheses and retained intended use. No unexpected parameter, typeclass, quantifier, projection, coercion or conclusion was found.

Independent reconciliation `ad0f0f` verified the complete block partition, exact original name order, current program/input hashes, 26 candidate source blobs, 78 current local objects/hash/trace files, ten configurations, nine clean pinned dependencies and twelve runtime/profile files. The saved pre/post identities are equal and all current rehashes matched. The four closed runs have agreeing actual, owned, native and recorder results; each outer log is exactly its saved prefix plus native body plus suffix. The inherited Chapter 3 verification record observed during the focused/type runs is explicitly stale for XT01 and supplies no XT01 full-check credit.

These observations do not prove loaded-object origin, absence of transient edits or absence of undeclared inputs. They accompany actual compiler output and isolated-checkout discipline. The full candidate check, exhaustive audit and this final independent assessment now provide distinct, matching evidence for this candidate.

## Completed full normal validation

This final continuation binds the exact seven original paths: `Applications/Trees/Observations.lean`, `Applications/Trees/Cached.lean`, `Applications/Resources/TreeCache.lean`, `Examples/TreeCache.lean`, `SquareApplications.lean`, `docs/research/fdsa-tree-cache.md`, and `docs/research/fdsa-reconstruction-map.md`. The candidate diff against incorporated Chapter 3 and the original donor diff against the original unit base contain exactly this same scope. The retained XT01-01 through XT01-07 assessments above are complete; review was not reduced to the proof corrections or final validation artifacts.

The complete normal run used the unchanged native kit/profile, one Lean thread and `./check.sh --candidate HEAD`. Actual tool terminal `4e4f6d`, owned CLOSED record, process recorder and native result all report exit 0. The recorded initial and final HEADs are the exact candidate with clean status. There is no timeout, recorder error or progress-bookkeeping error. The complete outer log is byte-for-byte the saved 70-byte prefix, 325,734-byte native output and 159-byte suffix. The retained native copies also match their original native-run records. Historical launch/progress fields do not override this secured terminal result and are not used as claims of a live process.

| Full-run evidence | Exact result |
|---|---|
| Closed outer log | 325,963 bytes; SHA-256 `dbd8ba410b64f7ee2eedc9389c4dceb907549dabbada6fee358277b760141dd8` |
| Native output | 325,734 bytes; SHA-256 `df724e47d431fd2f8aff4bab7c1097862a1dd9a92f527ce24957c9c1b9eceb09` |
| Matching success record | 867 bytes; SHA-256 `329f0d0087adc21b3446d7f10b67c472cdf62238ccf578865eec20569c04da61`; candidate `90469ce`, incremental mode; completed `2026-11-05T02:46:41.104505+00:00` |
| Source/coverage gate | Source policy and entrypoint/version checks passed; no weakened restriction |
| Output-integrity guards | Both hashed 3,336 artifacts; zero invalidated and zero inconsistent modules |
| Complete build/check | 1,112 build targets; 1,113 checked modules |
| Exhaustive audit | 1,111 unique module rows; 50,288 kernel-safe logical declarations; 29,430 theorem declarations; zero unsafe runtime declarations |
| Axiom union | Exactly `propext`, `Classical.choice`, `Quot.sound`; exhaustive audit passed |

The current qualified checkout's success-record bytes equal the retained record. Its compiler string identifies official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; its nine dependency revisions equal both the manifest and the current clean dependency checkouts. The native and recorder completion timestamps follow the candidate success record. The exact candidate and clean status were also independently rechecked in both receiving and qualified worktrees. The accepted integration branch still names the incorporated Chapter 3 base at this review observation.

Every audit row was independently parsed and summed, with unique module names and contiguous coverage of full-log lines 1658–2768. The semantic row-sequence digest is `64414ef6fbd94384d11f9e2a84bc8e31b0cb5f4ff1718021f46f83456c85cac4`. All 1,107 module rows of the accepted Chapter 3 full audit remain unchanged; exactly the following four rows are added. Whole-project totals and generated declarations are kept distinct from the 115 authored public names and 90 authored theorems.

| Added audit module | Logical declarations | Theorem declarations | Unsafe declarations |
|---|---:|---:|---:|
| `Applications.Trees.Observations` | 19 | 13 | 0 |
| `Applications.Trees.Cached` | 30 | 21 | 0 |
| `Applications.Resources.TreeCache` | 12 | 10 | 0 |
| `Examples.TreeCache` | 92 | 70 | 0 |
| Total compiled XT01 footprint, including generated declarations | 153 | 114 | 0 |

The source/type inputs were independently reconciled again after the full run. The original pre-observation, post-type observation and final observation have identical identities. All 26 current source files and candidate Git blobs, 78 local compiler objects/hash/trace files, ten configurations, nine clean dependencies and twelve runtime/profile files match. All 22 pre-existing closure sources still match both the original donor and accepted Chapter 3. The accepted Chapter 3 configurations, dependency identities and runtime/profile identities also match, so the full normal check is the applicable gate and no new fresh-check trigger is introduced.

The exact actual-type program `Statements115-complete.lean` is **4,721 bytes**, SHA-256 **`eea207cce83ce453b3625076041ff1262235771a8b92add322a149a044c98738`**. Its ordered 115 names, the complete actual-output partition and every retained semantic assessment remain matched. The final input observation is 33,026 bytes, SHA-256 `77d1486a596f4ea372a4d15f961323aa3dad3dd7339396ea5eba884968860fcf`. These are exact observation and output bindings, with the loaded-object/transient-input limits stated above retained.

Independent terminal/source/input reconciliation `833852` exited 0 and is saved in `final-evidence-reconciliation.json`. All 59 source-stage evidence bindings and nine protected prior records were rehashed without alteration. The full log's complete bytes and every audit row were processed; the meaningful guard, candidate, build, audit and final-result ranges were read. This does **not** claim a human reading of every build warning. Full final-read receipts are saved separately. The initial final-stage schema display `2cd713` was truncated and is not credited as a complete read; bounded follow-up `68016a`, complete terminal read `dfaf2f` and the independent reconciliation recovered the relevant metadata without changing evidence inputs.

## Findings and continuation boundary

There are **zero concrete Standards findings and zero unresolved findings**. The full original source assessment, all 115 actual type assessments and the complete applicable full-validation assessment are finished. The outcome of this same Standards axis is **Passed** for exact candidate `90469ce4ba3fc49397d369a5db7d58aec7014f58`. The former source-stage Blocked report remains unchanged as `source-type-report.md`, together with its structured assessment and hold. Its validation blocker is resolved by the closed evidence assessed here; no source-scope requirement was dropped. Both ordinary axes must approve this same candidate. Root must then perform immediate `./check.sh --verify-candidate HEAD` before the authorized exact local fast-forward and acceptance checkpoint. Those subsequent caller duties are not prerequisites for this review axis to report Passed.

This shared unit does not accept Chapter 4 or any later chapter. Whole-fold and inorder execution costs, shape/logarithm theory, all Chapter 4 algorithms/exercises, interval/AVL algorithms, raw maximum-cache correspondence and the existing-leftist representation adapter remain in their original scopes. Accepted Chapters 1–3 retain their accepted state.

The structured evidence and precise read boundaries are saved in `provenance/binary-tree-cache-standards-receiving-20261105/`. One reviewer-only metadata read used the earlier prepared-program filename and exited 1 after reading the complete focused log (`f0ca3d`); the correct `Statements115-complete.lean` and remaining metadata were fully read in `809804`. An initial combined prior-report rendering omitted part of its tail; `10010c` recovered lines 70–89. An overlong input-schema display (`d2474e`) is not claimed as a full textual read; `ad0f0f` independently parsed and reconciled every entry. These read/display incidents changed no files and are separate from compiler/candidate outcomes.

The first structured-evidence save was rejected before any subprocess was created because a complete set of tool outputs exceeded the argument-length limit. The absent output files were confirmed, then compact receipt metadata was saved successfully (`f1ded3`). This reviewer-only write preparation incident changed no project or evidence input; its exact boundary is retained in the read ledger.
