# XU03 Tail integration readiness

Prepared 2026-11-04T15:19:59.878965+00:00. **Preparation only: prospective base J is unaccepted, the receiving Tail candidate is null, and receiving type/validation/acceptance credit is zero.** This package does not authorize assembly. Root must first accept J through its complete gates and expose its verified acceptance checkpoint, then separately release Tail source work. No source, ref, index, compiler, cache, runtime, artifact capture or process action occurred. Only this new provenance package is written; all earlier packages remain unchanged.

## Exact baseline, history and whole original scope

Accepted book currently remains I `312aafb4446b995ff5542041b4e2e074f776db1e`; F `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` and accepted C1 R `07e480f6ec9958d4975bb90151005b84f2907614` are preserved. Prospective J is `932438a765340d69fa6402f6abd17def6ec28d13`. Corrected Tail tip T is `02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9`. Original Tail draft is `a0597381f02eddd074ee96cabaa974f2062285f8` over original Order base B `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`. An actual read-only Git merge-base calculation gives exactly B for J/T. The eight-commit original Tail/correction history is retained in the inventory; no history rewrite or cherry-pick is proposed.

The original B-to-T delta is exactly six paths, four additions and two modifications:

| Path | Corrected T blob | Bytes / lines |
|---|---|---|
| `Applications/Probability/PermutationTail.lean` | `437552dda711378d6a0910d9aa79bd99caae8977` | 23521 / 487 |
| `Examples/PermutationTail.lean` | `baa3e26a3c72a4589765562167d1d85edc011e67` | 9826 / 222 |
| `Examples/PermutationTailBoundary.lean` | `5b0283972ed1bfd0f2e12d30e0d2189203f04af0` | 12064 / 266 |
| `SquareApplications.lean` | `2cd4b70ebb4b89bfcfcd61c98f1b9594f5a38d7b` | 8392 / 255 |
| `docs/research/fdsa-permutation-tail.md` | `233136b41f38efafa0d5e1d8f22d8c2864340335` | 10367 / 203 |
| `docs/research/fdsa-reconstruction-map.md` | `0655c5824d0e5b06a0c128de0ea0645fd8f116d3` | 18893 / 312 |

Retain the entire six-path scope, all original frozen obligations and cases, private/anonymous/generated obligations, source citations and previous findings. The three Tail defining Lean files must remain exact T blobs; the public root/map require their unit-specific union with J and the Tail note requires only the narrow dated reconciliation below. Later XP/XR/XW/XU04–06/C2 payloads and any Chapter 3 activation remain outside this stage.

## Unexecuted history-preserving assembly recipe

The new branch `work/fdsa-tail-integration` was absent at preparation. After exact J acceptance, exposed durability and separate root release, verify an idle qualified worktree, clean source/index and matching accepted tip. If that tip has changed through a required correction, explicitly rebind the incorporated base and preservation checks before assembly; do not pretend this prepared J identity describes another commit.

```sh
git -C /workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review switch -c work/fdsa-tail-integration 932438a765340d69fa6402f6abd17def6ec28d13
git -C /workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review merge --no-ff --no-commit -s ort 02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9
```

These are proposed commands only; no merge or merge simulation was run. Record actual exits, conflicts if any and each resolution. Keep an ordinary merge with ordered parents J then T, retaining all original refs/history. No squash, `ours` shortcut, rebase/reset, cherry-pick, old whole-tree copy or cumulative later branch. Preserve the six predecessor Lean files and two notes below, every J path outside the six declared Tail paths, and all three exact Tail defining blobs. Reconcile only the planned note/root/map additions, verify the complete staged diff and commit locally using command-local `ChatGPT <chatgpt@openai.com>` and a Conventional Commit including `(#174)`. Freeze a clean immutable handoff and hold source before validation. Stop on an actual meaningful write failure; do not retry blindly.

## Preserve corrected Minimum and Order

The incoming T sources below all equal B's older versions. J contains the required later corrected versions, so a normal three-way merge is expected to retain J automatically; the actual result must be verified and no conflict-free result is claimed in advance.

| Preserved source | Old T = B blob | Required J blob |
|---|---|---|
| `Applications/Probability/PermutationMinimum.lean` | `9be74c11fda2de70b0fa02fcb597c631dc8e666e` | `084f3297508ae9311cf9d6fafe8d2976c3ab703d` |
| `Examples/PermutationMinimum.lean` | `e49e17a2a70836bd2cb8d4fc9bf799dd2be6bad9` | `ea120642c760ca7a7947689b3eb2b5a1f2af5876` |
| `Examples/PermutationMinimumBoundary.lean` | `05642e65256626b6ac881c9c2fe6de822858ca2d` | `2e7ca462be60d0e3c484573950b194cce532d26c` |
| `Applications/Probability/PermutationOrder.lean` | `948b428687adb0c370c30298ce22c02e1bd863b6` | `b039038772d2ecdb17864678021ffa9aff4efa63` |
| `Examples/PermutationOrder.lean` | `c6f0d7d2a08b5bfc1b9b34563a8a5578a3fcd52d` | `e99c5a1b0716bb4d1a1f9155e10c0a56bbc99e35` |
| `Examples/PermutationOrderBoundary.lean` | `9e384a46b8fda579ccee3605928a0fde864c881e` | `7465d577dd4aa30b2f5e6bacfb257b75c2466f59` |

All six required J source blobs equal the historical reviewed Z inputs. Preserve J's two current predecessor notes too: Minimum blob `052101180ceaf79f81e0873f24160fc73ae52f33` and Order blob `8d8f68c95185bd787ce26bb5ba6cf3a6f652862a`. T carries their older base versions, so whole-tree copying would also regress accepted/current documentary corrections. Their old/current full identities, and J's root/map identities, are in the inventory. The complete J reconstruction-map prefix and all unrelated inherited C1/F/shared-four/Order content remain intact.

## Exact proposed documentary/import wording

### SquareApplications.lean

Preserve all current J imports and add exactly `import Examples.PermutationTail` immediately after `import Examples.PermutationOrder`. The Tail main example already imports its core and boundary. No other root import or status comment is needed.

### docs/research/fdsa-permutation-tail.md

Use the exact held corrected proposal at `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-correction1-20261104/proposed/fdsa-permutation-tail.md`. Keep its previously assessed removal of the opening obsolete uncompiled status and later “These mathematical expectations and source-written proofs remain uncompiled” sentence. Keep its normative predecessor-acceptance wording at the end. Replace only its dated validation snapshot paragraph with:

> **Development validation — 4 November 2026.** The conditional-tail core and both example modules had individual compilation successes in development checks that failed overall. All 61 explicit public declarations from the corrected source were subsequently included in the successful 815-declaration type inspection at `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`; both independent reviewers assessed their complete printed types. These are historical results for that development candidate. Reuse requires matching integration-candidate evidence. The full acceptance gates below remain required.

All other mathematical prose, contract assumptions, source links, notices, cases and full gates remain byte-for-byte as the held proposal. Both the earlier original proposal and its correction1 package remain unchanged historical artifacts. The earlier snapshot accurately recorded the core success, failed boundary checks, unvalidated later correction and pending types; later boundary/main successes and actual815 advance that historical state. Do not erase any actual failed run/probe or claim that all three modules passed one aggregate check. Do not reintroduce the unsupported phrase “cited checks”.

### docs/research/fdsa-reconstruction-map.md

Preserve all J content and append/reconcile the complete original “Shared conditional remaining orders (draft)” section. Retain its mathematical description, two-step use, null/containment cases and chapter limitations verbatim. Replace only the sentence `The source is uncompiled and
unaccepted.` with:

> The source note retains the 4 November 2026 development validation history; full immutable-candidate acceptance gates remain required.

Retain the following original sentence: “Local FDSA-XU03 retains the frozen scope, exact expectations, candidate identity and later validation/review evidence.” The dated historical and normative language supplies no receiver credit and does not require another status commit merely because later acceptance succeeds.

## Complete declaration/program scope and actual history

| Defining module | Public | Named private | Anonymous instances |
|---|---:|---:|---:|
| Applications.Probability.PermutationTail | 15 | 8 | 0 |
| Examples.PermutationTail | 24 | 1 | 2 |
| Examples.PermutationTailBoundary | 22 | 10 | 6 |
| **Total** | **61** | **19** | **8** |

There are no anonymous `example` commands. The inventory retains all 61 public names in program order, all 19 named private declarations and all eight anonymous source anchors, verified against the exact immutable source lines. Compiler-generated declarations remain full build/audit scope; these are source counts, not kernel totals or newly accepted results.

The complete standalone input already exists at `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-tail-acceptance-preparation-20261104/StatementsTail61.lean`: 4,105 bytes, 75 lines, SHA-256 `50d89e5f2118f345624a6eb51c0c6b075af0af416f454a141893b460f1ea17aa`. It contains exactly three Tail imports, the retained explicit/full-name/universe options and all 61 checks. Reuse those file bytes unchanged; no duplicate program or compiler command is prepared here. Its old 84-name ancestor also included numerical-mean imports and must not be substituted wholesale for this earlier Tail stage. Both historical inputs/inventories remain unchanged.

The core actually passed individually in closed aggregate attempt 6 at `f673ee87195e4aaeef4b41767a7468c70ad6214f` (90s); boundary in closed attempt 9 at `0a7ef0784e1b140b356b4ce7b79ba65a79edf3c3` (128s); main in closed attempt 10 at `8ba7ae11a657e8a4af025f60b4e1a54dddb3c512` (331s). All three enclosing aggregates exited 1. Attempt 6 main `Ran` was not a pass; attempt 9 main failed and its six-body successor later passed in attempt 10. Root's exact terminal records and actual successful log lines were rechecked here; all failures, intermediate corrections and probe boundaries remain historical evidence.

All 61 public types were checks 203–263 in the successful actual815 inspection at Z `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`, and both independent axes completely assessed those printed types. The three corrected Tail sources match Z exactly. Their completed assessments and original source scope are retained, not repeated or reset. The command's full log is 874,944 bytes, SHA-256 `a5347095b4f93728b1b384c415189e1d934084eca4af8999028d0864fab9fc6b`; its actual pre/post observations and both dispositions are bound in the inventory. C02-TYPE-001 is resolved for exact Z only.

## Source-compatible closure and receiving qualification gap

The prospective static closure contains exactly nine local modules: the three Tail modules plus the three corrected Order and three corrected Minimum modules. All nine source blobs equal Z; the 19 distinct external import names and actual local edges are recorded. A source-only immutable Git search found no existing J Lean module importing Tail. Only the public root wrapper changes among existing Lean files; no existing declaration-bearing J module is modified by the proposed six-path union. This comparison identifies no additional public-name group that is structurally forced to be reprinted beyond the existing 61-name obligation.

**This is source correspondence, not qualified evidence reuse.** Root reports a concrete current-versus-Z trace/dependency-path gap. This author has not captured or reconciled current output objects/traces, dependency paths, runtime/configuration observations or a nonexistent Tail receiver. No receiver input hashes or success claims are invented. Exact source equality alone cannot bridge that gap. Any reuse requires actual receiving source/artifact/configuration/pin/runtime/import-instance lineage and both independent dispositions under the existing rules; otherwise provide matching actual inspection. The same conditional boundary applies to inherited J/I/Foundation evidence. No automatic reuse or unconditional redundant run is imposed by this preparation.

## Original review/finding continuation

### Original frozen scope and preparation

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/tickets/FDSA-XU03.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-tail-requirements.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-tail-start.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-tail-candidate.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-tail-api-preflight.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-tail-source-preflight.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-tail-calculations.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-tail-draft-preflight.md`

### Existing complete C2 independent source/type continuation

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-round1.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-standards-source-preparation-20261104.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-spec-source-preparation-20261104.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/successor-source-reconciliation-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/source-scope-successor-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/actual815-complete-type-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/actual815-complete-spec-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/actual815-execution-input-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/actual815-execution-input-qualification.json`

### Corrections and stable findings

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-proof-style-correction-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-proof-style-correction-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-api-correction-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-api-correction-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-elaboration-correction1-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-elaboration-correction1-20261104/source.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction2-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction2-20261104/source.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction3-20261104/findings.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction3-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction3-20261104/root-source-assessment.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction4-20261104/source-preparation.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-boundary-elaboration-correction4-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-main-elaboration-correction5-20261104/diagnostic-mapping.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-main-elaboration-correction5-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu03-main-elaboration-correction5-20261104/commit-record.json`

### Historical note proposals and assessments

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/proposed/fdsa-permutation-tail.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/patches/fdsa-permutation-tail.md.patch`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-correction1-20261104/proposed/fdsa-permutation-tail.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-correction1-20261104/patches/fdsa-permutation-tail-vs-original.patch`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-correction1-20261104/patches/fdsa-permutation-tail-vs-prior-proposal.patch`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-correction1-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/shared-note-proposals-assessment-6b95185.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/shared-note-status-assessment-5398db.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/shared-notes-six-plus-correction1-assessment.json`

### Historical actual815 and observed inputs

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/secured-terminal.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/actual-type-ranges.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/full.log`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-statements815-input-observations-20261104-attempt1/pre-inputs.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-statements815-input-observations-20261104-attempt1/post-inputs.json`

### Existing type programs and held source bindings

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-tail-acceptance-preparation-20261104/StatementsTail61.lean`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-tail-acceptance-preparation-20261104/inventory.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-tail-acceptance-preparation-20261104/source-and-evidence.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-tail-acceptance-preparation-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-tail-numerical-statement-source-20261104/Statements.lean`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-tail-numerical-statement-source-20261104/inventory.json`

### Prior sequence, Order readiness and immutable J handoff

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/REQUEST.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/shared-integration-preflight.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-acceptance-sequence-20261104/plan.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-acceptance-sequence-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-integration-readiness-20261104/readiness.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-integration-readiness-20261104/inventory.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-integration-readiness-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-source-integration-20261104/handoff.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-source-integration-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-source-integration-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-order-source-integration-20261104/source.diff`

Retain XU03-SRC-001; XU03-ELAB-001/002; the original XU03-BND-ELAB-001, -002–006 and -007–009 groupings; XU03-ELAB3-01–16; XU03-MAIN-ELAB-001–006; and the C02-DOC-003 receiving application. The six current ite-name replacements and three later explicit NNReal-to-ENNReal arithmetic repairs also retain their original records without inventing new IDs. The original bounded contributor preflight explicitly opened no XU03-SP finding; do not invent one.

That contributor preflight excluded the core and boundary proof implementations. It cannot replace either existing complete C2 axis assessment, which retained all 81 paths, 112 obligations and ten shared scopes. Both axes must continue the entire original Tail scope at the actual incorporated base/candidate, preserving earlier source/math/type assessments and reviewing all actual resolutions and new terminal evidence. No review is reduced to changed proof bodies, public names or this final integration diff alone. No mathematical/path-scope mismatch was found in the planned union; its current outstanding boundary is actual receiver assembly/validation and the reported evidence-qualification gap.

## Mandatory later gates and read boundary

Keep the established accepted I → accepted Order → Tail → new complete C2 sequence. Tail cannot start assembly before J acceptance and exposed durability. Chapter 3 remains queued. All original optional-head/tail, a.e. versus pointwise support, positive versus null conditioning, same-sample projection, original complete positions, nested-conditioning and fixed-subset containment obligations remain. The 1/3-versus-2/3 noncontained-set counterexample and all arbitrary-environment HasLaw premises are unchanged; no algorithm-history, joint independence, sampling coupling or cost conclusion is supplied.

After an actual immutable handoff, root owns applicable focused/type evidence, the normal-or-fresh candidate mode required by README, full guarded build, exhaustive permitted-axiom audit, complete closed logs and matching verification, both independent final full-scope axes, immediate qualified `./check.sh --verify-candidate HEAD`, exact accepted integration and exposed checkpoint. Source-only incorporation is not itself a fresh trigger; no new threshold, prerequisite, profile or gate exception is introduced. Existing verification records are historical and cannot validate a future commit. No artifacts/traces are transplanted.

Full frozen Tail requirements, current ticket, original candidate and bounded draft-preflight, complete corrected historical note/patch and complete standalone 61-name input were read. Correction dispositions, diagnostic mappings, closed result records/success lines and completed actual815 axis dispositions were read. Immutable ancestry, six-path identities, the nine-source import closure, program/public-name equality and private/anonymous source anchors were reconciled. Prior complete mathematical/source/type assessments were retained by exact identity rather than repeated. No live outputs were inspected, compiler/process polled, receiving artifact input captured or source/ref mutated. Only this new package is written; it will be held after complete author readback.
