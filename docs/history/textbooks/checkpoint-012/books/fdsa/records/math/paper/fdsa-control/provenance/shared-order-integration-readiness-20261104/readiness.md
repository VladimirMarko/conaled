# XU02 integration readiness — source-only preparation

Prepared 2026-11-04T15:02:27.887638+00:00. This records the two completed read-only Order handoffs. **I is still unaccepted. The receiving candidate is null; no merge, source/ref mutation, compiler/cache action or receiving type/acceptance credit has occurred.** Root must separately release actual assembly after I acceptance and its verified, uploaded and exposed acceptance checkpoint. The observed accepted book and Foundation refs remain F. All earlier packages remain historical and unchanged.

## Exact source and history

Accepted C1 R: `07e480f6ec9958d4975bb90151005b84f2907614`. Accepted Foundation F: `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`. Prospective combined-four base I: `312aafb4446b995ff5542041b4e2e074f776db1e`. Corrected minimal Order tip O: `bdac9703aab4b383fa775568d36bf685af329389`. Original Order base and actual merge base of I/O: `ff3dd88082c6283df40bcd86a4363841a0360b12`. Original Order draft: `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`. Historical development/type candidate Z: `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`. The proposed new branch `work/fdsa-order-integration` was absent at this read boundary.

The original-base-to-corrected-tip diff is exactly six paths, four additions and two modifications. Keep each entire original path in review scope, including private helpers, anonymous instances, examples, source citations and exclusions. The exact corrected incoming identities are:

| Path | Corrected O Git blob | Bytes / lines |
|---|---|---|
| `Applications/Probability/PermutationOrder.lean` | `b039038772d2ecdb17864678021ffa9aff4efa63` | 15304 / 321 |
| `Examples/PermutationOrder.lean` | `e99c5a1b0716bb4d1a1f9155e10c0a56bbc99e35` | 6706 / 152 |
| `Examples/PermutationOrderBoundary.lean` | `7465d577dd4aa30b2f5e6bacfb257b75c2466f59` | 5605 / 148 |
| `SquareApplications.lean` | `b9b45c865f4345fe58ebcf1b2c14766c4abe0202` | 8360 / 254 |
| `docs/research/fdsa-permutation-order.md` | `d3a16fc8713c5dda2797a07ad14f3174ea97f841` | 8851 / 166 |
| `docs/research/fdsa-reconstruction-map.md` | `ebd4016c479ea8e1cf53193eb1aac7f4fd9dffaf` | 17824 / 294 |

The machine-readable inventory also records SHA-256 hashes, the full original-to-corrected six-commit chain, the actual merge base and all expected future parents. The three defining Lean files must remain exact O blobs; the root/map need a minimal union with I and the note needs only the dated status reconciliation below. The original source written on 2 November and later correction addenda retain their historical validation descriptions.

## Unexecuted normal-merge recipe

The governing sequence plan is `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/shared-acceptance-sequence-20261104/plan.md` (steps 2–7 and the stale-predecessor warning); the original requirements end by requiring accepted repaired C1 and the prior Minimum stage plus this unit's own gates. Keep the existing F → combined four → Order → Tail → new full C2 order. No whole-chain shortcut, later unit payload, chapter activation or changed requirement is proposed.

Only after I is actually accepted, its acceptance checkpoint is exposed, the qualified worktree is idle and root releases assembly: verify the exact accepted tip is I, the tracked tree/index and authorized status are correct, and the new branch is still absent. Record that starting state. Then use the same qualified worktree and an ordinary history-preserving merge:

```sh
git -C /workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review switch -c work/fdsa-order-integration 312aafb4446b995ff5542041b4e2e074f776db1e
git -C /workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review merge --no-ff --no-commit -s ort bdac9703aab4b383fa775568d36bf685af329389
```

These commands have not been executed or simulated. Reconcile actual conflicts if any; do not assert a conflict-free merge in advance. Preserve all original refs/history. Do not use a squash, rebase, reset, cherry-pick, `ours` merge, full old-tree replacement or a cumulative C2 branch. Before committing, preserve the three corrected Minimum files below, all other I source, the exact three O defining blobs, and only the six intended path changes. Apply the narrow documentary/import union. Verify the staged full diff, source headers/contracts, absence of unmerged paths and whitespace checks. Stop on a meaningful write failure and preserve the actual state instead of retrying blindly.

The resulting ordinary merge must have first parent I and second parent O; record both actual parents, actual conflict resolutions, full diff and each source identity. Use command-local `ChatGPT <chatgpt@openai.com>` identity and a local Conventional Commit including `(#174)`, for example `feat(probability): integrate restricted permutation orders (#174)`. No commit or resulting tree is supplied here. Recheck accepted/protected refs, O ancestry, clean candidate, exact six-path I-to-result scope and preserved predecessor identities before passing a frozen successor to both axes.

## Preserve corrected Minimum and inherited I content

O leaves the following files byte-identical to the old merge base. I has the required later corrections; a normal three-way merge should retain them, but that expected behavior must be checked against the actual result:

| Retained path | O = original merge-base blob | Required I blob |
|---|---|---|
| `Applications/Probability/PermutationMinimum.lean` | `9be74c11fda2de70b0fa02fcb597c631dc8e666e` | `084f3297508ae9311cf9d6fafe8d2976c3ab703d` |
| `Examples/PermutationMinimum.lean` | `e49e17a2a70836bd2cb8d4fc9bf799dd2be6bad9` | `ea120642c760ca7a7947689b3eb2b5a1f2af5876` |
| `Examples/PermutationMinimumBoundary.lean` | `05642e65256626b6ac881c9c2fe6de822858ca2d` | `2e7ca462be60d0e3c484573950b194cce532d26c` |

All three required I blobs equal Z. Keep I's `docs/research/fdsa-permutation-minimum.md` and all inherited C1/F and I four-unit corrections unchanged. `inventory.json` binds the I root, map and Minimum note; only root/map receive the unit-specific additions. The three old Minimum sources must not be copied from O. No later Tail, potential-accounting, natural-run or other draft payload belongs in this six-path candidate.

## Exact narrow documentary/import proposal

### SquareApplications.lean

Keep all I imports; insert only `import Examples.PermutationOrder` immediately after `import Examples.PermutationMinimum`. The main example already imports the boundary and core. No status comment or additional public-root import is needed.

### docs/research/fdsa-permutation-order.md

Keep the earlier proposed deletion of the opening “source draft, not compiled or accepted” wording and the later “These source-written examples remain uncompiled” sentence. Replace only that proposal's validation paragraph with:

> **Development validation — 4 November 2026.** The whole-order core and both example modules had individual compilation successes in development checks that failed overall. All 53 explicit public declarations from the corrected source were subsequently included in the successful 815-declaration type inspection at `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`; both independent reviewers assessed their complete printed types. These are historical results for that development candidate. Reuse requires matching integration-candidate evidence. The full acceptance gates below remain required.

The earlier proposal, patch and receipt remain unchanged historical artifacts under `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/`. Their earlier “53 awaiting” snapshot predates the actual815 result; do not present it as the later development state. Preserve all other mathematics, assumptions, source citations, notices, case descriptions and normative acceptance text byte-for-byte, including XU02-SP01's corrected “a different numeric order that is not strictly increasing”. No unsupported history about authorship timing is added.

### docs/research/fdsa-reconstruction-map.md

Preserve all I content and incorporate the complete original “Shared whole-subset ordering (draft)” section. Retain its mathematical description, connected cases and exclusions verbatim; replace only the final obsolete “source draft is uncompiled and unaccepted” status sentence with:

> The source note retains the 4 November 2026 development validation history; the local FDSA-XU02 record retains the frozen exact scope and subsequent candidate/review evidence. Full immutable-candidate acceptance gates remain required.

These dated historical/normative statements do not require a new status commit merely because a later acceptance gate succeeds. They do not grant the future receiving candidate any historical-result reuse.

## Complete declaration and evidence boundary

The complete explicit source inventory is 53 public declarations (core 17, main 18, boundary 18), five named private declarations (core 4, main 1), six anonymous instances (main 2, boundary 4), and no anonymous `example` commands. Retain all of them and all compiler-generated/full-audit scope; these source counts are neither new accepted theorem counts nor kernel totals.

Reuse the exact existing 53-name input at `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-statement-source-20261104/Statements.lean`: 3,522 bytes, 61 lines, SHA-256 `e2a9cbb72b7d24ef6fc53732a8f597ac32eca4f0f2a10e135745b5444d1a81c3`. Its old adjacent inventory has historical source bindings; preserve it and use the corrected bindings in the held Order/Tail package and this record. No duplicate program or unconditional extra compiler command is proposed.

All 53 names were checks 33–85 in the closed actual815 run at Z, whose full log is 874,944 bytes, SHA-256 `a5347095b4f93728b1b384c415189e1d934084eca4af8999028d0864fab9fc6b`, actual exit 0. The Standards and Spec final receipts both completely assessed those printed types. The original three individual module successes were core in failed aggregate attempt 3, boundary in failed aggregate attempt 4 and main in failed aggregate attempt 5; those are not whole-candidate passes. The exact closed record/log identities and individual-success lines are retained in the inventory.

The prospective static Order closure is exactly the three corrected Order modules plus three preserved Minimum modules; all six source blobs equal Z, with 14 distinct direct external import names. An immutable Git search found no existing I Lean module importing an Order module. No existing declaration-bearing I source changes; only the public import wrapper changes among old Lean files. Thus this source-only comparison identifies no additional public-name group beyond 53 structurally needing reprinting. It does not qualify any existing I 314/Foundation 110 or historical Z result for the receiver. Actual source, artifact lineage, configuration, pins, runtime and import/instance inputs must satisfy the existing qualification rules, and both axes must assess that evidence. An unmet qualification requires matching actual inspection. No receiver artifact/runtime capture has occurred.

## Exact continuation records and findings

### Frozen scope and original source preparation

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-order-requirements.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-order-start.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/permutation-order-candidate.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/tickets/FDSA-XU02.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-order-api-preflight.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-order-source-preflight.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-order-calculations.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/permutation-order-draft-preflight.md`

### Existing full independent continuation and coordinator

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-round1.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-standards-source-preparation-20261104.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/reviews/chapter02-spec-source-preparation-20261104.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/successor-source-reconciliation-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/source-scope-successor-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/actual815-complete-type-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/actual815-complete-spec-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/actual815-execution-input-assessment-4b5dbfa0.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/actual815-execution-input-qualification.json`

### Original historical documentary proposal and assessments

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/proposed/fdsa-permutation-order.md`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/patches/fdsa-permutation-order.md.patch`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-shared-notes-status-preparation-20261104/receipt.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-standards-source-preparation-20261104/shared-note-proposals-assessment-6b95185.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/shared-note-status-assessment-5398db.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-spec-source-preparation-20261104/shared-notes-six-plus-correction1-assessment.json`

### Closed actual815 and input evidence

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/secured-terminal.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/actual-type-ranges.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-complete-public-statements815-20261104-attempt1/full.log`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-statements815-input-observations-20261104-attempt1/pre-inputs.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-statements815-input-observations-20261104-attempt1/post-inputs.json`

### Existing 53 program and old binding

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-statement-source-20261104/Statements.lean`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-statement-source-20261104/inventory.json`

### Original correction/finding receipts and diffs

- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-proof-style-correction-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-proof-style-correction-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction1-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction1-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction2-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction2-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction3-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction3-20261104/correction.diff`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction4-20261104/result.json`
- `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter02-xu02-elaboration-correction4-20261104/source.diff`

The correction records retain XU02-SRC-001 and XU02-ELAB-001–014. The original candidate/draft-preflight retains XU02-SP01; its source prose correction remains in scope. C02-DOC-003 stays open for this unit until exact receiving application/assessment. C02-TYPE-001 was resolved by both axes for Z only, without full candidate acceptance or automatic receiver credit. Do not reset resolved historical assessments or treat earlier pending statements as current.

There is no six-path or mathematical-scope mismatch in this proposed union. The concrete review-boundary caution is that the original contributor draft-preflight excluded the core and its own boundary module and expressly was implementation-side, not an independent complete axis. It cannot substitute for the existing complete C2 Standards/Spec assessments. No dedicated permutation-order Standards/Spec final report was found in the bounded review-prefix inventory. Continue those existing full axis/finding records on the entire original six-path unit, rebind the incorporated base and immutable successor, and assess all actual merge resolutions, documentary changes, inherited compatibility and validation evidence. Do not reduce review to the final diff or public declarations alone.

The existing 81-path/112-obligation C2 records retain their original whole-project review scope; this stage does not accept C2. The complete source mathematical assessments and complete 815 semantic reads are retained by identity rather than repeated here. Both axis continuation files, original requirements, preflights, old proposal and all relevant evidence identities are listed in `inventory.json`.

## Gates after an actual immutable handoff

Root owns later validation. The applicable focused evidence and complete statement evidence must match the receiving inputs. Apply the README's normal-versus-fresh rules: source-only integration is not itself a fresh trigger. Through the qualified unchanged native environment with one thread, the normal full `./check.sh --candidate HEAD` must secure its actual exit, complete closed logs, both integrity phases, full build, exhaustive permitted-axiom audit and matching verification record. No artifact transplantation or alternative compiler/profile is proposed. Existing copied F/I verification cannot establish a new candidate result.

Only after all mandatory gates and both independent full-scope axes pass with no unresolved findings: qualified immediate `./check.sh --verify-candidate HEAD`, exact local accepted fast-forward, accurate tickets/coverage and verified uploaded/exposed acceptance checkpoint. Preserve the recorded unrelated accepted-worktree exclusions without allowing the fast-forward to overwrite them. No GitHub mutation or push is authorized. Then proceed separately to XU03 and new complete C2, preserving the established order.

## Read boundary and hold

This saves the two completed read-only handoffs plus a fresh immutable identity/ancestry/import check. The frozen requirement, candidate and contributor scope/finding contexts, documentary proposal and original section, relevant terminal results and complete-axis dispositions were read; source identities and declaration/import mappings were reconciled against existing full inventories. No new full mathematical or 815 semantic assessment is claimed. No Lean/Lake/compiler, build/cache/output capture, live-process polling, source/ref/index mutation or candidate assembly occurred. Only this new preparation package is written. All earlier records stay unchanged; root must separately release source assembly after accepted I durability.
