# Tail/XU03 source integration handoff

## Immutable result and explicit boundary

The authorized ordinary integration is complete at **`726cb9a9b9ff4444a7614383de4fb336e8804aa7`**, branch **`work/fdsa-tail-integration`**, tree **`43f1c15166931d4bd3e91e6dbf12059d0da1cfc2`**. The checkout is clean. This is an **uncompiled receiving candidate**, with no receiving type, full-check, audit, final-review, immediate-verification or acceptance credit.

The ordered actual merge parents are:

1. Accepted Order J: `932438a765340d69fa6402f6abd17def6ec28d13`.
2. Corrected minimal Tail T: `02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9`.

Both are actual ancestors. Every original/corrected Tail history commit from `a0597381f02eddd074ee96cabaa974f2062285f8` through T is retained; the common base remains `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`. This is an ordinary merge and resolved union, without a squash, rewritten original history or substituted old source tree.

The accepted `work/fdsa-book` remains J. All **65 pre-existing refs** are unchanged; the new Tail branch is the sole added ref, bringing the total to 66. The original foundation, shared-four and Order refs are preserved. Source HOLD starts at this immutable commit; root owns every subsequent compiler, review, final verification, accepted fast-forward and checkpoint action.

## Authority and clean baseline

Root released this precise assembly after J's complete acceptance and checkpoint 0116 durability. The complete updated `CURRENT.md`, Order acceptance/durability, both held bounded Tail preparations, frozen Tail requirements and held documentary proposal were read. Their exact observed identities are in `baseline.json`; earlier dated preparations remain unchanged.

J acceptance is recorded at `provenance/shared-order-acceptance-20261104/acceptance.json`; the later `durability.json` binds checkpoint `conaled-fdsa-0116-accepted-order-and-tail-ready.tar.gz` (25,111,562 bytes, SHA-256 `a3af479ecf3818f06ac1a421d3dd17d47b0bebe681ed4f95ed3da88d7fef13ae`, Library ID `libfile_60dcf58fbe508191ab2e60043e427ef5`). The older acceptance record's pending-checkpoint field is historical and is resolved by that later durability record.

The repository was the existing qualified `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review` checkout, initially on `work/fdsa-order-integration` at J. Index, tracked files and complete untracked status were empty; the target branch and this provenance directory were absent. The actual baseline had 65 refs and 15 worktrees. No new worktree or cache was created. Read-only baseline observations showed ordinary available space zero and raw free 1,213,554,688 bytes; the authorized source writes completed without a resource error. This observation is not a build-capacity or compiler-installation claim.

## Actual commands and conflict resolution

All mutating Git commands used command-local `user.name=ChatGPT` and `user.email=chatgpt@openai.com`; no persistent Git configuration was changed. Exact argv, UTC times, actual exits, stdout/stderr and statuses are retained in the numbered records.

| Step | Actual operation | Exit and effect |
| --- | --- | --- |
| 01 | `git switch -c work/fdsa-tail-integration 932438a765340d69fa6402f6abd17def6ec28d13` | 0; created the authorized branch at clean J. |
| 02 | `git merge --no-ff --no-commit -s ort 02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9` | 1; one content conflict in `docs/research/fdsa-reconstruction-map.md`; the three Lean additions arrived cleanly and the public root auto-merged. |
| 03–04 | Preserve actual conflict bytes and stage identities, then apply the exact held documentary union | Completed; no formal proof/statement changes. |
| 05 | `git add -- SquareApplications.lean docs/research/fdsa-permutation-tail.md docs/research/fdsa-reconstruction-map.md` | 0; no unmerged paths remain. |
| 06 | `git diff --cached --check` plus exact staged/source/ref comparisons | 0; no whitespace error or unstaged changes; exact six-path scope. |
| 07 | `git commit -m 'feat(fdsa): integrate conditional permutation tail laws (#174)'` | 0; ordinary two-parent merge commit `726cb9a9b9ff4444a7614383de4fb336e8804aa7`. |

The actual conflict concerned the accepted Order status paragraph at the end of J versus the stale Order paragraph followed by T's Tail section. Its full pre-resolution bytes remain in `actual-map-conflict.txt`; stage 1/2/3 identities remain in `03-conflict-before-resolution.json`. Resolution retained **all 614 J map lines byte-for-byte** and appended the complete original Tail section with only the approved historical-status sentence replacement. No mathematical contract, previous source correspondence or accepted C1/foundation/appendix snapshot was removed.

The public-root auto-merge already equaled the prepared result: exactly `import Examples.PermutationTail` after `import Examples.PermutationOrder`, with all other J bytes preserved. The Tail note starts from the held correction1 proposal, replaces only its dated validation paragraph with the prepared historical development wording, and retains the proposal's narrow obsolete-uncompiled/prerequisite corrections. All original mathematical, case, source-citation and normative gate text remains.

The three prepared documentary SHA-256 expectations were independently supplied by the held Spec preparation and match the actual receiving bytes exactly:

| Path | Expected and actual SHA-256 |
| --- | --- |
| `SquareApplications.lean` | `a30e93ebbdb80f40d751cc30a5185e5e96ce40861540c35fb439362d66d2678d` |
| `docs/research/fdsa-permutation-tail.md` | `bebf1822c26e94c35d1474a99687156ffe44d3c2f37bcb76ed7c930fdf37236d` |
| `docs/research/fdsa-reconstruction-map.md` | `b5997a67ca8e23f4418b5428db17bedcf960f262f2e9a9e711255799970689d6` |

## Complete changed-path and preservation accounting

The actual J-to-candidate diff is exactly six paths and **1,198 insertions, no deletions**. Four paths are added; the public root and reconstruction map are extended. `source.diff` is the complete 60,434-byte / 1,241-line binary-capable Git diff, SHA-256 `825737dfb5fc507013f9ab5d156a3e4a68339b1305fa09fac45924b20e68c5db`.

| Path | Candidate Git blob | Bytes / lines | SHA-256 |
| --- | --- | ---: | --- |
| `Applications/Probability/PermutationTail.lean` | `437552dda711378d6a0910d9aa79bd99caae8977` | 23521 / 487 | `62e2e11c82415bcb558779c599bf07745fa9abab4305ec87d11c9eaa86a9eaed` |
| `Examples/PermutationTail.lean` | `baa3e26a3c72a4589765562167d1d85edc011e67` | 9826 / 222 | `bc6753118198b91de684e50bd6196b4b68035b92461a34c0528dbd7f7742099e` |
| `Examples/PermutationTailBoundary.lean` | `5b0283972ed1bfd0f2e12d30e0d2189203f04af0` | 12064 / 266 | `a09f8d39371d63ced20624b71148b72a150727eb96d809094211a4da45336b54` |
| `SquareApplications.lean` | `623b77c69d1ff2cf09a9429eefbd69641370b9cc` | 8609 / 262 | `a30e93ebbdb80f40d751cc30a5185e5e96ce40861540c35fb439362d66d2678d` |
| `docs/research/fdsa-permutation-tail.md` | `8cb9419840e7f6d2c553765d05d8aa39fe58c389` | 10871 / 205 | `bebf1822c26e94c35d1474a99687156ffe44d3c2f37bcb76ed7c930fdf37236d` |
| `docs/research/fdsa-reconstruction-map.md` | `0944dfd5fde6895f2c4cc0db9bd015f3e71ffed1` | 41477 / 631 | `b5997a67ca8e23f4418b5428db17bedcf960f262f2e9a9e711255799970689d6` |

The first three defining modules are **byte-for-byte exact T**, including every import, option, definition, theorem header, proof, private helper and local instance. They also retain the historically assessed corrected development source; no compiler evidence is inferred from this source equality.

The following accepted predecessor paths remain exact J:

| Protected path | Preserved J blob |
| --- | --- |
| `Applications/Probability/PermutationMinimum.lean` | `084f3297508ae9311cf9d6fafe8d2976c3ab703d` |
| `Examples/PermutationMinimum.lean` | `ea120642c760ca7a7947689b3eb2b5a1f2af5876` |
| `Examples/PermutationMinimumBoundary.lean` | `2e7ca462be60d0e3c484573950b194cce532d26c` |
| `Applications/Probability/PermutationOrder.lean` | `b039038772d2ecdb17864678021ffa9aff4efa63` |
| `Examples/PermutationOrder.lean` | `e99c5a1b0716bb4d1a1f9155e10c0a56bbc99e35` |
| `Examples/PermutationOrderBoundary.lean` | `7465d577dd4aa30b2f5e6bacfb257b75c2466f59` |
| `docs/research/fdsa-permutation-minimum.md` | `052101180ceaf79f81e0873f24160fc73ae52f33` |
| `docs/research/fdsa-permutation-order.md` | `8d8f68c95185bd787ce26bb5ba6cf3a6f652862a` |

The complete tree comparison verifies **all 1,604 J paths outside the six declared paths** unchanged, including all other predecessor notes, accepted C1/foundation/appendix sources, compatibility clients, checker/configuration files and exact pin files. J has 1,606 tracked paths; the candidate has 1,610. Thus no later C2 payload, XP01 or unrelated shared draft was introduced by this merge. `result.json` retains the full post-ref list, worktree topology, ancestor exit checks, six-path identities and preserved predecessor identities.

## Full original scope, author reading and retained findings

The full frozen `reviews/permutation-tail-requirements.md` remains controlling. This handoff retains **61 public declarations (46 theorems and 15 definitions), 19 private named theorems and 8 anonymous local instances**, with no anonymous examples. These are source-accounting counts, not kernel/theorem-audit totals. Per-module counts are core 15/8/0, main examples 24/1/2, and boundary examples 22/10/6 (public/private/anonymous).

The author read all six candidate paths completely: **2,073 lines**, including all **975 lines** of the three Tail Lean modules, the full 205-line public note, 262-line root and 631-line map. `author-readback.json` records the actual complete displayed line ranges, input identities and owned read chunks. The complete root/map diff and Tail-note-versus-T diff were separately read; all newly added source diff content was read as the complete files. This is author integration readback, not a replacement independent Standards or Spec assessment.

The unchanged mathematics retains arbitrary current-environment `HasLaw`, only a.e. measurability where specified, hypothesis-free optional-head/cons-tail identity, exact same-sample/on-event projection bridges, complete original positions, fixed remaining-subset containment, positive conditioning versus null zero measures, and the original factorial normalization. All connected cases remain: distinct 1/2 tails, unsupported output, filtered projection, changed environment (1 versus 1/3), a second reveal (1/2) and final singleton, singleton/empty/outsider/empty-index boundaries, selected-versus-global swap, and the actual Fin3 outside-subset 1/3-versus-2/3 counterexample.

`scope-and-continuation.json` preserves the exact existing original-scope, correction, finding, review and historical type/evidence paths from the held readiness package. Continue XU03-SRC-001, XU03-ELAB-001/002, the recorded BND-ELAB groups, XU03-ELAB3-01 through 16, XU03-MAIN-ELAB-001 through 006 and C02-DOC-003. Preserve the exact six API-ite and three NNReal-to-ENNReal correction records without inventing additional IDs. There is no original XU03-SP finding. This author handoff changes no finding disposition, ticket or old report. C02-TYPE-001's historical Z resolution supplies no current receiving type credit.

The two current bounded receiving preparations are retained unchanged:

- `reviews/permutation-tail-standards-receiving-preparation-20261104.md`, SHA-256 `2e48e156f69effb51aba01146b44f6a359284d509078e58a7083df955e8ac8a6`.
- `reviews/permutation-tail-spec-integration-preparation-20261104.md`, SHA-256 `cf82fe7273fbdcd88abba72b79de324f7acd082f6ef9cff9072b6b64cb0961ec`.

They remain full-scope continuations of the existing review loop. Their earlier J-unaccepted and receiver-null preparation boundaries are historical; they are not silently rewritten as approval of this new candidate.

## Historical evidence and remaining gates

The dated note accurately preserves three individual module successes inside failed development aggregates: core in focused6, boundary in focused9, and main in focused10. All 61 names subsequently appeared at positions 203–263 in the successful actual815 inspection at Z=`4b5dbfa07288acc73f25c27838d3fb2f78e77d71`, with complete independent type assessments. The exact closed results, candidates, log hashes and reviewer paths remain in the continuation record. These historical facts are not receiving-candidate validation.

Reuse the existing standalone input `provenance/shared-order-tail-acceptance-preparation-20261104/StatementsTail61.lean` (4,105 bytes /75 lines, SHA-256 `50d89e5f2118f345624a6eb51c0c6b075af0af416f454a141893b460f1ea17aa`) for root's eventual actual receiving inspection; this handoff neither copied nor executed it. The old 84-name program includes numerical-mean material outside this Tail stage.

Root's saved readiness found exact six predecessor sources and twelve `.olean`/hash records matching Z, but all six traces and all nine complete dependency paths differed. That concrete qualification gap remains; this author made no receiver output observations or automatic type transfer. Any inherited-type reuse also needs actual receiving input qualification and independent assessment.

The existing checkout's inherited J verification record does **not** verify this candidate. Root must secure the applicable full guarded candidate build and exhaustive audit, actual statement inspection/qualified inherited evidence, both final axes on this exact full scope, immediate qualified `./check.sh --verify-candidate HEAD`, and only then the exact accepted fast-forward and durable acceptance checkpoint. No installation/cache/output regeneration or fresh-mode decision is made here.

The sequence remains accepted J → accepted Tail → new complete C2, then queued Chapter3. Tail assembly does not discharge full histories, joint independence/partition, sorting or selection recursion, coupling, total costs, treap obligations or any new chapter. **All source and this completed provenance package are held after final receipt/readback.**
