# XR01 receiving source handoff — 4 November 2026

## Frozen candidate and original scope

The source candidate is **`4df3bc95b96342250c9b3ff946773449e308e11b`**, tree **`74c359e65645a8fdd6dcb7ac1549f380fa6e4b12`**, on `work/fdsa-affine-integration` in `conaled-ch02-natural-runs`. Its sole parent is accepted Chapter 2 **`2da5708478a1d943a9214b5b386ec2db16cd9eca`**. The worktree is clean. This is source preparation for receiving validation, not acceptance.

The original unit is **`d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2`**, parent `c28ba71863d2a35ee1c3a089caa90464e4cca692`, tree `7b27a47b60253b398d5f75ce4308915302f7858d`. Its complete five-path scope and all frozen requirements/cases remain applicable. The receiving delta is exactly those same five paths: 521 insertions and two deletions. Neither the old potential-accounting prefix nor any other later shared draft was merged.

| Path | Bytes | Lines | Receiving Git blob | SHA-256 |
| --- | ---: | ---: | --- | --- |
| `Applications/Resources/AffineRecurrence.lean` | 5839 | 113 | `afba9e03f3d8178c6fcd469e064f07ddff53c32b` | `0f867ba6fa96cbeaaaeeba6c4a24cc71b38fdbf798b684d484234eabb283d17d` |
| `Examples/AffineRecurrence.lean` | 5165 | 142 | `e16bc2401027fdced90b86edd15d9eb8b79759b9` | `eb9239f5810887ba988420c3fe8538eab21285c1e6173eb5467133baa63868d5` |
| `SquareApplications.lean` | 9405 | 287 | `d3ce332d0f9978a752650a6b6275867476928942` | `75563d66c31e9cc1456cedf639812e6025486f69cf8ab50f3961d038a6219d18` |
| `docs/research/fdsa-affine-recurrence.md` | 10290 | 236 | `762109da0f1d8be2605d691f5bf50b51db57e084` | `8996a9212bd8cf05ec26519cf51ca9ce69f560170512df647fa3fdb9869032f6` |
| `docs/research/fdsa-reconstruction-map.md` | 46693 | 710 | `772e92b364c1077e141a160adf7213d0a2ceef02` | `fdf63be72114a8002cd4c3786007c8ff0e722c0465f819b00dd93ba2ffe3185e` |

Both defining Lean files are byte-identical to the original XR source. Every Q path outside the five declared paths is unchanged. The full receiving five-file scope is 1,488 lines. That count is source text, not new theorem or audited-kernel counts.

## Actual integration and resolutions

`baseline.json` records clean natural-runs HEAD `47f66dccc414d41bddf0dc6576a2338227ee221e`, its retained old branch, absence of the new branch, the 69 then-existing references and the accepted Q tree. Branch creation exited zero. The ordinary `git cherry-pick --no-commit d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2` exited one with exactly one conflict, `SquareApplications.lean`. All three conflict-stage blobs are preserved in this package. The reconstruction map auto-merged.

The root conflict's incoming side also contained old-parent `Examples.MappedPotentialAccounting`. Resolution kept Q's complete import order and added only `Examples.AffineRecurrence` after `Examples.PotentialAccounting`. Removing that single new line reproduces Q's root byte-for-byte. No potential-accounting source or import was included.

The new XR map section retains the original mathematical text. Its preparation status and the public note's three status passages are explicitly dated to the 4 November receiving-preparation snapshot: both original independent source assessments complete, no new XR source findings, and no XR compiler/type/full-check/audit result at that snapshot. Live validation and acceptance are referred to the local control evidence. This historical wording will not require a source change merely because a later check completes.

The map also carries the exact previously reviewed **XP01-DOC-001** correction from `cfa413e247c084245a270ae7bcc91fd9ea24b002`: “For Chapter 1” scopes the existing-interface sentence. All previous mathematical explanation and citations remain. Removing the XR section and reversing that exact qualifier produces Q's map byte-for-byte. `note-vs-original.diff` isolates the three public-note status changes.

Staging and `git diff --cached --check` exited zero; that check is only a text/whitespace check. The final local Conventional Commit uses command-local `ChatGPT <chatgpt@openai.com>` and issue `#174`, with the original cherry-pick source identity in its message. It is an ordinary cherry-pick successor, not a claim that d64 is a Git ancestor of the new commit. The original draft and old references remain available.

`candidate.json` records the actual concurrent movement of the separately assigned `work/fdsa-ch03-values` branch from Q to `a5341e132c63aa8c9e8af13e24b441b42de2fe27`; it does not falsely claim all 69 observations stayed fixed. A separate comparison against the accepted Chapter 2 fast-forward receipt confirms that all **67 checkpoint0122 references**, including accepted `work/fdsa-book`, are unchanged. Only this author's new affine branch was mutated by these commands. Root later selected the qualified worktree independently.

## Retained mathematical and example obligations

The public theorem retains the exact `CommRing`, `LinearOrder`, `IsStrictOrderedRing` and `Archimedean` assumptions; total scalar `f`, natural child maps, eventual strict contraction and upper recurrence; and one fixed nonnegative pair of witnesses covering every natural input, including zero and the complete finite prefix. No field, nonnegative-function, monotonicity, cancellation addition or execution-cost assumption was added. Child decrease remains proved inside the strong induction argument.

The terminating quarter recurrence retains values 1, 1, 5, 7, 19, 31 at inputs 0, 1, 2, 4, 8, 16 and its application to the generic theorem over rational casts. The signed integer recurrence, negative-value/negative-toll case, one-sided-versus-absolute-value example, parameterwise application, and both no-uniform-family witnesses remain exact. There are **21 authored public names = 19 theorems + two definitions**, with zero authored private declarations, anonymous examples or instances; generated helpers remain subject to the full audit.

XR does not discharge Chapter 3's exact ceiling/negative-offset bridges, prescribed thresholds and sharper constants (including potentially negative intercepts), actual selector-to-cost correspondence, grouping or noncontracting counterexample. Chapter 3 retains all 83 recorded IDs (80 original plus C03-081–083); this handoff changes none of that scope.

## Existing and receiving type inputs

The original `provenance/affine-recurrence-public-statements21-prepared-20261104/Statements.lean` remains unchanged: 1,474 bytes, SHA `13d96149ecb926ead0a9b892f72331fceeef6e85d674bf5f0d6d0682e03e7d60`. Its historical inventory embeds an earlier Spec report identity; this is left intact as history. `baseline.json` binds the later completed Spec report actually read for this receiving task.

The separate **`Statements21.lean`** here binds `4df3bc95b96342250c9b3ff946773449e308e11b` and preserves both imports, all 21 explicit-`@` commands in original order, and `pp.universes`, `pp.explicit`, `pp.fullNames`. It adds supported pinned options `pp.deepTerms true`, `pp.proofs true`, `pp.maxSteps 1000000`. The full receiving name/header/source/configuration inventory is `statements21-inventory.json`.

Pinned Lean's `PrettyPrinter/Delaborator/Options.lean` and `Basic.lean` define these controls; exact hashes and read ranges are in `printer-option-source.json`. The installed Lean source subtree has no `pp.maxDepth` occurrence. Depth omission is disabled by `pp.deepTerms`; proof omission is disabled by `pp.proofs`; `pp.maxSteps` is a visited-expression limit, not a depth setting and not unlimited when zero. The higher limit does not automatically establish output completeness: root and the independent axes must inspect actual blocks for omissions and diagnostics.

The two required focused targets are `Applications.Resources.AffineRecurrence` and `Examples.AffineRecurrence`. Their local source closure is those two files, with six direct Mathlib imports recorded in the inventory. This is a source binding only. No receiving compiler object, runtime, actual printed type or pre/post execution qualification is claimed by this package. Root retains exclusive serial native execution, one thread, exact pins and the existing capture/recording workflow.

## Continuation records and actual evidence boundary

Continue the original `reviews/affine-recurrence-round1.md`, `reviews/affine-recurrence-requirements.md`, `reviews/affine-recurrence-candidate.md`, `tickets/FDSA-XR01.md` and `research/affine-recurrence-preflight.md`; preserve full scope and the inherited documentation finding. The complete original source reports are:

- `reviews/affine-recurrence-standards-preparation-20261104.md`, SHA `bff3e140f1178b6f77ac2d12a42e544dbf2d7522bc27bcf793d1e7ef55b24e92`.
- `reviews/affine-recurrence-spec-preparation-20261104.md`, SHA `8ee3cac08c1cb0d4b4d8b29821b5de9b54e549530d081155130065c3bb8e8b32`.

Those source assessments do not supply receiving acceptance or actual type credit. Both original axes must assess the receiving source/documentary resolution and actual terminal evidence under the complete original scope. Full guarded candidate check, exhaustive permitted-axiom audit, independent passing final reviews and immediate qualified candidate verification before an exact accepted fast-forward remain mandatory; no gate or native profile was changed here.

After this source candidate froze, root separately ran focused attempt1. Its complete 3,800-byte log, SHA `6d0b02515abb300fef8abf747e3845ee091ce3ec6281506c093c3c1aa16b0a53`, is `provenance/affine-recurrence-receiving-focused-attempt1-20261104/full.log`. It reports the core built in 5.9 seconds and Examples failed at 108:27 with `expected no space before`; aggregate exit one. That actual failure is preserved and does not change this source snapshot. Root has authorized a separate minimal syntax successor and separately rebound 21 input. This package gives no whole-unit pass or type credit.

## Author readback and hold

The complete five receiving source files, all current integration/documentary hunks and original requirements/cases were read; the two defining files were compared byte-for-byte with d64. The root/map preservation equalities, all five path identities, source headers/order, and original-program identity were mechanically checked. Relevant current activation/acceptance and XR control rows were read; no claim is made to a fresh complete reread of the entire global historical tracker. Pinned pretty-printer source was read only at the recorded API/consumer ranges; no new mathematical assessment or compiler probe was performed.

All source at `4df3bc95b96342250c9b3ff946773449e308e11b` and this completed preparation package are held unchanged. Any actual parser repair is a distinct commit and provenance package. No Lean/Lake, installation, hydration, runtime, compiler-output, global-control, ticket, review or accepted-ref mutation was performed by this author.
