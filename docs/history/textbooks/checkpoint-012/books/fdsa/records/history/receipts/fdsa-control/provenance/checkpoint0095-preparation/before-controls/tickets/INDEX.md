# Local ticket tracker

Scope owner: FDSA-000. Source version: July 27, 2026.
Chapter 1 is accepted at 07e480f. Later chapters remain queued until their
predecessor passes both independent review axes and candidate verification.
Appendix obligations are tracked alongside the chapters that use them and
receive a final completeness review.

| Ticket | Title | State | Dependencies |
| --- | --- | --- | --- |
| FDSA-000 | Complete FDSA formalization in conaled | active | all chapters and appendices |
| FDSA-ENV | Establish exact pinned development environment | historical acceptance retained; reset-host exact setup and smoke passed | none |
| FDSA-SOURCE | Pin edition and source inventory | checked | none |
| FDSA-RECOVERY | Recoverable checkpoint delivery | active | none |
| FDSA-INC01 | Chapter 1 validation disk exhaustion | recovery resolved by separate passing full fresh run; old failure retained | FDSA-001 |
| FDSA-INC03 | New-host recovery storage prerequisite | resolved by reset; source recovery and exact native setup passed | FDSA-ENV |
| FDSA-INC02 | Chapter 1 execution/session outcome unavailable | recovery resolved; attempts 1/2/3 terminal outcomes remain unknown | FDSA-001 |
| FDSA-001 | Basics | accepted at 07e480f; both reviews, full audit and immediate verification passed | FDSA-ENV, FDSA-SOURCE |
| FDSA-X002 | Shared insertion costs for Sorting and Selection | focused builds pass; full gates pending | FDSA-001 acceptance |
| FDSA-XB01 | Shared list call counts from Appendix B.1 | focused foundation build passed; full gate and final axes pending | FDSA-001 acceptance |
| FDSA-XP01 | Shared ordered and signed potential accounting | draft written; compilation and final reviews pending | FDSA-001 acceptance |
| FDSA-XR01 | Shared affine upper recurrence bound | committed draft; compilation and final reviews pending | FDSA-001 acceptance and shared integration |
| FDSA-XD01 | Shared difference-list closure observations | corrected core/examples and all72 types passed; full source/type readback complete; final integrated gates pending | accepted FDSA-001 and required shared integration |
| FDSA-XW01 | Shared bounds for accumulated random work | committed draft; compilation and final reviews pending | repaired FDSA-001 acceptance |
| FDSA-XU01 | Shared uniform-permutation minimum law | three focused targets and37 explicit types/source assessments passed; full independent/integrated gates pending | accepted FDSA-001 and required shared integration |
| FDSA-XU02 | Shared uniform relative order on a fixed subset | all three targets individually passed;53 explicit types and complete independent gates pending | repaired FDSA-001 and FDSA-XU01 acceptance |
| FDSA-XU03 | Shared conditional remaining-order laws | core individually passed; exact ee2ea240 boundary repairs integrated under focused7; types and full gates pending | repaired FDSA-001 and preceding minimum/whole-order acceptance |
| FDSA-XU04 | Shared preceding-count and ordinal-position means | committed draft; compilation and final reviews pending | repaired FDSA-001 and preceding shared-base acceptance |
| FDSA-XU05 | Shared joint relative orders on disjoint subsets | committed draft; compilation and final reviews pending | repaired FDSA-001 and preceding shared-base acceptance |
| FDSA-XU06 | Shared fixed-placement and internal-order independence | committed uncompiled draft 49d6d47; final gates pending | repaired FDSA-001 and inherited shared-base acceptance |
| FDSA-XT01 | Shared binary-tree observations and cached folds | committed draft; compilation and final reviews pending | repaired FDSA-001 acceptance |
| FDSA-XT02 | Shared binary-tree shape bounds | committed draft; compilation and final reviews pending | repaired FDSA-001 and FDSA-XT01 acceptance |
| FDSA-XT03 | Shared measured whole-tree folds | committed draft; uncompiled, final gates pending | repaired FDSA-001 and FDSA-XT01 acceptance |
| FDSA-XT04 | Shared tree suffix invocation and measured construction | committed uncompiled draft b035f11; final gates pending | repaired FDSA-001, FDSA-XT01 and FDSA-XT03 acceptance |
| FDSA-XT05 | Shared shape-sensitive traversal work | committed uncompiled draft 317aae7; final gates pending | repaired FDSA-001, FDSA-XT01, FDSA-XT03 and FDSA-XT04 acceptance |
| FDSA-XT06 | Shared root rotations and cached rebuilding | committed draft 28ba79d; uncompiled; all acceptance gates pending | repaired FDSA-001 and FDSA-XT01 acceptance |
| FDSA-XT07 | Shared ordered-tree observations | committed draft 66eae34; uncompiled; all acceptance gates pending | repaired FDSA-001, FDSA-XT01 and FDSA-XT06 acceptance |
| FDSA-XQ01 | Shared three-way partition values and source execution | focused targets and all48 shared/legacy types passed; full readback complete; final integrated gates pending | accepted FDSA-001 |
| FDSA-XA01 | Shared Set/Map contracts and refinement | committed draft 20a5b55; uncompiled; all acceptance gates pending | repaired FDSA-001 acceptance |
| FDSA-XH01 | Shared exact priority-queue observations and merge | committed draft c088bee; uncompiled; all acceptance gates pending | repaired FDSA-001 acceptance |
| FDSA-XM01 | Shared ordinary-list merge observations | focused targets and17 selected types passed;78 additional types now explicitly pending; full source assessments zero findings; integrated gates pending | repaired FDSA-001 acceptance |
| FDSA-XS01 | Shared ordered-tree search paths | committed clean draft 863aedb; full source assessment complete; uncompiled; checkpoint0056 saved | repaired FDSA-001 and applicable shared-tree acceptance |
| FDSA-XT08 | Shared ordinary leftmost extraction | clean committed draft 7b8ab2b; full source assessments; checkpoint0058 saved; uncompiled | repaired FDSA-001 and applicable shared-tree acceptance |
| FDSA-XI01 | Ordered insertion observation readiness | complete root-assessed preparation; thin implementation deferred to active C2; no new shared unit | retain C1 acceptance and exact initial C2 prefix |
| FDSA-XT09 | Shared Braun structural facts | clean committed draft156ba817; complete source assessments; checkpoint0061 saved; uncompiled | repaired C1, XT01 and XT02 acceptance |
| FDSA-XL01 | Shared logarithm bounds | clean a601ad71 draft; complete five-path author/root source assessments; checkpoint0063 saved/inspected; uncompiled | repaired C1 acceptance; later focused/full gates and both review axes |
| FDSA-002 | Sorting | active112; full81-path source scope and public docs/imports integrated at5398db7; focused6 closed failure, focused7 live; 941 types retained/793 pending; both axes Blocked | FDSA-001 |
| FDSA-003 | Selection | queued | FDSA-002 |
| FDSA-004 | Binary Trees | queued | FDSA-003 |
| FDSA-005 | Binary Search Trees | queued | FDSA-004 |
| FDSA-006 | Abstract Data Types | queued | FDSA-005 |
| FDSA-007 | 2-3 Trees | queued | FDSA-006 |
| FDSA-008 | Red-Black Trees | queued | FDSA-007 |
| FDSA-009 | AVL Trees | queued | FDSA-008 |
| FDSA-010 | Beyond Insert and Delete: Union, Intersection and Difference | queued | FDSA-009 |
| FDSA-011 | Arrays via Braun Trees | queued | FDSA-010 |
| FDSA-012 | Tries | queued | FDSA-011 |
| FDSA-013 | Region Quadtrees | queued | FDSA-012 |
| FDSA-014 | Priority Queues | queued | FDSA-013 |
| FDSA-015 | Leftist Heaps | queued | FDSA-014 |
| FDSA-016 | Priority Queues via Braun Trees | queued | FDSA-015 |
| FDSA-017 | Binomial Priority Queues | queued | FDSA-016 |
| FDSA-018 | Dynamic Programming | queued | FDSA-017 |
| FDSA-019 | Amortized Analysis | queued | FDSA-018 |
| FDSA-020 | Queues | queued | FDSA-019 |
| FDSA-021 | Splay Trees | queued | FDSA-020 |
| FDSA-022 | Skew Heaps | queued | FDSA-021 |
| FDSA-023 | Pairing Heaps | queued | FDSA-022 |
| FDSA-024 | Graph Algorithms | queued | FDSA-023 |
| FDSA-025 | Knuth-Morris-Pratt String Search | queued | FDSA-024 |
| FDSA-026 | Huffman's Algorithm | queued | FDSA-025 |
| FDSA-027 | Alpha-Beta Pruning | queued | FDSA-026 |
| FDSA-APP-A | List Library | implemented; focused build passes; full gates pending | FDSA-001 acceptance |
| FDSA-APP-B | Time Functions | B.1 draft; remaining subsections queued | cross-cutting chapter coverage |
| FDSA-APP-C | Notation | focused foundation build passed; full gate and final axes pending | cross-cutting chapter coverage |

## Checkpoint 0087 continuation — 4 November 2026

Chapter 1 remains accepted at R07e480f; the first foundation acceptance is
still pending at exact f17cc6b. No ticket is closed by this update. Bottom-up
comparison core/examples and all 105 declaration inspections passed; full
source/type readback remains. The six earlier measured modules have completed
174-declaration author source/type assessments. Shared partition focused
results and all actual failures are retained. New corrected variant/XD01
focused validation is in progress at 4ac0e7e; natural composition is held as
uncompiled draft 9c5858d0. Both XD01 source axes retain the full frozen scope
and final validation gates. All 112 Chapter 2 obligations, the XU01→XU02→XU03
acceptance order, operational/probability continuation and the complete book
goal remain. CURRENT.md and the exact provenance records control continuation.

At capture, the six-target check has closed with actual exit1 and clean unchanged
HEAD. Three-way core/examples and random-pivot core passed individually; XD01
core and random examples await bounded repairs. Both XD01 source axes are now
complete, zero mathematical source findings, overall Blocked on full gates.

## Checkpoint 0088 continuation — 4 November 2026

No acceptance or ticket closure is made by this update. Bottom-up105, shared partition48, three-way36, XD01 72 and initial random-pivot62 public declarations now have complete focused/type/source assessment evidence. All earlier failed attempts retain their actual outcomes. Natural composition is undergoing its final bounded example repair; complete105-type assessment follows its actual successful check. C02-090 generic arbitrary-sorter equality is newly confirmed outstanding, alongside the already mandatory natural operations and two probability analyses. Full public imports/map, all112 obligations, exact shared dependency acceptance order and all independent/full/immediate-verification gates remain. See CURRENT.md and checkpoint0088-preparation/capture-state.json for exact state.

## Checkpoint 0089 continuation — 4 November 2026

No acceptance or ticket closure. Natural composition now has all105 types and complete source/type assessment. All112 Chapter2 rows are reconciled; existing rank clients are identified. Generic uniqueness3b727e8 and random mean7b1851c are complete uncompiled two-file source drafts with full author/root assessment. The approved natural operational slice is aligned and released, with no Lean file yet written at hold. XU01 three focused targets pass after recorded proof repairs; its exact type-inspection state is in CURRENT.md. XU02/03 are recovered source-only with bounded local-instance corrections. Exact foundation acceptance remains first; all full audits, both axes, immediate verification and chapter order remain mandatory.

## Checkpoint 0090 continuation — 4 November 2026

No acceptance or ticket closure. Uniqueness now has individual two-target passes and all9 explicit type/source assessments, while the unrelated aggregate failure remains. Mean proof repairs through1f315fdb and whole-order support repairs throughfbc9a32 preserve every public contract. XU02 core compiled; its complete triple/types remain pending. Natural operations e1f3b5c has106 fully source-assessed claims; actual quicksort transport5a3af21 has11. Their first check joins the mean and XU02 targets at immutable centrale4965499, live at capture. Harmonic/rank plans are approved; the numerical two-file draft is deliberately untracked/uncompiled and preserved, rank source has not begun. Uniform-input plan awaits root assessment. XU03 remains source-only at6f76a4d. All112 obligations, original dependency order, full audits, both axes and immediate verification remain mandatory. CURRENT.md and exact provenance control continuation.


## Checkpoint0091 continuation — 4 November 2026

No acceptance or ticket closure. Closed attempt4 at e496 exited1, preserving
actual mean/transport individual passes and XU02/natural failures. Full/native
logs are secured. Proof successorsbdac970 andc7aa6fa retain every contract/case.
Clean centralc0440a99 now runs the recorded12-target check including first
Tail6f76a4d, numerical012ff45 and rankc19a85f compilation. Numerical23public+
1private and rank30public+7private complete source assessments have zero
findings. Uniform-input has a coherent1116-line two-file UNTRACKED draft at
204dba; written125-claim assessment/commit/root review and compilation remain.
The actual random-growth bridge and final112-row/public-import documentation
preparation remain unfinished. No prepared inspection program or partial log
is success. Exact foundation first acceptance, shared sequence, all112 Chapter2
obligations, full audits, both independent axes and immediate verification
remain. Read CURRENT.md and actual provenance; then continue the complete book.

## Checkpoint0092 continuation — 4 November 2026

No acceptance or ticket closure. ExactF still live. Closed attempt5 exit1/full native evidence secured, preserving XU02main and natural core individual passes. Source repairsfa86/b87/e0df/a111 and complete U9d/G08a1 are combined at f673ee87195e4aaeef4b41767a7468c70ad6214f. All125uniform/31growth source claims and bounded repairs are root-assessed; actual compiler/types/full gates remain. Complete112-row mapping is root-read; public docs/imports remain. Independent nonauthor C2 Standards/Spec preparations have begun, with fullR scope and Blocked outcomes. See CURRENT.md for exact records, resource/command isolation and the required foundation-first sequence.

## Checkpoint0094 continuation — 2026-11-04T08:39:55.037607+00:00

Focused6 at immutableM2 actually closed exit1; the complete48390-byte log SHA
4d18122cfbe8698979673c10b4bdf76b0fb7442d48f75882b95d89c6bae1aa95 and native evidence
are secured. Tail core and numerical mean pair passed individually; natural
examples5, Tail boundary9, rank core4 and Uniform core24 errors remain preserved.
After closure, exact reviewed successors47f66d/ee2ea240/6f3e010/aa89ae were
integrated, with complete public docs/map and23 SquareApplications imports, at
5398db774ed5ca9938d0562e379d757323e7a355. Recorded focused7 session27917 is live;
no compiler/type/acceptance success is inferred from source assessments.

The fixed complete review scope remains R through this81-path successor, with
all112 obligations and ten shared scopes. Both independent nonauthor axes assess
all original scope plus every corrective delta, with zero new concrete source
findings and overall Blocked. Both independently read all941 retained actual
public types against exact current source bytes. Their reports/receipts retain
all prior findings, failed commands and qualified evidence profiles.

C02-TYPE-001 remains OPEN pending actual remaining output and complete readback.
Final inventory:1762 public names =941 matching prior evidence +793 pending
(468 original,145 foundation,78 additional XM01,98 earlier sorting,4 constructors)
+28 byte-preserved accepted-R names. Nineteen anonymous instances and70 private
names remain source/audit obligations. Both exactF145 and current5398db7 793-name
programs are PREPARED ONLY. Source inventory is not compiler evidence.

C02-DOC-001: the original proposal redundantly targeted ProofAudit directly.
The applied correction imports examples only in SquareApplications, which
ProofAudit already imports. No checker/policy or audit-root change. Both axes
assessed the correct reachability. C02-DOC-002: complete actual failed6/correction
lineage and every required shared acceptance dependency are explicitly recorded.
The original draft/proposal is retained;112 mathematical rows are unchanged.

Only C1 remains accepted. ExactF full check71528 remains live and must finish its
terminal/type/full-review/immediate-verification gates before the accepted FF.
Required shared scopes and XU01→XU02→XU03 acceptance dependencies remain; complete
C2 acceptance precedes C3. No scope or validation gate is waived by this update.
