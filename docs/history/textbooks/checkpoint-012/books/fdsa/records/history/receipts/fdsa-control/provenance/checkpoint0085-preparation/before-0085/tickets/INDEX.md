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
| FDSA-XD01 | Shared difference-list closure observations | committed draft; compilation and final reviews pending | repaired FDSA-001 acceptance |
| FDSA-XW01 | Shared bounds for accumulated random work | committed draft; compilation and final reviews pending | repaired FDSA-001 acceptance |
| FDSA-XU01 | Shared uniform-permutation minimum law | committed draft; compilation and final reviews pending | repaired FDSA-001 acceptance |
| FDSA-XU02 | Shared uniform relative order on a fixed subset | committed draft; compilation and final reviews pending | repaired FDSA-001 and FDSA-XU01 acceptance |
| FDSA-XU03 | Shared conditional remaining-order laws | committed draft; compilation and final reviews pending | repaired FDSA-001 and preceding minimum/whole-order acceptance |
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
| FDSA-XQ01 | Shared three-way partition values and source execution | committed draft de54102; uncompiled; all acceptance gates pending | repaired FDSA-001 acceptance |
| FDSA-XA01 | Shared Set/Map contracts and refinement | committed draft 20a5b55; uncompiled; all acceptance gates pending | repaired FDSA-001 acceptance |
| FDSA-XH01 | Shared exact priority-queue observations and merge | committed draft c088bee; uncompiled; all acceptance gates pending | repaired FDSA-001 acceptance |
| FDSA-XM01 | Shared ordinary-list merge observations | focused targets/types passed at 72a0951; both full source assessments have zero findings; integrated gates pending | repaired FDSA-001 acceptance |
| FDSA-XS01 | Shared ordered-tree search paths | committed clean draft 863aedb; full source assessment complete; uncompiled; checkpoint0056 saved | repaired FDSA-001 and applicable shared-tree acceptance |
| FDSA-XT08 | Shared ordinary leftmost extraction | clean committed draft 7b8ab2b; full source assessments; checkpoint0058 saved; uncompiled | repaired FDSA-001 and applicable shared-tree acceptance |
| FDSA-XI01 | Ordered insertion observation readiness | complete root-assessed preparation; thin implementation deferred to active C2; no new shared unit | retain C1 acceptance and exact initial C2 prefix |
| FDSA-XT09 | Shared Braun structural facts | clean committed draft156ba817; complete source assessments; checkpoint0061 saved; uncompiled | repaired C1, XT01 and XT02 acceptance |
| FDSA-XL01 | Shared logarithm bounds | clean a601ad71 draft; complete five-path author/root source assessments; checkpoint0063 saved/inspected; uncompiled | repaired C1 acceptance; later focused/full gates and both review axes |
| FDSA-002 | Sorting | active; foundation full gate running; insertion/top-down, quicksort and natural-run values focused-checked; cost and remaining value work in progress | FDSA-001 |
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
