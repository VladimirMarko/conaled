# Phase 1 structural observations: implementation handoff

Candidate: `5b17c8e4a962a8e79251eda1b5f94f97a3d4cc34`, on `work/fdsa-ch04-structural`, with parent `90469ce4ba3fc49397d369a5db7d58aec7014f58`. The original whole Chapter 4 base remains `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`; this is one author contribution within its existing loop, not a new acceptance scope.

## Scope and implementation statement assessment

The source delta is exactly the two assigned new files. `phase1-public-statements.json` lists every authored public definition, theorem, inductive type and constructor with source header and exact file/blob identity. No generated kernel declarations are excluded from the eventual exhaustive audit. Actual elaborated types have not been inspected by this author.

- `setTree`, `setTree_nil` and `setTree_node` give an independent structural `Set α` observation. The nil/node equations exactly match the source recurrence and use no decidable equality. Labels have arbitrary universe/type and the tree carrier remains Mathlib's `BinaryTree`.
- `preorder`, its two equations, and `preorder_length` preserve root-left-right order and repeated labels; length counts labelled nodes, not external leaves or implementation `sizeOf`. The map theorem quantifies over arbitrary functions from arbitrary source to target label types, with no injectivity premise.
- `mem_inorder_iff_mem_setTree` and `mem_preorder_iff_mem_setTree` quantify over every label and finite tree. Their two directions connect independently defined observations; neither assumes the desired equality or an ordering invariant. The source proofs use structural induction.
- `Subtree` and its three constructors mean reflexive rooted-descendant containment. The first argument is the contained tree. The left/right constructors retain the entire child subtree, ruling out pruning and replacement by a tree with an equal set.
- `nil_subtree` has no premise and includes the nil tree itself. `subtree_nil_iff` exposes its unique contained tree; `subtree_node_iff` includes exactly the root and the two descendant cases. `Subtree.trans` composes two meaningful containment premises; reflexive and concrete descendant examples witness satisfiable uses.
- `subtrees` is the set of structural descendants. `mem_subtrees_iff`, both exact nil/node set equations, self membership and nil membership establish the book's set formulation. Empty external leaves are included, with no label inhabitedness assumption.

These source statements match the assigned mathematics. No circular or unsatisfiable premise was introduced. All inference/elaboration details still require root's actual-type and compiler evidence; this assessment is implementation support, not independent Standards or Spec approval.

## Worked expectations and connected uses

The `sample` definition is the source's root 9 with children 3 and 7. Its independent visit calculation is preorder `[9,3,7]`, inorder `[3,9,7]`, set `{3,9,7}`, and three labelled nodes. The corresponding named declarations prove these through the public nil/node equations. `sample_preorder_length` consumes `preorder_length` and the independently calculated node count.

`sample_contains_seven` transfers membership from the explicit preorder through `mem_preorder_iff_mem_setTree`; `sample_excludes_eight` uses the other bridge and explicit inorder. `sample_constant_map` consumes `preorder_map` for the explicitly typed constant Nat map, yielding `[5,5,5]` and exposing an inappropriate injectivity restriction.

`sample_left_subtree`, `sample_has_empty_subtree` and `sample_has_self_subtree` exercise descendant construction and both boundary membership laws. `nested_left_subtree` explicitly composes containment with `Subtree.trans` under an extra enclosing root 20.

`leftRepeated` and `rightRepeated` are two nodes labelled 5, with the second node on opposite sides. `repeated_traversals` retains both expected lists `[5,5]`; `repeated_sets` retains the singleton `{5}`. `repeated_trees_distinct` compares their left children, and `leftRepeated_not_subtree_rightRepeated` consumes the structural decomposition law. `same_set_not_subtree` connects the equal-set observation with failed structural containment. The independently expected distinction was fixed before source writing.

`empty_label_observations` specializes the nil equations at `BinaryTree Empty`. The tree exists despite the uninhabited label type. No additional label instances are introduced to make this boundary case possible.

## Governing inputs and preparation evidence

The agent read AGENTS (8e29e0), implement (0e2075), EDD (ce8890), worked example (0ecde1), architecture (e40c57), domain (6de36e), review procedure (850aa2), glossary/ADR index (bb2282), actual ADR0001/0010 (7063ef), and README development/build/proof sections (f698f2). Nix remains explicitly waived by the user; exact pins and proof restrictions remain binding. The existing whole-task loop owns reviews and root owns all compilation.

Primary source text PDF pages 53–55 was read completely in 970b9c; pinned Mathlib BinaryTree source was read completely in d4a24f. Current ordinary observations were read completely in 165a06. The chapter inventory had already been completely read in the immutable preflight; a later combined 1–150 display a3ae40 was aggregate-truncated and is not claimed as a new complete read. The exploratory ADR lookup initially used nonmatching filenames, skipped them without changes, then read the actual filenames in 7063ef. The missing source-name search bf21c9 exited 1 with no matches, a normal read-only result.

The contract was frozen before source writes at actual4176b2. Both source files were displayed completely at cb0864 (139 lines) and 2c2bab (107 lines). Before-stage source identities are saved. Actual9db505 confirms only the assigned paths were staged, a clean whitespace check, absence of forbidden proof tokens, and unchanged protected source/control identities. These are source hygiene and scope checks, not Lean validation. Commit8562d2 exited 0 under per-command ChatGPT/chatgpt@openai.com identity.

## Pending validation and ownership

**Uncompiled draft.** No Lean, Lake, build, check, audit, candidate verification, dependency/output mutation or upload was performed. The entrypoint and all accepted source files remain unchanged. Root must route these new modules into its captured candidate and inspect actual public types, compile, run the applicable full candidate check/audit, continue independent whole-task review and verify immediately before any eventual acceptance. Neither XT01 nor any Chapter 4 obligation receives acceptance credit from this handoff.

Phase 2 may now proceed in the two separately assigned weighted-path files because the Phase 1 source commit is complete. These Phase 1 source bytes are retained in this commit for future correction/review history.
