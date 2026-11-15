# Phase 2 preparation at durability hold

Status: design notes only, not a frozen implementation contract and not source/compile/acceptance evidence. No Enumeration or Reconstruction module/example exists yet. Mandatory C04-019/020 and C04-027/028 remain open in the enclosing Chapter 4 scope.

## Executable enumeration design

The root-position suggestion is not required for correctness. A simpler equivalent enumeration inserts the next first inorder label at every position down the existing tree's left spine. Intended computational definitions (not yet written in Lean):

- `insertFirst x nil = [node x nil nil]`.
- `insertFirst x (node a l r) = node x nil (node a l r) :: map (fun l' => node a l' r) (insertFirst x l)`.
- `enumTree [] = [nil]`.
- `enumTree (x :: xs) = (enumTree xs).flatMap (insertFirst x)`.

Both algorithms terminate structurally, on the tree and list respectively. No label equality/default assumptions, quotient extraction, noncomputable toList, or runtime claim are needed.

Public mandatory endpoints remain `Trees.enumTree xs`, membership iff `Trees.inorder t = xs`, and `List.Nodup (Trees.enumTree xs)` for ALL lists, including repeated labels. Support lemmas should prove insertion soundness, completeness, and duplicate-free output. A computable `removeFirst` deletes the leftmost node: nil stays nil; node a nil r becomes r; node a l r with nonempty l becomes node a (removeFirst l) r. Every insertion output is nonempty and removes uniquely to its input. Therefore insertion lists from distinct predecessor trees are disjoint even when every label is equal. Within one insertion list, the head has an empty left child whereas each mapped alternative has a nonempty left child; constructor injectivity plus recursive Nodup handles the tail. FlatMap Nodup then follows from those two facts. This avoids any label-distinctness restriction.

Completeness can be proved by structural induction on an arbitrary t with inorder t = x::xs, decomposing t into an insertFirst output over a tree with inorder xs. In a nonempty-left-child case, split that child's inorder into head/tail; it cannot be empty because node inorder contains its root label. In the empty-left-child case, t is the head insertion into its right subtree. The recursive enumerator's exact membership then follows by induction on xs.

Pinned API reads, source inspection only: List.mem_flatMap, List.Nodup.map, List.Nodup.append, List.disjoint_left, List.nodup_cons, List.pairwise_flatMap, and the standard map/constructor observations. No compiler has checked this plan.

Independent expected cases before any Phase 2 source:

- `enumTree ([] : List Empty) = [nil]`.
- `enumTree [a] = [node a nil nil]`.
- `enumTree [a,b]` must return, in that order, `[node a nil (node b nil nil), node b (node a nil nil) nil]`.
- For `[a,a]`, those two distinct shapes remain distinct and both appear exactly once, although their inorder labels coincide. The general Nodup theorem must be consumed on this input; no decidable label equality should be introduced.
- For `[a,b,c]`, the proposed order is: root a with right chain b/c; root b with leaf a and leaf c; root a with right subtree root c/left leaf b; root c with left subtree root a/right leaf b; root c with left chain b/a. All five have inorder `[a,b,c]`.
- Positive membership examples must consume the general iff, and at least one wrong-inorder tree must be excluded using it.

## Reconstruction requirements and unresolved design

The total public entrypoint remains `Trees.reconstruct` on preorder and inorder lists with `[DecidableEq α]`, and no `Inhabited α`. Intended theorem: `List.Nodup (Trees.preorder t) -> reconstruct (Trees.preorder t) (Trees.inorder t) = t`. Exact malformed-input behavior must be frozen before code: a checked Option core with nil fallback is a viable design, but has not yet been selected or implemented. Proofs must justify the root position using distinctness and split preorder by the left inorder length, with a terminating recursion. No runtime claim.

Independent source counterexample must survive: `node a (node a nil nil) nil` versus `node a nil (node a nil nil)` are different trees with identical preorder and inorder `[a,a]`. A theorem must expose this ambiguity; neither repeated labels nor malformed input may be silently treated as satisfying the reconstruction hypothesis. The inherited Basic module already has traversal membership/length/map bridges and repeated-label examples, but it must not be edited by this author. Request any missing shared helper from the coordinator.

## Required continuation

Freeze precise Phase 2 public contracts and algorithm behavior; implement both complete module/example pairs; prove enumeration soundness, completeness, termination and Nodup on repeated labels, and reconstruction under exactly the source distinctness hypothesis; commit each pair and provide immutable source/public-statement identities. Root alone performs compiler qualification, full candidate/audit checks, independent axes and immediate verification. None of this work is replaced by the present design notes.
