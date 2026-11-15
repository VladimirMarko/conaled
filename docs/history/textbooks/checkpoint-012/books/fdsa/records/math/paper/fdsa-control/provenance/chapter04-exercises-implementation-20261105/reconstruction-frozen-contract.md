# Reconstruction frozen contract — Phase 2B

Frozen before either Reconstruction source file exists. UNCOMPILED intended interface, not acceptance. Source parent is `b6affb296a8782284b2ebcaff2d7bd894337c578`. This continues the original whole-Chapter4 implementation/review loop (base `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, all76obligations). Prior commits, frozen records and holds are not edited.

Source basis: C04-027/028; primary July27 2026 book PDF page56 (printed50), reread a5a763. Inventory SHA-256 `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`; primary PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. No manuscript copy enters the repository or deliverable.

## Representation and total behavior

Use existing `BinaryTree α`, `Trees.preorder` and `Trees.inorder`, with `{α : Type u}`. Equality testing in the executable parser requires `[DecidableEq α]`; no `Inhabited α` or order assumption is introduced.

`Trees.reconstruct? : List α → List α → Option (BinaryTree α)` has these exact branches:

- Empty preorder and empty inorder return `some nil`.
- Empty preorder and nonempty inorder return `none`.
- For preorder `a::pre`, if `a` is absent from inorder `ino`, return `none`.
- Otherwise let `k = ino.idxOf a`, the first occurrence. Parse left with `pre.take k` and `ino.take k`; parse right with `pre.drop k` and `ino.drop (k+1)`. If both return `some`, build their node with label a; otherwise return `none`.

Termination is measured by preorder length. Both recursive preorder slices are at most the tail length, strictly less than the parent preorder length, regardless of malformed inputs. The public `reconstruct pre ino` returns the Option result with `.nil` as explicit fallback. Empty trees exist without a label default.

This defines behavior on every pair of lists. It rejects the stated empty/missing-root/failing-child cases; it is not specified as a search for some successful duplicate-label interpretation. For duplicate labels it commits to the first inorder root occurrence, and the source correctness theorem is asserted only under the exact distinct-preorder hypothesis. No general successful-parse soundness theorem or runtime bound is claimed unless separately proved.

## Frozen public declarations

All names are in `Trees`; each declaration below using the parser carries `[DecidableEq α]` explicitly.

```
def reconstruct? [DecidableEq α] : List α → List α → Option (BinaryTree α)

reconstruct?_nil_nil [DecidableEq α] :
  reconstruct? ([] : List α) [] = some .nil
reconstruct?_nil_cons [DecidableEq α] (a : α) (ino : List α) :
  reconstruct? [] (a :: ino) = none
reconstruct?_cons [DecidableEq α] (a : α) (pre ino : List α) :
  reconstruct? (a :: pre) ino =
    if a ∈ ino then
      match reconstruct? (pre.take (ino.idxOf a)) (ino.take (ino.idxOf a)),
        reconstruct? (pre.drop (ino.idxOf a)) (ino.drop (ino.idxOf a + 1)) with
      | some l, some r => some (.node a l r)
      | _, _ => none
    else none
reconstruct?_cons_of_not_mem [DecidableEq α] (a : α) (pre ino : List α)
  (ha : a ∉ ino) : reconstruct? (a :: pre) ino = none

def reconstruct [DecidableEq α] (pre ino : List α) : BinaryTree α :=
  (reconstruct? pre ino).getD .nil

reconstruct_nil_nil [DecidableEq α] : reconstruct ([] : List α) [] = .nil
reconstruct_of_none [DecidableEq α] {pre ino : List α}
  (h : reconstruct? pre ino = none) : reconstruct pre ino = .nil
reconstruct?_traversals [DecidableEq α] (t : BinaryTree α)
  (hn : (preorder t).Nodup) : reconstruct? (preorder t) (inorder t) = some t
reconstruct_traversals [DecidableEq α] (t : BinaryTree α)
  (hn : (preorder t).Nodup) : reconstruct (preorder t) (inorder t) = t
```

The proof must derive absence of the root from the left inorder by the existing independent preorder/inorder membership bridges, using Nodup preorder. This justifies `idxOf` equalling left inorder length. Existing traversal-length laws justify slicing preorder at that same index. Recursive hypotheses come from Nodup of each preorder subtree. It must not assume correct splits or reconstruction as extra hypotheses.

## Independent expected cases, before source

- A sample tree has root9, left child3 with right leaf5, and right child7 with left leaf6. Independently calculated preorder is `[9,3,5,7,6]`; inorder is `[3,5,9,6,7]`. Its preorder is distinct. Both Option and public reconstruction examples must consume the corresponding general reconstruction laws after proving these observations/hypothesis.
- Generic singleton a reconstructs from `[a]`,`[a]` through the public general law, requiring only decidable equality.
- Empty lists over `Empty` reconstruct to the empty tree, showing no default label is needed.
- `reconstruct? [] [1] = none`, hence the public fallback is nil.
- Missing-root case: `reconstruct? [9] [3] = none`.
- Surplus preorder: `reconstruct? [1,2] [1] = none` because a recursive child parse lacks its root.
- Surplus inorder: `reconstruct? [1] [1,2] = none` because a recursive child has empty preorder and nonempty inorder.
- Same labels in inconsistent order: `[1,2,3]` and `[3,1,2]` are permutations, but `reconstruct? [1,2,3] [3,1,2] = none` because their recursive left inputs are `[2]` and `[3]`. This demonstrates that multiset equality alone does not satisfy the valid-traversal contract.
- For an arbitrary label a, define `leftRepeated a = node a (node a nil nil) nil` and `rightRepeated a = node a nil (node a nil nil)`. Both exact preorder and inorder lists are `[a,a]`; the trees differ by their left child; their preorder is not Nodup. Those counterexample facts require no typeclass assumptions.
- With decidable equality, the specified first-occurrence parser chooses `rightRepeated a` on `[a,a]`,`[a,a]`. Thus it does not recover `leftRepeated a` from that tree's traversals. This is outside, and does not weaken, the required distinct-preorder theorem.

Closed malformed/duplicate computations use the public parser equations and failure/fallback laws; sample and singleton correctness use the all-tree public theorem. No runtime test or compiler result will be invented. Complete authored names/headers and immutable source identities accompany the commit. Root alone performs Lean/Lake/check/audit/type extraction and independent review/immediate verification. No new implementation/review loop is started.
