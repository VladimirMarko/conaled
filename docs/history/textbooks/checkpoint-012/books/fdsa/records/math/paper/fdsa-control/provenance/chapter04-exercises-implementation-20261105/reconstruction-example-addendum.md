# Reconstruction example contract addendum

Frozen before adding this derived application. The original algorithm and ten core public declarations in `reconstruction-frozen-contract.md` do not change. All source remains UNCOMPILED.

The independently expected inconsistent lists `[1,2,3]` and `[3,1,2]` have no common tree: root1 would require left inorder `[3]` while the left preorder prefix is `[2]`. In addition to recording the parser failure and list permutation, expose the exact application:

```
TreeReconstructionExamples.same_labels_not_joint_traversals :
  ¬ ∃ t : BinaryTree Nat, preorder t = [1,2,3] ∧ inorder t = [3,1,2]
```

The proof must use the general `reconstruct?_traversals` theorem, the independently true Nodup of `[1,2,3]`, and the already specified parser-failure example. Thus parser rejection is connected to impossibility of consistent traversals in this distinct-label case, without claiming a general completeness theorem for malformed or duplicate-label parsing. This strengthens the checked-use connection without altering a source precondition or expected result.
