# Frozen Chapter 4 prefix-balancing value and cost contract

Frozen before the four assigned source paths are created. This is one source
assignment in the original Chapter 4 loop, whose full base is
298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2 and whose 76 obligations remain mandatory.
The author start is 90469ce4ba3fc49397d369a5db7d58aec7014f58 on
work/fdsa-ch04-balancing. XT01 is still awaiting its full acceptance; these
source drafts cannot accept it or Chapter 4.

## Primary meaning and phase boundaries

The July 27, 2026 book, Chapter 4 printed pages 54–56, and the complete frozen
chapter inventory (SHA-256 e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4)
supply C04-047–053, the concrete part of C04-058 and C04-061. The height,
minimum-height, almost-completeness and strict-order results remain mandatory
later phases after their shared prerequisites; no omission or acceptance is
implied by this implementation partition.

The original algorithm consumes its left prefix first, reads the next element
as the new root, and passes that returned suffix's tail to the right recursion.
The implementation will not split the input with take/drop. Arithmetic is on
the requested size; both recursive sizes strictly decrease at a positive call.
Arbitrary label types, including Empty, remain supported.

## Phase 1: ordinary values

Allowed files: Applications/Trees/Balance.lean and Examples/TreeBalance.lean.
Namespace Trees.Balance; the existing Mathlib BinaryTree and Trees.inorder
remain the carrier and independent ordered observation.

`bal (n : Nat) (xs : List α) : Option (BinaryTree α × List α)` has the equations:

- bal 0 xs = some (nil, xs).
- At n = k+1 let m = (k+1)/2. Evaluate bal m xs. None propagates failure.
  A successful empty suffix also returns none. For some(l,a::ys), evaluate
  bal (k-m) ys; none propagates failure, while some(r,zs) returns
  some(node a l r,zs). Here k-m = n-1-m, the book's right size.

The explicit failure policy is none exactly when xs.length < n. It introduces
no label default, equality decision or ordering assumption. Total source-facing
wrappers use nil only when the safe core fails:

- balList n xs extracts the returned tree, using nil for none.
- balanceList xs = balList xs.length xs.
- balTree n t = balList n (inorder t).
- balanceTree t = balTree t.numNodes t.

Public recurrence names will be bal_zero and bal_succ. Core correctness will
expose bal_spec (every success gives xs = inorder t ++ zs and t.numNodes=n),
bal_exists (n≤xs.length gives a successful result), bal_succeeds_iff and
bal_eq_none_iff (the exact domain), plus bal_inorder, bal_suffix and
bal_suffix_length. The success-only bal_spec is stronger than the book's
premised implication: successful execution itself supplies the domain.

The wrapper interface will include balList_of_some, balList_of_none,
inorder_balList, inorder_balanceList, inorder_balTree, inorder_balanceTree,
numNodes_balList, numNodes_balanceList, numNodes_balTree and
numNodes_balanceTree. Prefix wrappers retain their source length premise;
full-list/full-tree laws require no extra premise. A universal prefix consumer
will demonstrate the exact untouched suffix without equating trees merely
because they have the same inorder.

### Independent expected cases chosen before source development

1. Zero size returns nil and the identical arbitrary suffix; an oversized
   request returns none. For arbitrary lists over Empty, success is exactly
   the zero-size request.
2. Consuming 3 from [9,3,7,8,8] yields root3, singleton children9 and7, and suffix
   [8,8]. Its independent inorder is [9,3,7], with three nodes. The example is
   deliberately not sorted.
3. Consuming all of [1,1] yields root1 with singleton left child1 and empty right
   child. Inorder retains both occurrences; no distinctness or BST property is
   assumed.
4. The already visually verified Figure4.3 on [0,1,2,3,4,5,6,7,8,9] has root5,
   children2/8;2 has1/4;8 has7/9;1,4,7 have left children0,3,6. All omitted
   children are nil. Independent counts:10nodes,11external leaves,height4.
   The actual full structure and the generic inorder/size laws will be connected.
5. Rebalancing an arbitrary tree preserves the entire inorder sequence and
   exact node count; no structural identity or equal-shape premise is asserted.

## Phase 2: actual measured execution

Allowed files: Applications/Resources/TreeBalance.lean and
Examples/TreeBalanceCost.lean. Namespace Resources.TreeBalance.

`balRun (n : Nat) (xs : List α) :
  Resources.Measured (Option (BinaryTree α × List α)) Nat`
will execute the same recursive calls, Option branches, suffix reads and node
construction as bal. It uses Resources.bind to retain actual left/right
observations and Resources.CallCount.tick for one call-entry charge at every
invocation, including zero. Variables, arithmetic, list head/tail pattern
matching and tree construction are uncharged primitives in this declared
source model. No synthetic cost is assigned to the value-only bal result.

Public balRun_value will refine the value for all inputs. Public balRun_cost
will state (balRun n xs).2 = 2*n+1 under n≤xs.length. A combined exact theorem
and successful-result forms may package these already independent results.
The counted algorithm's failure branches are real and need not cost 2*n+1.

Independent cost expectations: zero costs1, the valid three-node prefix costs7,
the valid ten-node input costs21, and requesting1 from [] returns none with
cost2 (one zero left call and the parent call). The last case explicitly
prevents dropping the successful-input premise. Generic examples will consume
both the public value refinement and exact count, not merely reduce arithmetic.

This cost model does not prove Lean wall-clock, allocation, integer-bit cost,
or a linear bound for balanceTree's preceding direct inorder traversal.

## Method and validation boundary

Use the inherited implementation/EDD/statement-review workflow. Every expected
case above is an independent obligation; source reduction may establish the
concrete shape but public correctness results must supply the stated semantic
connections. No proof admissions, axioms, unsafe/partial operations or native
shortcuts are permitted. Keep autoImplicit false and warningAsError true.

The root agent exclusively runs Lean/Lake/check/audit and owns acceptance.
This author performs source reading and local Git checks only, records complete
source and statement assessments, commits only its allowed paths, and reports
all drafts as UNCOMPILED. Later compilation may require proof corrections; it
cannot justify weakening any frozen mathematical conclusion.
