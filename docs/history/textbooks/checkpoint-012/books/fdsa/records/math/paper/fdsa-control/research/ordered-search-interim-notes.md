# Ordered-search preparation: interim continuity notes

Recorded by root during the second C1 session recovery. These are incomplete
preflight findings, not frozen requirements, implementation, validation or
chapter acceptance. The three assigned full source/API/case reports are still
being completed; no new worktree or Lean source has been released.

## Primary source and existing interface observations

The source author found the common LT-left, EQ-hit, GT-right query in Tree_Set,
Tree_Map, Isin2 and Lookup2, with direct use in binary red-black/AVL and join
representations. Source Cmp performs `<` then `=`. Its membership result is
Boolean; map lookup returns an option, with Some false distinct from absence.
The inspected query theories have no time_fun/T_isin/T_lookup theorem. An
invocation counter would be a declared Chapter 1-style reconstruction with
comparator/projection work uncharged, not recovered generated timing evidence.

The proposed raw result is an optional stored entry. Membership can observe
isSome; map lookup can map the payload projection. No concrete definition or
carrier choice is frozen. If V counts visited nodes/three-way comparisons and
E counts invocations including an empty terminal call, the direct recurrence
calculations give E = V on hits and E = V + 1 on misses. The merge unit's
uniform +1 relation is false for a root search hit. V and literal primitive
comparison work are distinct: source LT uses one test, EQ/GT two. Source p.59
worst-height tightness retains a deepest-present-key witness on a nonempty
strict BST; it must not disappear behind only an upper/logarithmic claim.

Chapter 7's Node3 performs a second three-way comparison only after GT at its
first key. It needs its own reconstruction and is not a direct single-node
BinaryTree specialization. All updates, balancing and logarithmic invariants
remain later chapter obligations.

The API author found the pinned existing BinaryTree.indexOf and BinaryTree.get
in Mathlib.Data.Tree.Get. Root read that complete file: indexOf chooses a path
using cmpUsing, while get follows PosNum.one/bit0/bit1. The file supplies these
operations but no correctness/order/cost theorem. Homogeneous search followed
by get, or first mapping labels to keys, can provide useful value semantics;
the extra traversals do not become one-pass resource equalities.

Root also read the complete retained Applications/Trees/Ordered.lean at
66eae34815a177c6b4bf5120e05202ebb8876c91. It supplies recursive bounds, pairwise
inorder equivalence under transitivity, keyed strict order under a preorder,
mapped-key nodup and exact map/rotation transports. It defines no lookup.
All inherited shared tree units remain uncompiled and unaccepted.

The API author identified the existing Ordering.Compares predicate and its
Order.Compare laws as a possible minimum local comparison contract. A raw
label-to-Ordering route can avoid payload order, equality and inhabitance;
a key specialization may use input-local Compares assumptions over a preorder,
with Mathlib cmp available for linear keys. This remains proposed, not proved.
Mathlib cmp tests `<` then reverse `<`; its Ordering value correspondence with
source Cmp needs the stated order laws and gives no primitive-tariff equality.
A bare preorder can make cmpUsing falsely report EQ for incomparable keys.
No new comparison-law record or general search/state-machine framework is
presumed necessary.

## Outstanding preparation

Wait for the complete stopped source/API/case reports, read all of them and
reconcile concrete disagreements. Decide whether the primary E observation
alone with derived V suffices or whether the existing product observation is
justified; do not fix a representation merely from a numerical example.
Record exact assumptions, full source obligations and independent expectations
before any implementation scope is frozen. All three report writers own only
their respective preflight files; this interim note is root's continuity aid.
