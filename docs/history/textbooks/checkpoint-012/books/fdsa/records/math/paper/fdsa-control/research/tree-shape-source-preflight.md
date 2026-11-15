# Shared tree-shape mathematics: source and proof preflight

Prepared 2026-11-02. **Bounded source/proof preparation only.** XT01's shared
tree draft was reported committed at `64c6b77` and saved in checkpoint 0028;
neither that receipt nor this note establishes an accepted unit. Chapter 1
remains the sequential prerequisite. This note does not activate Chapter 4,
implement an exercise, freeze new requirements or change an existing inventory.
Its path was checked absent before writing.

## 1. Scope and source evidence

A useful next mathematical unit is small: minimum external-leaf height, the
two power bounds on external leaves, complete-tree equality and strictness,
almost-complete floor/ceiling logarithms, and the resulting height optimum.
These are shape facts on the existing `BinaryTree`, independent of labels,
ordering, search, annotations and algorithms. The complementary
`tree-shape-api-preflight.md` owns exact pinned Lean theorem signatures and
reuse decisions. No new tree carrier or logarithm implementation is indicated.

The source is the retained July 27, 2026 book PDF
`book-source/functional_data_structures_algorithms.pdf`, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Relevant passages are Chapter 4's basic observations on pp. 47–48 and
complete/almost-complete trees on pp. 51–53, Chapter 11 pp. 128–130, and
Chapter 15 pp. 183–186. PDF page numbers are printed numbers plus six.

Supporting theories use the existing Isabelle mirror pin
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. This pin postdates the manuscript;
it is inspected support, not an asserted manuscript build revision.

| Retained file | Exact source support | Previously recorded SHA-256 |
|---|---|---|
| `book-source/Tree.thy` (`src/HOL/Library/Tree.thy`) | `min_height`, `complete`, `acomplete`; `size1_height`, `min_height_size1`, both incomplete strictness results, complete equivalences and `acomplete_optimal`. | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/Tree_Real.thy` (`src/HOL/Library/Tree_Real.thy`) | Real-log bounds; `min_height_acomplete`, `height_acomplete`; one-node sibling-size difference and symmetric weight-balance constructor support. | `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` |
| `book-source/Braun_Tree.thy` (`src/HOL/Data_Structures/Braun_Tree.thy`) | `braun`, `braun_Node'`, `acomplete_if_braun`; the later Braun predicate bridge is separate from the common shape bounds. | `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1` |
| `book-source/Leftist_Heap.thy` (`src/HOL/Data_Structures/Leftist_Heap.thy`) | `mht`, `ltree`, `mht_eq_min_height`, `T_merge_min_height`, `T_merge_log`. | `894e22da05b2dbf37ce46b8401958957e5d4a729c691d6a402b0e66dd8a22450` |

Hashes above are provenance copied from the retained inventories, not a new
hash-helper run. Isabelle's recorded BSD-3-Clause notices remain applicable to
later translated code. Mathlib stays at the retained pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No retrieval or enumeration campaign
was needed. The prior `binary-tree-shared-source-preflight.md`, Chapter 4/11/15
inventories and their exact scope remain unchanged.

## 2. Exact observations and domains

Write `E` for an empty tree and `N l a r` for a payload-bearing node. This is
source notation only; the existing Lean node constructor puts `a` first. Let
`n` denote `BinaryTree.numNodes`, `L` denote `BinaryTree.numLeaves`, and `h`
denote `BinaryTree.height`. The source's `size1` is `L`, not `n` or `sizeOf`.
The existing identity `L t = n t + 1` gives **positive leaf count on every
tree**, including the empty tree.

The minimum observation is

```text
m E           = 0
m (N l a r)   = min (m l) (m r) + 1.
```

It counts edges from the root to the nearest **external empty leaf**. A
singleton therefore has `m = h = 1`, not zero. The existing ordinary fold can
express this observation with base 0 and combine `min left right + 1`; a new
folding framework is unnecessary. Its recurrence, `m <= h`, and invariance
under arbitrary label maps are the pertinent shared facts. Nonempty trees
have positive `m`; `m = 0` occurs precisely at `E`.

Source completeness is recursively

```text
C E           = True
C (N l a r)   = (h l = h r) AND C l AND C r.
```

All external leaves are at one depth. This is often called *perfect* elsewhere;
do not import a convention about left-filled levels merely because it is named
complete. Source almost completeness is

```text
AC t = (h t - m t <= 1),
```

where subtraction is natural truncated subtraction. After proving `m t <= h t`,
it is equivalent to `h t <= m t + 1`. Leaves occupy one level or two adjacent
levels, with **no left-packing constraint**. Both predicates hold on `E`.
No payload order, equality, finiteness, nonemptiness or `Inhabited` assumption
belongs in these statements. In particular, `BinaryTree Empty` still contains
`E`, and shape comparisons may quantify over different payload types and
universes.

These are structural observations even on arbitrarily corrupted annotations.
Connecting them to a stored cache is a separate validity theorem; the present
power bounds are not bounds on arbitrary raw annotation fields.

## 3. Discrete proof spine and complete-tree strictness

The following targets exactly support C04-009–013 and C04-031–037. They need
no real analysis.

| Target | Source | Bounded proof route |
|---|---|---|
| `m t <= h t` | `min_height_le_height` | Structural induction, child bounds, `min`/`max` monotonicity and successor. |
| `2^(m t) <= L t` | `min_height_size1` | At a node let `k = min (m l) (m r)`. Both child leaf counts are at least `2^k`; add them and use `2^(k+1) = 2^k + 2^k`. Empty gives `1 <= 1`. |
| `L t <= 2^(h t)` | `size1_height` | The dual proof with `k = max (h l) (h r)`: each child's leaves are at most `2^k`. |
| `C t <-> m t = h t` | Lemma 4.1; `complete_iff_height` | Under equality at a node, `min(m l,m r) = max(h l,h r)`. The chains `min m <= m l <= h l <= max h` and the right analogue force both child equalities and equal child heights. Inductively obtain both child completeness predicates. The converse follows directly. |
| `C t -> L t = 2^(h t) = 2^(m t)` | Lemma 4.2; `size1_if_complete` | Equal child heights and complete children give the doubling recurrence; then use `m = h`. |
| `not C t -> L t < 2^(h t)` | Lemma 4.3; `size1_height_if_incomplete` | If child maximum heights differ, one power is strictly smaller. If they agree, at least one child is incomplete, so one induction bound is strict. |
| `not C t -> 2^(m t) < L t` | Lemma 4.4; `min_height_size1_if_incomplete` | Use unequal child minimum heights, or equal minimum heights and one incomplete child. In the latter split, two complete children with equal minimum heights would have equal maximum heights and make the parent complete. The completeness/height equivalence is therefore genuinely used. |

Consequently equality at **either bound** characterizes completeness:

```text
C t <-> L t = 2^(h t)
C t <-> L t = 2^(m t).
```

The first is printed Corollary 4.5; the second is also justified by the pinned
`complete_if_size1_min_height` plus the complete equality. An incomplete tree
satisfies both strict bounds simultaneously. The source does not require an
extra nonempty-tree hypothesis: the incomplete case already excludes `E`.

Being some power of two is insufficient on its own. A three-node chain has
`L=4`, `m=1`, `h=3` and is incomplete; its leaf count is not `2^m` or `2^h`.
Likewise, no strictness should be transferred to rounded integer logarithms:
the two-node chain is incomplete with `L=3`, yet `Nat.log 2 3 = m = 1` and
`Nat.clog 2 3 = h = 2`.

## 4. Almost-complete logarithms and height optimum

For arbitrary trees the power bounds imply

```text
m t <= Nat.log 2 (L t)
Nat.clog 2 (L t) <= h t.
```

For almost-complete trees, C04-044–045 require the exact equalities

```text
m t = Nat.log 2 (L t)
h t = Nat.clog 2 (L t).
```

The complete/incomplete split used in `Tree_Real.thy` is a short proof route:

- If complete, `L=2^h=2^m`, so both natural logs return the same exponent.
- If incomplete, `m<h`; almost completeness then forces `h=m+1`. The sharp
  bounds give `2^m < L < 2^(m+1)`. The floor and ceiling are therefore `m`
  and `m+1`, respectively. For the floor characterization its lower premise
  can be weakened to `2^m <= L`; for the ceiling its upper premise can be
  weakened to `L <= 2^h`.

This order avoids proving rounded equalities by ad hoc real arithmetic.
The API note checks the pinned `Nat.log`/`Nat.clog` power characterizations and
`Real.natFloor_logb_natCast` / `Real.natCeil_logb_natCast` bridges. The final
source correspondence still has to state the book's real expressions, not
merely rename a discrete log:

```text
AC t -> m t = floor_nat (Real.logb 2 (L t : Real))
AC t -> h t = ceil_nat  (Real.logb 2 (L t : Real)).
```

The source spells these as `nat(floor(...))` and `nat(ceiling(...))`; positive
`L` makes the base-2 logarithm nonnegative, so the natural floor/ceiling bridges
have the correct meaning. It also gives the real bounds `m <= log_2 L <= h`,
with both inequalities strict on incomplete trees and equality on complete
trees. There is no floating-point approximation or zero-logarithm domain
exception to insert: `E` has `L=1`, `m=h=0`, and `log_2 1=0`.

### The actual optimum statement

Printed Lemma 4.6 and `Tree.acomplete_optimal` state the stronger comparison

```text
s : BinaryTree alpha, t : BinaryTree beta
AC s -> n s <= n t -> h s <= h t.
```

The source explicitly uses different label types. Equal node counts are a
corollary, not the most general premise. No BST property, shared labels,
`Nodup`, order or construction of either tree is needed.

A discrete proof can precede the logarithm results. If `s` is complete, chain
`2^(h s) = L s <= L t <= 2^(h t)` and reflect base-2 powers. Otherwise chain
`2^(m s) < L s <= L t <= 2^(h t)`, obtaining `m s < h t`, then use
`h s = m s + 1`. Alternatively, the exact `clog` height of `s`, monotonicity of
`clog`, and the arbitrary-tree upper-height lower bound give the comparison.
Choose one proof and reuse it; neither route needs a new logarithm theory.

Do not strengthen this to strict height comparison when node counts are
strictly ordered: an almost-complete two-node tree and a complete three-node
tree both have height 2. Nor does minimum height imply almost completeness.
The tree `N E a P`, where `P` is a complete three-node tree, has four nodes,
five leaves, `m=1` and `h=3`. Its height is the possible minimum
`ceil(log_2 5)=3`, but `h-m=2`. The optimum theorem is not a characterization
of all optimizers and does not establish a machine-time optimum.

## 5. Exact later client boundaries

### Braun arrays: the shared result and the still-separate bridge

C11-014–018 use the almost-complete logarithms and optimum after establishing
Braun shape. The relevant source is `Braun_Tree.acomplete_if_braun`, where the
recursive invariant allows left node count equal to right or greater by one.
The proposed common results immediately support C11-017 **after** that bridge.
They do not prove Braun indexing, array order, cache correctness or operation
costs merely from leaf counts.

The supporting constructor mathematics in `Tree_Real.thy` has a precise
bounded route if later needed. Suppose both children are almost complete and
`n l = n r + 1`. Put `k = L r >= 1`, so `L l = k+1`. Monotonicity and the
exact logarithmic heights give

```text
h (N l a r) = Nat.clog 2 (k+1) + 1
m (N l a r) = Nat.log 2 k + 1.
```

If `i = Nat.log 2 k`, then `2^i <= k < 2^(i+1)`, hence
`2^i < k+1 <= 2^(i+1)`. Thus `Nat.clog 2 (k+1)=i+1`, and the parent is almost
complete. This is the discrete counterpart of the source's floor/ceiling
argument in Lemma 11.1; it includes empty `r`, where `k=1`.

For equal child node counts, the same `L` and the two exact log formulas give
equal maximum heights and equal minimum heights; the parent retains the
children's height gap. Mirror the one-larger argument for the other side.
This supports the source's symmetric local condition that sibling node counts
differ by at most one, and then its recursive weight-balance implication.
Such pure constructor lemmas can be a later bounded client; the first shape
unit need not introduce a Braun predicate, a balancing algorithm or a weight-
balanced-tree implementation solely to demonstrate them.

Almost completeness is weaker than Braun/left-packed shape: a root with empty
left child and singleton right child is almost complete, but violates Braun's
left-biased count inequality. It does not justify contiguous Braun indices.
Conversely, merely having almost-complete children with height difference at
most one does not guarantee an almost-complete parent: a complete height-3
left child and an incomplete height-2/minimum-height-1 right child give parent
`h=4`, `m=2`. Keep size balance, height balance and almost completeness distinct.

This groundwork also does not solve Exercise 11.1's requested independent
height-bound argument without using almost completeness (C11-122). That proof
route remains a distinct exercise obligation. Array path/call-count bridges
likewise remain separate; pure height is not automatically a count that
includes the final empty-tree call.

### Leftist heaps: preserve the existing rank proofs

C15-005–006 and C15-036–039 use `2^m <= L` and its logarithmic consequence;
they do **not** need almost completeness. The pinned source proves
`T_merge l r <= m l + m r + 1` under `ltree` for both inputs, then substitutes
`m <= log_2 L` to obtain its logarithmic merge bound. Actual timing and cache
invariants remain prerequisites of that application.

Existing `Search.LeftistQueue` already distinguishes stored `rank`, actual
`shortPath` and actual `rightPath`. Preserve `rank_paths`, `rank_size` and
`rank_log` and the existing queue carrier. A checked representation/observation
bridge may connect `shortPath` to the common `m` and `size+1` to `L`; under
`Ranked`, `rank_paths` then identifies the stored field with those paths.
The existing binary `.log2` statement should be related to the common
`Nat.log 2`/real-log forms through the pinned standard bridge, not replaced
with a separate proof or a changed public cache convention.

A nonempty all-left chain can have valid rank 1 at every node, `m=1` and
maximum height equal to its node count. The shortest/right spine is logarithmic;
the maximum height need not be. A singleton with a false stored rank, meanwhile,
still satisfies the structural leaf bounds but need not satisfy any bound on
that raw rank. These cases prevent applying the new shape theorem without the
existing validity/observation law. The source's zero-charge cache/smart-node
helpers and actual merge recurrence are not changed by this mathematics unit.

## 6. Small independent expectations, without enumeration

The following hand calculations exercise the distinctions above. All labels
may be repeated or replaced by unrelated types; no traversal order is used.
`P` denotes a complete three-node tree solely to describe a fixture, not an
algorithm for constructing arbitrary complete trees.

| Shape | Nodes | External leaves | `m` | `h` | Complete? | Almost complete? | `(log_2 L, clog_2 L)` as natural logs |
|---|---:|---:|---:|---:|---|---|---|
| `E`, including payload type `Empty` | 0 | 1 | 0 | 0 | Yes | Yes | `(0,0)` |
| Singleton | 1 | 2 | 1 | 1 | Yes | Yes | `(1,1)` |
| Two-node right chain | 2 | 3 | 1 | 2 | No | Yes | `(1,2)` |
| `P` | 3 | 4 | 2 | 2 | Yes | Yes | `(2,2)` |
| Three-node chain | 3 | 4 | 1 | 3 | No | No | `(2,2)` |
| Root, singleton left, two-node chain right | 4 | 5 | 2 | 3 | No | Yes | `(2,3)` |
| `N E a P` | 4 | 5 | 1 | 3 | No | No | `(2,3)` |

The two four-node shapes show why height optimum is not an equivalence; the
three-node shapes show why a power-of-two leaf count alone is insufficient.
The two-node right chain checks both strict power bounds, both rounded
equalities and the absence of a left-packing premise. A future cross-type
example can compare the almost-complete four-node shape labelled by naturals
with the final four-node shape labelled by booleans, applying the actual generic
optimum theorem rather than first relabelling both into one payload type.

## 7. Bounded recommendation and proof limits

The proposed extension is warranted by two distinct clients: maximum-height
control for almost-complete/Braun trees and minimum-height control for leftist
spines. Keep the proof order small: minimum-height observation and its map law;
power sandwich; complete equivalence and strictness; almost-complete natural
logarithms; real-log source bridges and cross-type optimum. Existing XT01
fold/map machinery and existing Mathlib counts/heights should be reused.

The source mathematics checked here is consistent. The hazards are convention
changes or invalid strengthenings, not a newly discovered false source theorem:
confusing nodes with leaves, excluding `E`, losing cross-type quantification,
assuming left packing, making rounded strictness claims, reversing optimality,
or bounding a raw cached rank/maximum leftist height by the shortest-path result.
The explicit boundaries above should be retained in any later requirements.

No tree enumeration, balancer, maximal-complete-subtree algorithm, Braun array
operation, leftist merge implementation, complete-tree checker exercise or new
resource executor belongs in this bounded proposal. No compiler, checker,
project hash helper, enumeration, Git/ref/cache/gate or remote operation ran.
Only this new report was written; prior reports, requirements, inventories and
chapter/acceptance states remain unchanged.
