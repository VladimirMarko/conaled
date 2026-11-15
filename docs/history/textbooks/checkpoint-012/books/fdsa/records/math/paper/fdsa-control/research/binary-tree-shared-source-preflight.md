# Shared binary-tree traversal and augmentation: source preflight

Prepared 2026-11-02. **Bounded read-only preparation, not a scope freeze,
implementation, independent final review or chapter acceptance.** Chapter 1
remains the sequential prerequisite. No existing inventory, requirements,
repository source, Git ref, compiler output, cache, gate or tracker is changed.
The sole new artifact is this report; its path was checked absent before use.

## 1. Recommendation and evidence boundary

A small shared unit on Mathlib's existing node-labelled `BinaryTree` is
justified. Its source-backed core is an ordinary structural fold with explicit
empty value and ternary node operation, traversal/map/erasure laws, and the
reader/smart-constructor/all-node-validity laws for cached folds. Size and
height give two independent structural specializations; interval maximum and
leftist minimum height give concrete later clients with additional conditions.
No new tree carrier, container hierarchy, monoid requirement or global
inhabited-payload assumption is warranted.

The complementary `binary-tree-shared-api-preflight.md` owns the exact pinned
Lean API assessment. This report checks source meaning and useful connected
cases. It does not authorize implementing Chapter 4 exercises, AVL algorithms,
interval search, Braun conversion or leftist merge. An actual measured full
fold is optional for the first unit: its value/cost contract is clear below,
but source usefulness does not require expanding the unit to every traversal
and algorithm now.

### Retained primary evidence

The book is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026, retained at
`book-source/functional_data_structures_algorithms.pdf`; SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The relevant Chapter 4 passages are printed pp. 47–49 and 56–58. Later client
locations and their retained obligation IDs appear below. Page numbers are
printed numbers, six less than the PDF page number. Extracts in
`book-source/chapter04.txt` and the other chapter files are reading aids; the
PDF and pinned theories determine the statements.

The Isabelle mirror revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It postdates the manuscript; it is
reproducible supporting evidence, not an asserted manuscript build revision.

| Pinned reading copy | Exact declarations used |
|---|---|
| `book-source/Tree.thy`, upstream `src/HOL/Library/Tree.thy` | `tree`, `size1`, `height_tree`, `min_height`, `preorder`, `inorder`, `inorder2`, map/count/height laws and `inorder2_inorder`. |
| `book-source/Tree2.thy`, upstream `src/HOL/Data_Structures/Tree2.thy` | The same carrier with pair labels; erased `inorder`, `set_tree`, `bst`, `set_inorder`, `length_inorder`. This file does not itself define a generic cache invariant or generic smart constructor. |
| `book-source/Interval_Tree.thy` | `max_hi`, `max3`, `inv_max_hi`, `node`, `max_hi_is_max`, `max_hi_exists`, `search`, `search_correct`. |
| `book-source/AVL_Set_Code.thy` and `AVL_Set.thy` | `ht`, `node`, `balL`, `balR`, erased-inorder laws, `avl` and `ht_height`. |
| `book-source/Leftist_Heap.thy` | `mht`, `ltree`, `node`, `mht_eq_min_height`, `ltree_node`, actual `merge`, the two zero-cost auxiliary timing declarations, and `T_merge_min_height`. |
| `book-source/Time_Functions.thy` | `T_append`: append costs first-list length plus one in its recursive-entry model. |

Exact theory hashes are already retained in `chapter04-obligations.md`,
`chapter05-obligations.md`, `chapter09-obligations.md`,
`chapter15-obligations.md` and `appendix-b-obligations.md`; no source download,
version replacement or new source campaign occurred. The Isabelle files have
the pinned BSD-3-Clause provenance recorded there. Preserve applicable notices
if adapting their code. The full manuscript remains a research input, not a
new deliverable.

The architectural instructions, glossary, ADRs 0001/0010 and
`fdsa-control/DECISIONS.md` were read. The source observations below retain the
separation of operations, semantic laws and resource observations they require.
Mathlib's carrier, `map`, `numNodes`, `numLeaves`, `height` and
`numLeaves_eq_numNodes_succ` were also read at
`conaled-permutation-joint/.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean`,
the retained Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The independent fixtures in `binary-tree-shared-case-preflight.md` were read
after the source analysis; they agree with the conventions and cost separation
below and are suitable connected examples for a future frozen unit.

## 2. Carrier and observation conventions that must survive reuse

Write `E` for the empty tree and `N l a r` for a node carrying payload `a`.
These are explanatory source notations, not a proposed replacement Lean type.
The corresponding Mathlib constructors are `.nil` and `.node a l r`; the
argument order changes. In particular:

| Observation | Empty | Node |
|---|---|---|
| Number of payload-bearing nodes `n` | `0` | `n l + n r + 1` |
| Number of external leaves `ell` | `1` | `ell l + ell r` |
| Height `h` | `0` | `max (h l) (h r) + 1` |
| Minimum height `mh` | `0` | `min (mh l) (mh r) + 1` |
| Inorder `I` | `[]` | `I l ++ (a :: I r)` as a value specification |

Thus `ell t = n t + 1`. Empty leaves contain no payload. `BinaryTree Empty`
still has its empty tree; no default payload is necessary. `sizeOf` is not
the book's number of nodes. Maximum height, minimum height, cached rank and
right-spine length must not acquire a single ambiguous `size`/`rank` meaning.

The book writes ordinary inorder with two appends, `I l ++ [a] ++ I r`;
`Tree2.inorder` writes an append to a cons. They have the value specification
in the table, but this does not identify their measured executions. The source
preorder places the root first; postorder occurs in `Tree.thy` but is explicitly
omitted from the printed Chapter 4 discussion. Its existence in a companion
file does not automatically enlarge a bounded shared unit.

Existing `Bracketing.Tree` and `RandomAccess.Tree` have payloads at leaves and
different constructors. Their flattening and accumulator results offer proof
patterns, not a definitionally matching node-labelled carrier. A conversion
must explain what happens to empty trees, labels and counts; no such conversion
is needed merely to use Mathlib's matching carrier.

## 3. The smallest common value laws

For explicit `z : beta` and `f : beta -> alpha -> beta -> beta`, let

```text
F E           = z
F (N l a r)   = f (F l) a (F r).
```

This is the book's pp. 57–58 operation after forgetting any annotations.
It needs no associativity, commutativity, order, decidable equality or monoid.
The empty value is a parameter, not an `Inhabited alpha` requirement. In
particular, height is a structural fold and is not determined by the inorder
word: a three-node chain and the balanced three-node tree can have identical
inorder `[1,2,3]` but heights 3 and 2.

Useful common laws are:

1. Ordinary label map preserves node/leaf counts and both height observations;
   `I (map g t) = List.map g (I t)` for arbitrary, possibly noninjective `g`.
2. Fold fusion uses the actual algebra premises. If `q z = z'` and
   `q (f x a y) = f' (q x) a (q y)`, then `q (F t) = F' t`. Product projection
   is an immediate useful specialization, without a new algebra class.
3. For an annotated tree `t : BinaryTree (alpha × beta)`, `erase = map fst`
   preserves shape, and `I (erase t) = List.map fst (I t)`. This is the exact
   relationship between Chapter 4's two proposed erased-inorder definitions.
   The analogous set and length facts preserve occurrences before taking sets.
4. The source accumulator obeys `I2 E suffix = suffix` and
   `I2 (N l a r) suffix = I2 l (a :: I2 r suffix)`, with the all-suffix law
   `I2 t suffix = I t ++ suffix`. This remains Exercise 4.1's actual recurrence,
   not an instruction to implement that exercise in the present preparation.

For the cache layer on this existing pair-labelled carrier, define the intended
mathematical contracts as follows:

```text
read E                      = z
read (N l (a,b) r)          = b
smart l a r                 = N l (a, f (read l) a (read r)) r
Valid E                     = True
Valid (N l (a,b) r)         =
  b = f (read l) a (read r) AND Valid l AND Valid r.
```

The reusable facts are `Valid l -> Valid r -> Valid (smart l a r)` and
`Valid t -> read t = F (erase t)`, together with the unconditional erasure law
`erase (smart l a r) = N (erase l) a (erase r)`. On this definition the smart
constructor's validity is equivalent to validity of both children; it repairs
the new root field, not arbitrary descendants.

Changing labels or rotating a tree does not automatically preserve `Valid`.
An erased-inorder equality preserves ordered contents, whereas a structural
height cache must be recomputed after a rotation. A label map can invalidate a
maximum cache even while preserving shape. Any cache transport needs the actual
fold-algebra/representation compatibility premise.

`Sequences.OrderedSummary.Valid` is a useful existing whole-representation
contract: it combines a supplied representation invariant with a root cache
equal to a monoidal summary of a decoded list. It neither supplies recursive
tree-cache validity automatically nor makes a branch-sensitive fold into a
monoidal word summary. Its `cache` recomputes that summary; the value theorem
does not make this operation an incremental constant-time smart constructor.
Once a tree's ordered observation is established, its existing
`summary_append`, `summarySquare` and composition results remain appropriate
clients. No competing summary framework is needed.

## 4. Concrete later clients and exact remaining bridges

### Interval maxima: Chapter 5, pp. 71–75

Rows C05-066–085 use the same pair-labelled tree. The pinned source uses
endpoint `linorder` plus `order_bot`, with `max_hi E = bot` and a root cache
otherwise. Its node algebra is
`f x interval y = max (high interval) (max x y)`.
The generic all-node cache law supplies the structural part of
`inv_max_hi` and smart-node preservation, independently of BST order.

The actual search still needs two further maximum facts: every stored endpoint
is bounded by the cache, and on a nonempty subtree some endpoint attains it.
The second is essential to its one-branch pruning. An inflated upper bound is
insufficient: use left interval `[0,0]` with cache 100, root `[1,1]` with cache
100, right interval `[2,2]` with cache 2, and query `[2,2]`. Interval BST order
and all upper-bound inequalities hold, but the source search commits left and
misses the right-hand match. Exact cache validity excludes this tree. This
already retained source boundary should not be weakened by a shared adapter.

The local bottom requirement is specific to this interval realization. It is
not a reason to impose `OrderBot` on every tree payload. Exercise 4.11's
maximum of an arbitrary linearly ordered payload instead needs an optional
empty observation: a raw root cache of type `alpha` and a reader of type
`Option alpha`. It is not silently the same carrier as a tree storing
`Option alpha` at each node. Keep a later explicit adapter or specialization;
do not enlarge the first cache interface merely to hide this difference.

### AVL height caches: Chapter 9, pp. 105–107, 112 and 116

`AVL_Set_Code.ht` is exactly the root reader for `z = 0`;
its `node` uses `f x _ y = max x y + 1`. The `AVL_Set.avl` predicate additionally
requires a height difference of at most one at every node. Generic cache
validity is therefore a component of AVL validity, not a proof of balance.
The source theorem `ht_height` is the intended observation bridge.

The repeated nested `node` calls in `balL`/`balR` provide a concrete client for
local cache reconstruction. Their erased-inorder laws must stay separate from
height/balance preservation. For future Exercise 9.5, a prefix-consuming
balanced construction may build caches simultaneously or use a separate linear
annotation pass; either way, its actual work includes the chosen passes
(C09-062–066). Exercise 9.6's `debal2` must make one recursive traversal and no
structural-height calls; product fold summaries or smart reconstruction over
already reconstructed children are useful shared ingredients (C09-095–100).
Equality to the repeated-height reference conversion does not transfer cost.
These exercises remain queued.

### Leftist cached minimum height: Chapter 15, pp. 183–186

The source `mht` is a root cache read. On `ltree`, `mht_eq_min_height` identifies
it with the structural fold `mh`, whose algebra is `min x y + 1`. The source
smart constructor compares cached children and may swap them; it stores the
smaller cached height plus one. The leftist inequality is a further shape
condition, not a property of all valid minimum-height caches.

Existing `Search.LeftistQueue.PQ` already retains the actual cached-rank
constructor, `rank`, `shortPath`, `rightPath`, `fork`, `Ranked`, `rank_paths`,
`rank_size` and `rank_log`. Preserve that carrier and its existing queue proofs.
A future representation bridge to `BinaryTree ((value × priority) × Nat)` can
connect observations without replacing the implementation. `fork_entries`
deliberately proves a permutation of root/left/right entries because `fork`
can swap children. For example, a zero-rank left child and rank-one right
singleton are swapped: ordinary inorder changes from `[a,b]` to `[b,a]`.
Multiset/permutation content is the right unconditional contract. A generic
fixed-child smart-node inorder equation cannot be applied across this swap.

### Relevant boundaries inside Chapters 4–17

Braun arrays in Chapter 11 (pp. 128–134, C11-008–025) use the same carrier but
the observation is `L (N l a r) = a :: interleave (L l) (L r)`. It is not
inorder; in general it is not ordinary breadth-first order either. Node count,
shape-map facts and erased annotations can be shared, while actual array
indexing and interleaving need their own laws and costs. Its outer cached length
is distinct from a cache at every node. A single visit to every tree node does
not make a recursively interleaving list observation linear.

Chapter 17's binomial tree is the nonempty rose tree `T rank payload children`,
and an empty queue is an empty forest. Its cached rank and child-list traversal
are not this binary-tree fold. The retained binomial inventory also distinguishes
Batteries' binary child/sibling encoding and its rank scan from a constant-time
source rank field. No generic BinaryTree foundation may bypass those adapters.
The analogous multiway-tree/trie carriers likewise do not become identical
because their diagrams contain nodes.

## 5. Resource observations: exact proposed recurrences and limits

All formulas here are about explicitly named abstract measured executions.
They do not assert the cost of Lean's compiled constructors, `++`, arbitrary
precision arithmetic, allocation, sharing, retained memory or a runtime.
The existing `Resources.Measured`, `bind` and `CallCount.tick` suffice; no new
resource carrier is indicated.

### Recursive fold versus local cached construction

Suppose a measured fold charges one entry at **every** empty/node call and
actually invokes a measured combine callback once at every node, on the two
returned child summaries and the current payload. Its value must be proved
to be `F`; its cost recurrence is

```text
W E         = 1
W (N l a r) = W l + W r + C_f (F l) a (F r) + 1.
```

It follows that the exact cost is `2*n(t)+1` plus the occurrence-sum of callback
costs at the nodes. If every callback reached in this execution costs at most
`K`, then `W t <= (K+2)*n(t)+1`. A uniform bound on all callback inputs is a
convenient sufficient premise, not a hidden fact about arbitrary `f`. Empty
input costs one and invokes no callback. A fixed pair `(size,height)` algebra
is a concrete useful specialization; its two projections should invoke the
public fold laws, rather than be separate arithmetic demonstrations.

For an **explicitly separate local-access tariff**, charge one for each of two
root-cache reads and one for the smart-constructor entry, with projections,
pair formation and primitive arithmetic otherwise inlined. Actually sequencing
those two measured reads and the callback gives
`W_smart l a r = C_f (read l) a (read r) + 3`, hence at most `K+3` under the
stated callback bound, independently of subtree size. Its value is the actual
`smart l a r`; validity is needed for semantic cache correctness, not for this
local cost equation. Additional charged helpers change the constant explicitly.

This positive local tariff is **not** the source leftist selective timing:
`Leftist_Heap.thy` explicitly introduces `time_fun mht` and `time_fun node` as
two zero-cost auxiliaries and proves `T_mht_0`. Its merge theorem charges the
recursive merge execution and bounds it by `mh l + mh r + 1` on valid inputs.
Treating a cache projection as one unit can be useful, but it needs a separately
named cost model and a proved comparison if used to transfer that theorem.

There is an existing nonconstant callback that makes this distinction concrete:
use `Resources.ListReversal.appendRun leftSummary (a :: rightSummary)` as the
actual measured inorder combine. Its value is `leftSummary ++ (a :: rightSummary)`
and its callback cost is `leftSummary.length + 1`. Two charged reads and one
entry therefore give local work `leftSummary.length + 4`, not a universal
constant. This uses the existing append execution and its exact value/count
theorem; no synthetic expensive callback or whole-fold executor is necessary.

The book's constant-overhead smart-constructor statement on p. 57 is directly
appropriate for the displayed size operation under its local unit-cost
conventions. For arbitrary `f` on p. 58, retain the callback work; the generic
value invariant alone does not establish a constant-time operation.

### Inorder: append shape and empty calls affect exact counts

`Resources.ListReversal.appendRun_exact` already observes both append's value
and `xs.length+1` recursive-entry cost. `TreeFlattening.appendWithCost` instead
counts copied cells, giving zero on an empty first list. The latter's tree
carrier is also different. Neither can be substituted without both bridges.

For an explicitly parenthesized node-labelled execution with a **single**
measured append, `I l ++ (a :: I r)`, one entry per tree call and inlined cons,
write `A E = 0` and `A (N l a r) = A l + A r + n l`. Then

```text
W E         = 1
W (N l a r) = W l + W r + (n l + 1) + 1
W t         = 3*n(t) + 1 + A t.
```

This recurrence matches the value shape written in `Tree2.inorder`, but an
operational correspondence is still required before assigning it to source
evaluation. The source's unparenthesized two-append `Tree.inorder` expression
must not acquire this exact cost merely by associativity or singleton-append
simplification. To illustrate the distinction, **if** both appends are retained
in `I l ++ ([a] ++ I r)`, the same explicitly chosen tariff gives
`5*n+1+A`; if instead the retained expression is `(I l ++ [a]) ++ I r`, it gives
`5*n+1+2*A`. These are three specified recurrences, not three claims about the
one pinned compiler. The imported Isabelle list-notation declaration and any
evaluation rewrite are not recovered by the `Tree.thy` reading copy itself;
no exact literal two-append timing is asserted here. A future source-timing
adapter should resolve this small concrete syntax/evaluation point first.

For the source accumulator recurrence from §3, charge only its tree entries and
inline cons: the exact count is `2*n+1`, independent of suffix length. In strict
evaluation it computes the right result before passing it into the left call;
the output is still left/root/right followed by the original suffix. Neither
cost nor value requires a sorted tree or distinct labels.

Under the single-append tariff, three-node trees give a useful check: a balanced
tree costs 11, a right chain 10, and a left chain 13; the accumulator costs 7
on each. On a left chain `A=n*(n-1)/2`; on a right chain `A=0`. Thus the printed
Exercise 4.1 quadratic statement is a worst-case statement, already qualified
in C04-018. A one-pass claim also needs to count any list-combining callback:
visiting each tree node once does not imply constant work per node.

## 6. Small independent boundary cases worth retaining later

These are source-level expected cases for a possible future checked unit, not
new frozen requirements or executed Lean tests.

| Case | Mathematical expectation and purpose |
|---|---|
| Empty tree, including payload type `Empty` | Inorder `[]`, nodes 0, leaves 1, height 0, fold `z`; accumulator returns the arbitrary suffix. A charged recursive entry still costs 1. No default payload. |
| Root 1 with two singleton children both labelled 2 | Inorder `[2,1,2]`, preorder `[1,2,2]`, nodes 3, leaves 4, height 2. Annotate it arbitrarily and erase: repetitions and order survive. With suffix `[9]`, accumulator value is `[2,1,2,9]`. |
| Pair summary `(nodes,height)` | Zero `(0,0)`; node combines `(nl+nr+1,max hl hr+1)`. The projections recover two different existing observations through generic fusion. The balanced/chain case separates height from inorder alone. |
| Correct whole-root size but corrupt descendant | Let `bad = N E (a,7) E` and `t = N bad (b,2) E`. Root read 2 equals true whole-tree size 2, but the child's true size is 1 and recursive validity fails. Root-value equality is insufficient. |
| Locally consistent smart root over that child | `smart_size bad b E` stores 8. Its root equation holds, but true size remains 2 and the descendant is invalid. Smart construction requires valid children; it is not an arbitrary repair traversal. |
| Both root checks hold, descendants still fail | The independent four-node fixture has stored sizes 4 at the root, 2 at its singleton left child, 1 at its two-node right child and 1 at that child's leaf. The root's true size is 4 and its local equation is `4 = 2+1+1`, yet two descendants are invalid. See `binary-tree-shared-case-preflight.md` for the exact asymmetric tree. |
| Source leftist child swap | Valid empty left child and singleton right child force a swap. Rank/min-height and permutation content are preserved by the appropriate laws; original inorder is not. |
| Cache read versus recursive recomputation | On an actually valid large tree, both return the same fold value. The named positive local reader costs 1; the recursive fold still visits `2*n+1` tree occurrences and pays callback costs. Semantic equality alone cannot equate them. |

The interval-search inflated-cache counterexample in §4 is an additional
consequential later client, not a request to implement search now. Arbitrarily
large or repeated labels do not affect the structural laws, while the actual
cost of operations on those labels remains part of the chosen callback tariff.

## 7. Bounded implementation recommendation and remaining work

If the coordinator later freezes a shared unit, prefer these small steps:

1. Extend/reuse Mathlib's carrier and existing count/height/map operations;
   supply only missing structural fold and traversal/erasure compatibility
   facts. Keep source `N` argument order out of the public carrier.
2. Add the explicit-parameter cached-fold reader, smart constructor and
   recursive validity law. Connect size, height and a product projection case
   to those generic theorems, including the malformed-descendant boundaries.
3. Reuse existing measured execution if a cost component is chosen. Name its
   tariff and connect actual callback calls/read operations to the value laws;
   retain the source's zero-helper leftist timing separately. Full measured
   traversal and Exercise 4.1's accumulator need not enter the first unit.

The later bridges remain actual obligations: interval maximum attainment and
search pruning, AVL balance/rotation/cache updates and one-pass conversion,
the source-to-existing-leftist representation with permutation observations,
Braun interleaving/indexing costs, and binomial carrier/rank correspondence.
No equality of final values discharges any of those execution contracts.
This preflight neither changes their scope nor treats those chapters as active
or accepted. No compiler, proof audit, implementation check or source-validation
claim is made.
