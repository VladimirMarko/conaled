# Balanced interval augmentation: unqualified preparation

C05-085 under CTB-24 remains open. This paper curates 18 November 2026 preparation
by `/root/balanced_interval_preparation` and the subsequent root annotation
paper. It preserves their mathematical design and counterexamples without
claiming a completed interval instance or new checked cases. Current requirements and receiving status are tracked in [CTB](../textbooks/CTB.json): CTB-78 integration acceptance precedes resumed book formalization. This paper is not a Lean dependency or a receiving validation receipt.

The initial note predated cached AVL implementation. Its former statement that
those modules were absent is historical and no longer describes the donor.
The [local-rebalance](fdsa-height-rebalance.md), [update](fdsa-height-updates.md),
[Set-refinement](fdsa-height-set-refinement.md) and [height-bound](fdsa-height-bound.md)
owners now supply complete-annotation, fixed-tolerance balancing foundations.
The interval-specific instance, overlap-operation bridge and measured operation
costs still need to be supplied. The actual sweep-cost preparation has one owner
in [the sweep note](fdsa-rectangle-sweep.md#unqualified-preparation-for-the-measured-sweep).

The canonical [Chapter 5 requirement](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md)
requires a named cross-chapter balancing dependency. AVL is a permissible
concrete choice for the open-ended exercise; a conditional theorem alone does
not discharge that instance. It must include cache-aware local rotations and
updates, ordered-set semantics, balance and overlap correctness.

## Relevant existing contracts

The original author read these modules and their relevant derivations at donor
`cb53530ae9c020395d85f37f2e59a168bdee55c9`. This is an attributed interface
inventory, not current receiving validation. Later cached-height owners are
identified in the next section.

| Current owner | Usable contract and limit |
|---|---|
| `Applications/Trees/Cached.lean` | Root-only `read`, local `smartNode`, recursive `Valid`, and `read_eq_fold`; shape/inorder erasure and full annotation laws. `smartNode_valid_iff` requires both children already valid. It supplies an appropriate shared foundation for two caches. |
| `Applications/Trees/CompletenessCache.lean` | A worked product-summary cache `(Bool,Nat)` with proved height and completeness observations. It is not dynamic AVL balancing. |
| `Applications/Search/IntervalTree/Basic.lean` | Complete key κ is independent of endpoint α. The raw tree is `BinaryTree (κ × α)`; `maxHi` reads the root, `node` uses the generic smart constructor, and `CacheValid` requires exact maxima recursively. |
| `IntervalTree/Maximum.lean` | `highTree` preserves raw annotations while projecting keys to highs; `cacheValid_iff_invarMx` transports the actual cache law. `maxHi_spec` gives both an attained high and its upper-bound property without a BST hypothesis. |
| `IntervalTree/Insert.lean`, `Leftmost.lean`, `Delete.lean` | Actual unbalanced insertion, optional/nonempty split-min, successor join and deletion. Erasure transports their exact programs; cache preservation is independent of strict search order. Equality insertion retains the old annotated node. These are not balanced updates. |
| `IntervalTree/Refinement.lean`, `Contract.lean` | Exact strict-list insertion/deletion observations and an `AbstractSet.Refinement`; this derives all seven `DeleteLaws`. `Valid` separates maximum-cache validity from strict complete-key inorder. `intervalSetLaws` adds overlap correctness using low compatibility. |
| `IntervalTree/Search.lean` | Actual one-branch search, unconditional soundness and completeness under exact cache validity plus weak nondecreasing projected lows. `search_correct_of_strict` needs a proved key-order-to-low-order implication. It does not need injective interval projection. There is no measured interval-search wrapper in the inspected resource modules. |
| `Applications/Trees/Balance.lean`, `Resources/TreeBalance.lean` | Sequential prefix reconstruction with exact inorder/size/suffix laws. The actual `balRun` costs `2*n+1` recursive calls on a sufficient size-n input, before charging the preceding inorder traversal. Rebuilding the whole active tree after every update would therefore not supply logarithmic updates. |
| `Applications/Search/RedBlack/Basic.lean` | The VFA-facing colored carrier, four-case insertion balancer, raw `ins`, root blackening and `insert`. This module has no deletion. It does not itself provide the augmented dynamic interval-set instance. No claim is made here about every capability of its underlying Batteries provider or all other red-black modules. |
| `Applications/Resources/SourceMergeSort.lean` | Actual measured splitting, recursive sorting and merging; value equals the source sorter. Each of split visits and merge head comparisons is bounded by `length * Nat.clog 2 length`; `work_le_clog` bounds their sum by twice that and `work_isBigO` supplies real-log growth. Its declared observation excludes comparator implementation work, function-entry overhead and length-test costs. |
| `RectangleSweep/Events.lean`, `Scan.lean` | Actual generation binds `rs.zipIdx` once, maps insertion/deletion payloads and appends them; `eventAt` indexed lookup is specification-only. `length_events=2*rs.length`. `sweep` binds one sorted schedule and scans it. A true insertion query returns immediately, before insertion; deletion does not query. The scan and generator still lack the measured wrappers required for 090. |

## Current named cross-chapter dependency

Use the existing `BinaryTree`/`Trees.Cached` carrier and
`Trees.HeightBalance.HeightAnnotation`, its full recursive cache and shape
invariants, `balL`/`balR`, actual recursive updates and ordered-set refinement.
The ordinary AVL family specializes tolerance one; the sharper AVL Fibonacci
height theorem remains available separately from the generic logarithmic bound.
C09-039–041/060 measured operation obligations remain open; a logarithmic
height theorem does not itself bound an actual update's measured cost.

Keep the source's operational distinctions. Cached AVL deletion uses the **left
subtree maximum**, whereas current unbalanced interval deletion uses the right
subtree minimum. They can have the same abstract list/set result while producing
different trees. Do not try to prove an incorrect exact-tree equality between
them. Insertion grows height by zero or one; deletion/predecessor extraction
shrinks height by zero or one. The simultaneous height-and-invariant contracts
are needed by induction. Deletion balances on the opposite side from the
modified child. Heavy-child equality belongs to the source's single-rotation
branch and is exercised by deletion.

## Reusable augmentation design and proof boundaries

A natural shared carrier is `BinaryTree (κ × (Nat × α))`, where κ remains the
complete semantic key and the annotation contains height and maximum high.
Keep key, endpoint and state universes independent as in the accepted modules.
With the existing bottom-based endpoint convention, the empty summary is
`(0, bot)` and the local combination of summaries `(hL,mL)` and `(hR,mR)` is
`(max hL hR + 1, max (iv key).high (max mL mR))`.

This is a specialization of `Trees.Cached`; it is not a reason to introduce a
second generic cached-tree carrier. Its proposed proof-only projections are:

- height projection: `(key,(h,m))` maps to `(key,h)`;
- maximum projection: `(key,(h,m))` maps to `(key,m)`;
- semantic erasure: retain only key and shape.

Prove that the product cache invariant implies, and if useful is equivalent to,
the two projected cache invariants. Prove projections preserve shape, inorder,
height and size. A local smart-constructor compatibility theorem should derive
both projection laws from the generic cache equations. The generic height projection is now supplied by `HeightBalance.HeightAnnotation`
and `ht_eq_height_of_cacheValid`; the interval-specific projection/operation
correspondences described here still need to be established.

Implement every chosen AVL balancing rewrite using that local smart constructor
at **every reconstructed node**, bottom-up. A single rotation rebuilds the
demoted node before the new root; a double rotation rebuilds both children before
the root. Prove height projection commutes with the actual cached AVL balancer
and updates. This reuses the existing Chapter 9 generic invariance and height theorems
without copying their entire proofs. Separately prove maximum-cache preservation
from valid child summaries and exact local reconstruction. Recursive maximum
validity and structural balance remain independent obligations; neither can be
replaced by a predicate only about the final root.

For semantic correctness, use exact inorder preservation of rotations and the
Chapter 9 list refinements. The complete key order is used for updates; cache
fields must never become part of the semantic comparison key. Compose these
facts with the existing `AbstractSet.Refinement`/`OrderedList.laws` route and
derive an augmented `DeleteLaws` instance. The valid-state predicate can conjoin
strict complete-key inorder, actual AVL shape balance and product-cache validity.

For overlap search, run a direct one-branch recurrence on the richer carrier,
reading its maximum component. Prove its value agrees with the existing
`IntervalTree.search` on the maximum projection, then reuse `search_correct`
and low compatibility. That projection is a proof observation; executing a
whole-tree conversion for every query would cost linear work and defeat 090.
No operation equality with the old unbalanced updates is needed. The exact
interval-set laws are the interface consumed by the already proved generic
sweep, including its complete occurrence keys and noninjective interval image.

The present reusable maximum theorems assume `LinearOrder α` and `OrderBot α`.
Preserve those actual premises if using that route. A bottom-free extension or
a `WithBot` endpoint embedding could be useful, but neither is proved here and
must not be silently advertised. A concrete bottom-based instance does not
weaken the already general semantic sweep or its existing Int/list clients.

### Two endpoint choices must remain distinct

The earlier bottom-based proposal above reuses `IntervalTree` contracts with
`LinearOrder α` and `OrderBot α`. The later optional-maximum route below uses
`Trees.MaximumCache` and does not invent an empty numeric sentinel. Its existing
Nat client demonstrates the full-summary law; it is not yet an augmented interval
search implementation. Prove the appropriate maximum/search projection for the
chosen representation. Do not silently drop `OrderBot` from the first route or
claim the optional route already supplies the first route's search bridge.

## Optional-maximum algebra and a second stale-summary separator

Putting an interval subtree maximum inside the payload of the current
height-only AVL tree and then reusing height-only rotations does not preserve
that maximum. Rotations promote an old payload unchanged, although its subtree
changes. Recomputing the height alone cannot repair the other summary.

For a concrete single-left-heavy case, let A be the singleton interval[0,1],
a be[2,3], B and C empty, and the parent payload c be[4,100]. AB has root a,
children A/B, height 2 and maximum endpoint 3; C has height 0. The +2 trigger and
single-rotation side test hold. The balancer promotes a above a new c node.
The new root subtree includes endpoint 100, so retaining a's former maximum 3
is wrong. Shape balance, raw inorder and repaired height can all hold despite
that invalid maximum. This is a paper counterexample, not a checked client.

### Reusable complete-summary interface

Use the existing generic cached carrier BinaryTree(alpha × sigma), with empty
summary e:sigma, local combine F:sigma→alpha→sigma→sigma, and a projection
H:sigma→Nat satisfying H(e)=0 and

    H(F l a r) = max(H l)(H r)+1.

Read height as H(Cached.read e t), and make every new node using the SAME
Cached.smartNode e F. A structural fold argument proves that projecting the
full summary gives ordinary tree height. Combining it with the existing
Cached.read_eq_fold law gives the cached/actual height bridge under recursive
Cached.Valid e F. No order or balance assumption is needed for this bridge.

The existing generic `HeightBalance.balL`/`balR` now use these height reads and
this complete local smart constructor. Its raw inorder proof remains independent of cache validity.
Full cached-summary validity follows from the existing smart-node validity law
and child validity exposed by destructuring. Its balance and height proof uses
the height projection bridge and the separately derived numerical case proof.
Do not silently give a raw annotated tree the projection bridge without validity.
The fixed d≥1 requirement and all strict/tie/general-d cases remain mandatory.

The ordinary source AVL implementation specializes sigma=Nat, e=0,
F=heightCombine and H=id. The raw reader, constructor, recursive invariant and balancing recurrence
now have ordinary bridges in `AVL/Rebalance.lean`; the later update and Set
refinement owners extend those connections. Measured counts remain separate
work. The augmented interval instance must reuse these owners rather than add
a second unchecked balancing implementation.

For interval augmentation, take sigma as the pair of height and the existing
optional maximum-endpoint summary. The local combine pairs max-height+1 with
the existing maximum fold operation applied to both children and the interval.
The height-projection law is then immediate arithmetic, and the two components
of the generic cached-summary invariant recover both cached height and maximum.
Use the actual existing optional-empty/max endpoint owner and key ordering;
do not invent a numeric empty sentinel, change duplicate-key handling, or fold
summary metadata into the search key. Ordering is a separate erased-payload law.

### Algorithm and cost obligations remain concrete

Updates must perform local combinations at the actual rotated nodes. Whole-tree
annotation or rebuilding after every operation would lose the required local
program/cost correspondence. The generic summary constructor's cost must be
explicit in the measured recurrence. A height/optional-maximum pair has bounded
local primitive work under the selected comparison/arithmetic cost model; this
is not a machine-time or bit-cost claim. Preserve the existing separation between
pure binary trees, measured construction, shared-store graph references and any
later physical representation claims.

The generic route now avoids a need to duplicate the balanced-interval rotation
proofs, once the complete interval annotation and its operation bridges are supplied. It is not required to choose this exact
interface: reuse the mathematical point that every augmentation must be rebuilt
locally at rotated roots, and retain the concrete stale-maximum separator.

## Independently selected separating cases

These are mathematical predictions for future checked clients, not compiled
results from this preparation.

1. **Stale maximum after rotation.** Start with the valid right chain of
   intervals[1,1],[2,2],[3,100]. After the left rotation the root is[2,2],
   with leaf[1,1] and leaf[3,100]. The demoted first node's maximum must become 1.
   Reusing its former 100 cache leaves the whole root maximum unchanged but makes
   query[3,3] choose the left branch and miss the overlapping right interval.
   Recomputing only the new root is insufficient even when ordering/balance hold.
2. **Double reconstruction.** In the left-right shape with root[3,3], left
   child[1,100] and that child's right child[2,2], a double rotation produces
   root[2,2], left[1,100], right[3,3]. The new root must acquire 100 and the
   demoted old root must lose its stale 100 and become 3. This exercises multiple
   changed annotations in one constant-size rewrite.
3. **Deletion tie.** Use ordered keys with root 4, left subtree rooted 2 with
   leaves 1/3, and right leaf 5. Deleting 5 makes the root left-heavy with equal
   grandchild heights. The canonical `<=` branch is a single right rotation,
   yielding root 2 with left 1 and right 4 whose left child is3. Preserve this exact
   source case; insertion-only examples do not exercise all deletion branches.
4. **Duplicate interval projections.** Two equal x intervals with different
   occurrence IDs remain two complete keys through rotations. Deleting one ID
   leaves the other, and subsequent overlap observation must still see it.
   Node/cardinality reasoning uses complete-key uniqueness, not injectivity of
   interval projection.
5. **Malformed descendants.** A local smart-node rebuild with one invalid
   child must not be claimed to repair the whole cache. Equality insertion
   preserves the old node, including a bad cache on a raw input. Valid-input
   preservation and raw semantic equations have different premises.

The whole-rebuild, empty-state tariff and early-termination separators are retained
with the measured-sweep preparation. Both interpretations must preserve complete
occurrence keys, independently meaningful endpoint observations and the original
semantic sweep's generality. Primary Chapter 9 inspection is attributed separately
in [the continuation paper](fdsa-avl-continuation.md); this curation does not turn
old discovery searches or unread external theories into new evidence.

## Earlier red-black reuse constraints and counterexamples

The following mathematical observations come from the receiving integration
agent's 18 November 2026 preparation for C05-085–090, originally a 36,362-byte
paper with SHA256
`c3b03a4ecda6c8f55cccd76707c5f4626ee0bf2d5c071661e209120c68f8e417`.
They remain useful unqualified preparation for comparing a red-black alternative
with the now available cached-height route. No new implementation or source
qualification follows from retaining them.

The existing source-facing red-black ordering predicate is still
`BST (decode : κ → Int)`. Its shape/color erasure and height facts are reusable,
but this decoder does not directly provide the required generic interval-key
order. There can be no global strictly increasing embedding of `IntervalKey Nat`
into Int: the keys `[0,0] < [0,1] < [0,2] < …` all lie below `[1,1]`, while a
strictly increasing integer sequence cannot be bounded above by one integer.
A finite-input rank adapter would need its own proved correspondence; it cannot
be silently assumed for every interval key.

Preserve branch priority as well as the usual valid-tree rotation equations.
The existing raw matcher tests right-left before right-right, as the overlapping
red-red example in [`Examples/RedBlackTrees.lean`](../../Examples/RedBlackTrees.lean)
shows. The earlier recovery preparation reports the FDSA/provider directional
right balancer testing right-right before right-left. That external comparison
remains attributed historical preparation, not a fresh provider inspection here.
A selected source program's exact overlapping raw result must be checked rather
than inferred from its behavior on valid trees. Cache-aware reconstruction does
not make these branch orders interchangeable.

The existing red-black matcher moves `(key,value)` bindings. Treating its value
as a subtree maximum does not make it cache-aware: rotations change descendants
and require complete bottom-up rebuilding. Let ascending keys be a=`[1,100]`,
b=`[2,50]`, c=`[3,4]`, with empty fringes. Every input below has valid local
maximum caches and the indicated temporary red-red defect, rather than being
a fully balanced public tree. All four should become red b/100 with black
leaves a/100 and c/4 under a cache-aware version of the corresponding rewrite.

| Source branch | Input shape and exact caches | Why payload movement is insufficient |
| --- | --- | --- |
| LL | Black c/100, left red b/100, its left red a/100 | The demoted c leaf needs 4 instead of its retained 100. |
| LR | Black c/100, left red a/100, its right red b/50 | The promoted b needs 100 and demoted c needs 4. |
| RL | Black a/100, right red c/50, its left red b/50 | The promoted b needs 100 and demoted c needs 4. |
| RR | Black a/100, right red b/50, its right red c/4 | The promoted b needs 100 instead of 50. |

The temporary shape premises are satisfiable with black-height-zero fringes.
Root blackening changes color, not the required cache. Recomputing only the final
root still leaves a bad c descendant in the first three branches. The fallback
case also matters: a root `[1,1]` whose new right leaf is `[2,100]` must recompute
its maximum to 100 even if no rotation occurs; retaining its former value 1 is
wrong. Complete local reconstruction preserves recursive cache equations from
valid children. Rotation invariance of an arbitrary shape-dependent fold does
not follow from this; maximum meaning uses the lawful maximum algebra.

The inspected source-facing red-black modules do not provide the missing
cache-aware balanced interval deletion. These remaining cases describe semantic
obligations without choosing an unimplemented deletion algorithm:

- A black root b=`[2,3]`, black left a=`[1,100]` and black right c=`[4,5]` has
  valid maxima and equal black heights. Deleting a must leave strict inorder
  `[b,c]`, a balanced state and maximum 5. Both black b with red-right c and
  black c with red-left b are possible balanced shapes; only a selected actual
  algorithm may determine which exact shape is its result.
- For black root `[-5,-4]` and black leaves `[-8,-6]`, `[-3,-1]`, deleting the
  right interval, then the original root, then the final interval requires
  readers `-1,-4,-6,⊥`. Finite zero is not the empty default, and empty has no
  attaining key.
- For complete keys `([2,8],0)`, `([2,8],1)`, `([2,8],2)`, deleting two keys
  must retain the remaining key, maximum 8 and point-query 8. Deleting the last
  key gives empty and false. The interval projection remains noninjective.

A direct colored overlap program should be related to color erasure in its
proof, without performing a whole-tree erasure during every query. Likewise,
whole-tree cache annotation cannot justify a logarithmic update claim. Existing
red-black affine/log lemmas can convert a proved actual operation-height bill;
they do not supply the cache-aware operation or its missing deletion bill.
