# Interval geometry, membership and maximum-cache foundations

This increment implements FDSA Chapter 5 obligations **FDSA-5-66 to FDSA-5-74**. It separates
complete-key membership, closed-interval geometry, independent overlap
observations, raw cached values and recursively valid maximum caches. The
unchanged [Chapter 5 obligation inventory](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md)
owns the mathematical scope. Interval insertion, deletion, overlap search,
point search, balanced augmentation, sweep-line correctness and distance
algorithms remain separate obligations.

## Sources and correspondence

The primary exposition is Tobias Nipkow's [Functional Data Structures and
Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
July 27, 2026 version, printed pages 71–73 (PDF pages 77–79). The consulted PDF
has SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion is the Isabelle mirror at revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`:

- [Interval_Tree.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Interval_Tree.thy),
  SHA-256 `0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2`.
- [Isin2.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Isin2.thy),
  686 bytes, SHA-256 `f6b0c6574c8fa618b5d42f3045e9af32731afd80a061173d8bc09eae9808df0c`.
- [Tree2.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree2.thy),
  1,560 bytes, SHA-256 `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e`.

These are source correspondences, not a claim that an Isabelle proof was checked
by Lean. The proofs below are local Lean derivations, reusing the existing tree,
ordered-map and maximum-cache interfaces. Mathlib is pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679`; Lean is 4.35.0.

| Canonical row | Local declarations | Connected examples |
| --- | --- | --- |
| FDSA-5-66: annotations do not select equality-membership branches | `OrderedMap.containsKey`, its empty/node equations, `containsKey_eq_member_erase`, `containsKey_congr_erase`, `containsKey_eq_true_iff_mem_inorder`, `containsKey_eq_true_iff_mem_setTree`, strict-inorder adapter | Higher-universe function annotations; numeric replacement annotations; equal-low keys and cache corruption; unordered lookup counterexample |
| FDSA-5-67: valid interval endpoints and ascending lexicographic order | `IntervalKey`, `ofBounds`, `low`, `high`, `low_le_high`, `ext`, `endpoints_injective`, linear-order instance, `lt_iff`, `le_iff`, `low_le_of_le` | Containment versus key order; Mathlib's different interval Lex order; proof-independent endpoints; equal-low high tie breaker |
| FDSA-5-68: closed overlap and common-point semantics | `IntervalKey.overlap`, `overlap_comm`, `overlap_self`, `toSet`, `overlap_iff_nonempty_inter` | Negative touching intervals; singleton intersection; a genuine gap; reversed endpoint countermodel |
| FDSA-5-69: independent abstract overlap observation | `IntervalSet.hasOverlap`, empty/insert/singleton laws, monotonicity, `hasOverlap_image_iff` | Two directly specified intervals; an unrestricted predicate-defined set; noninjective complete-key images |
| FDSA-5-70: literal augmented representation and root reader | `IntervalTree.maxHi`, `maxHi_nil`, `maxHi_node`, `combine`, `max3`, `max3_eq` | Empty/bottom singleton; each max3 contribution; negative finite endpoints above a true bottom; malformed raw readers |
| FDSA-5-71: recursive exact cache equations | `IntervalTree.CacheValid`, `cacheValid_nil`, `cacheValid_node`, `cacheValid_iff_invarMx` | Valid ordered and unordered trees; separate upper-bound, attainment and root-only countermodels |
| FDSA-5-72: every stored high is bounded | `IntervalTree.maxHi_spec`, `high_le_maxHi` | Maximum high on the least key; unordered valid tree; negative endpoints; both independent universe specializations |
| FDSA-5-73: an actual stored key attains the reader | `IntervalTree.maxHi_spec`, `maxHi_attained` | Bottom singleton; greatest-high witness; nonunique tied witnesses; indexed noninjective projection; explicit failure under upper bounds alone |
| FDSA-5-74: local smart construction and erasure/cache laws | `IntervalTree.node`, `node_eq`, `maxHi_node_smart`, `erase_node`, `node_cacheValid_iff`, `node_cacheValid` | Valid children; repaired malformed leaf; unchanged malformed children under smart reconstruction |

Library owners are [IntervalKey](../../Applications/Search/IntervalKey.lean),
[OrderedMap/Membership](../../Applications/Search/OrderedMap/Membership.lean),
[IntervalSet](../../Applications/Search/IntervalSet.lean),
[IntervalTree/Basic](../../Applications/Search/IntervalTree/Basic.lean), and
[IntervalTree/Maximum](../../Applications/Search/IntervalTree/Maximum.lean).
Examples live in [IntervalGeometry](../../Examples/IntervalGeometry.lean) and
[IntervalTreeFoundations](../../Examples/IntervalTreeFoundations.lean). Both are
imported by the existing public entrypoint without removing prior imports.

## Complete keys, intervals and membership

`IntervalKey α` wraps Mathlib's `NonemptyInterval α` data. Thus low is at most
high by construction, and endpoint extensionality does not depend on which
proof of that inequality was supplied. A separate wrapper is necessary:
Mathlib's ordinary interval order is containment, and its `Lex` interval order
reverses the low comparison. The book requires increasing low followed by
increasing high. Mapping to `α ×ₗ α` and using `LinearOrder.lift'` supplies that
lawful order without changing either Mathlib order.

Equal lows do not identify keys. For example, `[1,2] < [1,5] < [1,8]`, although
all three lows are equal. `low_le_of_le` therefore concludes only a weak low
inequality. The examples distinguish this order from containment using `[1,8]`
and `[2,3]`, and inspect the library's descending-low Lex order directly.

`OrderedMap.containsKey` observes whether the existing `lookup` returns a value.
It retains that program's two strict comparisons and all raw branch behavior.
Its definition needs only `LT κ` and decidable comparison; annotation values
need no equality, order or inhabitant. The erasure/path bridge uses the existing
linear-order `OrderedTree.member` API. It holds on unordered and corrupt trees.
The additional strict `OrderedBy Prod.fst` premise is needed to connect a path
answer with the independently observed whole-tree contents.

The function-annotation example has keys in `Type` and annotations in `Type 1`.
It checks both lookup values and presence, then replaces the annotations with
integers while preserving every key and branch. An empty tree also works with
the empty annotation carrier. No cache premise is smuggled into these laws.
The unordered example stores `[0,0]` in the right child of `[1,1]`, with `[2,2]`
on the left. Its cache is valid, but ascending lookup for `[0,0]` fails. This is
a counterexample to dropping order from the whole-tree membership theorem,
while both raw directed programs still agree.

## Closed geometry and independent observations

Overlap is the conjunction `low y ≤ high x` and `low x ≤ high y`.
Under a linear order it is equivalent to a nonempty intersection of the two
closed endpoint sets. The forward proof chooses `max (low x) (low y)`;
endpoint validity and the cross inequalities put that point in both sets.
The reverse proof composes the inequalities supplied by an actual common point.
Touching endpoints therefore count. Geometry needs no bottom element; the
negative examples use plain `Int`.

The raw reversed pair `(5,1)` illustrates why endpoint validity matters. Its
cross inequalities with `[0,6]` both hold, but its closed set is empty.
`reversed_pair_uninhabited` proves that no `IntervalKey Int` has those endpoints,
and `reversed_pair_counterexample` proves the failed raw-pair interpretation.

`hasOverlap` is an existential observation on a `Set (IntervalKey α)`, with no
tree, enumeration or finiteness assumption. Its image adapter returns an original
complete-key witness. The larger-key-universe example uses two distinct indexed
keys with the same interval `[2,8]`; a query at 8 overlaps and a query at 9 does
not. Removing one indexed key can leave the projected interval image unchanged
while changing complete-key membership. Equality search and geometric overlap
remain different observations.

## Raw cache representation and checked reuse

The carrier is `BinaryTree (κ × α)`, with independent universes for complete
keys `κ` and endpoints `α`. A projection `iv : κ → IntervalKey α` supplies each
key's interval. Taking `κ = IntervalKey α` and `iv = id` gives the literal book
carrier. `maxHi` is `Trees.Cached.read ⊥`: it reads the stored root field and
returns bottom at an empty tree. It performs no maximum traversal or repair.
The raw definition needs only `Bot α`.

`combine iv l a r = max (iv a).high (max l r)` is the shared cached-fold algebra.
`max3` applies it to the two raw readers. `CacheValid` and `node` specialize
`Trees.Cached.Valid` and `smartNode`; they do not introduce a second recursive
cache framework. The raw algebra, validity equations and constructor laws need
only `LE`, `Max` and `Bot`, with no order laws or BST predicate. A smart node
has valid caches exactly when both supplied children do.

Greatest-endpoint semantics adds `LinearOrder α` and `OrderBot α`. The
`highTree` map changes each complete key to its high and leaves its stored
annotation untouched. The map preserves tree shape and each node occurrence,
including multiplicity, although distinct keys can acquire equal labels.
`erase_highTree` and `inorder_erase_highTree` describe the corresponding key
and list maps. `setTree_erase_highTree` is their set-image observation; that
observation forgets occurrence multiplicity. No injectivity premise is used.

A small compatibility induction proves `cacheValid_iff_invarMx`. Its local
equation reconciles the bottom-valued empty reader with the existing
`MaximumCache` optional reader. Bottom laws and max associativity justify the
four empty/nonempty child combinations. The semantic proof then uses the
existing `MaximumCache.mx_eq_some_iff`, whose fold/list-maximum derivation
provides both attainment and the upper bound. Image membership recovers an
actual complete key. There is no second interval-specific maximum-correctness
induction and no annotation pass hidden inside the projection.

The distinction between a true bottom and an arbitrary default is material.
With endpoints `WithBot Int`, the valid three-node example has maximum high
`-1`, and the singleton `[-8,-6]` has reader `-6`. Replacing the empty-child
value by numeric zero gives an unattained answer. Over `Nat`, the empty tree
and the nonempty singleton `[0,0]` both read zero; only the latter has a stored
witness. Thus a reader equal to bottom is not an emptiness test.

The indexed example lifts complete keys to `Type 1` while endpoints remain
`Nat`; two key occurrences project to the repeated high list `[8,8]`. The dual
example uses keys `Fin 2` and endpoints `ULift.{1} Nat`. Both instantiate the
public bound and attainment results. No common universe or key-order premise
is required by those maximum theorems.

## Countermodels and hypothesis boundaries

The examples separate three plausible weakenings of recursive exact validity:

| Example | What holds | What fails |
| --- | --- | --- |
| `boundOnly` | Strict BST; every subtree reader bounds its stored highs; the root obeys its local equation | Reader 100 is unattained by highs 0, 1 and 2; the left leaf cache is invalid |
| `attainmentOnly` | Strict BST; every nonempty subtree reader is attained within that subtree; the root obeys its local equation | Stored high 5 exceeds root reader 4 and left-subtree reader 2; the left local equation fails |
| `correctRoot` | Strict BST; the root reader is the actual attained global maximum 100; the root local equation holds | A left leaf still stores 50 for `[0,0]`, so recursive validity fails |

Each property and each failure is a theorem about explicit finite trees.
They are not unsuccessful proof attempts. Together they show why neither
global correctness nor one of its two conjuncts can replace the all-node
cache invariant. Conversely, cache validity is sufficient, not necessary,
for a correct global reader, as `correctRoot` demonstrates.

Smart construction repairs exactly the new root. Rebuilding a malformed
`[2,5]` leaf changes reader 99 to 5 and preserves erasure. Rebuilding above
the malformed children of `boundOnly` or `correctRoot` returns those same
invalid trees. The exact value equations and generic constructor iff express
this boundary; no allocation, pointer-sharing or execution-time theorem is
claimed. The max3 calculations exercise root, left, right and tied maxima,
and two distinct stored intervals witness the tied case, ruling out uniqueness.

## Qualification and remaining work

Candidate-specific compilation, source-policy/entrypoint checks, elaborated
statement inspection, axiom audit and independent reviews belong to the
checkpoint's exact validation and review records. A focused donor check does
not establish full-library or receiving-branch acceptance. Existing module
system compatibility warnings are not a reason to change compilation inputs.

FDSA-5-75 to FDSA-5-84 still require smart insertion/deletion, exact erased list
refinement, combined invariants, pruning lemmas, one-branch overlap search and
the separately recursive point-search exercise. For generalized complete keys,
future search must explicitly require the order-to-low compatibility it uses;
an arbitrary `iv` does not follow key order merely because the cache theorems
allow it. FDSA-5-85 to FDSA-5-94 and the later books remain open. The receiving branch's
additional public imports and its effective Lake configuration must be reconciled
and validated on the actual integrated union. This bounded source increment
does not settle those obligations.
