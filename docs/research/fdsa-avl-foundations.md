# FDSA cached AVL foundations

The [foundation module](../../Applications/Trees/AVL/Basic.lean) implements the
height-cache and shape-invariant foundations of FDSA Chapter9, C09-001–009.
The [connected clients](../../Examples/AVLFoundations.lean) distinguish cache
correctness, recursive height balance and search ordering, and reuse the existing
ordered-map membership program. This increment does not implement rotations,
insertion, deletion or logarithmic operation costs.

## Source and shared owners

The primary source is Tobias Nipkow's Chapter9, printed105–116 of the July27,2026
edition of *Functional Data Structures and Algorithms*. The exact PDF has
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`;
its physical pages are six greater than the printed numbers. The official
[PDF location](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
is mutable, so the hash identifies this edition. The cache definitions and AVL
invariant are on printed105; the independent unannotated invariant is explicit
on printed111. The complete chapter, including its diagrams and algorithm
listings, was read during preparation.

The unchanged [canonical obligations](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md)
remain the requirement owner. Their companion-source inventory also locates the
shared augmented-tree search and Set interpretation. The companion theories
were not independently reread for this increment; the actual reused Lean
definitions and membership proofs were inspected directly.

The implementation specializes existing owners rather than introducing another
tree representation:

- `Trees.Cached` supplies the product-labelled carrier operations, root reader,
  smart constructor, recursive cache validity, erasure and bottom-up annotation.
- `Trees.Observations` supplies the independent fold, actual-height fold law,
  inorder and label-map observations.
- `Search.OrderedMap.Membership` supplies executable cache-independent search
  and its ordered-content semantics.
- `Resources.TreeCache` supplies a separate declared observation of the actual
  local reads, combination and node construction.

## Definitions and the exact source invariant

`Trees.AVL` uses `BinaryTree (α × Nat)` with the semantic payload first and the
stored height second. `heightCombine hl a hr = max hl hr + 1` ignores `a`.
`ht` is exactly `Cached.read 0`: empty reads0 and a node reads its stored natural,
including when that value is wrong. `node` is exactly
`Cached.smartNode 0 heightCombine`. It reads both child root summaries, computes
the new root annotation and retains both child trees. It does not compute
structural height, erase annotations or recursively repair children.

The distinction between observations is explicit:

\[
\operatorname{ht}(\operatorname{node}(l,a,r))
=1+\max(\operatorname{ht}(l),\operatorname{ht}(r)),
\qquad
h(\operatorname{node}(l,a,r))=1+\max(h(l),h(r)).
\]

Both equations hold on every raw input. Their right-hand sides need not agree.
Erasure and inorder likewise preserve the actual child shapes and payload
sequence without a validity hypothesis. Existing `Cached.height_erase`,
`numNodes_erase`, `numLeaves_erase` and `inorder_erase` remain their shared owners.

`CacheValid` specializes the existing recursively checked cached-fold invariant.
At every node it requires both children cache-valid and the root annotation
equal to the combination of their stored summaries. `node_cacheValid_iff`
states exactly that smart construction is cache-valid iff both children already
are cache-valid. A new root does not repair an invalid descendant.

`Balanced : BinaryTree α → Prop` is independent of caches and payload order.
At every node, both children must be balanced and their actual heights satisfy
both inequalities `hl ≤ hr+1` and `hr ≤ hl+1`. `height_balance_iff` proves their
equivalence to the source's signed integer condition:

\[
\left| (h_l:\mathbb Z)-(h_r:\mathbb Z)\right|\le1
\quad\Longleftrightarrow\quad
h_l\le h_r+1\ \land\ h_r\le h_l+1.
\]

A single truncated natural subtraction is insufficient: `0-2=0` in `Nat`.
`balanced_map` proves preservation **and reflection** under any payload map,
including noninjective maps and maps between arbitrary universes. This is a
shape property, so repeated labels and collapsed labels remain admissible.

`Valid t` is `Balanced (Cached.erase t) ∧ CacheValid t`. Its complete source
correspondence is the proved `valid_node_iff`:

\[
\begin{aligned}
\operatorname{Valid}(N((a,n),l,r))\ \Longleftrightarrow\;&
\operatorname{Valid}(l)\land\operatorname{Valid}(r)\\
&\land\left|(h(l):\mathbb Z)-(h(r):\mathbb Z)\right|\le1\\
&\land n=1+\max(h(l),h(r)).
\end{aligned}
\]

The proof first obtains the stronger cache-only result
`ht_eq_height_of_cacheValid`, by composing `Cached.read_eq_fold`,
`Trees.fold_height` and `Cached.height_erase`. No balance premise is needed for
that result. Correct child caches then turn the local cache equations into the
actual-height equations in `valid_node_iff`. This derives the source invariant
from the definitions; it is not a correctness field assumed in a structure.

`node_valid_iff` is the corresponding smart-constructor law: the result is valid
iff both children are valid and their actual height difference has absolute
value at most1. Unlike `valid_node_iff` for a raw node, it has no independent
root-cache equation, because the constructor computes that cache. `valid_nil`,
`valid_singleton` and `ht_eq_height` expose the useful base and observation laws.

All these shape/cache declarations support arbitrary payload universes without
order, equality, decidable equality, inhabitedness, distinctness or injectivity
assumptions.

## Decoration, recovery and its boundary

`annotate` is the existing bottom-up `Cached.annotate` specialized to height.
For every unannotated tree, including an unbalanced tree:

- `annotate_cacheValid` supplies recursively correct height annotations;
- `erase_annotate` recovers the original payload-labelled tree exactly;
- `ht_annotate` returns its actual height;
- `valid_annotate_iff` states `Valid (annotate t) ↔ Balanced t`.

Thus decoration repairs caches while preserving the original balance boundary.
It is a whole-tree construction, separate from the local `node` program. No
annotation/erasure round trip is asserted for arbitrary malformed annotated
trees, and no runtime decoration is inserted into search or future updates.

## Search retains its existing owner and assumptions

`Search.OrderedMap.containsKey query t` is the existing executable
`lookup query t |>.isSome`. Its raw empty/node equations require only `[LT α]`
and `[DecidableLT α]`: choose left if query<key, otherwise right if key<query,
otherwise return true. Under a linear order, the final branch represents equality.
No annotation is read, and no runtime erasure traversal occurs.

Under `[LinearOrder α]`, `containsKey_eq_member_erase` proves raw path agreement
with the existing ordered-set program even for unordered or wrongly annotated
trees. To identify that path answer with membership in the whole erased inorder,
`containsKey_eq_true_iff_of_inorder_pairwise` requires strict inorder. The
`OrderedBy` and set-observation versions remain available from the same module.
None requires `Trees.AVL.Valid`.

This increment reuses those public theorems through checked clients. It adds no
AVL search wrapper or duplicate universal membership proof. An AVL shape alone
does not establish search order: a correctly cached tree with root2, left3 and
right1 is valid, yet the actual search for3 returns false although3 is in the
whole-tree contents.

## Connected cases and declared local work

The clients retain the independently expected A01–A10 distinctions:

| Cases | Checked clients and public connections |
|---|---|
| A01 | `zeroLeaf_observations`, `zeroLeaf_invalid`, `singleton_repair`: raw stored0 differs from actual singleton height1; the repaired singleton uses `valid_singleton`, `ht_node_smart` and `erase_node`. |
| A02 | `correctRoot_observations`, `correctRoot_invalid`: root cache2 and balanced shape do not validate a child storing99; `valid_node_iff` exposes the recursive child obligation. |
| A03 | `propagated_observations`, `propagated_erases`, `propagated_invalid`: actual local construction computes100 above stored99, has structural height2 and inorder `[1,2]`, and remains invalid. |
| A04/A06 | `leftChain_cacheValid`, `leftChain_ordered`, `leftChain_not_valid`, `rightTall_cacheValid`, `rightTall_not_valid`: correct caches and individually valid children do not imply parent balance. Cache proofs consume `node_cacheValid_iff`. |
| A05 | `unit_height_gaps`, `two_height_gaps_fail`, `truncated_subtraction_loses_one_side`: both signs are checked through `height_balance_iff`. |
| A07 | `badOrdered_membership`, `badOrdered_set_membership`, `badOrdered_raw_path`, `badOrdered_answers`: strict contents support the existing program despite malformed caches, including arbitrary-query correctness and answers1/2/3=true,4=false. |
| A08 | `unordered_valid`, `unordered_not_strict`, `unordered_misses_present_key`: balance and cache validity do not provide search ordering. |
| A09 | `empty_payload_valid`, `generic_decoration`, `collapse_not_injective`, `collapse_balance_iff`: empty payload types, arbitrary universes and noninjective label maps need no extra assumptions. |
| A10 | `repeated_decoration`, `repeated_shape_counts`, `repeated_payload_occurrences`, `chain_decoration_not_valid`: decoration retains repeats and exact observations; a correctly decorated unbalanced chain remains invalid. |

The local-work client uses the actual generic measured construction
`Resources.TreeCache.nodeRun`. It declares one source event for each root read,
one for node construction, one for natural `max` and one for addition.
`heightCombineRun` returns the real `heightCombine` value with observation2.
The generic measured node executes the two root reads and that callback, and
constructs the node with the callback's returned annotation.

`local_node_value` proves its returned tree is exactly `Trees.AVL.node l a r`.
`local_node_cost` proves its observation is5, for arbitrary children without any
cache or balance premise. The five charges are two root reads, node construction,
max and addition. `malformed_child_local_execution` connects both components:
running this program above the stored99 child returns exactly `(propagated,5)`.

This is a declared source-event tariff with unit natural arithmetic. It proves
neither machine-bit costs nor allocation counts, physical sharing, wall-clock
time or whole-operation complexity. The value equality alone does not imply
the cost equation; they use the separate generic value and resource theorems.

## Requirement correspondence and remaining work

| Canonical row | Implemented/reused owner |
|---|---|
| C09-001 | Shared `BinaryTree (α × Nat)` in the actual public definitions; no new carrier |
| C09-002 | `ht`, `ht_nil`, `ht_node` |
| C09-003 | `node`, `node_eq`, `ht_node_smart`, shared `Cached.smartNode`; connected local-work clients |
| C09-004 | `erase_node`, `height_node`, `inorder_node`; existing shared erasure/size/height/inorder laws used by clients |
| C09-005 | `Valid`, complete signed actual-height `valid_node_iff`, `valid_nil` |
| C09-006 | `ht_eq_height_of_cacheValid`, `ht_eq_height`, `node_valid_iff`, `valid_singleton` |
| C09-007 | `Balanced`, `height_balance_iff`, `balanced_map`, `valid_iff`, and decoration/recovery laws |
| C09-008 | Existing `Search.OrderedMap.containsKey` and its raw equations; `empty_search` and raw-path clients |
| C09-009 | Existing strict-inorder/set membership laws instantiated by the clients; `valid_nil` and `empty_search` |

These are declaration and client correspondences, not a replacement for the
candidate's build, exhaustive focused proof audit, statement/type assessment,
independent reviews or receiving acceptance records. The source module and
connected clients compiled in development; qualification and checkpoint
publication are recorded by the enclosing workflow on its exact candidate.

C09-010 onward remains mandatory: Fibonacci and exact real-log bounds, numerical
coefficient correspondence, minimum-height witnesses, cached rotations and both
updates, measured operation costs, the balance-factor implementation, all seven
exercises and the generalized-height claim. C05-085/090 still require the actual
balanced interval instance and measured sweep; C05-092/093 also remain open.
Remaining FDSA chapters/appendices, PFDS book/thesis obligations, VFA receiving
acceptance and the complete three-book task are unchanged by this foundation.
