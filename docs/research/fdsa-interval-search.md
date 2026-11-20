# Interval-set laws, overlap search and independent point search

This contribution addresses C05-079–084: the complete interval-set contract,
the literal guarded overlap recursion, its two pruning arguments and full
correctness, and the separately recursive point program of Exercise 5.8. It
builds on the interval geometry, cache foundations and updates described in
[fdsa-interval-foundations.md](fdsa-interval-foundations.md) and
[fdsa-interval-updates.md](fdsa-interval-updates.md). The current tracker and
candidate evidence own qualification; this note explains the mathematics.

## Primary correspondence

The primary reading is printed pp. 74–75 of
[Functional Data Structures and Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
using the pinned PDF with SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion is
[Interval_Tree.thy at f86f290225eebcc52c1ae7dba2e098f405f51c21](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Interval_Tree.thy),
SHA-256 `0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2`.
The actual search proof, `Interval_Set` locale and all eight interpretation
obligations were read. No Isabelle execution is asserted. The canonical row
owner is
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md`,
SHA-256 `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad`.

| Canonical row | Source correspondence | Lean owners and public results |
| --- | --- | --- |
| C05-079 | Combined cache/strict-inorder invariant and the full interval-set interpretation. The four displayed update corollaries are only part of this contract. | `IntervalTree.Valid`, `deleteOps`, `inorderRefinement_of_singleton`, `setLaws_of_singleton`, their canonical specializations, `IntervalSet.Laws`, `IntervalTree.intervalSetLaws` and shared mixed-history APIs. |
| C05-080 | Empty false; root overlap true; otherwise choose exactly one child, retaining the nonempty-left guard. | `IntervalTree.search`, `search_nil`, the four node branch equations and `search_sound`. |
| C05-081 | A selected nonempty left subtree with no overlap excludes the right through an attained left maximum and ordered lows. | `high_lt_low_of_left_no_overlap` and `not_overlap_right_of_left`, using the existing `maxHi_attained`. |
| C05-082 | Empty left, or a failed maximum threshold, excludes overlap in the left subtree. | `not_overlap_nil` and `not_overlap_of_maxHi_lt`, using the existing `high_le_maxHi`. |
| C05-083 | Theorem 5.3, with boundary contact, singleton intervals and overlapping stored intervals. | `search_complete`, `search_correct`, `search_correct_of_strict` and `search_correct_book`. |
| C05-084 | Exercise 5.8's own point-containment recursion and semantic theorem. | `containsPoint`, `searchPoint`, `searchPoint_eq_search`, `searchPoint_correct` and its strict/book specializations. |

The Lean implementation and proof organization are original. They reuse the
repository's actual tree/list/set refinements and maximum-cache results, rather
than copying the companion's complete proof. The companion's query-first root
test and its exact guarded branch choice are preserved.

## Representation and observations

Endpoints are `α : Type u`, complete keys are `κ : Type v`, and
`iv : κ → IntervalKey α` projects a key to its interval. The concrete state is
`BinaryTree (κ × α)`, with a stored endpoint annotation at each node. The key and
endpoint universes are independent. The abstract contract additionally permits
an independent state universe `S : Type w`.

For discussion, write

* `I(t) = Trees.inorder (Trees.Cached.erase t)`;
* `K(t) = Trees.setTree (Trees.Cached.erase t)`;
* `V(iv,t) = CacheValid iv t ∧ OrderedList.Strict (I(t))`.

Erasure forgets annotations and preserves the complete-key tree. Inorder
forgets shape but retains order and multiplicity. The set observation forgets
order and multiplicity. The image `iv '' K(t)` can additionally identify
distinct complete keys. None of these forgetful observations supplies a unique
preimage or recovers a deleted occurrence.

`IntervalSet.hasOverlap_image_iff` provides the exact existential bridge:

```text
hasOverlap (iv '' K(t)) q ↔ ∃ key ∈ K(t), overlap (iv key) q.
```

No injectivity is required. The witness on the right is an original complete
key. Complete-key deletion observes `iv '' (K(t) \ {key})`; it generally does
not observe `(iv '' K(t)) \ {iv key}`. The retained indexed deletion example in
`Examples.IntervalTreeUpdates` proves that these sets can differ.

## All seven ordinary laws from one refinement

`IntervalTree.deleteOps` packages the actual annotated empty, insert and delete
programs with `OrderedMap.containsKey`. Its raw endpoint requirements are
`LE`, `Max` and `Bot`; its raw complete-key requirements are `LT` and
`DecidableLT`. The raw two-false-comparisons fallback has no general equality
meaning until the complete keys have a linear order.

The ordinary refinement uses linear complete keys, arbitrary `iv`, and the
universal singleton equation

```text
∀ key, (iv key).high = max (iv key).high (max ⊥ ⊥).
```

This is exactly the previously established key-local insertion premise,
quantified over every key that the operation bundle may insert. It is sufficient
at raw endpoint `LE`/`Max`/`Bot`; no general maximum algebra or semantic
greatest-element interpretation is used in this transport. The existing
constant-100 maximum countermodel explains why the singleton premise cannot
simply be omitted. The canonical `LinearOrder`/`OrderBot` endpoint corollary
discharges it using the ordinary maximum/bottom laws.

`inorderRefinement_of_singleton` instantiates `AbstractSet.Refinement` with
view `I`, auxiliary invariant `CacheValid iv`, target `OrderedList.ops` and
target invariant `OrderedList.Strict`. Its primitive obligations use the
following existing proofs:

| Primitive refinement fact | Supplier |
| --- | --- |
| Empty view and auxiliary validity | Definitional empty equality and `cacheValid_nil`. |
| Exact insert view | `IntervalTree.inorder_insert`, requiring strict complete-key inorder. |
| Auxiliary insert preservation | `insert_cacheValid_of_singleton`, applied to the inserted key's equation. |
| Exact delete view | `IntervalTree.inorder_delete`, requiring strict complete-key inorder. |
| Auxiliary delete preservation | `delete_cacheValid`, independent of key ordering. |
| Actual Boolean membership view | `OrderedMap.containsKey_eq_member_erase` followed by `OrderedTree.member_inorder`. |

`Refinement.laws OrderedList.laws` then derives the source's ordinary set laws.
`DeleteLaws.congr_observe` and `Trees.mem_inorder_iff_mem_setTree` present them
using the independent tree-set observation. The result includes every field:
empty validity, empty observation, insert validity, insert observation,
equality-membership correctness, delete validity and delete observation.
The source set laws are derived conclusions, not primitive refinement premises.

No compatibility of projected lows, injectivity, or disjointness of stored
intervals belongs to these ordinary laws. `setLaws` remains available for the
reversed-projection countermodel where overlap completeness fails.

The generic `IntervalSet.Laws` extends `AbstractSet.DeleteLaws` by one overlap
law. It takes the existing operation record and a separate Boolean search
parameter; it does not duplicate seven fields or introduce a second update
framework. Its only endpoint requirement is `LE`. The concrete
`intervalSetLaws` combines the derived ordinary laws with the independently
proved search theorem, using global weak low compatibility for the latter.

## Mixed words and all prefixes

The shared `AbstractSet.execute` is a fold of insert/delete updates. The new
contract uses `DeleteLaws.execute_valid`, `execute_observe`,
`execute_from_empty`, `member_execute` and `prefix_valid` without another
interval-tree induction. `Refinement.execute` and `execute_from_empty` prove
exact inorder/list-state agreement, stronger than equality of final sets.
`Refinement.member_execute` connects the actual Boolean implementations.

`IntervalSet.Laws.search_execute` first applies the overlap law at the valid
result state and then rewrites its observed contents by the existing mixed-word
semantics. It applies to every valid starting state and every mixed word. The
examples use both empty and the nonempty seven-node starting tree. The ordinary
history APIs retain independent universes; the existing same-universe
relational-square conveniences are not needed for this construction.

The natural-number word is

```text
insert b; insert a; insert c; insert b; delete a; insert d; delete [42,42].
```

Here `a=[1,2]`, `b=[3,6]`, `c=[5,20]` and `d=[8,9]` are the existing update
fixtures. `mixed_prefix_shapes`, `mixed_prefix_inorders` and
`mixed_prefix_readers` check every exact state, including duplicate insertion
and absent deletion. The final inorder is `[b,c,d]`, with reader 20.
`mixed_prefix_valid` applies to every natural prefix length, including lengths
beyond the word. The seven ordinary fields are each used on these states.
The membership, overlap and point vectors are connected to their respective
public semantic theorems. Exact singleton key `[18,18]` is always absent;
point 18 becomes present when c is inserted. Point 2 disappears when a is
deleted.

## Literal search and its assumption boundary

`search` has the following control flow, expressed by constructor matching for
the nonempty test:

```text
empty                         ↦ false
node with an overlapping root ↦ true
otherwise, nonempty left and q.low ≤ maxHi(left) ↦ recurse left
otherwise                     ↦ recurse right.
```

It reads annotations without recomputing or validating them. At each visited
nonterminal node it makes one selected recursive call. The raw program requires
endpoint `LE`, `Bot` and `DecidableLE`; it requires no `Max`, complete-key
order/equality, tree equality, valid cache or ordered-low premise.

`search_sound` follows this exact recursion. A root hit gives the root's
complete key; a recursive hit gives a child witness that is also in the parent
set. The program tests `overlap query (iv key)`, while the semantic observer
uses `overlap (iv key) query`; `IntervalKey.overlap_comm` connects those
orientations. This is an existential correctness statement, not a claim that
the Boolean program returns the witness. Arbitrary malformed caches or key
placement can cause false negatives, but a raw true answer has a real stored
overlap witness.

The core completeness invariant is deliberately weaker than complete-key
uniqueness:

```text
LowOrdered iv t := I(t).Pairwise (fun a b => (iv a).low ≤ (iv b).low).
```

It permits repeated complete keys, equal projected lows and repeated projected
intervals. Existing `List.pairwise_append`/`pairwise_cons` expose child order
and the left-to-right cross relation. `lowOrdered_of_strict` uses
`List.Pairwise.imp`; this bridge itself needs only `LT κ` and the explicit
implication `a < b → (iv a).low ≤ (iv b).low`.

### Two distinct pruning arguments

Semantic maximum facts use canonical linear/bottom endpoint structure.

| Argument | Exact relevant premises | Conclusion and proof source |
| --- | --- | --- |
| Exclude right after choosing left | Valid, nonempty left; `q.low ≤ maxHi(left)`; no actual left overlap; every left low is at most every right low. | `maxHi_attained` yields an original left key p. Its high passes the threshold, so nonoverlap forces `q.high < p.low`. Cross lows give `q.high < right.low`, excluding every right key. |
| Exclude left after a failed threshold | Valid left and `maxHi(left) < q.low`. | `high_le_maxHi` puts every left high below q.low. No left overlap exists. |
| Exclude empty left | No cache or order premise. | The erased empty tree has no key witness. |

The first argument has no right-cache or parent-cache premise, no root-miss
premise, and no whole-tree BST premise. The second has no key/low-order,
attainment or nonempty premise. Root nonoverlap and child correctness belong to
the surrounding completeness proof. A false child Boolean becomes absence of
actual overlap through that child's correctness argument, not through raw
soundness alone.

`search_complete` combines these facts by tree induction. When the chosen left
has an overlap, its induction hypothesis supplies true. Otherwise left pruning
rules out a right witness, and root nonoverlap rules out the root. When the
program chooses right, empty/bound pruning rules out the left, leaving the
right induction hypothesis. `search_correct` combines this direction with raw
soundness. It assumes valid caches and `LowOrdered`, with no complete-key
structure.

`search_correct_of_strict` derives the low invariant from strict complete keys
and global compatibility. `search_correct_book` uses `iv=id` and
`IntervalKey.low_le_of_le h.le` for the ascending interval-key order. The
concrete interval-set contract uses the same corollary for every valid updated
state; no second search induction is needed.

## Independent point program

`containsPoint point interval` means
`interval.low ≤ point ∧ point ≤ interval.high`. Under a preorder,
`containsPoint_iff_mem` identifies it with the existing closed-interval set
observation. The raw predicate itself requires only `LE`.

`searchPoint` has its own structural recursion, root containment test and
guarded one-child choice. Its definition does not invoke interval search.
After both definitions, `searchPoint_eq_search` proves equality with singleton
query `[point,point]` on every raw tree. With bare `LE`, the theorem explicitly
takes `point ≤ point` to construct that singleton; the point program itself
does not require reflexivity.

For the literal query-first test, `overlap [point,point] (iv key)` reduces to
the same conjunction order as `containsPoint`. Both branch thresholds and
constructor guards agree. The bridge needs no cache, low-order, strict-key or
injectivity premise. The stored-first semantic overlap reverses the two
conjuncts; the semantic point proof handles that equivalence after using the
raw bridge and full interval correctness.

`searchPoint_correct` therefore reuses the interval semantic proof only after
the independent program is defined. It retains the weak-low core and the
strict/book specializations. Agreement of the two raw programs alone does not
establish correctness against contents: the malformed-cache examples make
both programs miss the same stored witness.

## Connected cases and separating models

All new cases live in `Examples.IntervalTreeSearch` and reuse the accepted
foundation/update fixtures. Expected shapes and answers were calculated
independently before implementation. Exact reductions check literal behavior;
the semantic and history results also consume the public general theorems
with the required hypotheses established.

| Family | Checked content and connection |
| --- | --- |
| O10 | All seven fields; exact full mixed-prefix shapes, inorders, readers and answer vectors; shared set/history/refinement and overlap composition; a nonempty initial-state application. |
| O11 | Existing `mainTree`, root stop, chosen-left then right, chosen-right, closed endpoint contact and misses. `main_correct` and `main_semantic_answers` use the full book theorem; point contacts/gaps use the point theorem. |
| O12 | Nonempty selected left with no overlap; attained-key right-low exclusion even with right cache 999; bound-only exclusion on the existing valid unordered subtree; separate empty exclusion; full valid left/right branch clients. |
| O13 | `boundOnly`, `attainmentOnly` and `correctRoot` each return false despite an independently established actual overlap. Their raw point bridges and point false negatives are also checked. |
| O14 | A valid-cache, low-unordered empty-left example changes true to false when the guard is omitted. A valid ordered example chooses a different branch but both answers are false. |
| O15 | An injective reversed `Fin 3` projection has strict complete keys and valid caches, yet overlap/point search miss key 2. The ordinary set membership law still applies. The duplicate-key tree instead satisfies weak low order and the core search theorem, while its previously proved set-deletion failure remains. |
| O16 | The same generic contract/history at `IndexedKey : Type 1` and Nat endpoints; global compatibility, equal projected intervals, complete-key deletion with remaining coverage, a three-node equal-low search client, and the opposite universe direction using lifted endpoints. |
| O17 | `WithBot Int` searches before a positive-high insertion, after insertion and after exact deletion restoration. Query tables include negative contacts, gaps, finite zero, positive 2 and actual bottom. |
| O18 | Independent recursion, all-raw singleton bridges, semantic point applications and distinctions among interval overlap, containment of one point and exact complete-key membership. |
| Deferred O06/O07 geometry | Removing the original root key retains coverage through another overlapping interval; deleting the two largest highs changes queries according to the actual falling-maxima states. Existing update proofs supply all shape and invariant prerequisites. |

The three malformed-cache models distinguish the exact missing facts:

| Model/query | Why the literal program misses | Actual stored witness |
| --- | --- | --- |
| `boundOnly`, `[2,2]` | An unattained left reader 100 selects a nonoverlapping left subtree. Upper bounds alone do not justify left pruning. | Right `[2,2]`. |
| `attainmentOnly`, `[3,3]` | Left reader 2 is attained but does not bound stored high 5, so the program skips left. | Left `[0,5]`. |
| `correctRoot`, `[2,2]` | The global/root maximum is correct, but an invalid descendant left reader 50 misdirects the search. | Right `[2,100]`. |

The reversed projection maps complete keys 0,1,2 to singleton intervals at
10,5,0. Injectivity cannot replace weak low compatibility. In contrast,
`indexed_compatible` proves that compatibility for every lifted lexicographic
key pair through `ULift.down_le`, `Prod.Lex.monotone_fst` and
`IntervalKey.low_le_of_le`; it is not merely a check on the displayed keys.
Deleting one of two keys projecting to `[2,8]` leaves the other key, point 8
and interval query `[8,8]` present.

For the guard comparison, the checked low-ordered example establishes equal
final answers with different choices. The explanatory general reason is that
a divergent empty-left threshold under canonical bottom structure forces the
query low to bottom. A root miss then puts the query high below the root low;
weak ordered lows put all right lows still higher. Thus the right subtree
cannot supply an overlap either, irrespective of its caches. This explanation
does not claim an exported general guard-removal equivalence theorem. The
implemented program remains the guarded source recurrence.

For negative endpoints, empty reads actual bottom rather than finite zero.
Across the original, inserted and restored states, points 0 and 2 have answers
`[false,true,false]`; the restored maximum is again finite -1. The existing
update theorems establish restoration, and the new search tables consume their
valid states through the full correctness specializations.

## Scope and integration boundary

The generic contract owner imports only the shared set contract and interval
geometry. The concrete contract depends on the existing update refinement,
membership bridge and new overlap theorem. Point search depends on overlap
search, while overlap search does not depend on the concrete update contract.
The example import added to `SquareApplications` makes every new library owner
reachable without altering the existing import families.

Candidate-specific guarded builds, safe-root audits, complete elaborated-type
inspection and independent reviews are recorded outside this source note.
Focused validation does not establish the separate receiving union or its
whole-library build/exhaustive audit. The receiving integration must retain the
carried shared owners and both aggregate import families, not transfer only
these new leaf modules.

C05-085–090 still concern balanced augmentation, the sweep-line application and
their cost claims; C05-091–094 concern distance. This contribution makes no
balance, asymptotic, allocation, physical-sharing, runtime benchmark or
all-books completion claim. The remaining canonical rows and later chapters
retain their existing owners.
