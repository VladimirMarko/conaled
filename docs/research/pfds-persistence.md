# PFDS Chapter 2: immutable versions and shared representations

Historical checkpoint and local-ticket references in this account resolve through
the [preserved PFDS records](../history/textbooks/checkpoint-012/books/pfds/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This implementation record covers the published book's complete persistence
chapter, printed pages 7–16, including Exercises 2.1–2.6. Source identities and
the wider request are recorded in [the reconstruction scope](pfds-reconstruction.md)
and [the union ledger](pfds-union-coverage.md). The book's persistence exercises
have no corresponding exercise chapter in the thesis. Thesis Chapter 2 concerns
lazy streams and belongs with book Chapter 4; the thesis's trace/debit analysis
belongs with book Chapters 5–6. These later obligations remain open.

**The complete implementation is integrated; acceptance is pending.** Focused
compilation establishes the developments identified below. Whole-chapter acceptance requires
the final combined candidate, complete build and exhaustive audit, matching
verification record, final verification, and both independent review axes.
The local ticket and review records travel with recovery checkpoints; this
document does not replace their acceptance evidence.

## Interfaces and observations

[`AbstractStack`](../../Applications/Sequences/AbstractStack.lean) separates
`Ops` from `Laws`. The five operators are empty, emptiness, cons, head and tail;
the laws relate an implementation to ordinary finite lists. The relation may
carry a validity invariant and need not be a chosen total decoder. `lists`
uses Lean's lists; `custom` uses a separate inductive `Stack`. The same append
theorem applies to both implementations.

The generic `appendRun` calls only stack operators. Its fuel is an explicit
termination bound: `appendRun_correct` proves that any bound at least the
observed left length suffices, and yields the ordinary concatenation. Its
measure is exactly `4*n+1` primitive operator invocations, counting the final
emptiness test. This measure is distinct from fresh list cells. The direct
pattern-matching implementation is related to both standard concatenation and
the generic traversal by `appendDirect_eq` and `lists_appendRun`.

The existing `Relational.RelSquare` supplies composition. `appendSquare` and
`headSquare` compose to an observed append/head client; the connected cases in
[`Examples.AbstractStack`](../../Examples/AbstractStack.lean) instantiate the
generic laws at both realizations. Empty tail failure and successful singleton
tail removal remain different results.

[`AbstractSet`](../../Applications/Search/AbstractSet.lean) likewise separates
empty/insert/member operators, an independent membership observation and a
validity predicate. `Laws.insertMany_observe` reuses the existing reachable
list-fold fusion theorem. `member_from_empty` is a reusable client theorem for
an arbitrary valid set realization, not a separate proof for each tree.

[`OrderedMap.Interface`](../../Applications/Search/OrderedMap/Interface.lean)
specifies empty, bind and optional lookup. Its laws refine a map to a
key-to-optional-value function; a repeated binding replaces the previous value.
The generic `bindAll` client and its lookup theorem reuse those laws. Payloads
have no ordering or equality requirement. The concrete key-order invariant
belongs to the tree realization, not to the abstract operators.

## List persistence and the signed source index

The [shared-list prerequisite](pfds-shared-persistence.md) describes the cell
model, actual traversals, retained old roots, copied-prefix identity and the
suffix reachability proof. It reuses `Durability.Heap` and `Extends` without
assuming crashes, durable writes or a physical allocator implementation.

For a left operand of length `n`, append allocates exactly `n` cells, performs
`n+1` structural visits, and reaches the exact old right root after the copied
prefix. For a successful natural-index update at `i`, the corresponding counts
are `i+1`; the old version and the untouched suffix remain available. Suffix
enumeration observes `List.tails` in order, including empty, and returns roots
of the actual original tails. Its closed, distinct reachable-root enumeration
justifies the `2*n+1` result-space model: `n` shared element cells and `n+1`
outer result-list cells. Equal suffix values alone would not justify that count.

[`IntegerUpdate`](../../Applications/Sequences/SharedList/IntegerUpdate.lean)
accounts for the source's signed integer index. `updateIntegerValue` is direct
list recursion; `updateIntegerRunFuel` follows heap links and decrements the
integer at each step. For nonnegative inputs the entire measured execution
equals the existing natural-index traversal, including raw fuel behavior.
For every negative index on a valid list, the execution reaches empty and
fails after `n+1` visits. There is no preliminary negative-index shortcut.
`updateIntegerRun_correct` and `updateIntegerSquare` relate all signed inputs
to the direct value specification. The cases in
[`Examples.SharedListIntegers`](../../Examples/SharedListIntegers.lean) include
two negative indices and a successful update with retained suffix identity.

These are mathematical integers and explicit unit measurements. They do not
specify finite-machine integer overflow or the cost of arbitrary-precision
integer arithmetic.

## Ordered values and primitive comparisons

[`OrderedTree.Basic`](../../Applications/Search/OrderedTree/Basic.lean) reuses
Mathlib's node-valued `BinaryTree`. `Contains` means occurrence anywhere in the
tree, independently of directed search. `OrderedBy` requires strict key bounds
on every descendant, together with recursive validity of each subtree.
`Ordered` specializes it to the identity key. The ordered element interface is
Lean's lawful `LinearOrder`, so equality and less-than decisions agree.

The baseline `memberRun` charges each executed less-than test: one on a left
step, two on a right step or equality, and none at empty. Its correctness needs
the search invariant; its comparison bound is at most twice the node-height.
`insert` preserves that invariant and changes independent membership by adding
exactly the requested element. The finite-content development proves that the
inorder entries are strictly sorted and duplicate-free, with length equal to
the unfolded node count.

[`OrderedTree.Candidate`](../../Applications/Search/OrderedTree/Candidate.lean)
implements candidate-carrying membership, aborting insertion and the combined
candidate/abort insertion. Candidate search uses one less-than test per
visited node and at most one final equality, giving the exercise's `d+1`
comparison bound for node-height `d`. Correctness carries an explicit lower
bound invariant for the candidate. Empty search with no candidate uses zero
comparisons. The combined insertion is a single algorithm satisfying the
comparison and duplicate-abort contracts together.

The [`Comparison`](../../Applications/Search/OrderedTree/Comparison.lean)
development supplies valid right spines of arbitrarily large height and exact
baseline/candidate counts. These trees also have height equal to their size;
the chapter's unbalanced search trees do not acquire logarithmic height merely
from being ordered. Concrete cases and abstract-set clients are connected in
[`Examples.OrderedTree`](../../Examples/OrderedTree.lean).

## Actual tree roots and path copying

[`SharedTree.Basic`](../../Applications/Search/SharedTree/Basic.lean) reuses the
shared-list fresh-cell allocator with a tree label and left root in the
payload, plus the right root. `Represents` independently unfolds a root as a
binary tree. Child references point backwards; this supplies sufficient
frontier fuel and permits sharing without cycles in this representation.
It is not the later execution-history model, which has different graph rules.

[`Path`](../../Applications/Search/SharedTree/Path.lean) defines heap-following
by a sequence of left/right choices and the generic key-directed
`searchPathBy`. `Rebuilds` records each copied ancestor's label and the exact
unchanged opposite child root. Its `off_path` theorem establishes address
equality for probes diverging at an ancestor. `follow_mono` separately retains
successful observations of old roots under heap extension. The empty-path
constructor leaves the modified focus unspecified: it does not by itself
prove freshness or preservation of that focus's child roots.

[`Ordered`](../../Applications/Search/SharedTree/Ordered.lean) performs actual
heap traversal and allocates on successful recursive return. It does not first
decode a value and rebuild it. `insertRun_correct` proves the independent pure
insertion result, heap extension, the exact allocation frontier and `Rebuilds`.
Its profile keeps three measures separate: primitive comparisons, structural
visits and freshly allocated cells. For search-path length `p`, visits are
`p+1`; allocations are `p` on a directed match and `p+1` on a miss. The
comparison count equals the independent baseline `memberRun` count.

The ordinary equal-key branch returns its matched subtree, while successful
return through a strict ancestor still copies that ancestor. Thus insertion of
an existing key may yield the same unfolded value at a different root. The
connected three-node example inserts a duplicate below the root and proves
one allocation and a new root. Inserting an absent key instead proves the
three comparisons, three visits, three allocations, retained old version and
unchanged opposite subtree address calculated independently from the traversal.

[`OrderedObservation`](../../Applications/Search/SharedTree/OrderedObservation.lean)
exposes `insertSquare` on all represented tree values and separately combines
physical execution with ordered-set correctness. The generic optional
root-value observer in `SharedTree.Observation` preserves the outer execution
failure distinction. Its composition is checked in
[`Examples.SharedTreeOrdered`](../../Examples/SharedTreeOrdered.lean).

[`OrderedTerminal`](../../Applications/Search/SharedTree/OrderedTerminal.lean)
supplies the stronger duplicate contract. Following the search path from the
new root reaches the exact old matched nonempty root. The old version remains
valid, and only strict ancestors are allocated. The generic path-append law in
[`PathEndpoint`](../../Applications/Search/SharedTree/PathEndpoint.lean) extends
endpoint identity to every further descendant observation in the final heap,
including failure beyond an empty child. The connected
[`SharedTreeTerminal` cases](../../Examples/SharedTreeTerminal.lean) use a
duplicate below a copied ancestor whose matched subtree has a nonempty child;
the endpoint and that child's address both survive. This does not infer
endpoint preservation from the unconstrained `Rebuilds.here` case.

### Aborting and combined insertion

[`Optimized`](../../Applications/Search/SharedTree/Optimized.lean) executes both
exercise variants on actual heap roots. The raw result distinguishes malformed
input or fuel exhaustion, a duplicate abort, and successful insertion. Valid
represented inputs with sufficient fuel exclude the first outcome. Recursive
ancestors allocate only after success; a single public `handleAbort` maps the
duplicate outcome to the exact original store/root pair.

`insertAbortRun_duplicate` and `insertCandidateRun_duplicate` therefore state
zero allocated cells and equality with the original state, not just equality
of unfolded values or final frontier numbers. The absent-input theorems prove
the independent insertion result, ordering, exact frontier increase and
retained off-path addresses. The retention theorem for the combined algorithm
also gives its `height+1` comparison bound on that same execution. The combined
candidate path continues to empty even when an equal key was visited, so its
structural-visit count can differ from baseline early-match insertion.

[`OptimizedObservation`](../../Applications/Search/SharedTree/OptimizedObservation.lean)
relates both physical wrappers to their independent pure algorithms and
composes them with the shared optional root-value observer. The
[`SharedTreeOptimized` cases](../../Examples/SharedTreeOptimized.lean) establish
exact duplicate counts, invalid-root failure, absent insertion with a retained
opposite child address, and the composed observations. A comparison bound does
not assert a strict improvement on every individual call.

## General shared constructors: Exercise 2.5

The complete and nearly balanced constructors deliberately use general trees:
repeating one label at internal nodes does not satisfy a strict set invariant.
Their size is the number of nodes in the unfolded value, not allocated cells.

[`Complete`](../../Applications/Search/SharedTree/Complete.lean) constructs a
tree of natural depth `d`, with empty depth zero. The value has `2^d-1` nodes.
The actual execution allocates exactly `d` cells and makes `d+1` structural
visits. At each nonempty level the stored left and right roots are equal; both
refer to the one recursively constructed subtree. All old heap observations
remain valid.

[`Balanced`](../../Applications/Search/SharedTree/Balanced.lean) defines
`SizeBalanced` recursively: every node's two unfolded child sizes differ by at
most one. This is stronger than checking only the root or only heights.
`create2Value_fits` constructs a pair with sizes `n` and `n+1`, uniform payload,
and recursive size balance. `create2Run_correct` relates the two actual roots
to those values, proves extension, and counts exactly
`2*log2(n+1)+1` fresh cells and `log2(n+1)+1` structural visits. The separate
stored-child theorem identifies the actual reuse of recursively obtained roots.

At `n=0` the pair contains empty and a singleton, so one cell is allocated.
Selecting only the first result does not retroactively remove its companion's
allocation. The theorem counts allocated cells and does not claim minimal
reachable live space. `balancedRun_correct` gives the requested first tree
of exactly `n` nodes.

[`Resources.SharedTree`](../../Applications/Resources/SharedTree.lean) applies
the existing `Resources.isBigO_of_nat_bound` to explicit visit-plus-cell work.
It states linear complete-tree work and logarithmic paired construction with
the `n+1` small-size convention and the eventual logarithmic relation.
[`Examples.SharedTree`](../../Examples/SharedTree.lean) connects the contracts
to concrete size/depth cases, retained roots, actual stored child addresses and
composed allocation observations.

## Finite maps

[`OrderedMap.Basic`](../../Applications/Search/OrderedMap/Basic.lean) uses
key/value node payloads ordered only by the key projection. Its independent
`observe` searches whole-tree content; directed lookup agrees under the key
invariant. Binding preserves ordering and implements overwrite. A valid-tree
subtype realizes the abstract map laws, and the finite-domain theorem bounds
successful keys by a finite tree traversal. The examples include function
payloads, stored optional-none versus a missing key, successive bindings and
composed lookup. No payload equality is needed to state or prove these laws.

[`SharedTree.Map`](../../Applications/Search/SharedTree/Map.lean) performs actual
key-directed lookup and binding. Its valid-input execution theorem derives
sufficient fuel from the same backward-reference invariant. Binding uses
`path.length+1` structural visits and fresh cells, including the changed
endpoint. Its element-comparison count agrees with the independent key-only
search profile. Heap extension preserves every old version.

`Rebuilds` preserves opposite children at copied ancestors; `WrittenAt`
additionally records the new endpoint's binding and its two unchanged child
addresses. The latter matters for replacement at the root, where there are no
strict ancestors and the divergence condition would be empty. The concrete
root-replacement case has two nonempty children and proves that both exact
addresses survive, while old-root lookup still returns the earlier payload.

`bind_lookup` establishes the all-query update law for the actual execution.
`optionalLookupSquare` and `bindThenLookupSquare` compose the physical bind
with lookup while retaining each optional boundary. The connected cases in
[`Examples.SharedTreeMap`](../../Examples/SharedTreeMap.lean) distinguish a
stored optional-none result from a missing key and retain an unaffected
subtree during a deeper replacement.

The source's empty/missing exceptions are represented by optional failure.
Nested optional payloads retain the distinction between a successful stored
`none` and an absent key. This is a specified translation of the data-structure
interface, not a semantics for the whole Standard ML exception runtime.

## Contextual material

The destructive-append illustration motivates aliasing and ownership. Garbage
collection, imperative persistence techniques and historical attributions are
contextual material in the source ledger. Mentioned extensions such as set
deletion, enumeration or rank selection do not specify additional algorithms
in this chapter. No theorem here imports all results of a cited external paper,
models collection/reclamation, or proves a running-time property of Lean's
function-valued heap implementation.
