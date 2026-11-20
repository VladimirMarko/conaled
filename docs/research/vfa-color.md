# VFA Color: finite tries and graph coloring

This note records the CTB-99 finite foundation, CTB-100 preliminary lists,
CTB-101 graph selection, CTB-102 coloring semantics, CTB-103 normalized paths,
CTB-104 finite-trie primitives, CTB-105 finite traversals, and the complete
program resource implementation proposed as CTB-106. Source correspondence,
mathematical implementation and acceptance are distinct records.
The definitive bounded review/qualification status is in the checkpoint CTB and
BOOKS records. Receiving integration-quality review and whole-library acceptance
remain separate. Development compilation alone is not source qualification.

## Source and requirement identity

The complete chapter requirement owner is
[the frozen Color specification](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1017-Color.md),
77,948 bytes, SHA256 `8b69472e3eb9a0157375d2e47292af07ba0eaf098b5a22d418ea0021cd0ceed7`.
All its graph, related-list, resource, command, exercise and counterexample
requirements continue unchanged. Its former Tables locations were provisional;
the accepted Trie owner is now `Applications/Search/PositiveTrie`.

The primary is [VFA 2.1 Color](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Color.html):
602 lines, 23,243 bytes, SHA256
`67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370`.
The exact release archive has SHA256
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
Its unchanged inventory contains 53 declaration records, 14 standard exercises,
five module aliases and 35 pedagogical commands. The entire primary and canonical
plan were read; those totals are the full chapter denominator, not this
increment's completion count. The existing [VFA MIT notice](../licenses/vfa-MIT.txt)
is retained. Downloaded research copies are excluded from the checkpoint.

The used Rocq Stdlib provider realization is V9.0.0 at immutable commit
`fda356e01346f7766b282ef9f44080cce2be23b3`. VFA permits that version or later;
the chapter archive itself does not pin one unique Stdlib checkout. These exact
providers supplement the abstract APIs and prescribe traversal/choice behavior.

| Provider | Bytes | SHA256 |
| --- | ---: | --- |
| `theories/Structures/OrderedTypeEx.v` | 15,487 | `e30f31413cf5a544c1f997b02bb5ccd1f69e215c75b761fc12b184ec9af41ed5` |
| `theories/FSets/FSetPositive.v` | 38,480 | `596ebe108c8baa96cbe12670e6275355a3d4a48e91898a173d8a9f26802adb9a` |
| `theories/FSets/FMapPositive.v` | 33,802 | `49be1b1d115a068510b265581271421ec2780265cf0b63fa4b947b57a6b2005d` |
| `theories/Sorting/SetoidList.v` | 32,179 | `f8839b0249f9a260358445d93b300fd55c502dc4b43c962a72496cbc2a903b32` |
| `theories/Sorting/Sorted.v` | 5,111 | `5dcad96e1cf395d7783d8663fa0435756eb344bf84262544e3458db77d013e1a` |

Provider notices and the exact upstream LGPL2.1 license are preserved in
[rocq-stdlib-notice.md](rocq-stdlib-notice.md). The bit-order, carrier, lookup,
add, pruning erase, difference, prefix, enumeration, cardinality, choice, map
and fold sections used here were read directly. The exact related-membership,
pointwise-list, sorted-uniqueness and filtering sections of SetoidList, and the
complete Sorted definitions/bridges, were also read directly. Unused Stdlib operations are
not added to the coverage denominator. Source correspondence is not a certified
Rocq-to-Lean compiler.

The required [Appel2016 slides](https://www.cs.princeton.edu/~appel/Color.pdf)
were reacquired: 72 pages, 764,823 bytes, SHA256
`37238a67dda3adc00669e1a304634831b00e527d3fd0518798a9a639605cc5ee`.
All slide text was read, and slides9,19,38,39,63,71 were rendered and visually
inspected. The high-degree fallback heuristic on slides9–20 differs from the
chapter's stop-when-no-low-degree-node program on slide63. Slide71's all-bindings
palette prose is stronger than its displayed edge-guarded predicate; the two
claims are established separately by the coloring semantics. The suggested register-allocation
paper is context, not a proof dependency or a claim of implementing a coalescer.

## Maintained owners and reuse

| Owner | Contribution |
| --- | --- |
| `Applications/Numerals/PositivePaths.lean` | Explicit bit order, append and reversed-prefix laws on existing PosNum. |
| `Applications/Search/PositiveTrie/Finite.lean` | Sparse optional maps, Boolean sets, accepted insertion adapters, pruning erase, difference, cardinality, value map and source choice. |
| `Applications/Search/PositiveTrie/Enumeration.lean` | Actual source traversals/folds, canonical observation proofs, Finset/Finmap bridges, erase/filter laws and ordered-fold domain. |
| `Examples/PositiveFiniteTries.lean` | Connected presence, padding, ordering, choice, fold and exact source-map cases. |
| `Applications/Sequences/RelatedMembership.lean` | Generic existential related membership, filtering, quotient bridge and canonical sorted-list theorem without totality. |
| `Applications/Search/PositiveTrie/Relations.lean` | Source key/equality view, arbitrary pair-list results, adjacent sortedness and exact source removal/Forall₂ adapters. |
| `Examples/ColoringRelations.lean` | Mod10 source cases, generic theorem application, hypothesis counterexamples, arbitrary function payloads and reverse-fold composition. |
| `Applications/Graphs/Coloring/Graph.lean` | Raw graph view, finite domain/adjacency observation, actual predicate fold and whole-map vertex removal. |
| `Applications/Graphs/Coloring/Selection.lean` | Cardinality-founded source selection, exact residual trajectory, later-neighbor bound and conditional totality. |
| `Applications/Graphs/Coloring/Construction.lean` | Source edge insertion and right-fold graph construction, with exact domain/edge laws. |
| `Examples/ColoringSelection.lean` | Exact source palette/graph, selection and residuals, plus padding, directed, self-loop, absent-removal and early-stop boundaries. |
| `Applications/Graphs/Coloring/Coloring.lean` | Optional assignments, actual neighbor-color fold, available choice, exact update branches, original-graph right fold and finite observation transport. |
| `Applications/Graphs/Coloring/Correctness.lean` | Literal edge-guarded compatibility for arbitrary lists, including repeats, and the separate unconditional palette invariant. |
| `Applications/Graphs/Coloring/Support.lean` | Successful lookup on supported keys, finite image bound, actual suffix availability, exact selected support and conditional total coloring. |
| `Applications/Graphs/Coloring/SimpleGraph.lean` | Domain-preserving graph observation and finite palette-valued SimpleGraph colorings from successful lookup. |
| `Examples/ColoringCorrectness.lean` | Exact source coloring, finite graph client, optional/overwrite/repeat cases, directed/self-loop failures and an explicitly colorable high-degree core. |
| `Applications/Resources/PositiveTrie/Pruning.lean` | Actual optional/Boolean pruning erasure and simultaneous difference, with separate entries, prune attempts and emitted nodes. |
| `Applications/Resources/PositiveTrie/Cardinality.lean` | Measured TreeFold cardinality with exact traversal/addition counts and prices at actual addition operands. |
| `Applications/Resources/PositiveTrie/ValueMap.lean` | Actual returned payload mapping, separate outer counts and ordered callback observations, and reached-payload work bounds. |
| `Applications/Resources/PositiveTrie/Choice.lean` | Actual root/left/right choice, skipped branches, successful wrappers and raw versus normalized traversal bounds. |
| `Examples/PositiveFinitePrimitiveWork.lean` | Fifteen primitive case groups, public-law clients, operand/trace distinctions, tight normalized paths and raw counterexamples. |
| `Applications/Resources/WorkloadBounds.lean` | Restricted command/state invariant and weighted-work laws for the existing runner. |
| `Applications/Resources/PositiveTrie/{Traversal,MapFold,SetFold,KeyMap,Enumeration}.lean` | Actual prefix-aware traversals, conditional outer bounds and ordered callback bridges. |
| `Examples/PositiveFiniteTraversalWork.lean` | Sixteen traversal groups, an additional command-domain boundary and quantified raw/normalized families. |
| `Applications/Resources/ListExecution/MeasuredFold.lean` | Actual measured right fold, exact list counts, ordered runner recovery and the earlier pure-fold tariff. |
| `Applications/Resources/Coloring/{Model,Invariants,Helpers,Construction}.lean` | Explicit cost projections, actual primitive adapters, normalized bounded states and graph/palette construction. |
| `Applications/Resources/Coloring/{Selection,Coloring,Bounds,Export}.lean` | Actual selector and coloring, exact trajectory counts, constant64 polynomial and charged exports. |
| `Examples/{ColoringResourceHelpers,ColoringProgramWork}.lean` | Eighteen complete-program groups, original semantic clients, source bill1058, pipeline1584 and the fixed long-key BigO family. |

No new positive-number, tree, general finite-map or set carrier is introduced.
`SparseMap A` abbreviates `BinaryTree (Option A)` and `KeySet` abbreviates
`BinaryTree Bool`. `Numerals.PositiveKeys.numeric` retains unshifted numeric
labels. The prior shifted encode/decode convention remains unchanged.
`Search.PositiveTrie.ins` and its same/other lookup laws supply both additions.
`BinaryTree.get`/`getOrElse` and `BinaryTree.map` remain the shared primitives.

Map payloads range over arbitrary `Type u`. No equality, order or Inhabited
structure is required. Fold accumulator universes are independent of payload
universes. Finmap uses decidable equality only for PosNum keys. Every semantic
law applies to arbitrary finite raw trees, including empty padding. The later
resource normalization predicate is not hidden in an operation's type or a
semantic theorem premise.

## Exact operation and observation contracts

### Paths and orders

`PositivePaths.BitLt` compares the low outer bit first, with bit0 before one
before bit1 and recursion when tags agree. Irreflexivity, transitivity,
asymmetry and ordinary-equality congruence are proved. It is explicit and does
not replace PosNum's numeric order. Prefix append preserves and reflects it;
append is associative with one as identity and is injective in its suffix.
`reverseAppend`, `reverse`, reversal of append, involution and injectivity
justify the set provider's reversed-prefix convention. No comparator or
numeric-conversion cost is claimed by these value laws.

### Presence, insertion and pruning

`SparseMap.find` is accepted lookup with default none and is proved equal to
flattening `BinaryTree.get`. Thus absence of a tree node and an internal none
payload both mean no binding, while `some emptyAdjacency` remains a binding.
The full `find_add` and functional-update equations retain arbitrary values.
Set addition has Boolean membership `decide(query=written) || priorMembership`.

`prune` collapses only an unoccupied node with two structurally empty children.
Erasure at one clears the payload and prunes; erasure at bit0/bit1 recursively
erases the corresponding child and prunes. This reproduces the provider's
special-case map removal on every raw tree. It does not normalize an arbitrary
padded sibling. `find_erase`/`mem_erase` remove exactly the queried key and leave
every other observation unchanged. The padded-map example retains nonempty raw
padding after root erasure while its ordered elements remain empty.

Set difference simultaneously descends both trees. Empty left gives empty;
empty right returns the left raw tree; paired nodes prune the Boolean
`left && !right` and recursive children. `mem_diff` proves exactly that Boolean
membership formula, with no validity or normalization premise.

### Occupied cardinality and value mapping

Cardinality traverses the actual tree: nil gives0, an absent/false node adds
its child cardinalities, and a present/true node adds one. It is not raw node
count and is not a cached-size accessor. The erasure theorem says

`cardinal(erase key tree) + presence(key,tree) = cardinal(tree)`.

Successful optional lookup or true membership yields the add-one equality and
strict decrease; absence yields unchanged cardinality. There is no unjustified
strict-decrease claim for absent keys. Enumeration length and finite-domain
cardinality are separately proved equal to this occupied count.

Value-only map is `BinaryTree.map (Option.map f)`. Lookup becomes Option.map,
ordered entries retain every key while mapping each value, and occupied keys
and cardinality are preserved even if all values become equal or default.
`mapiFrom_key_ignore` proves raw-tree equality to the provider's key-indexed,
forward-prefix mapi when the supplied function ignores its key. The two routes
perform different key-building work; raw output equality is not cost equality.

### Source traversal, canonical order and finite observations

Map `elementsFrom` carries a forward prefix and appends the left output before
the optional root and right output. Set `elementsAcc` carries a reversed prefix
and an explicit tail; its recursive equation visits the right subtree to build
the tail, then the left subtree, producing the same left-root-right output.
The respective bridges to `rawEntries` and `rawKeys` are generalized over every
prefix and tail. These structural lists are proof observations, not a silent
replacement for the executable provider traversal.

For every raw map, `(key,value)` belongs to elements iff `find key = some value`.
For every raw set, key belongs to elements iff Boolean membership is true.
Both enumerations are Pairwise bit-sorted; map ordering uses only first
components. Projected map keys and set elements are nodup. Values retain their
literal equality and need no comparison decision.

The strict key relation's irreflexivity supplies nodup. Canonical list equality
uses `List.Pairwise.eq_of_mem_iff`: local strict-relation antisymmetry follows
from asymmetry by contradiction. This valid uniqueness argument requires no
totality and no order/equality instance on map payloads. It does not claim that
an impossible assumption establishes a usable data structure: actual raw trie
enumerations satisfy the sortedness assumptions, as proved by tree induction.

`KeySet.observe` is the element Finset. `SparseMap.keys` is the Finset of
projected entry keys. `SparseMap.observe` uses `Finmap.keysLookupEquiv` with the
actual optional lookup and proved finite support. Its lookup and keys equations
are explicit; add and erase commute with Finmap insertion/erasure. Value mapping
preserves keys. Finset add, erase and difference equations are proved.
Observational equality identifies these finite observations and their canonical
lists. It does not identify differently padded raw trees.

Elements after erasure are exactly the prior ordered list filtered by key
inequality, including unchanged values for maps. Both unconditional equations
and source member/domain-premised corollaries are present. The filter uses
ordinary key equality, not numeric order, bit-order equality approximation or
payload equality.

### Fold order, domain and deterministic choice

Map and set folds follow their actual forward/reversed-prefix recurrences.
`foldFrom_eq` and `foldl_elementsAcc` prove equality to a left fold over the
ordered elements for arbitrary callbacks and accumulators. The generalized set
proof retains both the output tail and seed. No callback commutation is assumed.
`Finmap.foldl`, which needs a commutation law, is not used as a replacement.

`SparseMap.domain` is the source map fold inserting every occupied key into an
initially empty Boolean trie. The fold-to-finite-observation law proves its
Finset observation equals keys, membership iff successful lookup, occupied
cardinality equality, and exact elements equal the projected map elements.
These laws include stored empty adjacency sets.

`KeySet.choose` checks a true root first, then a left result wrapped in bit0,
then a right result wrapped in bit1. Success implies membership; none is
exactly empty finite observation. `choose_ext` proves identical deterministic
choice from equal membership on arbitrary raw trees, including padding. This
is not bit-order minimum: the actual set{1,2} chooses1 while its bit-sorted
list is[2,1].

## Related membership and the preliminary list lemmas

`Sequences.RelatedMembership.RelatedMem R query xs` means that there is an
actual member `value` of xs with `R query value`. The query is the relation's
left argument. `SameRelatedMembers R xs ys` says this proposition agrees for
every query; it does not preserve multiplicities or positions. Source eqlistA
is existing `List.Forall₂`. Ordinary equality specializes related membership
to ordinary list membership and Forall₂ to literal list equality.

The two source mod10 cases are retained:27 is related to17 in[3,17,2], while
[3,17] and[7,3,27] expose the same residue classes despite different lengths.
The latter lists are explicitly proved neither a permutation nor pointwise
related lists. A separate positive case applies the generic theorem to the
residue-sorted lists[3,17] and[13,7], obtaining pointwise modular relatedness;
their literal list values differ.

### The exact sorted-equivalent-lists theorem

`forall₂_of_isChain_of_sameRelatedMembers` assumes an equivalence R, an
irreflexive transitive relation S, compatibility of S with R in both arguments,
adjacent S-sortedness of both lists, and equal related membership. It proves
`List.Forall₂ R`. No totality, linear order, decidable equality, payload order
or inhabitance premise is added. The source's displayed theorem has these
strict-order assumptions even though surrounding prose twice says total order.

The proof uses the quotient by R. Compatibility makes the lifted order
well-defined; strictness supplies the local Irrefl/Antisymm facts used by
Mathlib's `List.Pairwise.eq_of_mem_iff`. Independently proved pairwise
sortedness and quotient membership yield equality of the two quotient lists.
The existing Forall₂/map and quotient exactness lemmas recover pointwise R.
The local antisymmetry instance eliminates incompatible opposite strict
comparisons; it adds no global order instance and no totality assumption.

Source Sorted's constructor requires only the first element of the tail to
follow the head (HdRel), so its direct Lean meaning is `List.IsChain`.
`isChain_iff_pairwise_of_trans` explicitly supplies the transitive bridge to
all-pairs order. `isChain_filter_of_trans` uses that bridge and Pairwise.filter;
it needs transitivity but no predicate congruence. By contrast,
`relatedMem_filter` needs predicate congruence to characterize filtering by
the predicate at the query, rather than merely at its related witness. It
requires no equivalence or order assumption. Equality congruence follows from
`congrArg` for every Boolean predicate.

### Positive keys and arbitrary payloads

`PositiveTrie.Relations.Key` and `KeyEq` are only source-view abbreviations for
PosNum and ordinary equality. The two checked identity statements preserve
the source carrier/relation demonstrations; no new representation is created.
Bit-sorted key lists specialize the generic theorem and its filter law.

`EqKeyValue` is the conjunction of key equality and value equality and is
proved literally equal to pair equality. `KeyLt` compares only the first
components with BitLt. It is irreflexive, transitive and compatible with the
pair relation, without a payload equality decision or order. The projected
key membership theorem applies to every pair list, even with repeated keys,
and returns an existential payload witness. `isChain_keyLt_iff` reuses
`List.isChain_map`; this direct projection equivalence needs no transitivity.
The general pair-list canonical theorem consumes the generic relation theorem.

Set/map enumeration now has explicit IsChain and related-member adapters.
The source's `if key=erased then false else true` filter is proved equal to
the accepted `decide(key≠erased)` predicate. Set removal has the exact literal
source-list statement, and map removal has its full Forall₂ key-and-value
statement. Both retain the source membership-premised form alongside the
stronger unconditional finite result. `find_map_eq_some_iff` retains an actual
preimage payload witness even for a noninjective value map. Source cardinality,
strict present-erasure and finite-domain conclusions reuse the048 proofs.
`KeySet.not_mem_nil` supplies the explicit empty-set exclusion.

The arbitrary-accumulator source reverse-fold identity is exactly
`List.foldl_eq_foldr_reverse`; no new fold implementation is introduced.
Its connected decimal example gives123 for the left fold over[1,2,3] and for
the reversed right fold, but321 for the unreversed right fold with flipped
callback. The value-only and ordered finite folds from048 remain unchanged.

### Checked scope distinctions

The connected cases retain four consequential failed generalizations:

- Nonstrict natural order sorts both[1] and[1,1]; their members agree but their
  lengths preclude Forall₂ equality. Strictness prevents multiplicity loss.
- For the universal relation on Bool, queryfalse relates to the retainedtrue
  in[true].filter id although the query predicate isfalse. The query-predicate
  characterization therefore requires congruence.
- Under the universal relation on Nat, strictly sorted[0,1] and[0] have equal
  related membership but different lengths. Strict order alone cannot replace
  compatibility with the chosen equivalence.
- Successor-step order sorts[0,1,2] adjacently but not pairwise; removing1
  breaks adjacent sortedness. The filtering bridge uses real transitivity.

Function-valued pairs have a checked bit-sorted input and instantiate the
canonical theorem without Eq/Ord instances on functions. Distinct functions
at the same key are explicitly incomparable, so a trichotomy premise would
unnecessarily reject this intended setting. Repeated-key lists retain a
payload witness, while equal keys with unequal values fail EqKeyValue.
The exact source-map erase and set erase examples consume the new source
wrappers as well as their independently computed filtered lists.

## Raw graph contracts and source selection

`Graphs.Coloring.Node`, `NodeSet`, `NodeMap` and `Graph` are aliases of the
accepted carriers. `adj` takes the optional binding's empty default, while
`nodes` is the accepted domain fold. `observe` is the existing Finmap
observation after mapping each payload to its finite KeySet observation. It
preserves stored empty vertices. Its extensionality theorem requires both
equal domains and equal adjacency sets; adjacency defaults alone do not
identify a stored isolated vertex with absence. Undirectedness is precisely
edge reversal and NoSelfLoop excludes diagonal edges. Neighbor membership in
the stored domain is derived from undirectedness when needed.

`subsetNodes P` executes the map fold over every actual key and payload. Its
membership theorem is exactly an existential successful lookup with `P=true`.
The subset-of-nodes theorem needs no predicate compatibility, graph validity
or normalization. Transport between equal finite graph observations explicitly
requires P to respect finite adjacency observation. A raw-node-count predicate
distinguishes two observationally equal isolated graphs; the low-degree
predicate respects observation through the cardinality bridge.

`lowDegree K` retains its unused node argument and the executable strict test
`KeySet.cardinal value < K`. `removeNode n g` first erases the n binding, then
maps `KeySet.erase n` over every remaining stored payload. Its exact optional
lookup, adjacency, finite-neighbor and domain equations hold for arbitrary raw
graphs. A successful binding reduces occupied cardinality by exactly one; an
absent binding preserves that count but can still change other adjacency sets.
Separate theorems preserve undirectedness and looplessness under their actual
premises.

`select K` uses well-founded recursion on occupied map cardinality, keeping K
fixed and using the source root-first choice. Some n yields n followed by
selection on `removeNode n g`; none yields the empty list, including on a
nonempty high-degree core. The termination proof consumes the actual chosen
membership and cardinality decrease. The executable algorithm introduces no
fuel, normalization check, symmetry test or extra cardinality scan for that
proof measure. Selection has no repetitions, lies in the original domain,
has length at most its cardinality, and is empty for K=0. Equal finite graph
observations give the same deterministic selection through predicate, choice
and removal congruence.

`removeNodes` is the actual repeated removal of an arbitrary list, including
duplicates and absent targets. Its domain is the original domain minus the
list's finite set, and its edges are exactly the original edges whose two
endpoints are absent from that list. For a split of actual selection into
prefix and suffix, selection on the prefix residual is precisely the suffix.
At each actual step the next vertex is present and currently has degree<K.
For t at most the selected length, the residual cardinality is n−t. The
terminal residual has no eligible binding; it need not be empty.

For an actual split `before ++ node :: after`, original neighbors of node
that occur in after have cardinality<K. This follows from prefix/suffix
disjointness and exact residual restriction, without symmetry, looplessness
or a no-dangling-neighbor premise. The whole original degree need not be<K.
Conditional totality explicitly assumes a graph class closed under the
relevant removals and admitting an eligible vertex whenever its stored domain
is nonempty. An edgeless graph application instantiates these hypotheses for
positive K. No planarity, optimality or uncolorability consequence is inferred
from early stopping.

`addEdge (a,b) g` literally writes at b and then a, with BOTH adjacency reads
from the original g. Equal endpoints create a self-loop. `mkGraph` is the
actual right fold from empty. Exact edge membership is `(a,b) in edges` or
`(b,a) in edges`, and the stored domain consists exactly of input endpoints.
Construction is undirected; distinct endpoints on every input edge ensure
looplessness. Duplicate and reversed insertions agree at finite graph
observation, with no claim of raw-tree identity. Definition/body review retains
the literal read source and fold direction, since finite output observations
alone do not distinguish extensionally equivalent implementations.

## Connected cases and statement assessment

The expected results were worked out before implementation and are retained in
`Examples.PositiveFiniteTries`. Closed kernel reductions check their concrete
data; the observation, erasure, cardinality, fold, choice and domain theorems
connect those calculations to the general interface.

| Case | Independently expected result and connection |
| --- | --- |
| Positive labels | Numeric1<2 but bit-order2<1; append concatenates low-bit paths and reversal twice is identity. |
| Stored empty adjacency | Writing empty at2 returns some empty at2 and none at1, has card1, belongs to domain, and erasure has card0. |
| Generic/function payload | Arbitrary universe-polymorphic payload lookup works; a stored Nat function is observed and applied without function equality. |
| Empty padding | A raw false node has one node but card0, no elements and no choice; it agrees with nil only observationally. |
| Non-normalizing erase | Padded map root erasure can preserve the raw padded tree; enumeration is nevertheless empty. |
| Choice vs minimum | Set{1,2} enumerates[2,1], chooses1, and the chosen key is in the independent finite observation. |
| Noncommuting set fold | Decimal accumulation over[2,1] yields21; reversed or root-first fold order would yield12. |
| Repeated insertion | Adding the same key twice has the same cardinality as one insertion, by the Finset insertion law. |
| Source example_map | Exact nested writes3,9,2 to empty sets yield domain elements[2,9,3] and occupied count3. |
| Map erase/filter | Erase9 yields entries at2,3 with empty values retained; erase absent4 preserves the full ordered entries. |
| Noncommuting map fold | Decimal accumulation over[2,9,3] yields293 through the public fold law. |
| Value collisions | Mapping all three values to false keeps all three keys and occupied count3. |
| Difference/erase | {1,2,3} minus{2,4} observes{1,3}; erase2 has elements[1,3]; absent erase4 preserves card. |

Statement review checks ordinary key equality versus bit/numeric order;
all raw input quantifiers; optional presence versus default values; payload and
accumulator universes; one-way success and exact none equivalences; strict
decrease's actual membership premise; canonical finite equality versus raw
shape; prefix/tail generality and left-fold order. No global axiom replaces a
source signature field. No theorem in this increment claims graph coloring,
normalization bounds, physical allocation, runtime complexity or optimality.
Exact elaborated-signature probes, actual evaluation output and the exhaustive
focused proof audit accompany the immutable candidate outside the source note.

The graph-selection examples use the exact source palette[1,2,3] and edges
[(5,6),(6,2),(5,2),(1,5),(1,2),(2,4),(1,4)]. The kernel checks domain
[4,2,6,1,5] and selection[4,1,2,6,5]. In vertex order[1,2,4,5,6], original
degrees are[3,4,2,3,2]; in bit-domain order they are[2,4,2,3,3]. Residual
cardinalities are[5,4,3,2,1,0], and ordered candidate sets are[4,6],[6,1],
[2,6,5],[6,5],[5],[]. The second choice is1 although its candidate list
starts with6. Source construction theorems establish graph symmetry and
looplessness, and general residual/current-vertex/later-neighbor theorems
connect the calculated trajectory to the library interfaces.

Stored isolated1 is selected at K=1 while an absent vertex has the same
adjacency default and a different map observation. Empty padding can increase
raw nodes without increasing occupied cardinality. Removing absent2 from
the graph storing only1->{2} preserves cardinality1 but removes the edge.
The directed graph1->{2},2->empty selects[2,1] at K=1; the one-vertex self-loop
selects[1] at K=2. A four-cycle has degree2 everywhere and stops immediately
at K=2, retaining its nonempty residual. The coloring semantics below supply
the corresponding colorability and edge-correctness counterexamples. Repeated/absent
removal, equal-endpoint insertion and duplicate/reversed finite observations
are separately connected to their general laws.

## Faithful coloring and complete semantic contracts

`Graphs.Coloring.Assignment` is the existing optional sparse map of positive
colors. There is no color for an absent binding. `colorsOf f s` runs the actual
ordered set fold, looking up each visited node and inserting only a successful
color. The seed-general `mem_colorsFold` proves the exact invariant; its empty
seed specialization gives

```
mem c (colorsOf f s) = true ↔ ∃ n, mem n s = true ∧ find n f = some c.
```

The source introduction exercise is `in_colorsOf`. Different neighbors with
the same assigned color contribute one set member; an absent neighbor contributes
nothing. The connected case with neighbors1,2,4 and assignments1:3,2:3 has exactly
one used color and two bound neighbors.

`availableColors palette g n f` is the source difference between the palette
and colors of the original `adj g n`. `color1` chooses by the accepted root-first
policy. A successful choice overwrites n; failure returns the entire f unchanged.
The some/none equations and `find_color1` retain both behaviors exactly.
`chosen_color_facts` proves membership in the palette and exclusion from used
neighbor colors; `chosen_color_ne` connects that exclusion to any actual adjacent
successful binding. No fresh-node assumption occurs. The failed-choice case
with palette{1}, edge1→2 and assignments1:7,2:1 preserves the old7. If2 is absent
from the coloring, the same node update succeeds and overwrites7 with1.

`colorList` is the right fold from empty and `color` supplies the actual
`select (cardinal palette) g` list. The graph argument remains g through every
step. `colorList_eq_reverse_foldl` makes the reverse processing order explicit.
Available sets, single steps, list folds and the complete program respect the
finite palette, graph and assignment observations. These transport results use
lookup equality, set membership and choice extensionality; they do not identify
different raw representations. The padded isolated case instantiates the full
program transport and unconditional support result.

### Two distinct correctness conclusions

`ColoringOK palette g f` preserves the source predicate literally. For every
edge i→j, successful colors at i lie in the palette, and any two successful
endpoint colors differ. The edge premise guards both clauses. Thus arbitrary
out-of-palette assignments at isolated vertices can satisfy this weak predicate.
The isolated assignment1:7 with the empty palette is a checked separating case.

`coloringOK_color1` proves preservation for every already-compatible assignment
under precisely `Undirected g` and `NoSelfLoop g`. It handles overwrites: the
new left endpoint uses exclusion, the new right endpoint uses the reversed edge,
and equality of both endpoints contradicts looplessness. Existing bindings
elsewhere use the previous invariant. `coloringOK_colorList` therefore covers
every finite list, including repeated vertices, without degree or selection
premises. `color_correct` specializes it to the actual selection computation.
On one undirected edge, the repeated list[1,2,1] is checked through this theorem
and yields entries[(2,2),(1,1)].

`AllPalette palette f` separately quantifies over every successful binding,
including isolated ones. Its actual update/fold invariant yields
`allPalette_color` for every raw graph, without symmetry or looplessness.
The weak source predicate and this stronger result are not conflated.

### Exact selected support and totality conditions

`valueAt` obtains the actual `Option.get` value only for a key with evidence of
successful lookup. `find_valueAt` and `valueAt_eq` bind that value to the original
map; no default is introduced. `observe_colorsOf_image` identifies used colors
with the image of the finite intersection of neighbor keys and assignment keys.
Consequently `colorsOf_card_le` bounds distinct colors by bound neighbors, even
when many neighbors share a color.

The fold support is contained in its input list. For an actual selection split
`select(card palette) g = before ++ n :: after`, the already computed right-fold
tail is supported in after. The050 original-neighbors-in-suffix theorem then
gives `colorsOf_suffix_card_lt`. `exists_color_after_suffix` proves an actual
successful available choice at that step; it also supplies a public fact for
the later exact coloring-write count. The generic
`keys_colorList_eq_of_later_degree` composes those steps into exact support.

`keys_color` states that the successful-key set of the produced assignment is
exactly the selected set. It holds for all raw graphs, including directed edges,
self-loops, dangling neighbors and padding. These graph-validity assumptions
belong to edge correctness, not support. `exists_color_iff_selected` supplies
the optional-lookup formulation, and support lies in the original stored domain.
`keys_color_of_progress` and `total_coloring_of_progress` compose this equality
with050 conditional selection coverage for an explicitly removal-closed class
with an eligible vertex whenever nonempty. The connected edgeless-class theorem
establishes its closure and progress hypotheses for a nonempty palette.

### Finite SimpleGraph client and boundary cases

`simpleObservation` retains the explicit stored domain alongside the SimpleGraph
adjacency. Under the two graph hypotheses, `simpleObservation_eq_iff` proves it
has exactly the earlier finite graph observation. The stored isolated vertex
and empty graph remain distinguishable by that observation.
`coloredGraph` restricts to successful assignment keys. `paletteValue` uses their
actual lookup values to construct elements of the finite palette subtype.
`properColoring` discharges `SimpleGraph.Coloring.mk` from compatibility and
AllPalette; `producedColoring` supplies those proofs for the actual program.
Its lookup equation exposes the precise original value. Finite vertex and
palette cardinalities agree with the occupied map and set cardinalities.

The exact source selection[4,1,2,6,5] is processed as5,6,2,1,4. The successive
assigned colors are1,2,3,2,1, giving ordered map entries
`[(4,1),(2,3),(6,2),(1,2),(5,1)]`. `source_entries` kernel-checks this exact
program. The source graph hypotheses instantiate compatibility, AllPalette,
exact domain coverage and the SimpleGraph client on the same produced result.
The finite client has five vertices and three palette values, with node1 mapped
to color2. Both original source Computes are included in the execution probes.

The directed graph with edge1→2 and palette{1} selects[2,1] and assigns both
vertices1. The one-vertex self-loop with palette{1,2} selects[1] and assigns1.
Their exact supports and AllPalette properties still hold, while their edge
compatibility is proved false. The four-cycle at palette size2 produces the
empty coloring because selection stops, yet the explicit total assignment
1:1,2:2,3:1,4:2 satisfies palette membership and all eight directed edge views.
Early stopping therefore gives no uncolorability certificate. These are direct
claims about the actual operations and predicates, with positive theorem clients
retained alongside the counterexamples.

## Normalized finite tries and measured path foundations

The bounded contribution CTB-103 supplies structural prerequisites for
the canonical resource proof. Its independent qualification is recorded in the
checkpoint evidence. The semantic owners above retain their original bytes and
raw-input hypotheses. Normalization is an additional resource hypothesis.

`Search.PositiveTrie.Normalized occupied` requires normalized children and an
occupied root or a nonempty child at every internal node. `SparseMap.Normalized`
uses `Option.isSome`, so a present empty set or zero value remains occupied.
`KeySet.Normalized` uses the stored Boolean. Empty tries are normalized; actual
occupied insertion, pruning erasure and arbitrary sparse value mapping preserve
the predicate. Value mapping needs no injectivity. Actual set difference needs
only a normalized left operand; its right operand may contain empty padding.
Both empty-operand shortcuts remain the original operations.

`keyMass` sums positive bit lengths over the existing ordered occupied-key
observation. Its node equation adds both child masses and the entire node's
occupied cardinality. Under normalization, every nonempty subtree has an
occupied key and contributes at least one to that cardinality. Consequently,
raw nodes are bounded by key mass. If every occupied key has bit length at
most B, the following map and set laws hold:

`numNodes ≤ keyMass ≤ cardinal * B`, and `height ≤ B`.

The key-mass upper bound itself holds for arbitrary raw trees; normalization is
needed to pass from occupied keys to raw structure. The APIs allow any natural
B, including zero on empty input, and impose no equality decision on payloads.
`SparseMap.occupancyTree` preserves raw shape while observing `Option.isSome`;
it transfers membership, cardinality, height, node count and ordered key mass
from the Boolean proofs. It is distinct from the existing fold-based `domain`.
Neither observation adds a traversal to the coloring executor.

The positive-path length equations follow the actual constructor recurrences:
`bitLength (append p q) + 1 = bitLength p + bitLength q`, with the same equation
for `reverseAppend`, and `reverse` preserves bit length. A normalized nonempty
local subtree supplies an occupied witness, so a bound on its globally prefixed
keys also bounds its starting prefix. A constructed prefix for a nil child can
instead have length B + 1: prefix 8 has length 4, while its left-child prefix 16
has length 5. Both map and set clients exercise this boundary.

`Resources.PositivePaths.appendRun` and `reverseAppendRun` use the existing
`Measured` sequencing to return the actual recursively reconstructed path.
Literal erasure theorems identify their returned values with the original
operations. The two coordinates count entered recursive calls, including the
terminal one, and constructed branch wrappers. Their exact costs are
`(bitLength p, bitLength p - 1)`. Forward append consumes the returned child;
reverseAppend constructs its accumulator before the recursive call. Reverse is
the original reverseAppend-on-one adapter. Fixed input values and these public
wrappers carry zero additional tariff; arithmetic, conversion, printing and
physical allocation are outside these coordinates.

`Resources.PositiveTrie.Finite` specializes the already measured raw lookup and
insertion to optional maps and Boolean sets. General lookup enters at most the
key's bit length and constructs no nodes; it may stop early at nil. Insertion
enters and constructs exactly that many nodes. Looking up the actual result of
inserting the same key has exact cost `(bitLength key, 0)`. The composed write
then read uses `Measured.bind` and costs `(2 * bitLength key, bitLength key)`.
The wrappers carry zero tariff. No pruning-erasure cost is inferred from these
insertion and lookup laws.

The connected cases include a normalized cardinality-one map at key 8 with
four raw nodes, mass 4 and height 4; the analogous set; and a normalized
singleton family with unbounded key length and actual lookup work. Conversely,
arbitrarily long false-valued raw padding has cardinality and key mass zero,
yet arbitrarily many raw nodes, and is normalized only when empty. Generic
insertion of an unoccupied value into nil fails normalization. Present empty
payloads, noninjective maps, occupied and absent erasures, and difference with
a padded right operand exercise the precise public predicates and operations.

For the exact accepted source inputs, the outer graph map is normalized and has
cardinality 5, raw nodes 6, key mass 12 and height 3, with every stored key at
most 3 bits. Thus `6 ≤ 12 ≤ 5 * 3`. The palette is normalized with cardinality 3,
raw nodes 3, key mass 5 and height 2, and its keys are at most 2 bits, giving
`3 ≤ 5 ≤ 3 * 2`. These instantiate general public bounds; they are not a measured
whole-program execution or a bound for every adjacency value. The two original
source Computes and all 33 earlier Print/Check probes remain required evidence.

## Actual finite-trie primitive resources

CTB-104 instruments the accepted primitive recurrences without changing their
raw semantics. The executors use `Resources.Measured.bind` and consume the
actual returned children, payloads and arithmetic results. Their value-erasure
laws are literal equalities to the existing operations on every raw input.
Normalization is added only where it supports a resource bound or an output
invariant. Fixed input values and thin adapters have zero extra tariff.

The declared coordinates distinguish the following source events. Every
entered nil recursion counts one. An emitted `BinaryTree.node` counts even
when its value equals the old tree; a returned existing subtree emits no node.

| Executor | Exact coordinates or proved bounds |
| --- | --- |
| `Pruning.pruneRun` | One prune entry and at most one emitted node. It collapses exactly an unoccupied value with two literal nil children. |
| `Pruning.mapEraseRun`, `setEraseRun` | Primary entries equal raw lookup entries on the original key/tree. Entries are at most key bit length and at most height plus one; prunes are at most entries and at most height; emitted nodes are at most prunes. |
| `Pruning.diffRun` | With paired nonnil positions P, primary entries are `2*P+1`, prune calls are P and emitted nodes are at most P. P is at most either input's raw node count. |
| `Cardinality.mapRun`, `setRun` | For T raw nodes and n occupied keys, outer counts are `(2*T+1,T,n)`: entries, child-sum additions, occupied increments. Arithmetic price is separate. |
| `ValueMap.run` | Outer counts are `(2*T+1,n,T)`: entries, payload callbacks, emitted nodes. The callback observation is separate and need not commute. |
| `Choice.run` | Raw entries are at most `2*T+1`; failed choice has exactly that many entries and zero wrappers. Successful choice of q has `wrappers+1 = bitLength q`. |

Erasure recurses only into the key-selected child and prunes that actual result.
Its three-coordinate sum is at most `3 * bitLength key`. Erasing key 8 from its
normalized singleton costs `(4,4,0)`, while erasing absent key 16 costs `(5,4,4)`
and returns the original tree. Raw padding of height 3 erased at key 8 instead
costs `(4,3,0)`: its fourth call is nil. Root-only erasure of that padding costs
`(1,1,1)` and retains it. These distinguish entry, prune and reconstruction work.

Difference retains both literal nil shortcuts. In particular, `set8` minus nil
returns its four-node input at `(1,0,0)`. The paired observation P is mathematical
proof data, not a second execution. The three-coordinate sum is at most `4*P+1`,
hence at most `4*(cardinal left * B)+1` when left is normalized and its occupied
keys have at most B bits. The right operand can contain nonnormalized padding;
normalization of the output needs only normalized left input.

Cardinality reuses `Resources.TreeFold.run` with its actual left/right/combiner
order. The combiner adds the returned child cardinalities, then adds one to
that returned sum only when occupied. A tariff `price a b` is charged at those
actual operands. `arithmeticWork` is its independently collected observation;
the executor does not call that observer. With unit tariff, arithmetic work is
`T+n` and entry-plus-arithmetic work is `3*T+n+1`. Normalization supplies
`T ≤ n*B`, including the empty case B = 0 with one terminal entry. A standalone
source-graph cardinality run has counts `(13,6,5)` and total 24; the palette has
`(7,3,3)` and total 13. Neither run is inserted into graph termination proofs.
The palette and the all-true left chain at keys 1,2,4 have the same addition
counts, but the illustrative tariff `price a b = a+1` gives 9 and 12. Addition
counts alone do not determine operand-sensitive prices or native arithmetic.

Value mapping invokes its actual callback only on `some`, stores its returned
payload, and rebuilds every raw node without pruning. Its declared constructor
sequence is root, left, right, matching the source traversal convention; it
does not assert a native evaluation schedule. The executor requires only addition and zero. Its collected-observation law
uses `AddZeroClass` with explicit grouping, without associativity or commutativity. On root payload 7 and left payload 9, the
callback `x ↦ (x+100,x+1)` stores 107 and 109 and has observation 18. A separate
free additive monoid trace is `[7,9]`, distinguishing this sequencing from the
left/root enumeration `[9,7]`. Constant-zero mapping retains both keys and
normalization. Under an explicit Nat price bound K for every reached payload,
callback work is at most `n*K`; entries, callbacks, emitted nodes and callback
work together are at most `3*T+n+1+n*K`, or `3*(n*B)+n+1+n*K` under the stated
normalization/key bound. Key-aware mapi has additional prefix work; the
traversal section below records its separate measured implementation and bound.

Choice stops immediately at an occupied root, otherwise tries left and tries
right only after left fails. Normalization makes every nonempty subtree contain
an occupied witness, so normalized failed choice implies literal nil. For a
normalized nonempty tree, `entries+1 ≤ 2*height`; the uniform bound including
nil is `entries ≤ 2*height+1`. Occupied-key bound B gives the corresponding
bit bounds. The normalized singleton with h right branches has height and key
bit length `h+1`, cardinality one and costs `(2*h+1,h)`, attaining the nonempty
height bound for every h. By contrast, a false root with left padding of height h
and a true right leaf always chooses key 3 at `(2*h+3,1)`. Chosen-key length
alone cannot bound arbitrary raw choice. A complete false tree of height 3
has seven nodes and takes 15 calls, refuting the raw bound `2*height+1 = 7`.

The fifteen prewritten case groups retain both exact reductions and connected
general-law clients, including present-empty versus absent payloads, callbacks
that change results, preserved large subtrees, empty normalized inputs and all
zero-height family boundaries. These source-event projections exclude
unselected Boolean/Option/control tariffs, conversion, output, native allocation,
garbage collection and elapsed time. The canonical complete work model, its
explicit constant, and the whole coloring program's invariants remain required.

## Source correspondence retained from the semantic increments

“Foundation” identifies the retained CTB-99 finite result; “Preliminary” identifies
the additional list/source adapter supplied by CTB-100. “Graph selection”
identifies the CTB-101 contribution; “Coloring semantics” identifies CTB-102.
The normalized-trie and measured-path resource foundation is CTB-103; actual
pruning, cardinality, value-map, difference and choice resources are CTB-104.
Their definitive bounded review/qualification outcomes are recorded outside
this note. Those earlier increments alone did not constitute full chapter
acceptance. The complete-program section below addresses the resource duties.
Every one of the53 inventory IDs occurs once below, in source order.

| Source record | Status and maintained correspondence |
| --- | --- |
| `Color.lt_strict@117` | Foundation: `Numerals.PositivePaths.bitLt_irrefl`, `bitLt_trans`; exact constructor relation. |
| `Color.lt_proper@120` | Foundation: `bitLt_congr` for ordinary key equality. |
| `Color.Mdomain@132` | Foundation: `SparseMap.domain`, `observe_domain`, `mem_domain`, `cardinal_domain`, `elements_domain`; actual ordered fold. |
| `Color.example_map@139` | Foundation: `Examples.PositiveFiniteTries.sourceMap`; exact three nested writes of empty sets. |
| `Color.domain_example_map@144` | Foundation: `sourceMap_domain_elements`: `[2,9,3]`. |
| `Color.same_mod_10@166` | Preliminary: `Examples.ColoringRelations.SameModTen`; exactly equality of residues modulo10. |
| `Color.InA_example@167` | Preliminary: `related_twentySeven`, with actual witness17. |
| `Color.equivlistA_example@173` | Preliminary: `same_mod_members`, plus explicit unequal-length/non-permutation/non-Forall₂ boundaries. |
| `Color.goal_at_line_226@226` | Preliminary: `Relations.key_eq_posNum`; the source view introduces no new key representation. |
| `Color.goal_at_line_227@227` | Preliminary: `Relations.keyEq_eq`; ordinary literal equality. |
| `Color.eqlistA_Eeq_eq@231` | Preliminary: `Relations.forall₂_keyEq_iff_eq`, through existing Forall₂ equality. |
| `Color.SortE_equivlistE_eqlistE@242` | Preliminary: `Relations.forall₂_keyEq_of_sorted`, consuming generic compatible strict-order uniqueness with source IsChain. |
| `Color.filter_sortE@255` | Preliminary: `Relations.isChain_bitLt_filter`; explicit transitive Pairwise bridge and arbitrary Boolean predicate. |
| `Color.Sremove_elements@275` | Foundation: Pedagogical Abort, connected to the completed unconditional `KeySet.elements_erase`; no axiom introduced. |
| `Color.Proper_eq_eq@285` | Preliminary: generic `eq_predicate_congr`, specialized to the literal positive-key equality. |
| `Color.Sremove_elements@291` | Foundation plus preliminary adapter: `KeySet.elements_erase_source_of_mem`; exact source filter, unchanged ordered values and the original member premise. |
| `Color.InA_map_fst_key@328` | Preliminary: `Relations.relatedMem_map_fst_key`; arbitrary pair lists/payloads, existential value witness and no unique-key premise. |
| `Color.Sorted_lt_key@341` | Preliminary: `Relations.isChain_keyLt_iff`; exact adjacent source-order/projected-key equivalence. |
| `Color.cardinal_map@356` | Foundation: `SparseMap.cardinal_map`, `keys_map`, `mapiFrom_key_ignore`; arbitrary payloads/functions/raw maps. |
| `Color.Sremove_cardinal_less@377` | Foundation: `KeySet.cardinal_erase_lt`, with the required membership premise and stronger add-one law. |
| `Color.specialize_SortA_equivlistA_eqlistA@392` | Preliminary: `Relations.forall₂_eqKeyValue_of_sorted`; arbitrary pair lists and compatible strict key order, no payload order or equality decision. |
| `Color.Proper_eq_key_elt@409` | Preliminary: `Relations.keyLt_congr`, respecting both pair arguments through key-and-value equality. |
| `Color.Mremove_elements@418` | Foundation plus preliminary adapter: `SparseMap.elements_erase_forall₂_of_mem`; exact source filter and key-and-value Forall₂, arbitrary raw maps/payloads and source domain premise. |
| `Color.Mremove_cardinal_less@438` | Foundation: `SparseMap.cardinal_erase_lt_of_mem`; successful-lookup and add-one variants also provided. |
| `Color.fold_right_rev_left@449` | Preliminary: existing arbitrary-accumulator `List.foldl_eq_foldr_reverse`, with the connected123-versus321 decimal example. |
| `Color.Snot_in_empty@454` | Foundation plus explicit preliminary corollary: `KeySet.not_mem_nil` excludes membership for every key. |
| `Color.Sin_domain@459` | Foundation: `SparseMap.mem_domain`: membership iff an actual successful optional lookup, including empty values. |
| `Color.node@470` | Graph selection: `Graphs.Coloring.Node`, the existing PosNum carrier. |
| `Color.nodeset@471` | Graph selection: `NodeSet`, the existing raw Boolean KeySet. |
| `Color.nodemap@472` | Graph selection: universe-polymorphic `NodeMap`, the existing optional SparseMap. |
| `Color.graph@473` | Graph selection: `Graph`, sparse maps of raw node sets. |
| `Color.adj@475` | Graph selection: `adj`, actual optional lookup with empty default. |
| `Color.undirected@478` | Graph selection: `Undirected`, exact edge reversal; neighbor-domain closure is derived. |
| `Color.no_selfloop@481` | Graph selection: `NoSelfLoop`, exact diagonal-edge exclusion. |
| `Color.nodes@483` | Graph selection: `nodes`, actual ordered domain fold with successful-binding characterization. |
| `Color.subset_nodes@485` | Graph selection: `subsetNodes`, actual arbitrary-predicate fold; `mem_subsetNodes`. |
| `Color.low_deg@492` | Graph selection: `lowDegree`, literal strict occupied-cardinality test and unused node argument. |
| `Color.remove_node@494` | Graph selection: `removeNode`, binding erasure followed by set erasure at every remaining payload. |
| `Color.subset_nodes_sub@504` | Graph selection: `subsetNodes_subset_nodes`, arbitrary predicate/raw graph and no congruence premise. |
| `Color.select_terminates@509` | Graph selection: `select_terminates`, actual successful choice and exact occupied-cardinality decrease. |
| `Color.select@520` | Graph selection: `select`, exact well-founded source recurrence, deterministic choice and early stop. |
| `Color.coloring@528` | Coloring semantics: `Graphs.Coloring.Assignment`, the optional sparse map of positive colors without a default. |
| `Color.colors_of@530` | Coloring semantics: `colorsOf`, actual ordered neighbor-color fold; exact `mem_colorsOf` and finite image bound. |
| `Color.color1@533` | Coloring semantics: `color1`, actual available-set choose, overwrite on success and unchanged input on failure; exact lookup laws. |
| `Color.color@539` | Coloring semantics: `color`, actual right fold over the computed selection, always using original adjacency. |
| `Color.coloring_ok@549` | Coloring semantics: `ColoringOK`, with both palette and endpoint-distinctness clauses guarded by an edge. |
| `Color.adj_ext@555` | Graph selection: `adj_ext`, literal node equality gives raw adjacency equality. |
| `Color.in_colors_of_1@560` | Coloring semantics: `in_colorsOf`, from the stronger exact membership theorem and actual successful lookup. |
| `Color.color_correct@566` | Coloring semantics: `color_correct`, under exactly looplessness and symmetry, via arbitrary-list compatibility including repeats. |
| `Color.palette@582` | Graph selection: `Examples.ColoringSelection.palette`, source right-fold insertion of[1,2,3]. |
| `Color.add_edge@584` | Graph selection: `addEdge`, exact outer/inner writes with both reads from the original graph. |
| `Color.mk_graph@588` | Graph selection: `mkGraph`, source right fold from empty, exact endpoint and edge observations. |
| `Color.G@591` | Graph selection: `sourceGraph`, exact seven edges, graph hypotheses, domain and selection trajectory. |

The27 preliminary records through Sin_domain,19 graph/selection records and
seven coloring records have concrete mathematical correspondence, totaling53of53.
These dispositions
do not constitute full chapter qualification. The source admissions are replaced
by checked proofs; the pedagogical Abort remains an aborted attempt rather than
an admitted declaration. Both the exact graph domain and exact coloring
computation are included in this increment's probes.

### All source exercises

| Source exercise | Complete preliminary conclusion and proof route |
| --- | --- |
| `Sremove_elements` | `eq_predicate_congr` and `KeySet.elements_erase_source_of_mem`; exact source conditional filter and source member premise. |
| `InA_map_fst_key` | `Relations.relatedMem_map_fst_key`, through the arbitrary-list existential projection theorem. |
| `Sorted_lt_key` | `Relations.isChain_keyLt_iff`, directly from List.isChain_map. |
| `cardinal_map` | Retained `SparseMap.cardinal_map`, with source lookup/preimage, sorted enumeration and projection adapters now available as the stated proof-hint interfaces. |
| `Sremove_cardinal_less` | Retained `KeySet.cardinal_erase_lt`; occupied cardinality and actual membership, with exact removal/filter and add-one laws. |
| `Mremove_elements` | `SparseMap.elements_erase_forall₂_of_mem`, including payload equality and source filter spelling. |
| `Mremove_cardinal_less` | Retained `SparseMap.cardinal_erase_lt_of_mem`; Finset key membership is equivalent to a successful optional binding. |
| `two_little_lemmas` | `List.foldl_eq_foldr_reverse` and `KeySet.not_mem_nil`; both source conclusions, not just one of the two lemmas. |
| `Sin_domain` | Retained `SparseMap.mem_domain`: source fold-based domain membership iff an actual bound value exists. |
| `subset_nodes_sub` | `Graphs.Coloring.subsetNodes_subset_nodes`; every predicate and raw graph, without predicate-congruence or graph-validity assumptions. |
| `select_terminates` | `Graphs.Coloring.select_terminates`; success implies membership, then strict occupied-cardinality decrease after erase/map. |
| `adj_ext` | `Graphs.Coloring.adj_ext`; ordinary node equality preserves raw adjacency. |
| `in_colors_of_1` | `Graphs.Coloring.in_colorsOf`, through the seed-general actual-fold invariant and exact used-color membership. |
| `color_correct` | `Graphs.Coloring.color_correct`, with the exact weak source predicate and graph hypotheses; stronger palette/support conclusions are separate. |

These are all14 source exercise headings. Bounded
qualification is derived only from the
immutable review and validation records, not from the presence of this table.

### Used module views and pedagogical commands

Allfive source aliases are mapped at the level of their used APIs: E is the
literal positive key/equality and explicit BitLt view; S is KeySet; M is
arbitrary-payload SparseMap; WF is the proved lookup/value-map interface; WP is
the actual ordered-fold/finite-domain proof route. This does not copy Coq module
functors or claim every unused provider operation. Source Print Module commands
are adapted by this interface account and concise public type/definition probes.

| Source command line | Public Lean demonstration or adapter |
| --- | --- |
| 74, Print Module E | `Relations.Key`, `KeyEq`, `BitLt`, irreflexivity/transitivity/congruence laws. |
| 75, Print E.t | `Relations.Key` and `key_eq_posNum`. |
| 82, Print Module S | KeySet membership/add/erase/diff/cardinality/elements/fold/choose and their proved observations. |
| 83, Print S.elt | The same `Relations.Key`; KeySet operations accept PosNum directly. |
| 88, Print Module M | SparseMap optional lookup/add/erase/map/cardinality/elements/fold/domain. |
| 89, Print M.E | The same literal positive key/equality view used by map and set. |
| 103, Print Module WF | `SparseMap.find_map` and `find_map_eq_some_iff`; actual preimage witness, no injectivity. |
| 104, Print Module WP | `SparseMap.foldFrom_eq`, `fold_eq`, `observe_domain` and `mem_domain`; no uninstantiated law field. |
| 106, Check E.lt | `BitLt`, separate from numeric PosNum order. |
| 151, Print equivlistA | `SameRelatedMembers`, with the mod10 multiplicity distinction. |
| 203, Check SortA_equivlistA_eqlistA | `forall₂_of_isChain_of_sameRelatedMembers`, with no totality premise. |
| 268, Check S.remove | `KeySet.erase`, actual pruning implementation. |
| 269, Check S.elements | `KeySet.elements` and its source-order proof. |
| 322, Check M.elements | `SparseMap.elements` for arbitrary payload universes. |
| 362, Check M.cardinal_1 | `SparseMap.elements_length`, with equality symmetry if needed. |
| 363, Check M.elements_1 | Binding-to-related-member direction of `SparseMap.relatedMem_elements`. |
| 364, Check M.elements_2 | Related-member-to-binding direction of the same exact equivalence. |
| 365, Check M.elements_3 | `SparseMap.elements_isChain`, key-only order. |
| 366, Check length_map | `List.length_map`. |
| 367, Check eqlistA_length | `List.Forall₂.length_eq`. |
| 368, Check SortE_equivlistE_eqlistE | `Relations.forall₂_keyEq_of_sorted`. |
| 369, Check InA_map_fst_key | `Relations.relatedMem_map_fst_key`. |
| 370, Check WF.map_mapsto_iff | `SparseMap.find_map_eq_some_iff`. |
| 371, Check Sorted_lt_key | `Relations.isChain_keyLt_iff`. |
| 424, Check specialize_SortA_equivlistA_eqlistA | `Relations.forall₂_eqKeyValue_of_sorted`. |
| 425, Check M.elements_1 | The binding-to-related-member direction reused in removal reasoning. |
| 426, Check M.elements_2 | The converse direction, retaining the same value. |
| 427, Check M.elements_3 | `SparseMap.elements_isChain`, also instantiated after erasure. |
| 428, Check M.remove_1 | `SparseMap.find_erase_same`. |
| 429, Check M.eqke_equiv | `Relations.eqKeyValue_equivalence`. |
| 430, Check M.ltk_strorder | `Relations.keyLt_irrefl` and `keyLt_trans`, without payload comparison. |
| 431, Check Proper_eq_key_elt | `Relations.keyLt_congr`. |
| 432, Check filter_InA | `relatedMem_filter` with predicate congruence; `relatedMem_filter_eq` specializes equality. |
| 594, Compute domain of G | `sourceGraph_domain` and the actual ordered-domain probe with unshifted labels: exact[4,2,6,1,5]. |
| 596, Compute color of G | `Examples.ColoringCorrectness.source_entries` and the actual program probe: exact[(4,1),(2,3),(6,2),(1,2),(5,1)]. |

The33 preliminary Print/Check commands retain public proof/type correspondence
and actual Lean probes. Both Computes supply the final two correspondences,
preserving the full35-command denominator. Source-specific tactic search, generalized
rewriting and proof hints are adapted to existing Lean proofs, without treating
source tactic syntax or module-functor packaging as new mathematical obligations.

## Actual finite-trie traversal resources (checkpoint054)

The shared `Resources.WorkloadBounds` owner adds restricted-input invariant and
Nat-work laws over the existing `Resources.run`. There is no second list runner.
The initial state must satisfy the invariant, every command must be allowed,
and both state preservation and local billing are required only for allowed
commands at invariant states. The tail consumes the actual returned state.
The sum-of-command-weights theorem specializes to a constant bound times the
actual command-list length.

`Resources.PositiveTrie.Traversal` supplies mathematical observations shared by
the five actual executors. Write T for raw nodes, n for occupied cardinality,
W for occupied key-bit mass, F(tree,p) for the sum of forward-prefix lengths
over all raw nodes, W_r(tree,r) for occupied reversal mass, and A for the sum of
each raw node's occupied left-subtree cardinality. Its proved recurrences and
relationships include:

- F(nil,p)=0 and F(node,p)=bits(p)+F(left,append(p,2))+F(right,append(p,3)).
- F(tree,p)=F(tree,one)+T*(bits(p)−1), and T≤F, on every raw tree.
- W_r=W+n*(bits(r)−1), with n≤W_r. It equals the sum of the bit lengths of
  the actual generated keys `reverseAppend r key`.
- A(nil)=0 and A(node)=A(left)+A(right)+n(left), with A+n≤W on raw maps.

These observations do not run inside the measured algorithms. In particular,
A counts copied occupied output cells, whereas raw left-subtree size counts
absent nodes too. F includes absent nodes; W_r does not.

### Literal operations, sequencing and observations

| Owner / actual source operation | Declared source sequence and exact outer coordinates |
| --- | --- |
| `MapFold.runFrom` / `SparseMap.foldFrom` | Left, optional root callback, right. Each child uses the actual `PositivePaths.appendRun` result; each callback and right child consumes the returned state. Coordinates `(tree entries, callbacks, prefix entries, prefix wrappers)` equal `(2*T+1,n,2*F,2*(F−T))`. |
| `SetFold.runFrom` / `KeySet.foldFrom` | Left, occupied root callback, right. Direct bit0/bit1 wrappers construct reversed child prefixes; an occupied root consumes the actual `reverseRun` result. Coordinates `(entries,callbacks,direct wrappers,reversal entries,reversal wrappers)` equal `(2*T+1,n,2*T,W_r,W_r−n)`. |
| `KeyMap.runFrom` / `SparseMap.mapiFrom` | Root callback, left, right, rebuilding every raw node from actual returned payloads/subtrees. Coordinates `(entries,callbacks,prefix entries,prefix wrappers,nodes)` equal `(2*T+1,n,2*F,2*(F−T),T)`. |
| `Enumeration.Map.runFrom` / `SparseMap.elementsFrom` | Evaluate left and then right, cons an occupied root on the returned right tail, then run `ListAppend.copies` on the returned left list and that tail. Coordinates `(entries,prefix entries,prefix wrappers,append entries,copies,fresh cons)` equal `(2*T+1,2*F,2*(F−T),A+T,A,n)`. |
| `Enumeration.Set.runFrom` / `KeySet.elementsAcc` | Right with the supplied tail, occupied root reversal/cons, then left with the returned tail. Coordinates `(entries,direct wrappers,reversal entries,reversal wrappers,fresh cons)` equal `(2*T+1,2*T,W_r,W_r−n,n)`. There is no append or tail scan. |

Every coordinate theorem first establishes its additive wrapper identity:
map wrappers+2*T=2*F or set wrappers+n=W_r. The subtraction formulas therefore
do not conceal saturated-Nat cases. Each actual list append separately maps its
k copied cells to k+1 entries and k copies. This per-invocation offset gives
A+T entries; applying an affine offset once to the total would incorrectly give
A+1. Nil calls count one. Fixed input suffixes and thin public wrappers add no
tariff. These are selected source events, with explicit sequencing, rather than
a compiled evaluation schedule, native arithmetic model or physical allocation
measurement. Unselected Boolean/Option/control events, conversion and output
work remain part of the later complete tariff model.

The fold and key-map executors keep callback observation C separate from the
outer counts. Their value/count APIs need only `Zero C` and `Add C`. Each fold's
`runFrom_callback` identifies the pair of final state and callback observation
with the existing ordered list run under `AddMonoid C`, with no type order or
commutativity assumption. Map commands are the actual generated entries of
`elementsFrom tree p`; set commands are `rawKeys.map (reverseAppend r)`. This is
a proof comparison, without inserting an enumeration into the executor. The
restricted invariant/work consequences use those exact generated commands and
the actual callback trajectory.

Key-aware mapping has a different, root/left/right observation law; its explicit
tree grouping requires only `AddZeroClass C`. The callback receives the actual
generated key, while its output remains stored at the original local key. The
proved exact `occupancyTree` equality preserves raw shape, occupied cardinality
and normalizedness in both directions, without callback injectivity and across
payload types. It precedes the normalization consequence; the old
key-independent `normalized_map` is not substituted for this proof. Its Nat
callback bound ranges over successful local lookups and bills the callback at
`append p localKey`. Ignoring the key gives the previous ValueMap's returned
value, with no transfer of that algorithm's prefix cost.

### Conditional structural bounds

For normalized input, a bound B on every occupied generated forward key implies
F(tree,p)≤T*B. A nonnil subtree has an occupied witness, which bounds its parent
prefix; an unused nil-child prefix need not satisfy that bound. Nil is valid at
B=0 for any prefix. At root one, T≤W≤n*B and F≤n*B². The occupied reversal mass
satisfies W_r≤n*B under its generated-key premise even without normalization;
normalization is needed to bound raw T. The exact unit sums and convenient
root-one normalized bounds are:

| Operation | Exact outer sum | Normalized root-one bound |
| --- | --- | --- |
| Map fold | 4*F+n+1 | 4*n*B²+n+1 |
| Set fold | 4*T+2*W_r+1 | 6*n*B+1 |
| Key-aware map | 4*F+n+T+1 | 4*n*B²+n*B+n+1 |
| Map enumeration | 4*F+T+2*A+n+1 | 4*n*B²+3*n*B+n+1 |
| Set enumeration | 4*T+2*W_r+1 | 6*n*B+1 |

Callback work is additional. The fold total bounds retain the initial invariant,
allowed generated commands, restricted closure and restricted local-work
premises. These primitive bounds do not supply the full Color program's constant.

### Connected cases and boundaries

`Examples.PositiveFiniteTraversalWork` connects the public laws to all sixteen
prewritten case groups, with the command-domain separator T06b inside T06:

| Groups | Connection and distinguishing behavior |
| --- | --- |
| T01–T02 | Arbitrary-state/prefix/tail nil calls; present-empty payloads versus absent raw leaves; map enumeration totals7 versus6 and one terminal append per leaf. Empty normalized inputs instantiate a zero bit bound. |
| T03–T04 | The map callback visits payloads9 then7 at actual states0 then9, ending97 with bill11 and outer15, combined26. Root-first would give79/bill9; repeated initial-state billing gives2. The noncommutative public list-run bridge yields `[(2,9,0),(1,7,9)]`. |
| T05 | The set palette visits2,1,3 at states0,2,21, ends213, and bills26. Its ordered trace is `[(2,0),(1,2),(3,21)]`; outer23 gives combined49. Decimal arithmetic here is an illustrative callback, not a native cost claim. |
| T06/T06b | Saturation preserves state≤10 and bills11 on the two commands; the generic bound is22. An allowed command at initial11 bills12. The domain-restricted variant returns(11,100) off-domain, so both unrestricted closure and unrestricted local billing fail even from state0. |
| T07–T08 | Forward prefix5 generates map keys9,5 and raises F from3 to7; map enumeration totals35. Reversed prefix5 generates10,6; reversed prefix6 generates9,5. Both reversal masses are7, so equal lengths do not identify generated keys. |
| T09–T10 | Key-aware payloads store local entries `(2,209),(1,107)` at one and `(2,909),(1,507)` at prefix5, with root-first traces. Constant/noninjective and result-type-changing callbacks preserve occupancy. Key-ignore agrees in value with ValueMap, while outer work33 versus9 retains24 prefix events. |
| T11 | `twoValues` has A=1, append entries3 and total19; A+1 would give the false entry count2. Singleton8 has T=4,F=10,A=3,total52; singleton7 has T=3,F=6,A=0,total29. |
| T12 | The palette with tail42,43 returns2,1,3,42,43 through right/root/left construction. General tail, length and complete cost-independence theorems are instantiated; there is no hidden tail freshness/order premise. Singleton8 set enumeration totals25. |
| T13 | Explicit optional padding has cardinality/mass/copies0. A length-h raw chain satisfies 2*F=h*(h+1), map total2*h²+3*h+1 and set total4*h+1. Normalized iff h=0; the quantified family refutes an unrestricted cardinality-only bound. |
| T14 | Normalized left and right singleton paths, indexed by h with endpoint length L=h+1, satisfy T=L,n=1,W=L and 2*F=L*(L+1). Left A=L−1 gives map total2*L²+5*L; right A=0 gives2*L²+3*L+2. Both set totals are6*L+1. A quantified normalized cardinality-one family has unbounded enumeration work. |
| T15 | An occupied leaf at forward8 has occupied generated-key bound4. Its nil-child prefixes16 and24 have length5, while each actual append of input8 costs(4,3). The public bound uses the nonnil parent, not unused child prefixes. |
| T16 | Source graph enumeration has vector(13,28,16,11,5,5), total78 and key order4,2,6,1,5. The literal domain fold consumes actual setAddRun accumulators; the callback/list-run bridge and primitive insertion-cost law give bill(12,12). Outer62 plus unit callback24 is86, and its returned value is the accepted graph domain. |

The original53 source records,14 exercises,35 command correspondences, five used
aliases and both source Computes above remain unchanged. All new declarations'
actual elaborated types, focused validation, independent review reports and
bounded qualification are bound by the checkpoint's immutable evidence. The
source-domain composition prices that operation only, not graph construction or
the complete coloring program.

## Complete supplied-input program resources (checkpoint055)

### Shared execution and recovery contracts

`MeasuredFold.run` executes the recursive tail before the current measured
callback and passes the tail's actual returned state to that callback. Its
observations separate terminal-inclusive list entries, callback invocations
and callback observation C. Entries are length+1 and invocations are length.
For `AddMonoid C`, the pair of returned state and callback observation is
exactly `Resources.run callback xs.reverse seed`. No commutativity, order or
reversal operation is added to the executor. Restricted invariant and
weighted-work laws consume that bridge. Noncommutative trace and state-sensitive
clients distinguish the actual states and execution order. `pure_fold` recovers
both value and the older `ListExecution.foldr` tariff: that tariff omits the
separately observed callback-invocation coordinate, which the bridge drops.

Coloring `Cost` uses existing product/function addition on a structural count,
an arithmetic bill and natural event counters. `workHom`, `structuralHom`,
`arithmeticHom` and `countHom` expose additive projections. `enter` charges one
structural unit and records a helper entry; `observe` records an event without
charging it again. Primitive adapters reweight accepted measured lookup,
insertion, pruning, cardinality, fold, value-map and choice executors.
`bind` threads actual returned values. Erasure is literal raw equality, not
merely the existence of some valid answer.

The presentations have explicit information boundaries. The measured
right-fold bridge preserves the complete ordered callback observation;
projection to the pure tariff forgets coordinates. Coloring's scalar work
forgets the division between structural work, arithmetic work and individual
events. Primitive reweightings retain the coordinates used by this model and
need not be invertible. Finite graph observation forgets raw padding, so equal
finite graphs need not have equal work. No resource equality is transported
through that observation alone. These modules extend the existing carriers
and runners through proved recovery connections.

### Declared tariff and preserved states

Lookup prices primitive entries; insertion prices entries plus constructed
nodes. Erase and difference price entries, prune calls and constructed nodes.
Choice prices visited entries and returned-key wrappers. Cardinality prices
entries and supplied prices of the additions actually executed. Map/set folds,
value mapping and the shared list fold add their established outer events to
actual callback work. Each entered graph/helper operation costs one, every
low-degree comparison has an arithmetic price, and each selected cons costs
one. Bool/Option dispatch is included in the entered primitive, helper or
callback tariff. Proofs and bookkeeping projections are free. This is a
structural source model, with no native instruction, physical allocation,
garbage collection or elapsed-time conclusion.

`GraphValid b g` requires normalized outer storage, normalized adjacency
payloads at successful bindings, and bit length at most b for stored keys and
every mentioned neighbor. A dangling neighbor must satisfy the bound even if
it has no graph binding. `SetValid c palette` requires normalized storage and
bounded palette keys. `AssignmentValid` also retains actual palette membership
at every successful assignment binding. Nil, insertion, pruning, difference,
construction, selection and coloring use preservation laws on actual returned
states. Neither symmetry nor looplessness is a resource premise. Earlier raw
semantic correctness and support theorems retain their original assumptions.

`degreeMass g` sums actual adjacency cardinalities over stored keys. Its
ordered-entry equality lets a map-fold bill use each payload's degree.
Removal decreases this mass even for an absent outer key, whose occurrences
in other adjacency sets can still disappear. The original-neighbor total
along the selected nodup list is at most the original mass. These are proof
observations; the executor performs no extra enumeration for them.

### Construction and exact trajectories

`addEdgeRun` performs both adjacency reads on the same old graph, constructs
both new sets, writes the second endpoint, then writes the first endpoint
into that returned map. Equal endpoints still perform all six operations.
`mkGraphRun` right-folds every input occurrence. With E occurrences and endpoint
bit lengths at most b>=1, its work is at most `15*E*b+2`. `paletteRun` separately
right-folds color insertion. Supplied-input `colorRun` charges neither setup
operation implicitly.

`selectRun` executes eligible construction, actual root-first choose, removal
on success and recursion on the returned graph, followed by the selected cons.
Well-foundedness uses the actual successful choice and cardinal decrease.
Graph cardinality in that proof is not an executable setup pass; threshold K
stays fixed. `residuals_range` identifies actual states with removing successive
selected prefixes, with cardinalities n-t through the terminal stage. That
stage may be a nonempty stalled core.

For r selected vertices, put `A = sum(t=0..r)(n-t)`,
`B = sum(t=0..r-1)(n-t-1)` and `T = sum(t=0..r-1)(t+1)`.
The proofs first establish `A+T=(r+1)*n`, `B+T=r*n`, `A=n+B`
and `2*T=r*(r+1)`. Nat subtraction/division corollaries retain the required
nonnegativity. Full selection gives A=n*(n+1)/2 and B=n*(n-1)/2.

| Actual event | Exact observation |
| --- | --- |
| select, eligible, subset, candidate choose | r+1, including the terminal unsuccessful stage |
| predicate, low-degree call, adjacency cardinality, comparison | A |
| candidate insertions | Sum of actual eligible cardinalities over residual stages |
| outer erase, value-map call, selected cons | r |
| adjacency erase attempts | B, including attempts on payloads lacking the key |
| color1, colorsOf, difference, color choose | r |
| painting list entries / callbacks | r+1 / r |
| initial palette cardinality | One |
| neighbor assignment lookups | L, the sum of ORIGINAL adjacency degrees along selection |
| used-color insertion attempts | Actual successful neighbor lookups, including equal colors |
| assignment writes | At most list length generally; exactly r for actual selected suffixes |

`colorsOfRun` consumes the actual optional lookup at every original neighbor.
`availableColorsRun` reads original adjacency, then executes colorsOf and
simultaneous palette difference. `color1Run` inserts on actual successful
choice and returns the entire supplied assignment unchanged on failure.
`colorListRun` uses the shared tail-first fold with the same original graph.
`colorRun` computes palette cardinality once, selects with that returned K,
and colors the returned list. Exact selected writes use the existing suffix
availability theorem without adding normalization, symmetry or looplessness
to that semantic success result.

### Fixed bound and actual arithmetic prices

With n stored vertices, original degree mass D, k palette members, valid graph
and palette, and positive bounds b,c, `colorRun_work_le` proves

`work(colorRun unitPrices palette g) <= 64*P`, where

`P = n²*b² + n*D*b + D*(b+c) + (n+1)*k*c + n + 1`.

The selection induction gives `23*n²*b²+4*n*D*b+5`. The coloring-list bound
retains actual suffix invariants and L before using r<=n and L<=D. Normalized
n=0 is handled separately. Forward map-prefix work explains the b² term;
this is a conservative bound, with no optimality claim.

`Prices` supplies addition and comparison prices at actual operands. Changing
prices preserves values and the structural coordinate. `arithmeticTariff`
sums the initial palette additions and terminal-inclusive residual scans'
adjacency additions/comparisons. `colorRun_arithmetic` identifies this observation
with the executed arithmetic coordinate. For prices p,q, `colorRun_reprice`
gives `W(p)+A(q)=W(q)+A(p)` without truncated subtraction. Consequently
`W(p)<=64*P+A(p)` retains the actual extra tariff. It does not turn unit arithmetic
into a bit/unary or finite-word bound.

The normalized `isolatedLong height` family stores one empty adjacency at the
existing longKey, whose bit length is height+1, with palette{1}. Here n=k=1,
D=0, c=1 and b=height+1. Its polynomial is b²+4<=5*b². The fixed64 theorem gives
work<=320*(height+1)². `isolatedLong_isBigO` uses `Resources.isBigO_of_nat_bound`
with constant320 and threshold0 after real casting. The varying parameter is
key height; vertex cardinality remains one.

By contrast, `paddedGraph height` changes only the payload type of the accepted
all-absent raw family. It has n=D=0, no predicate callbacks, and is normalized
iff height=0. Selection costs4*F+5 and empty-palette coloring costs
4*F+9=2*height*(height+1)+9. Height5 gives69>64 while the cardinality-based
polynomial is1. Literal raw erasure remains valid on this counterexample.

### Charged exports and source clients

`domainExportRun` executes nodes, set enumeration and a measured decoder fold.
`assignmentExportRun` enumerates the actual assignment and decodes both fields.
The decoder returns the existing numeric key observation with an explicit
input/output tariff. List entries, callbacks and fresh output cells are charged;
each assignment pair has one additional charge. Numeric conversion here has
a declared abstract cost, rather than an inferred intrinsic conversion algorithm.
Parsing and byte formatting are outside the supplied-input theorem.

`pipelineRun` constructs graph and palette once, colors those actual values,
then exports the original domain and actual assignment. Its additive law
exposes five component bills and the pipeline entry; counters prove one graph
construction and one palette setup. The source example uses decoder price
numeric-value+1 and preserves the source output order.

| Source component | Exact work |
| --- | ---: |
| Graph construction, seven occurrences | 194 |
| Palette construction, three occurrences | 18 |
| Selection, including final failed stage | 731 |
| Original-graph painting list | 313 |
| Initial palette cardinality plus color entry | 14 |
| Complete supplied-input color | 1058 = 951 structural + 107 arithmetic |
| Domain export | 176 = 1 + 87 nodes + 49 enumeration + 39 decode/list |
| Assignment export | 137 = 1 + 78 enumeration + 58 decode/list/pairs |
| Explicit construction/color/export pipeline | 1584 |

The source polynomial is547 and the generic upper bound is35008. Selection
has six stage entries/choices,15 predicates/cardinality requests/comparisons,
ten candidate insertions, five removals and ten adjacency erase attempts.
Painting in order5,6,2,1,4 takes callback work43,55,83,69,51, with fourteen
lookups, seven successes/insertion attempts and five writes. Measured value
erasure connects to the earlier exact entries, compatibility, AllPalette,
domain and `sourceClient` SimpleGraph lookup. Both primary Computes remain
separate actual execution probes.

The eighteen frozen example groups cover the shared noncommutative fold,
restricted actual states, nil/present-empty inputs, old-graph construction reads,
quantified repeated self-edges, palette setup, residual selection, original
neighbor painting, the complete source bound, zero/stalled selection, raw
padding, dangling/asymmetric inputs, absent/repeated erasure, failed generic
choice, repeated successful colors, operand-sensitive arithmetic, charged
exports and the quantified long-key family. Repeated self-edges satisfy
work+4=45*E for E>=1 despite fixed finite n=D=1. Arithmetic price a+b+1 gives
20+5=11+14. Failed generic choices retain zero writes separately from the
selected-suffix exact-write theorem.

## Source prose and integration boundary

The chapter's proper-coloring discussion requires different colors at adjacent
vertices; the chromatic number asks for the least palette size admitting a
total proper coloring. Fixed-k colorability for k>=3 is the NP-complete
decision problem discussed there; two-colorability is a different case.
An impossibility of polynomial time is conditional on P!=NP. These contextual
remarks add no complexity-theoretic axiom or planar coloring theorem to the
development. The actual interference constraint proved here is partial
compatibility plus separate palette/support properties. Spill-code generation,
coalescing and minimizing uncolored vertices are unspecified.

The source Defined/Qed advice concerns its Rocq computation path. The existing
[Decide account](vfa-decide.md) distinguishes Lean's opaque Prop proof fields,
open computational data and opaque data declarations using checked examples.
This development uses those Lean interfaces and the actual well-founded
equations; it does not transfer a blanket Rocq transparency rule.

All 53 source records, 14 exercises, 35 commands, five aliases and earlier
contracts/cases remain represented in the mathematical maps and source owners.
[CTB-99 through CTB-106](../textbooks/CTB.json) record the donor's successive
bounded Color qualifications and their composition; this note does not itself
establish acceptance of another candidate or completion of the all-book programme.

Current CTB-78 requires integration-quality review of branch divergence,
complementary-presentation recovery and actual client/cost observations, followed
by receiving whole-library validation, exhaustive audit and independent Standards
and Spec review. The donor's focused validation does not replace those gates.
Only after current integration acceptance should formalization resume for every
remaining FDSA/PFDS chapter, exercise and appendix.
