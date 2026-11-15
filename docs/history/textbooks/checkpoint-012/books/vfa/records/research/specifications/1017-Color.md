# Local #1017 — VFA Color: complete requirements and reuse plan

**Planning only, 2026-11-02. Implementation remains blocked until #1016 Decide is accepted.**
The chapter order remains Trie → Priqueue → Binom → Decide → Color. Source
preparation does not accept those predecessors or authorize their implementation
out of order. This assignment writes only this plan; it adds no Lean algorithm,
proof draft, compiler result, tracker entry, or chapter acceptance. Root owns the
running candidate gate and the later implementation/review/checkpoint decisions.
Names below are proposals to reconcile with the actual accepted predecessor APIs.

## 1. Source identity, scope, and documentary boundaries

- Read the complete pinned `reference/vfa/vfa/Color.v`: **602 lines, 23,243 bytes**,
  SHA-256 `67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370`.
  Source: [VFA 2.1 Color](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Color.html),
  release cover `2026-08-24 10:11`, source footer `2026-08-24 09:43`,
  Coq/Rocq 9.0.0 or later. The inventory's moving `vfa-current` URL is historical
  metadata; the release URL, archive hash, and individual file hash are the pin.
- The unchanged inventory has **53 declaration records, 14 exercises, five
  module aliases, and 35 pedagogical commands**. All fourteen exercises are
  standard; none is optional or advanced. All remain required. The declaration
  statuses are 23 definitions, 12 source-proved records, 16 admissions, one
  pedagogical Abort, and one transparent Function proof. The latter depends on
  an admitted termination lemma and is not evidence that termination is already
  established. The admitted removal proof also contains four inner `admit`s.
- Verified archive: <https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>,
  SHA-256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Follow `../source/SOURCE-RECOVERY.md`; retain the VFA MIT notice and provenance.
  Downloaded research copies are excluded from recovery deliverables under
  conaled ADR 0001. The coverage and identity tables below survive independently
  of those copies.
- Inspected project HEAD: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.
  Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries
  `66e469188fe07963e5cf666c7d4433f45b8131c5`. This is a preparation baseline,
  not the eventual accepted predecessor candidate.
- The source aliases depend on external Rocq implementations. The independently
  inspected reconstruction baseline is **Stdlib V9.0.0**, immutable commit
  `fda356e01346f7766b282ef9f44080cce2be23b3`. This meets the release's version
  floor; the VFA archive does not itself pin a unique Stdlib checkout. Exact
  provider byte hashes are recorded below. Do not substitute a later library
  silently or claim that a Lean proof is a Rocq-to-Lean compiler theorem.

Read `REQUIREMENTS.md`, `POSITIVE-KEY-REUSE.md`, the computational and resource
notes, the frozen Trie plan, and the full staged positive-key and table-observation
modules. Their preparation proofs are useful inputs, not accepted chapter APIs.
Repository guidance includes AGENTS, architectural-quality/domain guidance,
GLOSSARY, ADR index and ADRs 0001/0010, the implementation workflow and its
existing review/validation requirements. The user's local-tracker and durable
checkpoint instructions replace GitHub tracking/publication.

### Required and suggested reading

The required [Appel 2016 slides](https://www.cs.princeton.edu/~appel/Color.pdf)
were read through all 72 pages; exact PDF identity is below. They motivate
low-degree removal and reverse-order coloring, and explain that phase-two
correctness does not depend on a particular vertex order. Slides 9–20 describe
a heuristic that removes a high-degree vertex when necessary; slide 63 and
the pinned chapter instead stop when no low-degree vertex is available.
Preserve the latter program. Slide 71's prose palette claim is stronger than
its displayed edge-guarded predicate; prove that stronger implementation
property separately. Planarity, four-/five-color theorems, historical anecdotes,
and the slides' heuristic variant are context, not additional chapter algorithms.

The suggested [Blazy–Robillard–Appel coalescing paper](https://www.cs.princeton.edu/~appel/papers/regalloc.pdf)
is a bibliographic pointer in the chapter. Its body was not used as a proof or
performance dependency here. The direct browsing request was blocked by the
provider. This plan claims neither whole-paper coverage nor a verified register
allocator, coalescer, worklist implementation, or spill-optimality theorem.

## 2. Architecture and actual provider contracts

### Primary representation and narrow shared extensions

Reuse the accepted positive-key and Trie work. The concrete carriers are
existing `PosNum`, `BinaryTree (Option A)` for a sparse map, and `BinaryTree Bool`
for a positive set. They are abbreviations/specializations, not new inductive
copies of positive numbers, trees, finite maps, or sets. Source
`Node left payload right` corresponds to `BinaryTree.node payload left right`.
Every raw finite tree has a finite observation and unique path keys; neither
BST order nor normalization is needed for the semantic laws. A separate
normalization condition is relevant to size-based resource bounds.

Place the source-facing finite operations with the accepted
`Applications/Tables/PositiveTrie` family, with graph operations/proofs in a
small `Applications/Graphs/Coloring` family and resource proofs in the existing
Resources organization. These locations remain provisional. Plain definitions,
observations and propositions should suffice; do not build a second general
map/set/graph/command hierarchy. Cross-domain checked clients belong in Examples.

`BinaryTree.get` on an optional-payload map has type
`PosNum → BinaryTree (Option A) → Option (Option A)`. Its flattened result
is the source optional binding; equivalently, use `getOrElse` with `none`.
The outer `none` means no tree node; `some none` means an unoccupied internal
node. Both mean no binding. `some (some a)` is a binding even if `a` is an
empty adjacency set. Set membership reuses `getOrElse` with false. Accepted
Trie insertion specialized to default `none`/payload `some a` or default
false/payload true has the source add recurrence; prove the all-input adapter.
Use accepted Maps laws for the resulting optional-function update observation.

The remaining finite operations—pruning erase, set difference, occupied-key
enumeration/folds/cardinality, and source choose—are genuine gaps in the
inspected `BinaryTree` API. Extend the accepted Trie family only for the used
operations, preserving the source equations. `BinaryTree.map (Option.map f)`
can realize source value-only map after an all-input raw-result adapter to
the source's key-ignoring `mapi`. Its avoided key-building work is a resource
difference, not a consequence of value equality.

Use `Finset PosNum` and `Finmap (fun _ : PosNum => A)` as independent finite
observations, with proved membership/lookup bridges from the actual finite
enumerations. Preserve raw value equality in the general map adapter. A later
graph observation may map adjacency trees to Finsets, but transport of an
arbitrary `P : node → nodeset → Bool` additionally requires P to respect that
observation. Cardinality-based low-degree tests do respect it once proved;
an arbitrary predicate on raw tree shape need not.

The accepted table seam handles empty/read/write and default observations;
it does not already supply erase, finite support, canonical enumeration,
fold order, cardinality, set difference, or deterministic choice. Add those
specific proved lemmas, keeping operations separate from semantic equivalence,
invariants and laws. No new axiom may stand for a Rocq module-signature field.

### Inspected public APIs and limitations

Paths beginning `Mathlib/` are relative to the pinned Mathlib checkout;
`Init/` and `Std/` paths are relative to the pinned Lean `src/lean` directory.

| Inspected provider | Exact reuse and boundary |
| --- | --- |
| `PosNum.one/bit0/bit1`, `natSize`, numeric casts; Mathlib `Data/Num/Basic.lean` and `Lemmas.lean` | Reuse the existing positive carrier and bit-length/numeric observations. Its ordinary comparator and order are numeric. They do not implement the chapter's alternative bit order or choose convention. No bounded machine-word assumption is implicit. |
| Staged `VFAStaging.PositiveKeys.numeric`, `numeric_one/bit0/bit1`, `numeric_injective`, `encode`, `decode`, inverse laws and `binaryNatEquiv` | Preserve unshifted positive numeric labels. The shifted key adapter sends Nat 0 to positive 1; it is not the interpretation of Color's printed numerals. Consume the accepted integrated seam, with no duplicate conversion definitions. |
| `BinaryTree.nil/node`, `map`, `numNodes`, `height`; `Data/Tree/Basic.lean` | Existing carrier and payload map; `map` preserves shape. `numNodes` counts every internal node, including absent/false payloads. It is not source map/set cardinality. |
| `BinaryTree.get`, `getOrElse`; `Data/Tree/Get.lean` | Exactly the low-bit-first path: one reads root, bit0 goes left, bit1 goes right, nil returns none. Flatten optional payloads for maps; false-default observation for sets. `indexOf` performs ordered label search and is not this lookup. |
| Accepted Trie insertion and Maps optional updates; staged `TablePreparation.Ops`, separate `Laws`, `observe_set`, `withDefault`, `hasBinding`, `binding_iff` | Empty/read/write observation and default/absence distinctions. `Valid := True` is justified for raw path-indexed lookup laws. Finite enumeration/erase/choice remain new obligations. No order or equality requirement on arbitrary map payload A. |
| `Finmap.lookup`, `lookup_empty`, `lookup_insert`, `lookup_insert_of_ne`, `lookup_erase`, `lookup_erase_ne`, `ext_lookup`, `keys`, `mem_keys`, `keys_erase`; `Data/Finmap.lean` | Existing extensional finite-map observation with constructive `DecidableEq` on keys. Its dependent payload is specialized to a constant family. Lookup equality identifies Finmaps, not arbitrary raw trees. |
| `Finmap.foldl`; same file | Its function has type `δ → ∀ a, β a → δ` and requires commutation of the two updates for every accumulator and pair of entries. This is a multiset fold. It is not a source ordered-fold implementation without a commutation or traversal bridge. |
| `Finset.card_erase_of_mem`, `card_erase_add_one`, `card_erase_lt_of_mem`, `card_image_le`, `sdiff_nonempty_of_card_lt_card`; `Data/Finset/Card.lean`; `sdiff_nonempty`, `Data/Finset/SDiff.lean` | Reuse erase/cardinality, image-size and available-color reasoning after proving actual finite observations. Decidable equality is needed for the executable Finset operations. The set laws do not prescribe source choose. |
| `List.mem_map`, `length_map`, `foldl_eq_foldr_reverse`; `Init/Data/List/Lemmas.lean` | Projecting pair keys yields the required existential payload witness. The reverse-fold equation already has the source orientation and arbitrary accumulator/function; no commutativity assumption is needed. |
| `List.pairwise_map`, `List.Pairwise.filter`; `Init/Data/List/Pairwise.lean` | Key projection and filtering preserve the all-pairs relation. Source `Sorted` is adapted through the accepted adjacent/IsChain bridge; transitivity justifies passage to Pairwise where required. |
| `List.Pairwise.eq_of_mem_iff`; Mathlib `Data/List/Sort.lean` | The surrounding section requires `[Std.Antisymm r]`, and the theorem adds `[Std.Irrefl r]`. It takes two Pairwise proofs and equal membership sets. Strict-order asymmetry discharges antisymmetry vacuously; no total order on payloads is needed. Do not miss the section-level assumption. |
| `List.Forall₂`, `forall₂_eq_eq_eq`, `Forall₂.length_eq`; `Data/List/Forall2.lean` | Source `eqlistA` is pointwise relatedness, becoming literal equality when its relation is equality. A general setoid version can pass through quotient equality; source `equivlistA` is only equivalent membership, not permutation/multiplicity. |
| `Std.TreeMap` empty/insert/erase/get?/getD/keys/toList/foldl, and `map` in `AdditionalOperations.lean` | An inspected alternative finite backend with an explicit comparator, not the selected source trie. TreeMap.map receives both key and value. Replacing the primary realization would require actual choice, enumeration, operation and resource adapters. |
| `TreeMap.getElem?_emptyc`, `getElem?_insert`, `getElem?_erase`, `size_erase`, `size_map`, `ordered_keys`, `ordered_keys_toList`; `Std/Data/TreeMap/Lemmas.lean` | These require `[Std.TransCmp cmp]`; insert/erase branch on `cmp stored query = .eq`. `mem_keys`, `mem_toList_iff_getElem?_eq_some` and the simple `getElem?_map` additionally require `[Std.LawfulEqCmp cmp]`. `foldl_eq_foldl_toList` is an unconditional exact fold equation. |
| `Std.TreeSet` insert/erase/diff/foldl/toList/min? and laws; `Std/Data/TreeSet/Basic.lean`, `Lemmas.lean` | `mem_toList` needs TransCmp and LawfulEqCmp; ordered_toList, size_erase and mem_diff_iff need TransCmp. `foldl_eq_foldl_toList` identifies ascending iteration. `min?_eq_none_iff` needs TransCmp; `min?_eq_some_iff_mem_and_forall` also needs LawfulEqCmp. This is minimum selection, which differs from source choose. |
| `SimpleGraph` fields `Adj`, `symm : Std.Symm Adj`, `loopless : Std.Irrefl Adj`; Mathlib `Combinatorics/SimpleGraph/Basic.lean` | Reuse for the graph observation after discharging precisely undirected and no_selfloop. It has no explicit stored domain and cannot replace the raw graph or its cardinality/isolated-vertex behavior. |
| `SimpleGraph.induce`, `induce_adj`; `SimpleGraph/Maps.lean`; `Coloring`, `Coloring.mk`, `Coloring.valid`; `Coloring/Vertex.lean` | `Coloring` is a total graph homomorphism into a complete graph. Apply it to the induced graph on the actually colored domain, with palette-subtype colors after proving the stronger all-bindings palette property. A partial map is not a total coloring of all PosNum vertices. |
| `Search.Heuristic.Graph V := V → List (V × Nat)`; `Applications/Search/HeuristicCore.lean` | Existing conaled graph clients use successor lists with weights. That interface does not enumerate stored vertices or retain explicit empty bindings. A graph observation can be adapted with unit weights if a client needs it; it is not a replacement finite representation or an additional mandatory search algorithm. |
| `SquareKit.ListFusion.foldl_reachable`, `foldr_reachable` | Reuse fold transport with a proved reachable accumulator invariant and commuting step. Preserve traversal order and the same original graph in every coloring step. The lemma does not supply those step laws automatically. |
| `Squares.Rep`, `Square`, `compose`, `vertical` | Package established optional-map and finite-observation correspondences. Existing packaging uses one universe; retain more general plain theorems where packaging would impose an unnecessary restriction. Exact meaning does not entail resource equality. |
| `Resources.Measured`, `bind`, `bind_erases`, `reweight`, `erasureSquare`, and `isBigO_of_nat_bound` | Instrument the actual operation trajectory, prove erasure, and state primitive tariffs before a bound. Natural structural counts and executable timings are different evidence. |
| Lean `Decidable` in `Init/Prelude.lean`; accepted Perm/Decide reflection | Lean 4.35 stores an executable Bool decision and a reflection proof. Use its actual decisions for key equality and Nat low-degree tests. Opaque proof evidence is not a reason to add an axiom, classical executable choice, or a native-decision proof shortcut. |

## 3. Keys, finite observations, traversal, and choice

### Three distinct observations of a positive key

Use H/O/I for one/bit0/bit1. Numeric meaning is 1/doubling/doubling-plus-one.
Trie traversal reads the outer, low-order bit first. The source bit order puts
all O-keys before H and all I-keys after H, recursing for matching outer O or I.
Prove irreflexivity, transitivity, equality congruence, and the constructor
correspondence to the pinned provider. Its structural comparison, if exposed
for an ordered backend, must have `.eq ↔ key equality` and both strict branch
laws. Keep it explicit rather than changing PosNum's global numeric order.

The primary trie needs no key comparator during lookup/add/erase. Do not add
numeric conversions or ordered-tree searches to those source operations.
Source equality is ordinary PosNum equality, independently of both orderings.
Filter's equality test must therefore remove exactly the queried key.

In-order key enumeration and source choice remain separate observations.
Choice on a node returns H immediately when its Boolean payload is true;
otherwise it takes a left result and wraps O, or, if there is no left result,
takes the right result and wraps I. Nil chooses none. Establish these exact
equations, membership on success, none iff empty observation, and extensional
choice agreement. Empty padding must not change the chosen key. Minimum in
bit order instead considers the left subtree before the root. On {1,2}, the
source chooses 1 and the bit minimum is 2. This is an essential checked
counterexample to the tempting library substitution.

### Required finite-operation laws

State laws on arbitrary raw maps/sets before adding any resource invariant.
For generic map payload A, assume no equality/order/Inhabited structure on A.

| Operation/observation | Required contract |
| --- | --- |
| Map lookup and add | Empty gives none. Writing k↦v gives some v at k and leaves every other optional lookup unchanged. The entire optional function is an accepted Maps update. |
| Set membership and add | Empty has no members; membership after adding k is exactly equality to k or prior membership. Repeated insertion does not increase extensional cardinality. |
| Erase and pruning | Erase k removes its binding/membership and preserves all other observations. Expose the source pruning equations, including absent keys and noncanonical all-empty internal nodes. A normalized result must not be assumed for an arbitrary unnormalized input. |
| Set difference | Membership is membership in the left input and absence from the right input. Preserve source simultaneous traversal and empty-input branches in the concrete operation. |
| Value-only map | Lookup becomes Option.map f; domain/occupied keys/cardinality are unchanged. BinaryTree.map realizes its result through a proved adapter; map does not discard values just because they equal a default. |
| Set elements | Exact bit-sorted List PosNum, complete/sound for membership, without duplicates. Elements equality is literal list equality. Cardinality equals its length and the Finset observation's card. |
| Map elements | Exact bit-sorted List (PosNum × A), complete/sound for successful optional lookup, with distinct keys. Values are retained unchanged and impose no order. Cardinality equals list length and finite domain card. |
| Erase/enumeration | Elements after erase are the original sorted elements filtered by key inequality. Map version is pointwise key-and-value relatedness, equivalent here to literal pair/list equality. Retain the source member-premised corollaries even if the general lemma needs no premise. |
| Map/set folds | Prove equality to a **left fold** over the respective ordered elements, with arguments rearranged to match source. Mdomain/subset_nodes/colors_of use those folds. Any unordered Finmap fold route must first prove the particular step commutes at the required observation. |
| Occupied cardinality | A map node contributes one iff its optional payload is some; a set node contributes one iff its Boolean is true. Present keys may carry empty sets. Erasing a present key loses exactly one occupied entry; absent-key erasure preserves cardinality. |
| Raw equality versus observations | Finmap/Finset equality and S.eq are extensional. Equal optional lookup/set membership does not imply equality of padded raw tries. Preserve that distinction in folds and statement review. |

The inspected Rocq provider details explain the fidelity boundary: map
enumeration/fold carries a forward positive prefix; set enumeration/fold carries
a reversed prefix and reconstructs keys at present nodes. Both folds agree
with left folds over bit-ordered elements. The source prose's nested expression
at 123–130 must not reverse this order. Map enumeration uses append, whereas
set enumeration uses an accumulator. Generic value-only map is defined through
key-indexed mapi. These choices affect path construction and list work even
when final observations agree. Provider locations and hashes are below.

### List relations and canonical enumeration

Adapt `InA R x xs` to an existential related member, `equivlistA R xs ys` to
equivalent such membership for every query, and `eqlistA R` to List.Forall₂ R.
Keep the mod-10 examples: 27 is related to the member 17; `[3,17]` and `[7,3,27]`
have equivalent related membership despite different lengths. They are not a
permutation or a multiplicity equality.

The generic sorted-equivalent-lists fact requires an equivalence relation,
an irreflexive transitive order, and compatibility of the order with the
equivalence. The displayed theorem does not require totality, despite the
surrounding prose twice saying total order. Preserve the weaker valid theorem.
Reuse a suitable accepted relation lemma or prove the small quotient/Forall₂
adapter to the inspected Pairwise uniqueness theorem; do not impose a linear
order on arbitrary payloads. For E.eq and eq_key_elt, ordinary equality
specializations recover literal key or pair equality. Source Sorted's
constructor/IsChain meaning and its transitive Pairwise equivalence remain
explicit. Filter/map/source-enumeration arguments must use the corresponding
relation, not a numeric-order shortcut.

## 4. Exact graph program and proof obligations

The following equations specify future obligations; they are not Lean code
added by this planning assignment. S and M denote the source-compatible finite
operations above. Keep graph operations on raw maps; graph hypotheses are
separate propositions, never prerequisites hidden in the carrier.

### Raw graph and removal

- Node is PosNum; nodeset is the finite positive set; nodemap A is the sparse
  finite optional map; graph is a nodemap of nodesets.
- `adj g i = (find i g).getD emptySet`. Absence and a stored empty adjacency set
  give the same adjacency observation but different domain membership.
- `undirected g` means `j ∈ adj g i → i ∈ adj g j` for every i,j.
  `no_selfloop g` means `i ∉ adj g i` for every i.
- `nodes g = Mdomain g`; Mdomain folds key insertion over every binding.
  Prove `n ∈ nodes g ↔ ∃ a, find n g = some a`, retaining explicit empty bindings.
- `subset_nodes P g` folds over the actual bindings, inserting n exactly when
  `P n adjacency = true`. Prove its exact membership characterization and then
  the source subset lemma for every Boolean P, without graph validity assumptions.
- `low_deg K n adjacency` is the Boolean strict comparison `card adjacency < K`;
  its node argument is intentionally unused. Degree K is not eligible.
- `remove_node n g = mapValues (eraseSet n) (eraseMap n g)`: erase the binding,
  then remove n from **every** remaining stored adjacency set, including sets
  that did not contain n. Do not replace the whole-map pass with a worklist
  or only-known-neighbor update while claiming the same recurrence.

Prove the precise optional-lookup law for removal: at n, none; at i≠n,
the previous optional set mapped by set erase n. It gives domain erasure,
occupied cardinality `card g - 1` when n is present, adjacency restriction,
and preservation of undirected/no_selfloop separately. Raw adjacency sets may
mention keys absent from the map; termination is still valid. Under undirected,
a referenced neighbor has a reverse edge and therefore a stored binding;
derive this domain-closure fact instead of adding an unmentioned hypothesis.

### Selection, termination, and source order

For fixed K, compute L = subset_nodes (low_deg K) g and branch on source choose L:

| Result | Exact selection equation |
| --- | --- |
| `none` | Return `[]`, even if g still has bindings. |
| `some n` | Return `n :: select K (remove_node n g)`. K remains unchanged. |

Membership of a successful choice, subset_nodes_sub, Sin_domain, value-map
cardinality preservation, and present-key removal give the required strict
decrease in map cardinality. Use Lean's well-founded definition with this
measure and expose the two equations. A fuel implementation is acceptable
only with an exact all-input equivalence and adequate-fuel proof; arbitrary
fuel exhaustion is not the source None branch. No graph symmetry, looplessness,
positive K, or degree bound is needed to establish termination.

Also prove that each chosen vertex is present and low-degree in its current
residual graph; the list has no repetitions; its length is at most the initial
domain card; and removing its prefix leaves exactly the unremoved initial
domain, with original adjacency sets restricted by those removals. When the
algorithm stops, every remaining binding fails the low-degree test. The list
does not necessarily cover all initial vertices. At K=0 it is empty for every g.

### Colors, available choices, and original adjacency

Coloring is a finite optional map from node to node/color; it has no default
color. `colors_of f s` folds over s and inserts c exactly when a visited neighbor
has optional binding some c in f. Absent neighbors contribute nothing; repeated
neighbor colors collapse as set members. Prove the stronger equivalence
`c ∈ colors_of f s ↔ ∃ n ∈ s, find n f = some c`; the source forward introduction
lemma follows. Do not treat an absent color as positive 1, Nat 0, or a palette member.

For one step, let A = palette \ colors_of f (adj g n). If source choose A returns
some c, `color1 palette g n f` overwrites n with c; if it returns none, the result
is **the unchanged f**. In particular, this helper's failure branch does not
erase an existing binding at n. Prove the exact optional-lookup equations and
the available-color membership/exclusion facts.

`color palette g` is the right fold of `color1 palette g` from the empty coloring
over `select (card palette) g`. Thus coloring proceeds in the reverse of the
removal list. Every step reads adjacency in the **original g**, not the current
residual graph from selection. The fold-right/reverse-fold-left theorem supplies
the alternate execution presentation without changing update order.

### Partial correctness and stronger implementation facts

Preserve the source predicate literally:

For every i,j with `j ∈ adj g i`, (a) any binding `find i f = some ci` has ci in
the palette, and (b) any two successful bindings at i and j have distinct colors.
The edge premise guards **both** clauses. On an isolated or wholly unrepresented
vertex, this predicate alone puts no restriction on an arbitrary candidate color.
It asserts no totality, optimal chromatic number, maximal colored domain, minimum
spilling, or correctness of compilation/register allocation.

Prove the source theorem for every finite palette and raw graph, assuming exactly
no_selfloop and undirected. A useful general proof first shows color1 preserves
edge compatibility on every already-compatible coloring. The case i=n uses
colors_of exclusion; the case j=n uses symmetry to obtain the reverse adjacency;
the double-equality case contradicts no_selfloop; other bindings are unchanged.
This works even when n was already colored. Therefore right-fold correctness
holds for **any finite list, including repeated vertices**, without a NoDup,
degree, or selection premise. The source theorem then specializes that result
to the actual computed selection list. Its correctness proof does not license
replacing the implemented selection algorithm with a different order.

Separately prove `AllPalette f := ∀ n c, find n f = some c → c ∈ palette`
for the produced coloring, by an invariant starting at empty. This stronger
property does not require graph hypotheses and covers isolated colored vertices.
Prove the produced domain is contained in the selected set, hence in nodes g.
Use the low-degree condition and the prefix/residual adjacency lemma to justify
that already colored neighbors at each source step use fewer than card palette
colors; a finite-set image bound yields a nonempty available set. This supplies
the stronger source-specific fact that every selected vertex gets a color.
Thus the produced domain equals the selected set for arbitrary raw graphs;
symmetry and looplessness are not needed for this support equality.
Its proof must retain the exact support and residual-graph correspondence;
the all-original-degree bound is generally false for vertices removed later.
No graph-closure premise may be silently inserted. This strengthening and the
phase-two partial-correctness theorem have different proof dependencies.

For a class of finite graphs closed under removal and having an eligible node
whenever nonempty, selection covers its entire domain. A conditional total-
coloring corollary explains the low-degree motivation without claiming planarity
or a four-/five-color theorem. A graph with a remaining high-degree core may
still be colorable; this source program simply stops selecting that core.

Connect the result to the existing Mathlib SimpleGraph interface: under the two
graph hypotheses, restrict the graph to the finite colored domain and use
lookup's successful value as a total color in the palette subtype. Prove the
Coloring.mk condition from edge compatibility. Preserve explicit domain data
alongside the SimpleGraph observation; isolated stored vertices would otherwise
be indistinguishable from absent vertices.

### Concrete graph construction

Preserve `add_edge (i,j) g` as an outer write at i and an inner write at j;
both adjacency reads use the **original g**. For distinct endpoints it inserts
both directions. Equal endpoints produce a self-loop, not an automatic loop
filter. Duplicate or reversed edges are extensionally idempotent as sets;
raw equality requires its own proved statement if claimed. `mk_graph` is a
right fold of add_edge from empty. Prove undirectedness for its output and
looplessness under the precise premise that every input edge has distinct
endpoints. Do not assume the arbitrary helper rejects invalid edges.

The exact palette is [1,2,3] inserted by right fold. The exact edge list is
`[(5,6),(6,2),(5,2),(1,5),(1,2),(2,4),(1,4)]`. Kernel-check and actually execute
the expected bit-ordered outputs:

- domain elements: `[4,2,6,1,5]`;
- color entries: `[(4,1),(2,3),(6,2),(1,2),(5,1)]`.

Prove the graph hypotheses and instantiate the general theorem on this same
computed output. A different valid coloring is insufficient for these exact
source executions. Numeral adapters must display unshifted positive values.

## 5. Complete declaration-to-Lean coverage map

All 53 inventory IDs occur exactly once in this table and in source order.
Each target below is a required obligation or a justified reuse/adapter, not
an assertion that the declaration has already been implemented. Source line
numbers refer to the pinned file, not to an independently changing webpage.

| Source record | Intended obligation/reuse |
| --- | --- |
| `Color.lt_strict@117` | Establish the explicit bit relation's irreflexivity and transitivity, matching E.lt. Reuse a proved comparator relation only after its constructor correspondence; numeric PosNum order is different. |
| `Color.lt_proper@120` | Equality congruence of the bit relation in both arguments, as an iff. No extra representation or quotient assumption is necessary when E.eq is equality. |
| `Color.Mdomain@132` | Exact ordered map fold inserting every occupied key into an initially empty set, independently of the payload. Prove optional-presence/domain semantics and finite cardinality correspondence. |
| `Color.example_map@139` | Preserve the nested writes of empty sets at keys 2,9,3, with 3 outermost; the map has these three bindings despite their empty values. |
| `Color.domain_example_map@144` | Kernel-checked exact elements `[2,9,3]` in bit order, connected to the domain theorem. It is not the numerically sorted list. |
| `Color.same_mod_10@166` | Nat remainder equality as the relation; exhibit its equivalence laws for the generic list-relation explanation without changing it to actual Nat equality. |
| `Color.InA_example@167` | A related-member witness for 27 in `[3,17,2]`, using 17 and the mod-10 relation. |
| `Color.equivlistA_example@173` | Equivalent related membership of `[3,17]` and `[7,3,27]`; explicitly different list lengths/multiplicities remain possible. |
| `Color.goal_at_line_226@226` | The E carrier alias is the chosen positive carrier, with the source positive ↔ PosNum constructor correspondence. Adapt the source definitional type-identity demonstration. |
| `Color.goal_at_line_227@227` | The E equality relation is ordinary equality on that carrier. Keep this separate from bit/numeric order. |
| `Color.eqlistA_Eeq_eq@231` | Forall₂ equality iff literal list equality, via `forall₂_eq_eq_eq`, retaining both directions for all lists. |
| `Color.SortE_equivlistE_eqlistE@242` | Bit-sorted lists with equal membership are pointwise/literally equal. Use the generic compatible strict-order/setoid adapter and the inspected Pairwise uniqueness theorem. |
| `Color.filter_sortE@255` | Every Boolean filter preserves source bit sortedness, via the explicit Sorted/IsChain/Pairwise bridge and Pairwise.filter. |
| `Color.Sremove_elements@275` | Pedagogical Abort: record the intended removal/filter equality and connect it to the later completed theorem. It is not a separate axiom, failed mathematical proposition, or duplicate implementation. |
| `Color.Proper_eq_eq@285` | Every key→Bool function respects E.eq because it is ordinary equality. The source admission must be replaced by a proof. |
| `Color.Sremove_elements@291` | If i is present, exact ordered elements after removing i equal filtering i out. Prove the possibly stronger unconditional law from membership and canonical order, then retain this source-premised form; discharge all four inner admits and the final admission. |
| `Color.InA_map_fst_key@328` | For any payload A and arbitrary pair list, key membership in mapped fst iff some payload forms a related pair member. List.mem_map supplies the existential witness; no unique-key premise. |
| `Color.Sorted_lt_key@341` | Sortedness by pair first components iff source bit sortedness of mapped first components. Values remain unordered; use pairwise_map and the source sortedness bridge. |
| `Color.cardinal_map@356` | For any A,B,f,g, mapping values preserves occupied cardinality/domain. Reuse BinaryTree.map with the optional-payload correspondence or prove by finite keys; do not use raw numNodes as cardinality. |
| `Color.Sremove_cardinal_less@377` | Removing a present set member strictly decreases card; stronger card−1/add-one law through the Finset observation. Keep the membership premise. |
| `Color.specialize_SortA_equivlistA_eqlistA@392` | For arbitrary A, sorted lists of pairs with equivalent key-and-value membership are pointwise related. E.eq is equality; key-and-value relation is literal pair equality, while the ordering uses only keys. |
| `Color.Proper_eq_key_elt@409` | Pair key order respects key-and-value equality in each argument. No comparison or equality decision on values is required. |
| `Color.Mremove_elements@418` | Under map-domain membership, elements after erase are Forall₂ eq_key_elt related to filtering that key from original elements. Preserve values and order; supply the unconditional strengthened variant if reused. |
| `Color.Mremove_cardinal_less@438` | A present key's removal strictly decreases occupied map card; use domain erasure/card−1 and positivity, not a conjecture about raw tree size. |
| `Color.fold_right_rev_left@449` | Exact arbitrary-type/function equation: left fold equals right fold with reversed list and flipped arguments. Reuse `List.foldl_eq_foldr_reverse`. |
| `Color.Snot_in_empty@454` | No positive key belongs to the empty source set, through the concrete membership equation. |
| `Color.Sin_domain@459` | Set membership in Mdomain iff existence of a successful optional binding in the finite map. Prove by the actual fold/finite-observation law, including present empty/default payloads. |
| `Color.node@470` | Alias the accepted positive carrier; source numerals retain their unshifted meaning. |
| `Color.nodeset@471` | Source-compatible finite Bool-trie set on that carrier, with Finset observation and source choice; no generic mathematical Set substituted as executable storage. |
| `Color.nodemap@472` | Polymorphic sparse optional-payload trie, with the used finite-map operations and proved laws. Preserve arbitrary payload universes where the actual APIs permit. |
| `Color.graph@473` | Raw finite map of adjacency sets, without graph validity hidden in its type. |
| `Color.adj@475` | Find-or-empty adjacency, keeping its default adapter separate from optional binding/domain. |
| `Color.undirected@478` | Exactly global symmetry of adjacency membership as the source implication; no enumeration or finite-domain premise added. |
| `Color.no_selfloop@481` | Exactly absence of each vertex from its own adjacency; not assumed of arbitrary graph constructors or helpers. |
| `Color.nodes@483` | Source alias of the occupied map domain; isolated stored vertices remain nodes. |
| `Color.subset_nodes@485` | Exact map fold with the supplied Boolean predicate, preserving input binding payloads and ordered execution; prove the full membership characterization. |
| `Color.low_deg@492` | Strict Nat cardinality comparison with fixed K and unused node argument; prove Boolean reflection including K=0 and degree=K. |
| `Color.remove_node@494` | Erase the vertex binding then map set-erasure over all other adjacency values; prove optional-lookup, domain/cardinality and graph-hypothesis preservation laws. |
| `Color.subset_nodes_sub@504` | For every P,g, chosen subset is contained in nodes g. No symmetry, looplessness, or semantic-congruence premise is needed for this same-representation statement. |
| `Color.select_terminates@509` | A successful choice is present in the map; erasure loses one binding and value-map preserves count. Strict decrease is unconditional on graph validity and K. |
| `Color.select@520` | Faithful well-founded recursion on cardinality, exact some/none equations, fixed K, and source deterministic choice. None stops on a nonempty high-degree core. Prove selection support/NoDup/current-degree and residual-domain facts separately. |
| `Color.coloring@528` | Sparse finite optional map node→color with no default color, even though colors and vertices share the positive carrier. |
| `Color.colors_of@530` | Source set fold, optional lookup, insertion only for some c. Prove its existential image-membership equivalence and image-cardinality bound. |
| `Color.color1@533` | Difference of palette and used neighbor colors, source choose, overwrite on success and unchanged coloring on failure; exact helper behavior even when n is already bound. |
| `Color.color@539` | Right fold from empty over source select with K=palette card; reverse removal order and original g for every adjacency query. |
| `Color.coloring_ok@549` | Retain the exact edge-guarded palette and pairwise color-distinctness clauses. Do not silently strengthen this definition to all-bindings palette membership or total coloring. |
| `Color.adj_ext@555` | Equal keys give extensionally equal adjacency sets; literal key equality is enough. Source S.eq is set equivalence, not an assertion that equivalent arbitrary raw sets are structurally equal. |
| `Color.in_colors_of_1@560` | A neighbor member with successful color lookup contributes that color to colors_of. Specialize the stronger existential membership law. |
| `Color.color_correct@566` | For every palette and graph satisfying no_selfloop and undirected, the actual computed color satisfies the exact source predicate. Prove a general phase-two invariant and instantiate it on the real selection output. |
| `Color.palette@582` | Exact right-fold insertion of positive colors `[1,2,3]`; distinguish its bit enumeration from source choose order. |
| `Color.add_edge@584` | Nested endpoint writes with both old-adjacency reads from original g; explicit distinct/self-loop/duplicate/reversed-edge cases. |
| `Color.mk_graph@588` | Exact right fold of add_edge from empty; prove edge-membership characterization, symmetry, and looplessness under distinct endpoints. |
| `Color.G@591` | Preserve all seven edges in source order, derive its five stored vertices and graph hypotheses, and use it for both exact computations and the public correctness/graph-observation client. |

## 6. Exercises, module aliases, commands, and substantive prose

### Exercise reconciliation

There are fourteen exercises, all standard. The two multi-declaration exercises
are retained; the aborted earlier statement is mapped in the declaration table.
No optional/advanced exercise is missing, and no manual-grading stub occurs here.

| Exercise | Stars; source range | Required coverage |
| --- | --- | --- |
| Sremove_elements | 3; 284–314 | Proper_eq_eq and the completed erase/filter theorem, including every inner admit. |
| InA_map_fst_key | 2; 327–332 | Existential payload witness for projected-key membership. |
| Sorted_lt_key | 3; 334–346 | Both directions of key-projected sortedness. |
| cardinal_map | 4; 355–374 | Occupied-cardinality preservation for arbitrary value map. All ten Check hints have a documented Lean counterpart. |
| Sremove_cardinal_less | 4; 376–385 | Member-premised strict set-cardinality decrease. |
| Mremove_elements | 4; 417–435 | Ordered map erase/filter correspondence with values intact and all nine hints accounted for. |
| Mremove_cardinal_less | 3; 437–445 | Member-premised strict map-domain-cardinality decrease. |
| two_little_lemmas | 2; 447–456 | Both reverse-fold equation and empty-set nonmembership. |
| Sin_domain | 3; 458–465 | The exact iff; fold_rec_bis is a proof hint, adapted to fold induction/observation transport. |
| subset_nodes_sub | 3; 503–506 | Arbitrary Boolean predicate, arbitrary raw graph. |
| select_terminates | 3; 508–514 | Successful source choose implies strict cardinality decrease. |
| adj_ext | 2; 554–557 | E equality implies extensional adjacency-set equality. |
| in_colors_of_1 | 3; 559–563 | Membership plus successful lookup contributes a color. |
| color_correct | 4; 565–572 | Exact partial-coloring theorem under precisely the two graph hypotheses. |

### Module reconciliation

These aliases become namespace/API views and checked realizations, not axioms
declared to reproduce module signatures. Printing a whole module is a language
demonstration, not a demand to duplicate every unused Stdlib member.

| Source module | Line | Lean treatment |
| --- | --- | --- |
| E = PositiveOrderedTypeBits | 73 | PosNum carrier, literal equality, explicit bit-order relation and used decision/order laws. |
| S <: FSetInterface.S = PositiveSet | 81 | Bool-tree realization of the used finite-set API, with separate membership/cardinality/enumeration/fold/choice proofs. |
| M <: FMapInterface.S = PositiveMap | 87 | Optional-payload-tree realization of the used polymorphic finite-map API; optional absence stays observable. |
| WF = WFacts_fun E M | 101 | Reuse proved finite-map facts, especially map/lookup correspondence, through the actual realization. |
| WP = WProperties_fun E M | 102 | Fold reasoning via standard List induction and existing fusion/finite observations; no placeholder law parameter left uninstantiated. |

### All 35 pedagogical commands

Use concise public `#check`/`#print` demonstrations or explanatory references
where source mechanics do not have a literal Lean command. For computation,
both kernel-checked expected output and an actual executable run are required.

| Source command | Meaning and Lean obligation |
| --- | --- |
| Print @74, Module E | Display/document the chosen carrier/equality/order view and its proved realization. |
| Print @75, E.t | Positive carrier alias; connect to its constructor adapter. |
| Print @82, Module S | Finite-set operations separate from laws, with exact choose exposed. |
| Print @83, S.elt | Same positive key carrier; no numeric-order replacement. |
| Print @88, Module M | Polymorphic optional-map operations and proved realization. |
| Print @89, M.E | Map and set share the exact positive-key view and equality. |
| Print @103, Module WF | Show the relevant lookup/map facts, not a copied module-functor hierarchy. |
| Print @104, Module WP | Show the fold/finite-domain proof route. |
| Check @106, E.lt | Explicit nonnumeric Prop relation on positive keys. |
| Print @151, equivlistA | Equivalent membership modulo a relation; preserve its difference from Perm. |
| Check @203, SortA_equivlistA_eqlistA | Equivalence + compatible strict order + two sortedness proofs + equivalent membership yield pointwise related lists; no totality assumption added. |
| Check @268, S.remove | Key→set→set erase operation, with its actual pruning adapter. |
| Check @269, S.elements | Ordered list observation on a finite set. |
| Check @322, M.elements | Arbitrary-payload list of key/value pairs, with distinct keys. |
| Check @362, M.cardinal_1 | Occupied cardinality equals elements length. |
| Check @363, M.elements_1 | Successful binding implies pair membership in elements. |
| Check @364, M.elements_2 | Pair membership implies the same successful binding. |
| Check @365, M.elements_3 | Source key-order sortedness of pairs, independent of value order. |
| Check @366, length_map | Existing List.length_map. |
| Check @367, eqlistA_length | Existing Forall₂.length_eq after the relation adapter. |
| Check @368, SortE_equivlistE_eqlistE | Previously proved canonical-list equality specialization. |
| Check @369, InA_map_fst_key | Previously proved existential payload/key-membership equivalence. |
| Check @370, WF.map_mapsto_iff | Binding after value map iff an original bound value maps to the result; does not require f injective. |
| Check @371, Sorted_lt_key | Pair-key order iff projected-key order. |
| Check @424, specialize_SortA_equivlistA_eqlistA | Compatible pair-relation specialization for map elements. |
| Check @425, M.elements_1 | Reuse binding-to-elements direction in removal proof. |
| Check @426, M.elements_2 | Reuse elements-to-binding direction in removal proof. |
| Check @427, M.elements_3 | Reuse source sortedness after removal. |
| Check @428, M.remove_1 | Removed key has no binding. |
| Check @429, M.eqke_equiv | Key-and-value equality is an equivalence; no DecidableEq payload needed. |
| Check @430, M.ltk_strorder | Strict key order on pairs, with equal-key pairs incomparable. |
| Check @431, Proper_eq_key_elt | Key ordering respects pair equality in both arguments. |
| Check @432, filter_InA | Related membership in a Boolean filter under the appropriate predicate-congruence condition; ordinary equality specialization uses List.mem_filter. |
| Compute @594, domain of G | Exactly `[4,2,6,1,5]`, with all numerals decoded unshifted. |
| Compute @596, color of G | Exactly `[(4,1),(2,3),(6,2),(1,2),(5,1)]`, plus connected theorem use. |

### Substantive prose and unlisted language mechanics

| Source range | Required treatment |
| --- | --- |
| 3–9, reading list | Required slides read and reconciled; suggested sophisticated coalescing implementation remains a contextual reference, not substituted for the simple chapter program. |
| 11–27, coloring/chromatic number/history/complexity | Explain proper coloring and chromatic number using existing graph vocabulary. The decision problem for fixed k≥3 is the relevant NP-complete problem; two-colorability differs. Absence of a polynomial-time algorithm follows only conditionally on P≠NP, not as an unconditional theorem. Historical four-color discussion adds no axiom or separate planar theorem obligation. |
| 29–43, partial colorings and register allocation | Prove the actual interference constraint property. State that minimizing uncolored nodes, actual spill code, coalescing and worklist optimization are unspecified. Keep the simple program's repeated scans and residual high-degree core. |
| 45–57, efficient finite representation | Connect actual finite optional maps/sets to their observations and bit-path bounds. Do not infer whole-algorithm linearity, constant-time cardinality, or runtime allocation from the word efficient. |
| 59–114, imports, aliases and order facts | Adapt List/Setoid/FSets/FMaps/PArith/Perm imports idiomatically; retain shared key equality and the explicit nonnumeric relation. Lean uses its actual decision/reflection API, not source tactic syntax. |
| 123–160, domain folds and equivalent lists | Occupied bindings, exact left-fold convention, source domain example, related-membership semantics including repeated elements. |
| 185–224, canonical list theorem | Retain general equivalence/order compatibility and the displayed theorem's actual strict-order assumptions. Sortedness plus only set membership is sufficient because strict order forbids duplicates; non-strict order would not. |
| 226–281, equality and aborted removal proof | Preserve two type/relation identity demonstrations, literal-list equality adapter, filtering and the delayed successful removal proof. Abort is pedagogical, not an admissible project declaration. |
| 284–435, proof hints, pair keys and cardinality | Discharge each exercise with actual API laws. Search/tactics and Check hints are idiomatic Lean adaptations; the mathematical conclusions and member/value witnesses remain required. |
| 447–465, folds and domain proof | Arbitrary reverse-fold identity and finite-domain proof. fold_rec_bis can be replaced by actual fold induction/fusion, preserving accumulator invariants. |
| 469–526, program and well-founded definition | Exact raw graph operations, cardinal measure, fixed K, successful-choice decrease. Recdef import is a Lean termination_by/decreasing proof adaptation. Source Defined/Qed advice is explained using the actual accepted Decide transparency treatment, not asserted as a Lean rule. |
| 528–572, coloring and correctness | Optional colors, actual source choice, right-fold order, original-graph adjacency, and precisely edge-guarded partial-coloring contract. The source concluding sentence follows an admission; completed Lean proofs must replace it. |
| 577–599, positive scope and execution | Source positive numeral scope becomes explicit checked numeral/constructor adapters. Preserve both folds, all seven edges, both exact outputs and a correctness instance; no additional performance benchmark is requested here. |

## 7. Resource and execution obligations

Follow the existing resource-contract distinction between value refinement,
instrumentation/erasure, termination, exact primitive counts, asymptotic families
and measured execution. The chapter's efficiency prose supplies no theorem
that these repeated map scans are linear or that all finite-set operations
are constant-time. It requests a concrete execution, not a comparative timing
benchmark. Preserve that scope while giving the substantive efficiency claim
an explicit structural model.

### Actual trajectory and exact callback counts

Let `g₀ = g`, `n = card g`, `r = length (select K g)`, and gₜ be the residual
graph after t successful removals. Prove `card gₜ = n-t` for `0 ≤ t ≤ r` and
`r ≤ n`. Let Lₜ be the actual low-degree candidate set at stage t. Instrument
the executed operations, using Measured and erasure proofs, with terminal
events explicitly separated from callbacks at occupied entries.

| Measured event | Required exact statement |
| --- | --- |
| Calls to select / candidate-set choose | Each is `r+1`, including the final unsuccessful call. |
| subset_nodes predicate evaluations | `Σ t∈{0,…,r}, (n-t)`; the entire map fold runs before each choose, including the last stage. |
| low_deg comparisons and adjacency-cardinality requests | Exactly the same sum, one of each per predicate evaluation. These are top-level comparisons, not bit/constructor counts of Nat comparison. |
| Candidate set insertions | `Σ t∈{0,…,r}, card Lₜ`, because each binding occurs once in the fold and a true predicate inserts once. The cost of each insertion remains separate. |
| Vertex-map erasures / value-map invocations | Each is r; both occur only on a successful selection branch. |
| Adjacency set-erasure callbacks inside mapValues | `Σ t∈{0,…,r-1}, (n-t-1)`, since the chosen binding is erased before mapping values. This counts attempts even when the adjacency set lacks the removed vertex. |
| Main coloring steps / colors_of / palette difference / color-choice calls | Each is r; fold termination adds one terminal list event. Palette cardinality is evaluated once to fix K in color. |
| Neighbor color lookups inside colors_of | `Σ v∈select K g, card (adj g v)`, over the **original** graph; do not use residual degrees here. |
| Neighbor-color set insertions | One per successful neighbor-color lookup, possibly repeated insertions of the same color. Cardinality of the resulting used-color set is not this insertion count. |
| Coloring-map writes | Generally at most r; for the actual K=card palette selection and proved selected-support result, exactly r. A generic arbitrary-list color1 fold can have failed choices. |

The first sum is `(r+1)*n - r*(r+1)/2`; the adjacency-removal callback sum is
`r*n - r*(r+1)/2`. Use a Nat-safe triangular-sum formulation/proof rather than
silently performing truncated subtraction algebra. When r=n they specialize
to `n*(n+1)/2` and `n*(n-1)/2`. Thus full selection already has quadratically
many degree tests and adjacency-erasure callbacks, before charging the work
inside any finite operation. For the source five-node graph, the corresponding
checked counts are 15 and 10.

`M.cardinal g` used solely as the well-founded termination measure is proof
data in the planned Lean recursion. Do not count an extra executable graph-
cardinality traversal at every select call without observing one in the actual
chosen implementation. Conversely, the `S.cardinal adjacency` in low_deg and
the initial palette cardinality are executable and must be charged. If an
alternative adequate-fuel realization computes a measure, its setup cost is
part of that realization and does not disappear by semantic equivalence.

### Primitive work and representation assumptions

Retain raw structural node counts independently of occupied cardinalities.
There are arbitrarily large empty observations represented by padded raw tries.
In particular, n=0 can coexist with arbitrarily many raw structural nodes, so
zero entry callbacks do not imply zero traversal work.
Consequently no bound in terms of n, degrees and maximum **present** key alone
can describe every raw input's traversal. Define a normalization predicate
separately: recursively, an unoccupied internal node must have a nonempty
child. Prove each used operation preserves it on normalized inputs. It is
true of the examples constructed from empty by insertion, but is not a premise
of the semantic source theorem.

| Primitive | Required work model and limit |
| --- | --- |
| Path lookup, add and erase | Count key/path constructor visits and rebuild events; bound by the positive key bit length with terminal convention explicit. Reuse accepted Trie results only after the exact optional/Bool/pruning adapters. Erasing may stop early at Leaf. |
| Set/map cardinality | Count every structural trie node and the additions/occupied increments. This is a traversal in the source realization, not a cached size read. Raw cardinality zero does not imply zero work. |
| Map fold / domain / subset folds | Charge structural traversal, actual forward-prefix reconstruction, callback work and accumulator insertions. Source forward append of a key prefix traverses that prefix; one callback per binding does not imply one unit of total work per binding. |
| Value map in remove_node | Charge structural map traversal and every invoked adjacency erase. If realized by BinaryTree.map after the adapter, use that actual recurrence. Source mapi's unused-key path construction has a different count; do not report equality of the two count functions. |
| Set fold / colors_of | Charge structural visits, reversed-path reconstruction at occupied nodes, every neighbor-color lookup and each successful color insertion. Duplicate colors still incur insert attempts. |
| Source choose | Charge root-first control flow, visited empty subtrees and constructor wrappers on the chosen path. General raw cost is bounded by the visited tree; a bit-height bound needs the appropriate normalization/nonempty-subtree argument. Both candidate sets built from empty and palette differences need their actual invariant proof. |
| Set difference | Charge its actual simultaneous traversal and pruning; left-empty/right-empty shortcuts matter. Do not replace it with a mathematical set subtraction and assume it is free. |
| Finite enumeration | Ordered list output has its actual traversal and key reconstruction cost. Source map enumeration also copies left lists by append, while set enumeration uses an accumulator. Execution/display that asks for elements must include export/conversion work; the coloring algorithm itself must not enumerate merely to obtain a proof observation. |
| Graph construction | For each input edge, charge two original-adjacency reads, two set insertions and two map writes in the stated order, plus list-fold traversal. Input-edge multiplicity and the number of distinct adjacency entries are different size parameters. |
| Arithmetic and data conversion | State costs for Nat additions/comparisons, positive key construction, parsing, numeric decoding and output. PosNum/PNat equivalences establish values, not free conversions. No hidden finite-word bound or machine-unit comparison assumption. |

For a useful conditional bound, take normalized graph/map/set inputs and palette;
let D be the sum of stored adjacency cardinalities, k the palette cardinality,
and Bₙ,B꜀≥1 bound positive bit lengths of all graph keys/mentioned neighbors
and palette colors respectively. Prove raw trie size ≤ the sum of occupied key
bit lengths before using `Tmap ≤ n*Bₙ`, total adjacency tree size `≤ D*Bₙ`, and
palette tree size `≤ k*B꜀`. This condition includes dangling neighbors if present;
undirectedness is not needed for a structural work bound. Removal only decreases
the relevant supports; generated color keys and values satisfy the same bounds.

In an explicitly selected model counting trie constructors, copied key bits,
list events, callbacks, and **unit-cost Nat arithmetic events**, establish an
upper bound by a concrete fixed constant times

`n²*Bₙ² + n*D*Bₙ + D*(Bₙ+B꜀) + (n+1)*k*B꜀ + n + 1`.

The map-fold forward-prefix cost accounts for the squared bit factor; this
is a conservative proof target, not a claimed optimal bound or a runtime
measurement. Derive the bound from the actual instrumented recurrence and
preserved invariants. If arithmetic is charged by bit/unary work instead,
retain its summed tariff as an additional term; do not carry this unit-event
bound over unchanged. If a better traversal is chosen, prove its value and
resource bridge and label its changed recurrence. Use Resources.isBigO_of_nat_bound
only for an explicitly fixed one-parameter input family after supplying the
constants, size interpretation and primitive model. No O(n), O(log n), optimal
spilling, physical heap, garbage-collection or wall-clock claim is implicit.

### Required execution evidence

After implementation acceptance prerequisites permit it, run the actual Lean
program for the book's graph and both displayed observations. Record command,
accepted candidate, compiler/runtime, target and actual output. Separately
kernel-check expected entries and graph hypotheses, and consume color_correct
and the SimpleGraph observation in the same example. This planning document
contains no execution result from Lean. Read-only source reasoning or an
in-memory independent trace is not a substitute for that later run.

## 8. Connected examples and statement review

Use example-driven development as each public claim is introduced, reusing
accepted predecessor cases where they already expose the relevant distinction.
Every example must use its public general theorem/adapter as well as any useful
closed computation; reflexive equations of unrelated specification functions
would not test that the algorithm meets its intended contract.

| Case | Required observation or failure boundary |
| --- | --- |
| Positive labels | Positive 1 has numeric label 1 and shifted Trie key 0; Color prints the former. Constructor 2 precedes 1 in bit order although numeric 1<2. |
| Choose versus ordered minimum | On {1,2}, source choose is some 1, bit minimum is some 2, elements are `[2,1]`. This tests concrete choice rather than only membership of an arbitrary result. |
| Source domain example | Keys 3,9,2 all map to empty sets; domain elements are `[2,9,3]`. There are three occupied bindings. |
| Absence versus isolated binding | Empty graph and graph containing `i↦emptySet` have equal adjacency functions but different nodes/cardinality and, with a nonempty palette, different selection/color domains. |
| Empty padding | An all-false/all-none internal tree can have empty observation with positive numNodes. Choose is none and semantic cardinality zero; raw equality/constant-work claims fail. |
| Setoid membership | Mod-10 related membership examples retain different lengths, while strictly sorted equal-membership lists are literally equal in the equality specialization. |
| Erase endpoints | Erase present and absent keys, root/left/right paths, and present empty values. Verify exact filtered ordered lists, unchanged payloads and card−1 only for a present key. |
| Value-map cardinality | A noninjective value map may collapse values but leaves all domain keys and cardinality intact; generic values require no order or equality decision. |
| Fold orientation | Use a noncommuting list accumulator to distinguish left fold over elements from an unreversed right fold. Then verify the reverse-fold theorem. Set-insertion commutation must not hide an incorrectly specified generic fold. |
| K=0 and empty palette | Select returns [] for every raw graph; color returns the empty coloring. Candidate construction still evaluates predicates on all stored bindings before none. |
| No eligible node in a colorable graph | A four-cycle with a two-color palette has degree equal to K everywhere, so source selection/coloring are empty despite a separately exhibited valid total two-coloring. This forbids totality/optimality claims. |
| Threshold equality | Degree K fails; degree K−1 succeeds when K>0. Isolated stored nodes are eligible exactly when K>0. |
| Original adjacency in phase two | A single undirected edge with two colors must get distinct endpoint colors. Reading reduced empty adjacency during re-insertion would wrongly allow the same color at both endpoints. |
| Helper success and failure | color1 overwrites an already-bound vertex on successful choice. On an arbitrary raw precolored input with no available color, it returns that input unchanged, including the existing vertex binding. |
| Repeated processing order | Under the two graph hypotheses, phase-two correctness holds for a list with a repeated vertex. The proof must not unnecessarily require fresh vertices or NoDup. |
| Partial versus all-palette specification | An isolated arbitrary candidate binding outside the palette can satisfy source coloring_ok. The produced coloring's separately proved AllPalette property rules that out. |
| Directed input | Graph `1↦{2}, 2↦∅` with palette {1} selects `[2,1]` and colors both vertices 1. Selected-support equality holds, but edge compatibility fails without undirectedness. |
| Self-loop input | Graph `1↦{1}` with palette {1,2} selects and colors 1; its self-edge prevents properness. The algorithm's raw termination/support laws still hold. |
| Graph helper semantics | A self-loop edge is retained; repeated/reversed nonloop edges do not multiply adjacency members. Both old adjacency reads and right-fold construction are exercised. |
| Exact source G trajectory | Candidate lists in bit order are `[4,6]`, `[6,1]`, `[2,6,5]`, `[6,5]`, `[5]`, `[]`; chosen removal list `[4,1,2,6,5]`. Tail-first painting yields exactly the source entries. Kernel-check this expected trajectory; source-derived planning calculations are not current compiler evidence. |
| Source G resources | n=r=5: 15 degree comparisons/cardinality requests, 10 adjacency-erasure callbacks, six selection/choose calls, five color steps and 14 neighbor-color lookups using original adjacency. Charge additional primitive work separately. |
| SimpleGraph composition | From the actual finite optional coloring and stronger palette theorem, construct a total proper coloring of the induced colored-domain graph into palette subtype. Explicit stored-domain facts remain available alongside it. |
| Measured erasure | Erasing measured select/color returns the same literal source removal list and optional coloring, with the same choice policy and original-graph parameter. Resource bounds attach to those runs. |

Statement review must explicitly ask whether any theorem accidentally replaces
partial optional lookup with default lookup; set equivalence with structural
equality; occupied cardinality with tree size; source choice with a minimum;
bit order with numeric order; literal ordered enumeration with membership only;
an exact input/output recurrence with merely proper coloring; a conditional
resource bound with an unconditional one; or graph symmetry/looplessness with
stronger hidden carrier constraints. Check all arbitrary-value, missing-key,
empty-palette, terminal-stage and isolated-node quantifiers.

## 9. Future implementation order and acceptance

1. Confirm #1016 and all earlier chapters accepted, recover exact candidate
   state, and reconcile proposed locations/names against their integrated
   APIs. Preserve root's existing work and current validation gate. A frozen
   plan is not permission to bypass chapter order.
2. Establish the positive constructor/equality/bit-order adapter and the used
   finite map/set realizations on existing carriers. Prove optional lookup,
   finite observations, occupied cardinality, ordered folds/enumerations and
   exact source choice, including noncanonical raw cases. Reuse the accepted
   Trie insertion and existing generic payload map through explicit adapters.
3. Complete every preliminary list/set/map declaration and exercise. Prove
   erasure/filter and cardinality laws with the source assumptions, not only
   enough weaker lemmas to force the final theorem through.
4. Define faithful raw graph operations and the well-founded selector. Prove
   exact equations, decrease, selection support/NoDup and residual adjacency.
   Define the original-graph right-fold coloring and its complete helper laws.
5. Prove phase-two correctness for arbitrary lists, the exact source theorem,
   stronger all-palette/support facts, low-degree availability and the connected
   SimpleGraph specialization. Retain every source-specific boundary case.
6. Instrument actual recurrences and prove erasure, exact callback sums and
   conditional primitive bounds with explicit arithmetic/normalization/input
   assumptions. Run the exact source example and preserve executable evidence;
   do not infer a timing result or compiler theorem from those proofs.
7. Integrate all public roots/examples, maintain source-to-Lean coverage and
   local ticket/review evidence. Apply the existing implementation workflow,
   example-driven statement review and the repository's Nix/direnv environment.
   Documentation/API checks alone do not accept Lean declarations.
8. Validate the exact isolated candidate with the applicable integrated build,
   integrity guard, exhaustive proof audit and audit regressions required by
   README/REQUIREMENTS; run `./check.sh --candidate HEAD`, obtain independent
   Standards and Spec review on that same candidate, then
   `./check.sh --verify-candidate HEAD` immediately before acceptance. New
   axioms, admissions, unsafe definitions, native-decide shortcuts or unexplained
   failures leave the chapter pending. Root owns the acceptance/tracker update,
   durable checkpoint, restore verification, exposure and upload.

## 10. Exact input identities and remaining limitations

The following local/core SHA-256 identities pin the files actually used in
this preparation. They are evidence of inspected bytes, not proof that future
adapters elaborate. The immutable toolchain and Mathlib revisions above qualify
core paths; all other paths are relative to this workspace. The plan's own
final digest is reported outside the file to avoid self-reference.

| Local/core input | SHA-256 |
| --- | --- |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |
| `reference/vfa/vfa/Color.v` | `67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370` |
| `work-state/source/Color.inventory.json` | `9af39e4c88d43d99c3aae211b49310ef0e9c4c2e088c8b38d8112b1abe6995f1` |
| `conaled/AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `conaled/docs/agents/architectural-quality.md` | `609c81cd22803888cfc8dafcfb6097f958e8e7c749df16b5156cd179b87835e6` |
| `conaled/docs/agents/domain.md` | `2f27fd2dec160969245bceba26cf65a0bc45fd2be24f065f84c766e5e5537a7d` |
| `conaled/GLOSSARY.md` | `de34dcd63191a11fa6c96d37c4c9457a77d8127ceb4156f6f8f44d3dbe3e88e6` |
| `conaled/docs/adr/0001-modules-and-proof-dependencies.md` | `83226e2d3ceb121348c97840026287a36fadaf638301b80ed9255383e322cae2` |
| `conaled/docs/adr/0010-composition-and-proof-audit.md` | `f76abfe4fafa7908a5f1605c8ffe9f717430ab0831682f74cc8c734a248c3fb8` |
| `conaled/.agents/skills/implement/SKILL.md` | `dcb604c159e9450af969fecedd595c216ac3850c8ee523766fa5cdc20b87d3df` |
| `work-state/source/POSITIVE-KEY-REUSE.md` | `ea930357c4547aebff68ae1a8464adb60af1dd336cb6e9669771dcf3db51df02` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `conaled/docs/research/data-structure-resource-contracts.md` | `460ea73bc3e24730dd593fc6a9f278ab81a33950b445b2755bfc1ecf0508eeb8` |
| `work-state/specs/1013-Trie.md` | `ff3874effda4d56e22a84d16b685e723c72dc210d70a1aec0d38799b7ceaa56e` |
| `work-state/staging/positive-keys/VFAStaging/PositiveKeys.lean` | `98c890672ed3e91b16089eb82037af46f15061af572c838f436b5692f5182f79` |
| `work-state/staging/table-specs/TableObservations.lean` | `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean` | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Get.lean` | `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean` | `92971636728e05bc108db821379b71e42c41a49a78eb7ef7674710228cb520f1` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean` | `5cec0cb9b3b20de90fddc44955c23fc5bd94e09aa630214b88e1a95997d7c8c7` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Finmap.lean` | `99638df454f40417c41825331272ac41a8494c45a612738c02085847329e6269` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Finset/Card.lean` | `300b99474dc58cca9b8724362a1a4673a217b2c66a0a7153ccc8eeb684ab51fa` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Finset/SDiff.lean` | `c455231312006244f45743f32be0481164844cb0820212aa7f27ca22a4edfc0d` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Forall2.lean` | `cf82dffa21e4159f40f23364f3f7f402cfadf00e0078fff568fcfdd10c76cd23` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `conaled/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Basic.lean` | `0434ed450cc0b055d35e60c611a9cd6b13890686708a5c4f64551e362f461376` |
| `conaled/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean` | `4ca03bcdbce93058ba64edafd9a6a9574a433468677bec165210a8eccb947a95` |
| `conaled/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean` | `9a803967ff799b1d5d47ecb14b1028e59436c7dbf5fdd3ad6071b7ca7cd71549` |
| `conaled/Applications/Search/HeuristicCore.lean` | `ff1e495264b02c72c5aeae997b042db47908f65ee51ffb8a0f7912771337c393` |
| `conaled/Squares.lean` | `2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7` |
| `conaled/SquareKit/ListFusion.lean` | `5ade8a9736d46b558e548aa7b1e8c60c6110f674c22deecb0038dc302b7b0164` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
| `Init/Data/List/Lemmas.lean` | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb` |
| `Init/Data/List/Pairwise.lean` | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4` |
| `Init/Prelude.lean` | `390e6b57ead28cb821a65533b21357f2f02d0a1525602f5a1ce9ee3eeb81fd12` |
| `Std/Data/TreeMap/Basic.lean` | `01f0ba418712fa6d55dcbb709d9637f8ef2805ddc6377a07fcfa5a17aace1c02` |
| `Std/Data/TreeMap/AdditionalOperations.lean` | `0cf3bd3110ccc8e43ceee5ed9fb56619866d7658a8a602be69f28e8979e81225` |
| `Std/Data/TreeMap/Lemmas.lean` | `005404f72f965c0e5c16422a50d795206be588100b0207967fb27e6b26e55dd4` |
| `Std/Data/TreeSet/Basic.lean` | `d5bfe94f73eaacbec88e9e0f8ef3e7db3b5190639d88136352ebc06d6540c671` |
| `Std/Data/TreeSet/Lemmas.lean` | `de4f5406196caba45862bcaad4ab72a7f4e58e7ad8bfe76e81af9832aa5fe642` |

### External provider identities

The three Rocq source files were read and hashed directly in memory at both
V9.0.0 and its immutable commit; their bytes agreed. Primary rendered source:
[OrderedTypeEx](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Structures.OrderedTypeEx.html),
[FSetPositive](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.FSets.FSetPositive.html),
[FMapPositive](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.FSets.FMapPositive.html).
Use the immutable commit paths to recover the exact audited providers, retain
their upstream license notices if adapting code, and preserve only required
provenance in checkpoints rather than downloaded research copies.

| External source at commit fda356e01346f7766b282ef9f44080cce2be23b3 unless otherwise stated | Bytes | SHA-256 |
| --- | ---: | --- |
| [theories/Structures/OrderedTypeEx.v](https://raw.githubusercontent.com/rocq-prover/stdlib/fda356e01346f7766b282ef9f44080cce2be23b3/theories/Structures/OrderedTypeEx.v) | 15,487 | `e30f31413cf5a544c1f997b02bb5ccd1f69e215c75b761fc12b184ec9af41ed5` |
| [theories/FSets/FSetPositive.v](https://raw.githubusercontent.com/rocq-prover/stdlib/fda356e01346f7766b282ef9f44080cce2be23b3/theories/FSets/FSetPositive.v) | 38,480 | `596ebe108c8baa96cbe12670e6275355a3d4a48e91898a173d8a9f26802adb9a` |
| [theories/FSets/FMapPositive.v](https://raw.githubusercontent.com/rocq-prover/stdlib/fda356e01346f7766b282ef9f44080cce2be23b3/theories/FSets/FMapPositive.v) | 33,802 | `49be1b1d115a068510b265581271421ec2780265cf0b63fa4b947b57a6b2005d` |
| [Appel2016 Color.pdf](https://www.cs.princeton.edu/~appel/Color.pdf), retrieved 2026-11-02 | 764,823 | `37238a67dda3adc00669e1a304634831b00e527d3fd0518798a9a639605cc5ee` |

Inspected Rocq source locations: bit relation and its transitivity/irreflexivity
at OrderedTypeEx 241–269; FSetPositive pruning/remove/diff at 81–126,
prefix/fold at 150–178, elements/cardinality/choose/minimum at 226–268 and fold
law at 775–776; FMapPositive find/add/remove at 99–165, elements/cardinality
at 169–191, pair relations at 493–496, mapi/map at 736–748, and fold at 905–937.
These provider equations supplement the chapter's abstract API uses. They do
not turn all unused Stdlib operations into a coverage milestone.

Remaining limitations are explicit: no Color Lean implementation was written,
compiled, audited or executed; no generic container substitution or performance
adapter is already proved here. The source-compatible finite extensions and
SimpleGraph bridge remain implementation work. The accepted predecessor names
and integration location must be checked after their gates. VFA permits later
Stdlib versions, but this plan pins one inspected baseline instead of assuming
all versions have identical choices or costs. Required-slide text and examples
were read; their heuristic/high-degree variant is distinguished from the exact
program. The suggested coalescing paper is not a proof dependency. No benchmark,
optimality, unconditional P≠NP conclusion, physical-memory claim or native
compiler correctness is established by this plan.
