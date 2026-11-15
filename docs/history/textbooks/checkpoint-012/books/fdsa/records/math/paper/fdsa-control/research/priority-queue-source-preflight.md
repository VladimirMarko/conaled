# Priority-queue observations and merge: bounded source preflight

Prepared 2026-11-02. **Source preparation only; no scope freeze, implementation,
validation, review approval, or chapter acceptance.** Chapter 1 remains the
active prerequisite, and Chapters 14–17, 22–23, and 26 remain queued. This note
does not change any inventory, requirement, ticket, integration prefix, or
compiler/checker session. In particular, root's session 83124 on candidate
`07e480f6ec9958d4975bb90151005b84f2907614` is untouched.

## 1. Recommendation and inspected scope

A small shared observation layer is warranted on the **existing**
`Search.PriorityInterface.ExactLaws` / `ExactQueue`: convert list permutations
to occurrence-multiset equations, project priorities, explain optional or
nonempty-domain minimum observations, and supply the two compatibility laws
for an actual merge operation when that implementation has one. This is
enough common mathematics to serve C14-001–013 and the later clients below.
It does not require another queue hierarchy or a dependency on XA01.

The direction of reuse matters. Existing `add_exact` and `remove_none` hold
on **all raw states**; the book requires the corresponding insertion and
emptiness statements only on valid states. Thus an existing `ExactQueue`
yields the weaker source laws, but an arbitrary instance of the book's ADT
does not automatically supply this stronger conaled interface. Preserve the
existing statements and verify any future source implementation separately.

The complete Chapter 14 text, `Priority_Queue_Specs.thy`, `Heaps.thy`, and
`Tree_Multiset.thy` were read. The existing exact interface and its two
realizations were read directly, together with the relevant leftist and
Huffman operations. Later source reads were limited to representations,
minimum/removal/merge equations, invariant definitions, and their queue
interpretations. This is not another whole-book inventory. The companion
`research/priority-queue-api-preflight.md` owns the fuller pinned Lean API
assessment; this note records source meaning and the required boundaries.

## 2. Source identities and exact locations

The book is the July 27, 2026 PDF at
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>. Chapter 14
is by Tobias Nipkow, printed pp. 179–182 / PDF pp. 185–188. The retained
extraction is `book-source/chapter14.txt`; it was read in full, rather than
substituting the earlier obligation inventory.

| Local reading file | SHA-256 |
|---|---|
| `book-source/functional_data_structures_algorithms.pdf` | `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645` |
| `book-source/chapter14.txt` | `b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a` |
| `book-source/Priority_Queue_Specs.thy` | `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a` |
| `book-source/Heaps.thy` | `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe` |
| `book-source/Tree_Multiset.thy` | `90524399a3894d8646c21377429a096345a0ddede243d966f8dd141853228508` |
| `book-source/Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/ISABELLE-COPYRIGHT` | `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d` |

The Isabelle files are retained at revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21` of
<https://github.com/isabelle-prover/mirror-isabelle>. Their immutable raw URLs
use `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/`,
that revision, and respectively
`src/HOL/Data_Structures/Priority_Queue_Specs.thy`,
`src/HOL/Data_Structures/Heaps.thy`, `src/HOL/Library/Tree_Multiset.thy`, and
`src/HOL/Library/Tree.thy`. This shared support revision postdates the PDF;
it is **not** claimed to be the manuscript's generation revision. The
retained Isabelle license is BSD-3-Clause; later translations must preserve
the applicable notices. No source was translated in this preparation.

The main source locations are:

- Printed p. 179 / `chapter14.txt:5–30`: minimum of a nonempty multiset's
  finite support, seven-law Figure 14.1, and the payload/priority discussion.
- Printed p. 180 / extraction lines 35–60: two-law merge Figure 14.2,
  Exercise 14.1, and the plain node-labelled heap observation.
- Printed p. 181 / extraction lines 65–92: root minimum, singleton-left
  insertion, child-merge deletion, the naive merge, and Exercises 14.2–14.4.
- `Priority_Queue_Specs.thy:11–27`: exact companion base contract;
  lines 31–34: same-carrier merge extension.
- `Heaps.thy:13–49`: plain-heap interpretation; lines 56–89: merge supplies
  insertion/deletion and the mergeable interpretation.
- `Tree.thy:98–101`: recursive heap ordering over all descendant labels;
  `Tree_Multiset.thy:16–45`: node/empty occurrence recurrence and
  empty/support/cardinality/traversal bridges.

## 3. Complete common source obligations C14-001–013

Write `M(q)` for the source multiset, `V(q)` for validity, `0` for the empty
multiset, and `{x}` for **one occurrence**. The element type is linearly
ordered. `minimum M` means the least element of its finite support and is
used only when `M ≠ 0`.

| ID | Exact mathematical obligation and domain | Existing-interface consequence or remaining adapter |
|---|---|---|
| C14-001 | Queue carrier; empty, singleton insert, minimum observation, deletion; separate `M` and `V`. | Existing `Operations`/`ExactQueue`, singleton `add`, and explicit observation/deletion views. Preserve independent payload, priority, and carrier universes. |
| C14-002 | `minimum M` observes finite support, with a nonempty premise. | Membership plus a lower-bound theorem, followed by the finite-support `Min_mset` bridge under a linear order. Multiplicity is irrelevant to choosing the minimum but essential to deletion. |
| C14-003 | `M(empty) = 0`. | `empty_entries` and the multiset observation. |
| C14-004 | `V(empty)`. | `empty_valid`. |
| C14-005 | `V(q) → M(insert x q) = M(q) + {x}`. | Singleton `add_exact`; its existing all-raw-state theorem is stronger. |
| C14-006 | `V(q) → V(insert x q)`. | `add_valid`; validity remains a real premise. |
| C14-007 | `V(q) ∧ M(q) ≠ 0 → M(del_min q) = M(q) − {get_min q}`. | Actual successful removal, occurrence decomposition, and agreement of the chosen observation with the removed source value. Subtract exactly one occurrence. |
| C14-008 | `V(q) ∧ M(q) ≠ 0 → V(del_min q)`. | Residual validity in `remove_spec`. The abstract book law does not constrain deletion on an empty input. |
| C14-009 | `V(q) ∧ M(q) ≠ 0 → get_min q = minimum M(q)`. | The removed priority is a member and a lower bound; linear-order antisymmetry identifies the source minimum. A separately implemented peek needs its own agreement proof. |
| C14-010 | `V(q) ∧ V(r) → M(merge q r) = M(q) + M(r)`. | Supply the actual same-carrier merge and its occurrence compatibility. There is no disjointness or distinctness premise. |
| C14-011 | `V(q) ∧ V(r) → V(merge q r)`. | Separate preservation theorem for that merge; content equality alone is insufficient. |
| C14-012 | Companion addition: `V(q) → (is_empty q = true ↔ M(q) = 0)`. | Existing `remove_none` is stronger and yields semantic reflection; direct structural emptiness can be connected independently. The displayed book figure omits this operation. |
| C14-013 | Separate arbitrary payloads from ordered priorities, then recover the book's element-only view. | Use the existing general interface; specialize payloads to `Unit`, priorities to source elements, and observe the priority multiset. No payload order, unique-key condition, or stable-tie condition is introduced. |

C14-003–009 are exactly the **seven** displayed base laws. The companion
adds `is_empty` and its reflection law, yielding **eight** base laws; the
merge extension adds two more. Neither count justifies dropping a source
law or inventing a missing eighth line in Figure 14.1. The HOL Boolean
equality for `is_empty` becomes a Boolean-to-Prop reflection in Lean, not an
ill-typed equality between a `Bool` and a `Prop`.

## 4. Observation bridge from the actual exact interface

The inspected files in `conaled-adt-refinement` have these identities:

| Repository file | SHA-256 |
|---|---|
| `Applications/Search/PriorityInterface.lean` | `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6` |
| `Applications/Search/ExactPriority.lean` | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| `Applications/Search/LeftistQueue.lean` | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| `Applications/Huffman/Priority.lean` | `c06cfbe28f488d5aed5ddc2cc2f8002244eb22818c875b3f752dfccc393048e1` |

These are actual source reads, not newly compiled artifacts. The existing
dependency pins remain Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries
`66e469188fe07963e5cf666c7d4433f45b8131c5`, and Lean 4.35.0
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

### 4.1 Occurrences first, priorities second

For `Q : ExactQueue α π`, let `L(q) = Q.entries q`, let `E(q)` be its
multiset of full `(payload, priority)` entries, and let
`P(q) = E(q).map Prod.snd`. Finite lists provide finite observations even
when payload and priority types are infinite. No enumeration of either
type and no extra surjectivity premise are required.

`ExactLaws` at `ExactPriority.lean:12–20` gives the following exact route:

1. Empty and insertion observations convert directly from list equality
   or permutation. In particular, all raw states satisfy
   `E(Q.add xs q) = multiset(xs) + E(q)`.
2. On every raw state, `Q.remove q = none` iff `L(q) = []`, equivalently
   `E(q) = 0`, equivalently `P(q) = 0`. Nonempty observation therefore
   yields an actual successful removal even before using validity.
3. Given `Q.Valid q` and `Q.remove q = some (e,r)`, obtain
   `Q.Valid r`, `E(q) = {e} + E(r)`, membership `e ∈ E(q)`, and
   `∀ a ∈ E(q), e.2 ≤ a.2`. Hence cardinality decreases by exactly one.
4. Projecting the same decomposition yields
   `P(q) = {e.2} + P(r)`. This retains all repeated priorities, including
   those belonging to different payloads.

The decomposition is the most general useful deletion statement: the
existing abstract contract requires only `[LE π]`, and entry decomposition
needs no decidable equality on payloads. The usual singleton subtraction
or erase presentation is a subsequent observation theorem; any required
decidable equality can be confined to the observed type. In particular,
projecting first avoids imposing payload equality merely to obtain the
source priority-multiset subtraction.

The companion API preflight identifies `Multiset.coe_eq_coe`, `coe_add`,
and `cons_coe` for the list bridge. The inspected pinned
`Mathlib/Data/Multiset/MapFold.lean:72–110` has `map_cons`, `map_add`, and
`map_eq_zero` for the projection. A least-element predicate uses membership
and the lower-bound relation; identifying it with `Finset.min'` of support
uses the source linear order and nonempty support. A mere preorder allows
different equivalent least priorities, so it does not by itself justify
equality with a particular minimum value.

### 4.2 Optional and nonempty-domain views

A possible semantic view is
`peekEntry? q = (Q.remove q).map Prod.fst`, followed by priority projection
when needed. A deletion view can return the residual on `some (e,r)` and
leave `q` unchanged on `none`. That explicit fallback is source-compatible:
the seven laws leave the empty-deletion case unconstrained. Its stronger
valid-empty behavior should not be mistaken for a requirement on every
source implementation. Other concrete empty behavior must be stated where
that source algorithm specifies it.

Alternatively, a minimum operation can take proofs of validity and
nonempty observation. Neither approach requires a default payload or
priority. This is substantive for empty payload/priority types: an empty
queue still exists, whereas a total `Carrier → Empty` cannot exist. An
optional observation handles this boundary without introducing a global
`Inhabited` premise. A queue carrier itself is inhabited by its `empty`
operation; the element types need not be.

No minimum or residual-validity promise follows from a successful removal
of an **invalid** state. The unconditional `remove_none` theorem detects
emptiness there; it does not silently strengthen `remove_spec`. Likewise,
an empty observation does not identify the raw state with `Q.empty`:
representations may retain irrelevant metadata.

### 4.3 Agreement and cost are separate obligations

For full entries, “peek returns a minimum” and “remove returns a minimum”
do not ensure they choose the same occurrence. Let the entries be
`[(A,1),(B,1)]` with `A ≠ B`. A peek selecting `(A,1)` and a removal
selecting `(B,1)` both satisfy priority leastness, but the residual full-entry
multiset is `{(A,1)}`, not `E(q) − {(A,1)}`. Thus a full-entry peek/delete
contract needs actual selection agreement. For the book's priority-only
view, equality of the least priority under a linear order suffices; it
does not choose a payload or impose stability among ties.

There is also a useful precise agreement statement between two valid
queues, even with different carriers or payload types. If their priority
multisets are equal and the priority relation is antisymmetric, their
actual removals agree after observation into
`Option (priority × residual-priority-multiset)`. Empty inputs give `none`
by `remove_none`. On nonempty inputs, each selected priority occurs in the
common multiset and is below the other, so antisymmetry makes them equal;
cancelling that one equal occurrence makes the residual priority multisets
equal. This argument needs neither a priority equality decision nor a total
order, beyond the existing removal laws and explicit antisymmetry. The
pinned `Multiset.cons_inj_right` cancellation identified by the API preflight
has exactly this role. It proves no equality of selected payloads, raw
residual states, tie-selected shapes, or work. Without antisymmetry, mutual
comparison alone need not make the selected priority values equal.

The deletion-derived semantic peek invokes the deletion computation. It
does not acquire a constant-time bound by projecting away the residual.
`LeftistQueue.deleteQ` (`:151–153`) constructs `combineQ l r`; `listRemove`
(`ExactPriority.lean:74–77`) invokes `mergeSort` before selecting the head.
An independent direct-root leftist peek can be a plain constructor match;
its agreement with `(deleteQ q).map Prod.fst` is a separate value theorem
that holds on all raw trees. Its minimum theorem then uses the appropriate
heap validity. Any runtime claim still needs the actual implementation and
its declared cost model; no compiler optimization is assumed here.

Similarly, the head of an arbitrary valid `exactList` is not necessarily a
minimum: that interface has `Valid = True`, so priority list `[3,1]` is a
valid example. Its removal sorts first. It is an exact-occurrence model,
but it does **not** solve Exercise 14.1's constant-time minimum/removal
requirement for a sorted-list representation.

## 5. Merge compatibility without another hierarchy

The common extension can take an actual operation
`merge : Q.Carrier → Q.Carrier → Q.Carrier` and, for valid `q,r`, require
only:

```text
(Q.entries (merge q r)).Perm (Q.entries q ++ Q.entries r)
Q.Valid (merge q r).
```

The first gives both entry- and priority-multiset addition; the second
retains the representation invariant for subsequent operations. The two
arguments must refer to the **same** existing carrier, operations,
observation, and validity predicate. `Priority_Queue_Specs.thy:29–34`
explicitly fixes this same-carrier point in the source locale extension.

There is no disjointness, `Nodup`, key uniqueness, stable-tie, or payload
ordering requirement. Overlapping heaps add multiplicities. Even
`merge q q` denotes two copies of every logical occurrence; persistent
sharing of a raw value does not make multiset addition idempotent. This
semantic fact grants no permission to spend an amortized potential twice.
Source amortized analyses retain their own computation-history premises.

Multiset associativity, commutativity, and empty identities become
**observational** consequences on valid states after carrying validity
through intermediate merges. They do not assert equality of raw tree
shapes, cached representations, or tie-selected deletion sequences.

Existing `LeftistQueue.combineQ_entries` (`:182–195`) is even stronger:
its occurrence theorem is unconditional on validity. `combineQ_valid`
(`:257ff`) requires both actual `Valid` premises. These directly serve
the proposed compatibility laws without replacing the carrier or its
proofs. The existing `exactList` also admits actual list append as a
compatible merge because its observation is the list itself and validity
is `True`; this remains an illustrative exact model, not the sorted-list
exercise implementation. No merge should be forced on a source that only
provides the base queue contract.

## 6. Source qualifications and later clients

No mathematical contradiction was found in C14-001–013. The concrete
qualifications that must remain explicit are:

- `Heaps.Heap` assumes `heap q → heap (del_min q)` even on empty inputs
  (`Heaps.thy:19`), which is stronger than the abstract nonempty deletion
  law. The derived `Heap_Merge.del_min Leaf = Leaf` (`:65–67`) supplies
  that behavior. Do not silently replace one statement by the other.
- The book's plain-heap interpretation uses `heap` as its invariant.
  Later cached/balanced representations need their **additional**
  invariants. Equal content, or the root's being least, does not establish
  cache consistency, Braun shape, binomial rank structure, or leftist
  rankedness. Existing `LeftistQueue.Valid = Ranked ∧ Heap` is retained.
- The pinned `Heaps.thy` supplies abstract interpretations, not the
  displayed naive-merge implementation or the chapter's exercise
  solutions. An extensional occurrence law does not identify that naive
  merge with rank-swapping leftist merge.
- The historical discussion of `decrease_key` on p. 182 does not add that
  operation to the seven-law contract. This preparation neither adds it
  nor removes any already inventoried mathematical assertion.

The following primary sources show concrete later reuse. Their operations,
algorithm-specific proof obligations, and costs remain queued.

| Chapter / primary location | Common contract use | Boundary retained |
|---|---|---|
| C15, `Leftist_Heap.thy:14–55,132–156` | `Priority_Queue_Merge` with label multiset ignoring cached ranks; validity is heap order plus leftist/cache invariant. | Source smart construction can swap children. Preserve occurrences, not unconditional inorder or shape. Root access, cache correctness, actual merge recurrence, rank/logarithmic costs, bottom-up construction, and exercises remain separate. |
| C16, `Priority_Queue_Braun.thy:41–44,155–158,185–226` | Base `Priority_Queue` with `braun ∧ heap` and `mset_tree`. | This pinned interpretation does **not** supply merge. Preserve its shape and nonempty helper premises; do not invent a Braun merge merely to fit the optional extension. |
| C17, `Binomial_Heap.thy:65–78,269–300,306–340,385–406` | `Priority_Queue_Merge` on forests, with multiset of all nodes and binomial/heap/strict-rank invariants. `get_min_rest_get_min_same_root` explicitly connects selected deletion tree and minimum. | Minimum scans roots; it is not a single binary-root lookup. Rank linking, carry/forest merge, reversal, selected-tree validity, and costs remain algorithm-specific. |
| C22, `Skew_Heap.thy:20–25,60–76` | Actual skew merge's occurrence and heap laws instantiate `Heap_Merge`, hence the base/merge observations. | Recursive operand order and child exchange differ from the naive/leftist algorithms. Actual recurrences, potential, and admissible amortized histories are not consequences of the ADT. |
| C23, `Pairing_Heap_List2.thy:16–40,42–68,72ff,155ff` | Optional nonempty rose-tree carrier, occurrence observation, and `Priority_Queue_Merge`. | `link` uses strict `<`, selecting the second root on equal priorities, unlike the first-root `≤` choice in the leftist source. Two passes, their fused equation, shape/value bridges, and all cost/amortized statements remain separate. |
| C26, printed pp. 308–309 / `chapter26.txt:156–186`; existing `Huffman/Priority.lean:13–49,54–143` | Exact occurrences allow two successive removals and insertion of one joined tree without losing repeated weights or equal payload occurrences. | The source uses weight-cached trees and `insortTree` on a sorted list. Existing generic Huffman requires its separate `Cached` invariant; queue priority leastness alone does not imply least semantic tree weight. Source carrier, recurrence, cache, coding, optimality correspondence, and runtime obligations remain. |

The Huffman client is already meaningful evidence for the selected existing
interface. `Good = Q.Valid ∧ Cached` (`Huffman/Priority.lean:29–31`);
`delete_cached` (`:88–105`) uses both components to turn the actual removed
priority into a minimum semantic tree weight and preserve residual cache
validity. `two_deletions` requires a valid queue with at least two
occurrences, and `step_spec` consumes validity of the first residual before
the second removal. Replacing this queue by a keyed structure that merges
equal weights could erase a forest occurrence and invalidate the step.
None of this identifies the actual tie-selected output tree with every
source realization or supplies a new source runtime proof.

The later primary identities inspected here are:

| Reading file | SHA-256 / provenance |
|---|---|
| `book-source/Leftist_Heap.thy` | `894e22da05b2dbf37ce46b8401958957e5d4a729c691d6a402b0e66dd8a22450`; same Isabelle revision, `src/HOL/Data_Structures/Leftist_Heap.thy`. |
| `book-source/Binomial_Heap.thy` | `821d4236fb294b3b73b9c119a40f36225d3f16d4030b805c045da39dcf63210a`; same Isabelle revision, `src/HOL/Data_Structures/Binomial_Heap.thy`. |
| `book-source/Priority_Queue_Braun.thy` | `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e`; retained dated AFP entry below. |
| `book-source/Skew_Heap.thy` | `212435f75ba99eb103c274cae4909ee4ac272add055ac3ffd1665eda7ea3a114`; retained dated AFP entry below. |
| `book-source/Pairing_Heap_List2.thy` | `cea84ce48af8653082f68ac84fd763fdfabea981952d292819c84b88f8ba4b76`; retained dated AFP Pairing_Heap entry below. |
| `book-source/chapter26.txt` | `ed82113d19a24fb4eaf5b4ea808900b258c7cfbae63287218ed2e4ec6512d42e`; extraction of the same pinned book. |
| `book-source/afp-Huffman-2026-10-26/Huffman/Huffman.thy` | `7bdc838bbdf7347fb78440a5b3c8dadaf6b7c228e6e3cae6f2d1fb49582837bf`; retained dated AFP Huffman source, used only for the already recorded representation/algorithm context. |
| `book-source/AFP-LICENSE` | `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`; retain applicable BSD notices in later translations. |

The existing dated archive URLs are
<https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz>,
<https://isa-afp.org/release/afp-Skew_Heap-2026-10-26.tar.gz>,
<https://isa-afp.org/release/afp-Pairing_Heap-2026-10-26.tar.gz>, and
<https://isa-afp.org/release/afp-Huffman-2026-10-26.tar.gz>. The retained
Braun, skew, and pairing archive SHA-256 values are respectively
`e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b`,
`0aa18ccafebd4767acc96ab29d3b653faaaf437fdfa7912f49fa9e29ed3f0437`,
and `fe2985e0b299455da334b51ef37c780e392f551dc47ea5f9a14bfbd53c1a3653`.
These support versions also postdate the book and are not claimed to be
its exact build sources. No archive was newly retrieved in this task.

The observation scope deliberately carries **no resource bound**. In
particular, `Leftist_Heap.thy:160–172` declares the auxiliary `mht` and
`node` timing functions to be zero in its selective tariff before timing
merge/insert/delete. That is different from XT01's declared positive
local-access charges. Value correspondence cannot transfer either tariff
to the other. The future chapter cost proofs must retain the actual
source recurrence and declared counted operations.

## 7. Smallest useful future work and independent cases

A bounded implementation could contain the following, without activating
Chapter 14 or changing existing operations:

1. Entry-multiset and priority-multiset observations with the empty,
   insertion, successful-removal decomposition, cardinality, and failure
   consequences of the actual `ExactLaws`.
2. The nonempty finite-support minimum bridge and explicit optional or
   proof-domain source views, including observation/removal agreement.
3. Two merge compatibility laws for a supplied actual operation; connect
   existing `combineQ` directly. An `exactList` append instance can serve
   as a second ordinary model without pretending to solve Exercise 14.1.
4. If direct leftist peek is included, use a real root match and prove its
   agreement with existing removal. State only the proved value contract
   unless an independent concrete cost model is intentionally in scope.

These mathematical checks are useful connected cases for a later freeze;
they are not new frozen requirements or completed Lean examples:

| Case | Independently determined observation / reason |
|---|---|
| Duplicate source priorities `[1,1,3]` | Removing a minimum leaves multiset `[1,3]`, not `[3]`. Distinguishes one occurrence from set deletion. |
| Merge `[1,1,4]` with `[1,3]` | Result has three occurrences of `1`, one `3`, and one `4`; one deletion leaves two occurrences of `1`. No disjointness premise is available. |
| Self-merge of `[1,3]` | Two occurrences of each value, rather than idempotent union. This is a content statement, not an amortized-work statement. |
| Distinct payloads `(A,1),(B,1)` | Both remain present; selected full entry and residual must satisfy the actual removal decomposition. Independent minimum choices need not agree on payload. |
| Empty and singleton queues | Optional minimum is `none` on empty observation; a valid singleton removes its one entry and leaves empty observation with valid residual. Empty payload/priority types remain expressible. |
| Invalid cached/ordered raw trees | Same multiset or root observation does not imply `Valid`; minimum/cached-rank claims keep their required premises. `remove_none` nevertheless keeps its existing unconditional meaning. |
| Existing Huffman step with tied weights | Two actual occurrences are removed in sequence, preserving intermediate validity and cache agreement, then one joined occurrence is inserted. Neither a second queue hierarchy nor a new Huffman algorithm is needed to exercise the contract. |

The generic occurrence-to-multiset bridge is a one-way source-law
consequence, not a representation isomorphism. No surjectivity premise is
needed: in fact, `Q.add xs Q.empty` is valid and has exactly the entry
multiset of `xs`, so every finite entry multiset has a valid representative.
For priority-only multisets this conclusion additionally needs an available
payload, as supplied by the `Unit` source specialization; it is false for
nonempty priority multisets if the payload type is empty. Neither statement
gives uniqueness, any prescribed concrete representation, or equality of
raw states from equal observations. Shapes and metadata can still differ.

## 8. Original scope that remains queued

All original book obligations remain mandatory. This preparation neither
accepts C14-001–013 nor claims Chapter 14 complete. C14-014–040 retain the
sorted-list exercise and its constant-time accesses, actual naive-merge
definition/termination/invariant/content proofs, the source heap
interpretation, heap enumeration and its quadratic bound, and the
inorder-preserving heap construction/existence/distinct-label uniqueness
exercise and duplicate boundary.

All concrete later heap algorithms, structural/cache invariants, source
operation correspondences, termination arguments, costs, amortized
premises, and exercises remain in their original chapters. Chapter 26
retains its exact cached-tree/list implementation and the already
inventoried correctness, coding, and complexity obligations. A common
queue observation result is only a reusable component of those proofs.

This report introduces no obligation to build a new generic queue,
resource translator, or history framework beyond what is actually needed
to meet the original source obligations. Previous inventories, scope
clarifications, frozen requirements, and the original Chapter 2-first
integration prefix are unchanged. No compiler, checker, project hash
helper, Git/ref/cache mutation, remote read/write, or acceptance action was
performed for this source preparation.
