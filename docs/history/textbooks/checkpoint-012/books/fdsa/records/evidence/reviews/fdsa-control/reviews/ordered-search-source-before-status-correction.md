# Ordered binary-tree search: bounded source preflight

Recorded 2026-11-02. **Read-only source preparation; no scope freeze, source
implementation, compilation, final review, chapter activation or acceptance.**
This is the sole new file written for this task. Earlier inventories, requirements,
source drafts and findings are unchanged. Chapter 1 remains the prerequisite;
the original Chapter 2 integration prefix remains `c80eec9`.

Status at this report's completion: root reported that Chapter 1 attempt 2's
session `61365` returned an unknown-process result and that the task process
view no longer contained the process. Its exit/cause and successful completion
are not established. Recovery review is coordinator-owned; **no compiler is
active or newly authorized by this task**. The earlier tree drafts remain
uncompiled and unaccepted.

## 1. Conclusion and smallest useful common component

A shared **one-path binary-tree query returning the actual stored entry** is
genuinely useful. The ordinary `Tree_Set.isin` and `Tree_Map.lookup` recurrences
are repeated, with ignored annotations, in `Isin2` and `Lookup2`. The red-black,
AVL and join-based sources explicitly reuse those operations and their query
correctness lemmas. This is stronger evidence of reuse than a similarity of
algorithm names. Bool membership can observe whether the returned option is
present; map lookup can project the semantic payload of that same entry.

The smallest useful source-faithful scope is the raw selected-child operation,
its stored-entry/absence and strict-key correctness laws, route-compatible label
transport, and an explicitly reconstructed search-invocation count with its
hit/miss distinction. A separate visited-node observation makes the book's
finite average example and comparator-call interpretation precise. Reuse
`BinaryTree`, `Ordering`, `Ordering.Compares`, `Trees.Ordered`, `Trees.inorder`
and existing resource observations. No new tree carrier, queue/Set/Map
hierarchy, search state machine, or general comparison-law record is needed.

**Chapter 7 is a separate operational boundary:** its `Node3` conditionally
compares a second stored key. It shares the mathematical pruning idea, but the
binary query is not its literal recurrence or its unchanged per-node count.
Likewise, interval-overlap queries and Chapter 10's reconstructing split are
not this read-only equality-key operation.

This recommendation is preparation for a possible bounded unit. It does not
freeze declarations or require every supporting observation below to become
a separate public definition. In particular, the two numerical observations
can be related without introducing a new product-resource framework.

## 2. Evidence, identity and provenance

The governing request, `DECISIONS.md`, current `conaled/AGENTS.md`, development
environment guidance, architectural-quality/domain guidance, glossary and
ADR 0001 were read. Existing chapter inventories and the retained tree-order
source preflight/candidate record supply continuity; their claims were checked
against the bounded primary passages below rather than treated as substitutes
for the sources.

Book: *Functional Data Structures and Algorithms: A Proof Assistant Approach*,
July 27, 2026 version, official URL
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
Local `book-source/functional_data_structures_algorithms.pdf` is 1,742,029 bytes,
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Printed pages are used below. Chapter 5 is by Tobias Nipkow and Bohua Zhan;
the inspected Chapters 6–10 are by Tobias Nipkow. No new manuscript download
or remote source campaign was performed.

Isabelle mirror revision: `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
Source URLs use
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`
followed by the path. This inspected companion revision is not asserted to be
the revision that generated the pinned PDF. Except for `Tree.thy`, whose path
is `src/HOL/Library/Tree.thy`, the theory names below are under
`src/HOL/Data_Structures/`.

| Retained theory | SHA-256 | Bounded role read here |
|---|---|---|
| `Cmp.thy` | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` | Complete comparator and branch-law source |
| `Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` | Retained carrier/height/inorder identity; existing source note supplies its earlier complete treatment |
| `Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` | Complete annotation-erasing observations |
| `Tree_Set.thy` | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | Query body, query correctness and contrast with partial `split_min` |
| `Tree_Map.thy` | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` | Query body and strict-key list observation |
| `Isin2.thy` | `f6b0c6574c8fa618b5d42f3045e9af32731afd80a061173d8bc09eae9808df0c` | Complete augmented membership source |
| `Lookup2.thy` | `3969a579629d0b60c01cc44da16866e09653d46f46f2a2d2f115905e06739023` | Complete augmented map lookup source |
| `Tree23_Set.thy` | `ae1317555ff4e8223d2e047098c62a954f09b8e45e8fd1b1d6522ecdbc888c31` | `Node2`/`Node3` query, query theorem and Set interpretation |
| `RBT_Set.thy` | `542519dc50a4ca03735f68f36bf6bf666f941a33502b028cf2f939b3119d80c8` | Imports and query reuse in Set interpretation |
| `RBT_Map.thy` | `18aad043c03697c6bd0fb3ad18387dd9030727dceaceee26abb7d5a108ca43ba` | Imports and query reuse in Map interpretation |
| `AVL_Set_Code.thy` | `423ea6e7e5d415a9d279ca24c48ce45b2d1bd60f591fae50a00ffa6e852cb2e3` | Shared `Isin2` import and distinct cache readers |
| `AVL_Set.thy` | `282cf829b7efc3421428cbe7ee3e590492d45ed0b8c7b80eff1ae3c57630f3b9` | Separate AVL/cache invariant and query reuse |
| `Set2_Join.thy` | `15edbd8a0b1b00633a15d9d1ccffb92d60ca9b313ba3b2f3bf4313af79f57d1b` | `Isin2` import, reconstructing split and inherited Set query |
| `Time_Functions.thy` | `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01` | Explicit zero-cost projections and invocation convention; no query timing declaration supplied here |

The applicable Isabelle BSD-3-Clause notice is retained as
`book-source/ISABELLE-COPYRIGHT`, 1,673 bytes, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
It names copyright 1986–2026 University of Cambridge, Technische Universitaet
Muenchen and contributors. Source adaptations must retain the full applicable
notice and attribution, not merely a label saying BSD. `Cmp` names Tobias
Nipkow and Daniel Stüwe; the query theories name Tobias Nipkow. Research
manuscript copies remain outside deliverables under ADR 0001.

Relevant extracted-text identities, all from the pinned PDF:

| File in `book-source/` | SHA-256 |
|---|---|
| `chapter01.txt` | `f4ec8604991945ca2c5376353bdc50fe5cca10e0077314994be6cc236d451aca` |
| `chapter05.txt` | `b00475b2893cf76a66a5c164a63ee99e065772fffa7ae56054359b278c5c4b1e` |
| `chapter06.txt` | `b50500309106a77b094aebbc807b5b6979feb72d03bb443f2fd2785ee5dc3681` |
| `chapter07.txt` | `696aa40eb81bbd1d1014dfaf131d7e85e0e281c27d3b5db1384d5de9c0336818` |
| `chapter08.txt` | `3e81ddb218a418f99a384b09db5ea71e87dd63fcd4ad1e2e9c7f3ddfeb05dcbc` |
| `chapter09.txt` | `ff8896571e431ae84be682581b682945ccfcf32e24475cd091318d087ded5aba` |
| `chapter10.txt` | `fb0b00d93e2f21772328a0420df29441a05f17ec1a074b9b5c226a7a50e04205` |
| `appendix-b.txt` | `f809cfd567c764cf8a2f3660774617e1a43f7089f2d42e7874e6e1936bef1929` |

## 3. Exact source operations and repeated clients

Use `E` for an empty tree and `N(l,a,r)` for a node. In Lean the existing
constructor is `BinaryTree.node a l r`, with a different argument order.
All trees here are node-labelled with empty leaves; no leaf-labelled
Bracketing/RandomAccess carrier is substituted.

| Source claim | Exact primary location | Consequence |
|---|---|---|
| Strict BST bounds quantify over every element in each child subtree. | Book p.59, `chapter05.txt:12–18`; `Tree2.thy:26–28` for annotations | Immediate-child-root comparisons alone are insufficient. Reuse the retained all-subtree invariant. |
| Compare query with stored key: first `<`, then `=`, otherwise GT. | Book p.60, `chapter05.txt:56–64`; `Cmp.thy:9–21` | Source LT/EQ/GT branch laws have a linear-order premise. The primitive-comparator speed remark is not a proved runtime equality. |
| Empty membership is false; LT selects left, EQ returns true, GT selects right. | Book p.61, `chapter05.txt:72–75`; `Tree_Set.thy:15–21` | Definition is total on raw trees. BST is a correctness premise, not an operation-construction premise. |
| Membership agrees with inorder/set membership under strict order. | Book pp.63/65/67; `Tree_Set.thy:68–69`; Chapter 5 Figure 5.1 | Supports the query clauses of C05-014/C05-028; does not establish their update clauses. |
| Augmented membership ignores the extra tag. | Book p.71, `chapter05.txt:435–444`; `Isin2.thy:12–24` | The same operation works with colors, height tags or other annotations. No cache/balance hypothesis is required for equality-key query correctness. |
| Map lookup returns `None` at E and `Some b` at a matching `(a,b)` node. | Book p.81, `chapter06.txt:166–171`; `Tree_Map.thy:11–14` | Values have no order/default requirement; `b` is semantic data. |
| Map lookup equals first-match `map_of` on full inorder under strict sorted keys. | Book p.83, `chapter06.txt:205–220`; `Tree_Map.thy:33–35` | Do not erase the value component or sort full key/value pairs lexicographically. |
| Augmented map lookup ignores only the outer tag in `((a,b),tag)`. | Book p.102, `chapter08.txt:249–253`; `Lookup2.thy:12–19` | Return the inner semantic value. The ignored color/height is a different component. |
| Red-black sets/maps reuse the common augmented queries. | Book pp.97/102; `RBT_Set.thy:5–10,278–284`; `RBT_Map.thy:5–8,110–116` | Concrete repeated clients; query theorem is independent of red-black invariants. |
| AVL sets reuse the same query while maintaining separate balance/cache validity. | Book §§9.1–9.2, pp.105–107; `AVL_Set_Code.thy:8–11`; `AVL_Set.thy:11–15,211–217` | Query does not read `ht`; rebuilding and rotations do, and remain separate. |
| Join-based sets retain ordinary membership. | Book pp.118–120; `Set2_Join.thy:5–7,328–335` | The Set2 interpretation uses `isin_set_tree`; join correctness does not replace this inherited query law. |
| A 2–3 `Node3` compares x with a, then compares with b only after GT. | Book p.86, `chapter07.txt:46–52`; `Tree23_Set.thy:17–32,150–151` | One selected recursive child, but up to two three-way calls per visited nonempty node. Its own carrier/recurrence remains required. |

`Tree2.inorder` at lines 18–20 erases the outer annotation. Applied to an
augmented map, its logical labels are still full `(key,value)` pairs.
`Tree_Map.lookup_map_of` and `Lookup2.lookup_map_of` use strict `sorted1`
on their key lists. The source observation `map_of ((a,b)::ps)` gives the
first binding precedence; its duplicate behavior matters on invalid trees.

There is no nonempty premise for any of these query definitions. This differs
from source `split_min`, which has only a node equation and whose laws retain
nonemptiness (`Tree_Set.thy:35–37,76–77`). No default key/value or global
`Inhabited` assumption is needed to make queries total in Lean.

## 4. Minimal mathematical contracts and existing reuse

### Raw path, correctness and transport

An ordinary `route : α → Ordering` suffices for raw operation construction:
empty returns `none`; a node returns `some a` on `.eq`, recurses into l on
`.lt`, and into r on `.gt`. No order, decidable equality or inhabitance on α
is needed. A successful raw result is an actual stored label. This alone
does not assert that its key equals a query: an arbitrary route may lie.

For correctness, keep independent label/key universes and take `key : α → κ`,
query `q : κ`, the retained invariant
`Trees.Ordered (fun a b => key a < key b) t`, and input-local calibration
`∀ a ∈ Trees.inorder t, (route a).Compares q (key a)`.
Architecture's bounded API read and the inspected definitions support a
`Preorder κ` theorem with this explicit local calibration; the comparator
itself supplies the query's three-way comparability with each stored key.
There is no need to assume the key function globally injective, or to order
payloads. The source's concrete comparator obtains calibration from a
`LinearOrder κ`.

Useful consequences are successful-result membership/key equality, success
iff a matching key occurs, absence iff none occurs, and equality with the
first matching inorder entry. The strict invariant supplies within-tree key
uniqueness, so arbitrary duplicate-free payload records are not a substitute.
The proof discards the opposite subtree by the root's strict bound and
transitivity, then applies induction to the actual selected child. The direct
structural proof route can support the query part of Exercise 5.3; it does
not prove the exercise's six other laws or remove its direct-proof condition.

Bool membership and map payload projection should consume that same result.
For `(κ × β)` use key `Prod.fst` and observe `Option.map Prod.snd`;
for `((κ × β) × γ)` ignore γ but preserve β. A label map f whose route agrees
on the actual input labels transports the returned option by `Option.map f`
and preserves the path counts. This raw transport needs no BST, cache validity,
global injectivity, or equality decision. It explains annotation erasure
without defining the executable query to traverse and erase the whole tree
before searching.

### Retained local and pinned library evidence

The saved `work/fdsa-tree-order` candidate is
`66eae34815a177c6b4bf5120e05202ebb8876c91`, with original parent
`28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2` and XT01 ancestor
`64c6b777d828ecfe83234fc2aed94600a1f24297`. Its removed worktree was not
recreated. Read-only `git show` ran through the repository's pinned Nix shell.

- `Applications/Trees/Ordered.lean`: all 126 lines read, 5,817 bytes,
  SHA-256 `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66`.
  `ordered_key_iff_pairwise`, `ordered_key_iff_sortedLT` and
  `ordered_key_nodup` expose exactly the strict-key observation under a
  key Preorder. `ordered_map_key_iff` retains key-preserving label transport.
  This source contains no query operation.
- `Applications/Trees/Observations.lean`: definitions and laws through line
  105 read; complete file identity is 4,119 bytes/107 lines, SHA-256
  `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752`.
  `inorder_node`, `inorder_length`, `inorder_map` and ordinary height
  observations are available. The displayed ordinary fold evaluates both
  child summaries under call-by-value; a combining function that later selects
  one does not turn that whole-tree execution into the source query path.
  Function-valued summaries would introduce a construction/invocation issue
  that this small direct recursion need not introduce.

Pinned Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no version/tooling changes are
proposed. The following library files were read in the relevant bounded scope:

| Mathlib path | SHA-256 | Exact reuse boundary |
|---|---|---|
| `Mathlib/Data/Tree/Get.lean` | `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` | `BinaryTree.indexOf` routes by `cmpUsing`, returns `Option PosNum`; `get` follows a supplied position and returns `Option α`. There are no correctness/cost theorems in this file. |
| `Mathlib/Data/Ordering/Basic.lean` | `8add9a4a99dd00271f4f50a73171d5a0f4af31e971c73a807da90a93e0aac89a` | `Ordering.Compares` at 24–27; `cmpUsing` at 48–49 and `cmp` at 55–56. |
| `Mathlib/Order/Compare.lean` | `2a1b09abbc7d20f75a832fc47d1b6014f606938ad1b3db8c9e2bf545fdaca0d4` | `Compares.eq_lt/eq_eq/eq_gt/inj` under Preorder; `cmp_compares` at 121–122 under LinearOrder. |

These Mathlib sources carry Apache-2.0 headers; `Get.lean` credits Mario
Carneiro and Wojciech Nawrocki. `indexOf` is homogeneous in query/stored-label
type, and following it with `get` traverses the path a second time. Searching a
mapped tree of keys additionally traverses the full carrier. Such value bridges
can be useful later, but do not supply this heterogeneous one-pass map query's
resource recurrence. The bounded API report owns any further reuse search;
this is not a claim that no relevant declaration exists anywhere else.

Mathlib `cmpUsing lt q k` tests `q<k`, then `k<q`, then returns EQ. The book
tests `q<k`, then `q=k`, then returns GT. They have the same result on lawful
linear orders, provable from existing branch laws; they are not literally
the same primitive-test program. Under a mere partial/preorder, incomparable
distinct elements make Mathlib return EQ. A singleton tree is strictly ordered
vacuously, but that comparator can then return a false positive for a distinct
query. This is precisely why local `Compares` cannot be silently dropped from
the weaker theorem or inferred from a Preorder instance alone.

## 5. Timing conventions and the exact hit/miss boundary

### What the source actually supplies

Book §1.5 pp.6–8 (`chapter01.txt:188–244`) counts nonprimitive function calls,
uses only the selected conditional/case branch, charges a recursive defining
equation one, and subsequently removes the entry charge for nonrecursive
helpers. Comparators and primitive operations are zero in the usual selected
source-call model when treated under that primitive/inlining convention.
Appendix B p.347 explicitly says zero time functions have been simplified
away; `Time_Functions.thy:12–18` gives zero-cost pair projections.

A scoped search found **no** `time_fun`, `T_isin` or `T_lookup` declaration in
the inspected `Tree_Set`, `Tree_Map`, `Isin2`, `Lookup2`, `RBT_Set`, `RBT_Map`,
`AVL_Set_Code`, `AVL_Set`, `Tree23_Set` or `Set2_Join` theories. Appendix B does
not give a search timing equation. Therefore the equations below are an
explicit **reconstruction of the literal recursion under declared charges**,
not a quotation of a generated source theorem. This absence does not waive
the book's mathematical complexity claims.

### Three distinct observations

Let F be the actual Option-entry query, E its source-style **search invocation
count**, and V its separately declared **visited nonempty node / evaluated
three-way route count**. Comparator internals, key projection, `Option`
constructors and nonrecursive observation wrappers are uncharged in E.

| Reached case | Actual F result | E | V |
|---|---|---:|---:|
| Empty | `none` | 1 | 0 |
| Node with route EQ | `some storedEntry` | 1 | 1 |
| Node with route LT | Actual left-child result | `1 + E(left)` | `1 + V(left)` |
| Node with route GT | Actual right-child result | `1 + E(right)` | `1 + V(right)` |

For all raw finite trees and routes, including malformed ordering and dishonest
routes, the exact relation is

`E(route,t) = V(route,t) + (if F(route,t).isNone then 1 else 0)`.

Success terminates at a node; failure reaches exactly one empty terminal call.
Consequently `E=V` on success and `E=V+1` on failure. It would be false to
copy ordinary merge's universal `entries=comparisons+1` law into this query.
Useful raw bounds are `1 ≤ E`, `V ≤ height t`, and `E ≤ height t + 1`.
Successful queries additionally have `1 ≤ V` and `E ≤ height t`. These bounds
require no BST, balance or cache validity. They must be connected to the same
actual branch execution, not assigned to a list search or a separate traversal
merely because its values agree.

The literal source comparator's **primitive tests** are a third observation:
one `<` test at each reached node, plus one equality test whenever that first
test fails. LT costs one such test; EQ and GT cost two. If Q counts reached
non-LT outcomes, the declared unit-test total is `V+Q`, while the separate test
counts are `<:V` and `=:Q`. Mathlib's two-`<` implementation has a different
test-kind trace. With equal unit charges and lawful comparison results its
aggregate Boolean-test total can be shown to coincide, but that needs a new
explicit observation bridge; value equality alone is not that bridge and
does not prove equal costs for real key comparisons.

An arbitrary `route : α → Ordering` can itself be expensive. The raw E/V bounds
do not account for that internal work. A time claim must retain the book's
constant-comparator/local-work assumption or add the actual comparator work.
No verified compiler, wall-clock, allocation or target-runtime result follows.

### Height, tightness and later logarithms

Book p.59 (`chapter05.txt:25–30`) says worst search time is proportional to
height. The safe all-input call upper bound is height plus one; at an empty
tree E is one while height is zero. For a **nonempty strict BST** with the
source lawful query family, a deepest stored label supplies a query with
`V=E=height t`. This is a concrete route to the stated worst-case lower/tight
bound. An upper-bound-only unit must leave that witness explicitly queued,
not label its upper bound as the entire worst-case claim. No depth datatype,
probability framework or choice of a maximum over an empty query type is
required merely to state the nonempty witness.

The height bound is not a logarithmic bound for arbitrary BSTs: increasing
chains have a successful last-key query visiting every node. Balanced-tree
chapters must establish their own shape invariants, height inequalities and
node-count/abstract-cardinality bridge, then compose them with the actual
query count. For all-length explicit inequalities retain the empty entry
constant; `E ≤ C*log₂(n+1)` alone is false at n=0. No particular new asymptotic
framework is proposed here.

## 6. Compact independent cases and the limits each tests

These are hand-derived expected cases for the case author, not newly run
enumerations, compiled Lean examples or acceptance evidence.

| Case | Actual expected observation | Boundary |
|---|---|---|
| Empty tree, including empty stored-label type | `none`, E=1, V=0 | Total operation and no default value; a query parameter is only quantified when such a value exists. |
| Singleton key k, query k | Stored entry, E=V=1 | Hit does not invoke an empty child. |
| Singleton key k, unequal lawful query | `none`, E=2, V=1 | Failure includes a final empty invocation. |
| Book p.59 tree: root6; left3 with children2/5; right9 with left8 | Query5: hit5, E=V=3. Query4: none, V=3/E=4 | Same-height concrete hit/miss distinction. |
| Ordered map node `(1,false)` | Query1 returns `some false`; an absent query returns `none` | Presence is not truth of the semantic Bool payload. |
| Duplicate key1: root payload false, left child payload true | Raw query1 returns root false; first inorder association returns true | No arbitrary-tree first-match correspondence; distinct full pairs do not imply distinct keys. |
| Root6 with key9 wrongly in the left child and key3 in the right | Query9 follows right and misses despite a stored9; V=2/E=3 | Ordered completeness is needed; raw height bound still holds. |
| Arbitrary color/height tags changed while logical labels and shape stay fixed | Logical query result and E/V stay fixed | Search ignores tags; no assertion that the old/new caches or balancing are valid. |
| Arbitrary route always EQ on a nonempty tree | Returns its root | Raw success is stored-entry evidence, not a query-key equality without calibration. |

The preserved C05-094 interpretation of the p.67 average claim is a uniform
query among the three **present** keys `{3,6,9}` and one unit per visited node/
three-way comparison. The balanced tree with root6 and children3/9 gives
query costs `[2,1,2]`, hence mean `5/3`; the increasing chain3→6→9 gives
`[1,2,3]`, hence mean `2`. These queries all succeed, so the same means hold
for E by the exact hit relation. The source does not provide a uniform
distribution on an infinite key type, an absent-key distribution or a theorem
for arbitrary nonuniform query weights. The fixed finite statement must remain
connected to actual query evaluation, rather than only arithmetic constants.

For map values of type `Empty`, a tree of `(κ × Empty)` entries can only be
empty and every available key query returns none. That is legitimate type
support, not a reason to assume `Inhabited` values or manufacture a default.

## 7. Prospective source/claim table and unchanged downstream work

The following table is a scope recommendation, not frozen requirements or
completed coverage. Partial source rows remain partial.

| Small shared claim | Existing obligation it supports | What it does not settle |
|---|---|---|
| Source comparator/result agreement and selected-child Option-entry query | C05-003/004; C06-045; C08-075 | Any update, deletion, split, balancing or arbitrary primitive-comparator runtime |
| Strict-key membership/absence and first-inorder-map lookup | Query parts of C05-014/028, C06-064/065, C08-021/076, C09-009 | Whole Set/Map contracts and their actual mutation validity/composition |
| Annotation-ignoring value/path transport | C05-066; C08-020/075; C09-008; inherited C10-003 query | Cache correctness, color/height invariants, interval-overlap search |
| Exact E/V hit/miss relation and raw height bounds | Query parts of C08-071/072 and C09-039/040; p.59 source search claim | Whole-operation work, rotations, predecessor/successor extraction, joins or log bounds |
| Actual finite present-key comparison | C05-094 | General probabilistic search/treap history or nonuniform-query claims |

Every original chapter obligation remains mandatory. In particular:

- Chapter 5 retains its all-node characterization and direct-proof exercise,
  insertion, both deletion algorithms, `split_min`, joins, union exercise,
  list refinement, rotations and rotation-distance claims, interval cache/
  overlap/point algorithms and sweep-line complexity. The p.59 deepest-key
  tightness witness remains explicit if not selected for a first shared unit.
- Chapter 6 retains concrete tree/list mutations, key-sorted validity,
  actual intermediate representation laws and full Set/Map realizations.
  Existing abstract ADT drafts do not turn query correctness alone into these
  implementations. The known p.82 wrong `split_min` section reference is an
  earlier retained finding, not a new query-domain change.
- Chapter 7 retains the `Node3` recurrence, its own query proof/count and
  complete-tree height/cardinality interpretation. A binary encoding would
  require an explicit adapter and would change node/height measurements;
  no such encoding is prescribed here.
- Chapters 8 and 9 retain every balancing branch, color/black-height or
  height/cache invariant, update/deletion reconstruction, actual helper work
  and valid-state logarithmic theorem. Full-tree carrier conversion before
  each query is not silently free.
- Chapter 10's `split` returns two rebuilt trees and a Boolean, invokes join
  on its selected recursion results, and must prove all partition and
  invariant conclusions. Shared query semantics may identify the Boolean
  observation, but do not prove the returned trees or total split cost.
  Union/intersection/difference, actual join algorithms and the conditional
  treap-work gap C10-117 remain unchanged.

No new mathematical source defect was established by this bounded read. The
material hazards are explicit comparator/model differences, missing generated
timing evidence, source-domain distinctions and false reuse without strict
key order. The companion mathematical search statements themselves agree with
the printed equations in the inspected scope.

## 8. Handoff and limits

The complementary `ordered-search-api-preflight.md` and
`ordered-search-case-preflight.md` are separately owned. Their authors received
the exact comparator, annotation, E/V, Node3 and malformed/duplicate boundaries;
this report does not claim to have read a completed version of either note.
Root interrupted those tasks for validation recovery, and owns any restart,
scope freeze, worktree, pre-code checkpoint or implementation release.

All conclusions here are source-level mathematics and reuse assessment.
No Lean declaration was written or elaborated, no project checker/hash helper
or compiler was invoked, no Git ref/worktree/cache changed, no remote operation
ran, and no chapter or final review was closed. Read-only source retrieval from
the preserved Git candidate and ordinary SHA-256 byte identities are not
validation evidence. Report edits stop after its complete readback and identity
handoff so root can capture the same bytes in a durability checkpoint.
