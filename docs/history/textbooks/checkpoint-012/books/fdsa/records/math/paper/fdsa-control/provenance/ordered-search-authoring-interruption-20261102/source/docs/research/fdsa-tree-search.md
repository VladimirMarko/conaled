# FDSA shared ordered-tree search paths

This note records FDSA-XS01's common binary query: follow the selected child
and return the actual stored entry, then observe membership or a semantic map
payload. The shared carrier is Mathlib `BinaryTree`; the key invariant is the
existing `Trees.Ordered`. The query's value, comparison assumptions and resource
observations are separate contracts.

**This is an uncompiled source draft.** Neither this unit nor its inherited
tree modules are accepted. The applicable integrated build, exhaustive audit,
independent Standards and Spec reviews and immediate candidate verification
remain pending. Chapter 1 remains active; its current validation attempt does
not validate XS01. Earlier unknown validation outcomes stay recorded in the
local tracker. This note does not activate or complete a later chapter.

## Source identity and repeated consumers

The source manuscript is the **July 27, 2026** version of *Functional Data
Structures and Algorithms: A Proof Assistant Approach*, from the
[official book site](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
The inspected PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Page numbers below are printed pages. The manuscript and extracted research
copies are excluded from the source deliverable.

| Source content | Location | Relevant meaning |
| --- | --- | --- |
| Strict binary search trees and worst-case search proportional to height | Chapter 5, p.59 | Bounds concern every label in each subtree; a deepest present key provides the nonempty lower witness. |
| Three-way comparison and membership recursion | Chapter 5, pp.60–61 | Compare query with stored key; LT selects left, EQ succeeds, GT selects right. |
| Search agrees with inorder/set membership | Chapter 5, pp.63–67 | Correctness retains strict key ordering. |
| Balanced three-key tree versus increasing chain | Chapter 5, p.67 | The retained finite interpretation uses uniform queries among present keys 3, 6 and 9. |
| Augmented membership ignores the annotation | Chapter 5, p.71 | No cache/color/height validity is needed for equality-key search. |
| Map lookup and first-binding association-list observation | Chapter 6, pp.81–83 | Return the stored semantic value; order keys, not complete key/value pairs. |
| Search in a 2–3 node | Chapter 7, p.86 | `Node3` may perform a second comparison and needs its own recurrence/count. |
| Red-black membership and map lookup | Chapter 8, pp.97/102 | Reuse augmented binary queries, ignoring color. |
| AVL sets and their independent height invariant | Chapter 9, pp.105–107 | The companion reuses the same query; balance/cache proofs are separate. |
| Join-based Set2 and reconstructing split | Chapter 10, pp.118–120 | Ordinary membership is inherited; split additionally returns and rebuilds two trees. |

The Isabelle companion is pinned to mirror revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It postdates the manuscript and
is **not** asserted to be its generation revision. Relevant files are under
[`src/HOL/Data_Structures/`](https://github.com/isabelle-prover/mirror-isabelle/tree/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures).
The exact inspected query and reuse identities are:

| Theory | SHA-256 | Source connection |
| --- | --- | --- |
| [Cmp.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Cmp.thy) | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` | Literal comparator at lines 11–12 and LT/EQ/GT laws at 15–18. |
| [Tree_Set.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Set.thy) | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | `isin` at 15–21; strict-inorder correctness at 68–69. |
| [Tree_Map.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Map.thy) | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` | `lookup` at 11–14; first-binding observation at 33–35. |
| [Isin2.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Isin2.thy) | `f6b0c6574c8fa618b5d42f3045e9af32731afd80a061173d8bc09eae9808df0c` | Annotated membership and its two correctness statements, 12–24. |
| [Lookup2.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Lookup2.thy) | `3969a579629d0b60c01cc44da16866e09653d46f46f2a2d2f115905e06739023` | `((key,value),annotation)` lookup, 12–19. |
| `Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` | Inorder erases only the outer annotation; map values remain semantic labels. |
| `RBT_Set.thy` | `542519dc50a4ca03735f68f36bf6bf666f941a33502b028cf2f939b3119d80c8` | Imports `Isin2` and uses `isin_set_inorder` in its Set interpretation. |
| `RBT_Map.thy` | `18aad043c03697c6bd0fb3ad18387dd9030727dceaceee26abb7d5a108ca43ba` | Imports `Lookup2` and uses `lookup_map_of`. |
| `AVL_Set_Code.thy` / `AVL_Set.thy` | `423ea6e7e5d415a9d279ca24c48ce45b2d1bd60f591fae50a00ffa6e852cb2e3` / `282cf829b7efc3421428cbe7ee3e590492d45ed0b8c7b80eff1ae3c57630f3b9` | Shared query import and its separate AVL Set interpretation. |
| `Set2_Join.thy` | `15edbd8a0b1b00633a15d9d1ccffb92d60ca9b313ba3b2f3bf4313af79f57d1b` | `Isin2` import and inherited membership law at 328–335. |
| `Tree23_Set.thy` | `ae1317555ff4e8223d2e047098c62a954f09b8e45e8fd1b1d6522ecdbc888c31` | Conditional second comparison at 24–32; not the binary recurrence. |

`Cmp` credits Tobias Nipkow and Daniel Stüwe; the ordinary and augmented query
theories credit Tobias Nipkow. The complete applicable Isabelle notice appears
below. Its retained source has SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.

## Existing Lean comparison and tree interfaces

Lean is pinned to 4.35.0, revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Their source is reused through
imports, with its existing Apache-2.0 provenance. The literal source comparator
already exists as
[`compareOfLessAndEq`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/Ord/Basic.lean):
it tests query `<` key, then query `=` key, then returns GT. No new comparator
wrapper is needed. Mathlib's existing
[`cmp_eq_compareOfLessAndEq`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Defs/LinearOrder.lean)
relates it to `cmp` under a linear order. `cmp_compares` supplies the
`Ordering.Compares` law, transported through that equality.

`Ordering.Compares` interprets LT as strict less, EQ as actual equality and GT
as reverse strict less. The abstract query theorem can use input-local
calibration with only a key preorder. A preorder alone does not calibrate
an arbitrary route: `cmpUsing` tests `<`, then reverse `<`, and can return EQ
for distinct incomparable keys. Comparator calibration and structural key
order are independent premises.

The unit uses the existing node-labelled `BinaryTree`, whose constructor is
`node entry left right`, and the retained `Trees.inorder`/`Trees.Ordered`.
The ordinary `Trees.fold` evaluates both child summaries in its displayed
call-by-value recurrence; choosing one summary afterward does not make that
a one-path query. Similarly, building inorder or mapping the whole tree to
keys before each query changes the execution.

Mathlib's
[`BinaryTree.indexOf` and `get`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Tree/Get.lean)
remain useful existing interfaces. The former returns a `PosNum` path using
`cmpUsing`; the latter follows a supplied path. Their homogeneous value
connection does not identify the cost of a two-pass search with one selected
traversal. No dummy semantic payload or global `Inhabited` assumption is
introduced to satisfy that homogeneous interface.

## Literal recurrence and resource interpretation

`Resources.TreeSearch.run` in
[TreeSearch.lean](../../Applications/Resources/TreeSearch.lean) is the one
structural recursion. It uses `CallCount.tick (pure none)` at nil, ticks
`pure (some a)` on a hit, and ticks only the actual selected recursive result
on LT/GT. `find?` and `entries` project that pair. `visits` subtracts the
terminal-miss indicator from its E component; it is not another executor.
Write F for the returned option, E for search invocations and V for nonempty
node visits. The source draft exposes these equations for the same execution:

| Reached case | F | E | V |
| --- | --- | ---: | ---: |
| Empty | none | 1 | 0 |
| Node, route EQ | some actual stored entry | 1 | 1 |
| Node, route LT | Actual left result | E(left)+1 | V(left)+1 |
| Node, route GT | Actual right result | E(right)+1 | V(right)+1 |

The source-style E tariff charges one search invocation, including an empty
terminal call; comparator internals, key projection, Option constructors and
nonrecursive observers are uncharged. It reconstructs the literal query under
Chapter 1's declared primitive/inlining convention. The inspected search
theories contain no generated `T_isin`/`T_lookup` declaration, and Appendix B
does not provide a search timing equation. E is therefore not attributed to
an absent generated timing theorem. The absence of such a theorem does not
waive the book's complexity claims.

The exact distinction is

`E = V + (if F.isNone then 1 else 0)`.

A successful run terminates at a node and has E=V; failure reaches one empty
call and has E=V+1. Deriving V by natural subtraction requires E positivity
and the direct V branch laws; the subtraction definition alone does not
establish its visit meaning. V is not an additive reweighting of E alone:
a root hit and an empty run both have E1, with V1 and V0 respectively. When
sequencing multiple queries, their correction is the sum of their actual
miss indicators. It cannot be recovered from the total E and only the last
returned option.

The literal comparator's primitive tests are a third observation. LT performs
one `<` test; EQ/GT also perform an equality test. V counts route evaluations,
not those primitive tests. `cmp` instead uses two directions of `<`; its
Ordering-result equality supplies neither a primitive-tariff theorem nor
an equality of real comparison costs. This unit introduces no primitive-test
counter. An arbitrary route can be expensive internally, so an E or V bound
is not a runtime bound without the additional local/comparator assumptions.

The post-body charge is the existing `Resources.CallCount.tick`. There is no
claim about Lean's stack behavior, compiler normalization, evaluation sharing,
allocation, wall-clock time or target execution. Exposing a measured result
with `let`, or reading its projections, is not a memoization theorem.

## Public declaration correspondence

The following names refer to the actual source draft, under namespace
`Resources.TreeSearch`. This records statement correspondence; no elaborated
types, compiled proof or final-review outcome is asserted by this table.

| Actual public source | Statement and retained premise boundary |
| --- | --- |
| `run`, `find?`, `entries`, `visits`; `run_nil`, `run_node`, `run_node_lt/eq/gt` | One actual selected execution, Option/E projections and derived V; raw labels/routes need no additional structure. |
| `find?_nil`, `find?_node_lt/eq/gt`; `entries_nil`, `entries_node_lt/eq/gt`; `visits_nil`, `visits_node_lt/eq/gt` | Direct branch equations include immediate hits and terminal empty calls. V's interpretation is established by its equations, not subtraction alone. |
| `entries_pos`, `entries_eq_visits_add_terminal`, `entries_eq_visits_of_some`, `entries_eq_visits_add_one_of_none` | Positivity justifies natural subtraction; E=V on actual hits and E=V+1 on actual misses. |
| `find?_some_spec` | A raw returned entry is stored and its reached route was EQ, without orderedness or comparator honesty. |
| `key_eq_of_find?_eq_some` | Local honest comparison turns a hit into key equality with only LT structure; no BST premise. |
| `find?_eq_some_iff`, `find?_eq_none_iff`, `find?_isSome_iff` | Full-entry, absence and presence semantics under strict key `Ordered`, key Preorder and input-local `Compares`. |
| `find?_eq_find` | First-inorder-entry observation uses only the decidable EQ result of `Ordering`, with the same semantic premises. |
| `map_find?_eq_lookup` | Semantic pair payload agrees with standard first-binding `List.lookup`; only this observer adds lawful key BEq. |
| `run_map`, `run_map_pullback`, `find?_map`, `entries_map`, `visits_map` | Actual result/path transport under input-local route agreement, across label universes, without injectivity, order or cache validity. |
| `entries_le_height_add_one`, `entries_le_height_of_some`, `visits_le_height`, `visits_pos_of_some` | Raw height bounds and stronger successful-query bounds; no balancing premise or logarithmic claim. |
| `exists_run_eq_height`, `exists_run_visits_eq_height` | A stored-key-pair-calibrated family on a nonempty strict tree has an actual full-pair height witness, with V=height as well. |
| `exists_source_run_eq_height` | The same general witness specialized through existing `compareOfLessAndEq`, `cmp_eq_compareOfLessAndEq` and `cmp_compares`. |

## Semantic contracts and their hypotheses

The raw operation takes `route : α → Ordering` and a tree and needs no order,
equality decision, finite enumeration or inhabitant on α. A returned `some a`
is evidence that a is an actual stored label and that the reached route at a
is EQ. A dishonest route can return the root for an unrelated query; raw
stored-entry soundness does not certify query-key equality.

For `key : α → κ` and query q, comparison calibration is local to the input:

`∀ a ∈ Trees.inorder t, (route a).Compares q (key a)`.

Calibration plus a successful result gives `key a = q` with only the LT
structure needed to state `Compares`; it does not require the tree to be
ordered. Completeness requires the actual strict key invariant
`Trees.Ordered (fun a b => key a < key b) t`. Under a key Preorder and these
two premises, the full-entry and absence contracts are:

```text
find? route t = some a ↔ a ∈ Trees.inorder t ∧ key a = q
find? route t = none ↔ ∀ a ∈ Trees.inorder t, key a ≠ q
```

The whole-subtree bounds justify pruning the opposite child; strict ordering
supplies uniqueness of matching keys inside this tree. Global injectivity of
key, an order on complete payload records, weakly sorted keys or merely
Nodup full records are not substitutes. Labels and keys may inhabit independent
universes. Calibration is a proof premise, not an instruction to compute
inorder before searching.

The first-inorder-entry specification uses existing `List.find?` and the
predicate `fun a => decide (route a = Ordering.eq)`. It requires no extra key
or payload equality decision. For labels `κ × β`, the semantic map observation
is `(find? route t).map Prod.snd`, compared to existing first-binding
`(Trees.inorder t).lookup q`. Only the lawful key BEq interface used by that
list observer is added; β remains unrestricted. A present Bool value false is
`some false`, while absence is none.

Exact label transport assumes only that routing agrees on the actual input
labels: `route' (f a) = route a` for each stored a. It relates the full measured
results, mapping the returned option by f and preserving E; the actual
isNone indicator then preserves V. It needs neither injectivity nor any
ordering, cache or balance premise. This follows the same reached branches;
inorder or height equality alone would not establish it. An actual client
that builds `t.map f` still performs that construction separately.

For source augmented maps, `((κ × β) × γ) → κ × β` erases only the outer γ
annotation and retains the arbitrary semantic β value. Changing Bool to Unit
in the existing `discardTag` fixture is a different, deliberately noninjective
payload map. It preserves the mapped entry and the query path, not the old Bool
payload. These are separate uses of the same raw transport law.

## Raw bounds and the selected nonempty tightness witness

The model has E≥1, V≤height and E≤height+1 on every raw tree and route. On a
successful query, V≥1 and E≤height. These conclusions do not require key
correctness, strict order, cache validity or balancing. At empty height zero,
E is one and V is zero.

The p.59 lower witness is explicitly part of XS01. For a nonempty strictly
key-ordered t and a family `route : κ → α → Ordering`, require calibration
only for stored queries against stored entries:

```text
∀ a ∈ inorder t, ∀ b ∈ inorder t,
  (route (key a) b).Compares (key a) (key b)
```

Then some a in inorder t satisfies
`run (route (key a)) t = (some a, t.height)`, and the hit relation also gives
V=height. A structural maximum-child argument chooses a nonempty child of
maximal height, or the root when both children are empty. Strict subtree
bounds and calibration force the selected stored-key query into that child.
This needs no absent key, default payload, depth datatype or maximum over an
empty query domain. The source LinearOrder case uses the existing literal
comparator and its established calibration.

This is present-key height tightness: an absent query can take height+1, and
a root hit can cost one even in a tall tree. It does not claim every query
costs height or establish logarithmic height. The latter requires each later
balanced representation's actual invariant and height/cardinality theorem.

## Case meanings fixed independently of the implementation

The retained printed-tree fixture has root6, left subtree3 with children2/5,
and right subtree9 with left child8. Its inorder is `[2,3,5,6,8,9]` and height
is three. Required actual observations distinguish early termination from a
reached empty child:

| Query | Stored-entry result | V | E |
| ---: | --- | ---: | ---: |
| 6 | some6 | 1 | 1 |
| 3 | some3 | 2 | 2 |
| 9 | some9 | 2 | 2 |
| 8 | some8 | 3 | 3 |
| 4 | none | 3 | 4 |

The existing legal left rotation preserves inorder and strict ordering.
Query6 still returns6, but E=V changes from one to two. This is value
preservation with a changed execution path, not a rotation-cost theorem.

The existing keyed Bool fixture has inorder
`[(0,false),(1,true),(2,false)]`. Query0 returns `some (0,false)` with E=V2;
its semantic payload is `some false`, and its presence observation is true.
Query3 is absent with V2/E3. The payload and presence clients must consume the
actual measured result through ordinary bind/pure and the existing
`CallCount.primitive_rule`, retaining E without evaluating another query.
The noninjective Bool-to-Unit map retains those path counts and maps the
returned entry; general outer-tag erasure retains semantic payloads instead.

Three independent invalid-input boundaries identify the missing premises:

- A malformed tree rooted at `(2,"root")` with `(5,"left")` in its left child
  has distinct keys but query5 follows the empty right child: none, V1/E2.
  Inorder association lookup still returns `some "left"`; ordered pruning is
  missing.
- The retained two records `(1,10)` and `(1,20)` have distinct complete entries
  and weakly sorted keys. Rotating their tree preserves inorder but changes a
  root-hit query1 from payload10 to20, each with E=V1. First-binding list
  lookup stays10. This refutes unconditional entry/payload lookup invariance;
  Bool presence happens to remain true in both runs.
- On a strict tree rooted at2 with leaves1/3, an always-EQ route for query9
  returns stored2 with E=V1. Ordering does not certify comparison calibration.

Empty results/counts quantify over arbitrary label types. The `Nat × Empty`
map case uses an available query0, so it demonstrates empty semantic payload
support without hiding behind an impossible query or inventing a default.

The p.67 comparison uses exactly the three present queries `[3,6,9]` on the
balanced tree rooted at6 with children3/9 and the literal right chain3→6→9.
Their actual successful E/V lists are `[2,1,2]` and `[1,2,3]`; sums are5 and6,
and rational arithmetic means are5/3 and2. This is the uniform finite
present-key interpretation retained by C05-094. It introduces no probability
framework, uniform law on infinite keys, absent-query distribution or claim
for arbitrary nonuniform weights. Standalone arithmetic constants would not
supply the required connection to the actual runs.

## Pending chapter work and acceptance

The scope is a common query and its explicit observations. All original book
obligations remain mandatory; partial rows remain partial. Chapters 5 and 6
retain all concrete mutation/list refinements and complete Set/Map laws;
Chapter 5's direct-proof exercise still requires its other laws. Both deletion
algorithms, split-min domains, joins, union construction, positioned rotations
and their reconstruction work, interval cache/overlap/point algorithms and
sweep-line complexity remain queued.

Chapter 7's Node3 has a conditional second comparison and needs its own carrier,
recursion and count. Chapters 8 and 9 retain every color/black-height or
height/cache invariant, balancer and update/deletion branch, and actual
logarithmic guarantee. Query correctness alone supplies neither cache validity
nor a balance theorem. Strict BSTs can be chains; successful last-key queries
can visit every node. An all-length E bound must also retain the empty-call
constant, since E is one at size zero.

Chapter 10's split returns two rebuilt trees and a Boolean and calls join on
actual recursive outputs. A query observation cannot establish those returned
trees or total work. Union/intersection/difference, actual joins and the
retained conditional treap-work gap C10-117 are unchanged. No new general
translator, history framework or additional algorithm is required solely by
these exclusions.

The original source base is
`66eae34815a177c6b4bf5120e05202ebb8876c91`, the unaccepted XT07 draft with
its preserved XT01/XT06 ancestry. Accepted repaired Chapter 1 and applicable
tree prerequisites precede integration/acceptance; the original Chapter 2
prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847` remains unchanged.
A checkpoint preserves progress and evidence; it does not certify this source.
All required focused/full candidate checks, both integrity passes, exhaustive
audit, independent Standards/Spec reviews and immediate candidate verification
remain pending.

## Applicable Isabelle notice

The source-derived query correspondence and adaptations retain this complete
notice from the pinned Isabelle distribution:

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
