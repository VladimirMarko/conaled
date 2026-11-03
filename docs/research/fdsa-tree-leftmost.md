# Ordinary leftmost extraction (FDSA-XT08)

This is an **uncompiled, unaccepted shared source draft** for the ordinary
successor extractor used by Chapters 5 and 6 of *Functional Data Structures
and Algorithms: A Proof Assistant Approach*. It does not activate or complete
either chapter. All original book obligations remain mandatory.

The selected operation returns the first inorder **full entry and its actual
residual tree**. Its entry count belongs to that same execution. Key minimum
properties are separate consequences of strict key ordering; the raw operation
needs no ordering, comparison, equality decision or inhabited payload.

The authoring base is the retained XT07 candidate
`66eae34815a177c6b4bf5120e05202ebb8876c91`, with its XT01/XT06 ancestry.
Those drafts remain unaccepted. The frozen XT08 requirements, source/API/case
preflights, release record and later validation outcomes are retained in the
checkpoint's accompanying `fdsa-control` records. Neither this document nor a
saved checkpoint is acceptance evidence. This unit leaves the original
Chapter 2 integration prefix unchanged.

## 1. Exact source and selected correspondence

The manuscript is the [official July 27, 2026 PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
1,742,029 bytes, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Page references below are printed pages. The companion source is pinned to
Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
That revision postdates the manuscript; it is not claimed to have generated it.

| Primary source | Exact identity and inspected correspondence |
| --- | --- |
| [Tree_Set.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Set.thy) | 3,801 bytes, SHA-256 `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b`. Lines 35–37 define guarded extraction; 39–45 use the returned successor/residual; 76–79 prove the exact head-inorder identity. |
| [Tree_Map.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Map.thy) | 2,028 bytes, SHA-256 `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43`. Lines 5–8 import Tree_Set; 23–28 reuse the same extractor on complete semantic pairs; 41–43 use its list refinement. |
| [Time_Functions.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Time_Functions.thy) | SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`. The pinned zero projection costs at lines 12–19 are consistent with the declared primitive tariff; this file supplies no ordinary extraction timing theorem. |

The ordinary set and map theories credit Tobias Nipkow. The complete applicable
Isabelle BSD notice appears below. The manuscript and extracted research text
are excluded from the source deliverable. Lean and Mathlib imports retain their
own Apache-2.0 provenance.

| Book claim or use | Selected support and limit |
| --- | --- |
| p.61, §5.2 ordinary split_min | The literal guarded left descent and ordinary node rebuilding, with an explicit Lean empty-domain adaptation. |
| p.61 successor replacement | Return the actual full successor and actual residual. The complete recursive delete operation is not supplied by this helper. |
| p.62 deletion-height discussion | Structural nonincrease of the extracted residual is a needed helper. Full replacing/joining deletion height proofs remain separate. |
| pp.82–83 map deletion/list refinement | Tree_Map literally reuses Tree_Set.split_min on `(key,value)`. The connected nonrecursive replacement body retains the successor's value. Full key-directed deletion and map laws remain separate. |
| §1.5, pp.6–8 invocation convention | One actual measured extractor, with explicitly declared zero primitive/reconstruction charges and a reconstructed nonempty invocation recurrence. No ordinary generated T_split_min is asserted. |

**Retained source correction.** The p.82 reference to §5.6.4 is erroneous for
this map operation. Its actual generic dependency is §5.2, p.61. Section 5.6.4
is the interval-tree smart-rebuilding variant, whose second field is a derived
endpoint cache. A map's semantic value cannot be treated as that annotation.
This existing correction remains attached to C06-047; no source assertion is
silently weakened to make the dependency fit.

## 2. One execution, its guarded branches and the empty extension

The selected namespace is `Resources.TreeLeftmost` in
[TreeLeftmost.lean](../../Applications/Resources/TreeLeftmost.lean).
Its primary operation has the ordinary existing type

```text
run : BinaryTree α → Measured (Option (α × BinaryTree α)) Nat
```

`extract?` and `entries` are transparent value/count projections. The frozen
contract uses one actual recursive execution, not a separate pure extractor
and analytical cost oracle. Labels may live in any universe; Nat is only the
observation type. No new tree carrier, comparison machine, order hierarchy,
second visit metric or generic rebuilder is selected.

Mathlib's constructor is `BinaryTree.node a l r`. The source constructor
notation places the label between its children; this argument-order difference
does not change the operation. The actual control is:

| Input | Returned value and reached computation | Count |
| --- | --- | ---: |
| `nil` | `none`; tick the pure failure result. | 1 |
| `node a nil r` | `some (a,r)` using the original r; tick that pure result. | 1 |
| `node a l r`, with l nonempty | Execute only `run l`; bind its actual result, map `(m,l')` to `(m,node a l' r)` inside Option, and tick the resulting bind. | `entries l + 1` |

The tick is the existing post-body `CallCount.tick`. The recursive branch's
actual child result supplies both m and l'; an arbitrary tree with the same
remaining set or list would not be the same implementation. The unreachable
recursive none alternative is handled by Option mapping, with no invented
label or fallback tree. Constructor matching decides whether the left child
is nil without deciding equality of labels.

On a valid nonempty source descent, the extractor **stops before calling the
terminal nil child**. It never visits a right subtree, computes inorder, scans
for a numeric minimum or searches by a query. Calling nil first and interpreting
failure as the base could yield the same value, but it would add a charged
invocation and would require a different cost correspondence.

The HOL source supplies only a node equation. Its empty-tree result is
unspecified, and HOL's nonempty type convention supplies no Lean value of
`Empty × BinaryTree Empty`. XT08 therefore selects a total Option adaptation,
including the explicit measured extension

```text
run nil = (none, 1).
```

The one charge is a deliberate Lean extension under this model. It is not a
recovered source timing case or a hidden default entry. Every nonempty raw
tree succeeds; failure is exactly nil, independently of any search invariant.
The source's deletion callers already establish nonemptiness by checking the
right child before extracting it. Full callers must preserve that domain fact
and consume the actual returned pair.

## 3. Raw values, occurrences and structural bounds

For an actual successful result `extract? t = some (m,r)`, the common source
identity is

```text
m :: Trees.inorder r = Trees.inorder t.
```

It retains full labels, list order and repeated occurrences. It is a one-way
consequence of the actual result. It is not an equivalence characterizing an
arbitrary residual tree: many distinct shapes have the same inorder list.

The selected raw consequences keep their different proof bases explicit:

| Observation | Required premise and meaning |
| --- | --- |
| Failure, success and isSome | Nil is exactly the failure domain; every nonempty raw tree supplies a successful pair. No BST premise is needed. |
| Entry and residual membership | m is in the original inorder; every residual entry was present; original membership is equality to m or residual membership. A repeated m can remain. |
| Head and tail | The original inorder head is some m, and its tail is the residual inorder. These observe the returned tree without replacing it by a list. |
| `r.numNodes + 1 = t.numNodes` | Derive from the exact list equation and existing `Trees.inorder_length`. It counts one occurrence, not a set-cardinality decrement. |
| `r.height ≤ t.height` | Prove from the actual splice and ancestor rebuilding. Inorder equality alone cannot establish this structural bound. Height need not drop by exactly one. |

The raw operation and these observations require no key or payload comparison,
DecidableEq, finite enumeration or Inhabited assumption. In particular, a raw
successful extraction on an unordered tree still returns its first inorder
entry, even if another stored number is smaller.

Arbitrary label mapping transports the whole measured result across independent
universes:

```text
run (t.map f) =
  ((run t).1.map (fun (m,r) => (f m, r.map f)), (run t).2).
```

The residual is mapped as well as the removed entry. Neither injectivity nor
order preservation is needed for this shape-sensitive raw law. The value and
count transports are projections of it. A separate computation of `t.map f`
still has its own work; this equation does not include preprocessing for free.
A constant map can preserve this execution correspondence while destroying
strict key ordering or a derived cache invariant.

## 4. Residual order and strict minimum are separate claims

`Trees.Ordered R` states child validity and the ancestor bounds over the
existing inorder observation. Successful ordinary extraction preserves it for
**arbitrary R**, with no transitivity premise: the actual residual keeps only
old subtree entries, so existing ancestor bounds remain applicable.

Concluding that m is R-related to every remaining entry is stronger. The
selected general all-tail theorem retains `Transitive R` as well as Ordered
input and the actual successful result. The existing ordered-inorder/Pairwise
bridge supplies that conclusion. The nontransitive successor relation in the
examples separates it from mere residual preservation.

For a key function `key : α → κ` and `[Preorder κ]`, the strict key predicate
`Trees.Ordered (fun a b => key a < key b) t` gives:

- The actual residual has the same strict key invariant.
- Every residual key is strictly greater than key m.
- `key m` is an `IsLeast` member of `{q | q ∈ (inorder t).map key}`.
- The removed key is absent from the residual key list.
- A key q occurs in the residual iff it occurred in the original key list and
  q differs from key m.

These propositions need neither linearity nor a comparator, key-equality
decision, order on payloads, or global injectivity of key. Strict ordering of
this particular tree supplies the needed local key uniqueness. Distinct full
records or lexicographic order on pairs cannot substitute for strict order of
their first components. No query-calibration premise from the separate search
unit belongs here: extraction makes no comparison.

The ordinary set specialization uses `key = id`; the semantic map
specialization uses `key = Prod.fst` and retains an arbitrary value type in an
independent universe. The full value returned by the source is never inferred
from the key or replaced by an old root value.

## 5. The declared invocation observation

The measured Nat is the number of entered extractor calls in the selected
model. Constructors, shape inspection, pair/Option observations and the
nonrecursive reconstruction body contribute zero. This matches the relevant
primitive/inlining convention of §1.5; it makes no claim about allocation,
physical memory, stack space, runtime or a compiler realization.

For nonempty input, the two literal source branches count the nonempty nodes
on its left spine. There is no need for a new independently recursive public
left-depth statistic. The direct equations and structural bounds are:

```text
entries nil = 1                         -- selected total extension
entries (node a nil r) = 1
entries (node a l r) = entries l + 1     -- l nonempty

1 ≤ entries t                          -- all inputs
entries t ≤ t.height                   -- nonempty / actual success
entries t ≤ t.numNodes                 -- nonempty / actual success
entries t ≤ t.height + 1                -- all inputs
```

The nonempty height-to-node bound reuses the canonical BinaryTree inequality.
The successful residual's height nonincrease is a different result about its
shape, not a replacement for the input-path count bound. Empty height is zero,
so the sharper bound must not silently include the extension at nil.

Left chains attain the height bound. Nonempty right chains have count one
at every height. Consequently there is no lower bound proportional to each
individual input's height, and strict BST ordering alone supplies no logarithmic
bound. The general families below connect these facts to actual full outputs.
Equal inorders, equal heights and equal extracted keys need not give equal
residual shapes or equal work.

The ordinary `Tree_Set` and `Tree_Map` sources contain no generated
`T_split_min` declaration; their invocation recurrence is reconstructed here
from the literal code under explicit charges. The scoped companion and
Appendix B reads are recorded in the source preflight. This is not an assertion
that no generated extractor timing exists anywhere.

In particular, the retained AFP *Work Bounds for Strongly Joinable Balanced
Binary Search Trees*, by Marco Haucke, dated September 24, 2026, has a different
join-based extractor. Its [dated archive](https://isa-afp.org/release/afp-Joinable_BST_Work_Bounds-2026-10-26.tar.gz)
has SHA-256 `5bf4d3bfc7f9106748163e8c7d4940d7756bcfe5a7ae197ce98dc520fb0b4911`;
`StronglyJoinable.thy` has SHA-256
`da113a8cbdadeb27b7c6689b9e9b929dfb654870484238d4a29e515868b7185f`.
It generates timing at line 699 and bounds it at 706–710 using an actual
`W_join` on the returned residual. Its locale adds rank, balance, size and
supplied join-cost assumptions. That result is not an ordinary-node extractor
cost theorem and does not settle C10-117 or later set work.

## 6. Connected cases and their intended observations

The following results were fixed independently before implementation. The
actual declaration map below connects them to the source statements; numerical
expectations alone are not compiler validation or chapter acceptance.

| Case | Exact expected behavior and meaningful boundary |
| --- | --- |
| Arbitrary base | `node a nil r` returns a and the exact original r with E = 1, for every label and right subtree. A large right fringe is not traversed. |
| One-parent splice | `node c (node a nil B) R` returns a and `node c B R` with E = 2; both opaque fringes remain actual input trees. The strict numeric instance removes 0 from inorder [0,1,2,3], leaves root 2 with children 1 and 3, nodes 4→3 and heights 3→2. |
| Printed tree | Root 6, left 3 with leaves 2 and 5, right 9 with left 8: remove 2, retain root 6 and the whole right fringe, leave left 3 with only right 5. E = 3, residual inorder [3,5,6,8,9], five nodes and unchanged height 3. |
| Empty payload domains | Every `BinaryTree Empty` and `BinaryTree (Nat × Empty)` is nil, with none/E = 1. No successful empty payload or impossible-query substitute is introduced. |
| Whole semantic-pair tree | Inorder [(0,false),(1,true),(2,false)]: remove (0,false), preserve root (1,true) and right (2,false), E = 2. Optional value is some false and presence is true. |
| Actual successor body | Extract only that tree's right singleton (2,false), then rebuild with its actual returned entry/residual and the old left (0,false). Result root (2,false), left (0,false), nil right, extraction subcost 1. This is not a complete deletion or its total cost. |
| Noninjective semantic map | Existing discardTag maps Bool values to Unit, preserves keys and the actual residual/count, and intentionally changes the semantic value. |
| Outer annotation map | Erasing only γ from labels `((κ × β) × γ)` preserves the inner semantic pair and maps the actual residual, with the same count. No cache-validity or free preprocessing claim follows. |
| Duplicate keys | sameKeyRecords removes (1,10), leaves (1,20), E = 1. Key 1 remains despite full-record distinctness. The key-projected duplicate-label case removes one occurrence while leaving the same represented set. |
| Malformed key order | three 2,0,1 removes 2 and leaves ordered root 0/right 1, E = 2. Entry 2 is not least because 0 was stored; successful extraction or an ordered residual does not repair the input premise. |
| Nontransitive relation | three 0,1,2 preserves residual Ordered next, but next 0,2 is false. The all-tail theorem needs transitivity. |
| Stale derived size cache | sizeSample removes (0,1), leaves root (1,4) over its unchanged right subtree of size 2, E = 2. The residual has 3 nodes and stale cache 4, although the input cache was valid. Raw erasure remains a separate correspondence. |

The semantic-pair lookup client observes the **actual successful result** via
standard `List.lookup`. A raw cons equation needs only BEq on keys; at the
extracted key, ReflBEq suffices to return its value. Identifying Boolean tests
with equality and proving a removed-key lookup absent require their applicable
lawful/local equality and strict-key premises. No BEq assumption belongs on
extraction. Concrete residual lookups preserve true at 1 and false at 2 while
key 0 is absent.

The false-payload and presence observers use ordinary bind/pure and the existing
primitive observation law. They preserve the entry count from the same measured
result. The nil observers return none/false with the selected extension charge;
absence is not a stored false value.

For all lengths, the strict left and right Nat chains have inorder `List.range n`,
nodes n and height n. On n>0, both remove 0. The left residual is the actual left
chain on [1,...,n−1] with E = n; the right residual is the original right child,
the right chain on those keys, with E = 1. The actual formal statements retain their
shifted residual constructors, not just their remaining lists. Both residuals
are nil at n=1. At n=3 they are root 2/left 1 and root 1/right 2; their shapes differ
for n≥3 and their counts differ for n>1. Length zero is solely the selected
empty extension. These families instantiate ordinary leftmost extraction,
not AVL's opposite-direction balanced operation.

## 7. Actual public declarations and source assessment

The complete core source has been read. The following are its actual public
names under `Resources.TreeLeftmost`; they describe source statements whose
elaboration and proofs remain unvalidated in this draft.

| Actual declarations | Source connection and retained premise |
| --- | --- |
| `run`, `extract?`, `entries`, `run_eq` | One actual guarded measured recursion and its value/count projections, over arbitrary-universe labels. |
| `run_nil`, `run_node_nil`, `run_node_node`, `run_node_of_ne_nil` | Full nil/base/recursive equations; the general recursive equation retains a nonempty left child. The nil result is the explicit extension. |
| `run_node_of_run`, `extract?_node_of_extract?` | Parent reconstruction consumes the actual successful child pair and, for the measured law, its actual count. The old right fringe is retained. |
| `extract?_nil`, `extract?_node_nil`, `extract?_node_node`, `extract?_node_of_ne_nil`; `entries_nil`, `entries_node_nil`, `entries_node_node`, `entries_node_of_ne_nil` | Direct value and count equations of the same branches, rather than a separately specified oracle. |
| `extract?_eq_none_iff`, `exists_extract?_of_ne_nil`, `extract?_isSome_iff`, `ne_nil_of_extract?` | Complete raw failure/success domain and the source nonempty premise recovered from actual success. |
| `inorder_of_extract?` | One-way full-label head/residual equation from an actual result; this is the counterpart of source split_minD. |
| `mem_inorder_iff`, `extracted_mem_inorder`, `residual_mem_inorder`; `head?_inorder_of_extract?`, `tail_inorder_of_extract?` | Raw occurrence/membership and list observations, with no uniqueness or key-order premise. |
| `numNodes_of_extract?`, `height_of_extract?` | One-occurrence decrement through the existing inorder-length law; structural height nonincrease through the actual splice. |
| `run_map`, `extract?_map`, `entries_map` | Arbitrary cross-universe label transport of the entire returned pair/residual and count; no injectivity or free preprocessing. |
| `ordered_of_extract?`, `rel_of_extract?` | Arbitrary-R residual preservation; separately, transitivity plus Ordered input gives the removed-to-all-tail relation. |
| `key_lt_of_extract?`, `isLeast_key_of_extract?`, `key_not_mem_of_extract?`, `mem_key_inorder_iff` | Preorder-key strict tail, leastness, absence and exact removal. Strict residual order is the existing generic `ordered_of_extract?` specialized to the key relation, without a duplicate wrapper. |
| `one_le_entries`, `entries_le_height`, `entries_le_height_of_extract?`, `entries_le_numNodes`, `entries_le_height_add_one` | Positive total count, sharp nonempty/successful height and node bounds, and the weaker all-input bound including nil. |


The complete [example source](../../Examples/TreeLeftmost.lean) has also been
read. Its actual namespace is `TreeLeftmostExamples`. These clients connect
the fixed independent expectations to public core statements and the retained
`OrderedTreeExamples`/`TreeCacheExamples` fixtures; their proofs remain
uncompiled.

| Actual example declarations | Connected result and boundary |
| --- | --- |
| `nil_run`, `arbitrary_base`, `opaque_promotion`, `every_node_defined`, `empty_payload_run`, `empty_map_value_run` | General guarded branch/domain clients, actual opaque fringes and the two empty-payload types. |
| `promoted_run`, `promoted_extract`, `promoted_observations` | Exact right-child splice, full inorder, occurrence decrement and structural height consequence through the public laws. |
| `printed_run`, `printed_extract`, `printed_residual_inorder`, `printed_residual_ordered` | Full actual printed residual and E = 3; source head/tail and generic residual-order connections. |
| `printed_minimum`, `printed_strict_tail`, `printed_removed_key`, `printed_key_removal`, `printed_size_and_height`, `printed_count_bounds` | Actual strict-key consequences, unchanged height, one-node decrement and successful bounds through the exported general theorems. |
| `payloadRun`, `presenceRun`, their `*_observation` theorems, `tagged_payload_and_presence`, `nil_payload_and_presence` | Actual measured bind/pure observers use `CallCount.primitive_rule`; some false is present, while nil is absent, with the same execution count. |
| `lookup_cons_of_extract`, `lookup_extracted_value`, `lookup_removed_key`, `tagged_lookup_observations`, `tagged_residual_ordered` | General actual-result lookup bridge: BEq for the raw test, ReflBEq for self lookup, and Preorder plus LawfulBEq/strict input order for absence. Concrete untouched values retain their semantics. |
| `successorBody`, `successor_child_run`, `successor_body_run`, `successor_body_inorder`, `successor_body_lookup` | Actual right-child extraction followed by full-entry reconstruction; key 2 retains false, key 1 disappears, and only the extraction subcost is asserted. |
| `discarded_run`, `discarded_order_boundary`, `outer_annotation_run`, `outer_annotation_success` | Whole-result/count transport with intentional Bool-to-Unit value change; separately, general outer-tag erasure retains the inner semantic pair across independent universes. |
| `sameKey_run`, `sameKey_boundary`, `projected_duplicate_run`, `duplicate_occurrence_laws`, `duplicate_set_difference_fails` | Full-record distinctness does not give unique keys. Actual key projection retains raw one-occurrence laws while refuting unconditional set-difference semantics. |
| `malformed_run`, `malformed_boundary`, `next_run`, `next_boundary` | First inorder can fail to be least; arbitrary structural order preservation does not supply the transitive all-tail claim. |
| `sizeSample_run`, `stale_cache_boundary`, `sizeSample_erased_run`, `stale_erased_inorder` | Actual stale residual cache and independent erased value/count correspondence. No smart cache repair is attributed to ordinary rebuilding. |
| `leftChain`, `rightChain`; their `*_inorder`, `*_ordered`, `*_numNodes`, `*_height` laws; `chain_inorders` | Ordinary shifted Nat-key families with complete inorder, order, size and height statements for every length. |
| `leftChain_run`, `rightChain_run`, their `*_run_of_pos` laws; `chain_entries`, `chain_residual_inorders`, `chain_residual_shapes_differ`, `chain_costs_differ` | Full shifted residual constructors and actual measured outputs; equal lists do not identify shape or count. |
| `chain_zero`, `chain_singleton`, `chain_three`, `leftChain_attains_height`, `rightChain_arbitrarily_tall`, `nil_count_boundary` | Empty/singleton/three-node boundaries, general height-bound sharpness, arbitrarily tall count-one strict trees, and failure of the nonempty bound at nil. |

The exact positive-length execution statements use the ordinary example-local
constructors, for every start and n:

```text
run (leftChain start (n+1)) =
  (some (start, leftChain (start+1) n), n+1)
run (rightChain start (n+1)) =
  (some (start, rightChain (start+1) n), 1).
```

`*_run_of_pos` retains these same residuals as length `n-1` under `0 < n`;
it does not infer shape from an inorder equality. The chain constructors are
fixtures, not extra extractor implementations or analytical cost oracles.


This implementation-side source assessment read the complete core and case
statements and their supplied proof scripts. The actual guard, successful-child
rebuilding, one-way inorder law, structural versus transitive order claims,
key-only assumptions, total-extension boundary and connected count/payload
observations match the selected source scope. No concrete mathematical or
source-correspondence mismatch was identified in that bounded read. This is
not an elaboration result or either independent final review axis; possible
proof-script, instance, termination and warning failures remain for validation.

## 8. Original coverage and remaining work

This unit supports only the corresponding helper portions of C05-006/007/008/
013 and C06-047/048/063. The raw head equation and structural bounds do not close
whole replacing deletion; joining deletion is another algorithm. C05-021 still
requires the source exercise's direct recursive BST/set proof route. All full
insert/delete recurrences, association-list refinements, Set/Map interpretations
and original chapter obligations remain mandatory.

Later families retain their distinct operations and proof domains:

| Family | Remaining source-specific obligation |
| --- | --- |
| Interval trees | Smart ancestor reconstruction must recompute derived endpoint caches. Erased inorder and cache validity have separate hypotheses. Ordinary full-pair rebuilding does not do this. |
| 2–3 trees | Node2/Node3 representation, underflow flags and helper domains; completeness is needed even for the inspected source head-inorder law on nonempty input. |
| Red-black replacement | Old-child-color tests and actual baldL/red rebuilding; raw erased inorder, black-height/color preservation, final painting, map adaptations and helper work remain separate. |
| AVL variants | Printed split_max descends right and returns residual before entry. Cached-height and balance-factor variants use their actual balancers and different validity premises. |
| Join-based trees | Actual join consumes the returned residual. The base locale's unconditional set conservation gives no raw inorder/multiplicity/node-decrement theorem by itself. Additional rank/size/balance/cost assumptions and C10-117's conditional work gap remain. |

No mirror extractor, generic rebuilder, allocation model, balancer or complete
delete framework is required by this unit's exclusion list. Original source
algorithms, logarithmic bounds and work proofs remain obligations at their
proper chapters; they are neither discarded nor silently replaced by a new
mandatory general framework.

The inherited tree drafts remain unaccepted, and this new unit remains
uncompiled/unaccepted in this authoring record.
A meaningful statement readback checks the claimed domains, actual outputs,
observation equations and public connections; it does not check elaboration,
termination acceptance, warning policy or kernel proofs. Acceptance still
requires prerequisite reconciliation, matching focused/full guarded immutable
candidate checks, both integrity phases, complete integrated build, exhaustive
transitive axiom audit, both retained independent review axes and immediate
candidate verification. Root owns that existing workflow and its evidence.

## 9. Complete applicable Isabelle notice

The following notice is retained in full from the pinned source distribution:
1,673 bytes, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
It applies to the source-derived correspondence; it is not a license for
redistributing the book manuscript.

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
