# Chapter 23: Pairing Heaps — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-023`.

**State: queued; source preparation only.** No Lean implementation, build,
ticket/acceptance change or remote write is performed by this note. Chapter 1
remains the active sequential chapter. The rows below are obligations for
future checked implementation and correspondence, not completed proofs.

## Sources and inspected pins

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 23, printed pp.257–263; p.264 blank, p.265 Part V title, p.266 blank. PDF pages263–272, July27,2026 version. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Functional companion | Hauke Brinkop and Tobias Nipkow, *Pairing Heap*, AFP2016, <https://isa-afp.org/entries/Pairing_Heap.html>. Dated archive <https://isa-afp.org/release/afp-Pairing_Heap-2026-10-26.tar.gz>, 5,077 bytes, SHA-256 `fe2985e0b299455da334b51ef37c780e392f551dc47ea5f9a14bfbd53c1a3653`. |
| Analysis companion | *Amortized Complexity Verified*, <https://isa-afp.org/entries/Amortized_Complexity.html>. Dated archive <https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz>, 31,633 bytes, SHA-256 `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`. |
| Direct manuscript links | `Pairing_Heap/Pairing_Heap_List2.html`, `Amortized_Complexity/Pairing_Heap_List2_Analysis.html`, and `Amortized_Complexity/Pairing_Heap_Tree_Analysis.html` under <https://isa-afp.org/browser_info/current/AFP/>. The dated archives identify the actual inspected sources; current browser pages are mutable. |
| Shared specifications | Chapter14 owns the exact multiset PQ/merge contract. AppendixB B-056–060 records the time-function tariff. Chapter19 owns the amortized operation-history framework and both-input potential accounting. |
| AFP license | Both entries advertise BSD. Shared <https://isa-afp.org/LICENSE>, SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Preserve relevant attribution/notices when adapting source. |
| Lean reuse | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; inspected workspace HEAD `1aabd512284fe86254278ac631eda061d311050b`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean4.35.0. The inspected pairing implementation is Apache-2.0. These pins do not imply acceptance of local candidate work. |

| Exact file | Bytes | SHA-256 |
|---|---:|---|
| `Pairing_Heap/Pairing_Heap_List2.thy` | 6632 | `cea84ce48af8653082f68ac84fd763fdfabea981952d292819c84b88f8ba4b76` |
| `Amortized_Complexity/Pairing_Heap_List2_Analysis.thy` | 9794 | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` |
| `Pairing_Heap/Pairing_Heap_Tree.thy` | 6311 | `70dc1433107d000ecc6fa195eb642ddd9251a8f6614c7d3afb7ffa9aac13434f` |
| `Amortized_Complexity/Pairing_Heap_Tree_Analysis.thy` | 9817 | `0e7f8008a2d06c7dbc2f8647b05f87324dafab5ff96daa96097bb2722cfdc368` |
| `Amortized_Complexity/Pairing_Heap_Tree_Analysis2.thy` | 9180 | `a04e140d2ff71d11bafd9e16e39359bcf132b194d7cbfe9a27206f261e53d191` |
| `Amortized_Complexity/Lemmas_log.thy` | 1768 | `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41` |
| `Amortized_Complexity/Priority_Queue_ops_merge.thy` | 241 | `1878defbd25e6fa4eb9d269d6da36f31049ed9e050586fab8203cd498e4488ea` |
| Batteries `Data/PairingHeap.lean` | inspected complete file | `394ca3c1b7f3b091bd77df7d752fcba2d3deb5434d04f64027070e9deb52ae82` |

The main book implementation and exact constants correspond to the **List2**
theories. The older binary-tree analysis has a different, looser deletion
bound; its proof cannot simply be cited as the List2 theorem with the book's
coefficient2. The simplified tree analysis and an explicit representation
bridge provide additional support. No admission markers were found in the
five listed pairing theories. No Isabelle or Lean build was run.

The source revision postdates the book. Reading copies stay under
`book-source/`; this original inventory and provenance, rather than the
manuscript or external papers, are the deliverable. All mathematical main
text, Exercise23.1, and the mathematical improvement claim in the chapter
notes remain in scope. Historical attribution, empirical comparisons and
the report that a final analysis was open are documented context, not
universal machine-performance theorems.

## Carrier, order and library reuse

The source nonempty rose tree is `Hp x children`, where every child is again
nonempty. A whole heap is `Option (Hp α)`. Consequently there is no
structural condition forbidding empty children: the type already excludes
them. The **heap-order** invariant is still necessary for minimum
correctness. The potential analysis itself requires neither heap order nor
payload comparisons beyond selecting a branch.

Batteries provides `Batteries.PairingHeapImp.Heap α` with `nil` and
`node value child sibling`. It is an exact carrier for **forests** under
the child/sibling encoding, while `Heap.NoSibling` characterizes whole
optional heaps. Mathlib `BinaryTree α` with `numNodes` is another exact
binary carrier, with a constructor-preserving equivalence as a possible
adapter. Lean `sizeOf` is not the payload-node count.

| Existing declaration | Checked support and material limit |
|---|---|
| `Heap.NoSibling`, `noSibling_merge`, `noSibling_combine`, `noSibling_deleteMin`, `noSibling_tail?`, `noSibling_tail` | Whole-heap structural support. Raw merge discards input sibling fields; whole-heap correspondence must require `NoSibling`. |
| `Heap.size`, `size_merge`, `size_merge_node`, `size_combine`, `size_deleteMin` | Payload counts and preservation/removal. `size_merge` needs both operands `NoSibling`; `size_combine` preserves an arbitrary encoded forest's node count. |
| `Heap.NodeWF`, `Heap.WF` | Local heap edges plus whole-heap structure. Edge constraints are conditional on `[TotalBLE le]`; totality alone is not transitivity. Under a lawful non-strict linear order they can be related to the source's descendant-wise invariant. |
| `Heap.WF.merge`, `merge_node`, `combine`, `deleteMin`, `tail?`, `tail` | Invariant-preservation building blocks. `WF.combine` assumes a common lower-bound parent value for the entire child forest; that is available when deleting a valid root but stronger than the source's standalone pass premise that each child is a heap. |
| `Heap.merge` | With standard `≤`, equal roots keep the first tree. Source `link` uses `<` and equal roots keep the second. These yield different valid shapes and possibly different subsequent deletion work. |
| `Heap.combine` | Fused adjacent pairing followed by right-to-left combination, with the same linking order as Exercise23.1 under a matching comparator. There is no intermediate list. A checked encoding correspondence is still needed. |
| `Heap.head?`, `deleteMin_fst`, `Heap.tail` | Explicit optional empty minimum; returned deletion key agrees with head. `tail` matches the source's empty-preserving deletion behavior. The file does not prove full source multiset/leastness semantics. |
| `Resources.Measured` | Reusable `Measured`, `bind`, `bind_erases`, `reweight_bind`, `erasureSquare`; no pairing-specific cost theorem is already provided. |
| `Resources.Workload` | Observation-polymorphic `run`, `run_append`, `run_invariant`, `run_value_fusion`. The amortized merge client additionally needs a two-operand usage history. |
| `Resources.Potential` | Current `run_potential`, `run_potential_exact`, `run_cost_le` use Nat-valued potentials/charges. The book's logarithmic potential is Real-valued; rounding it changes exact constants. Reuse a properly generalized telescope or the Chapter19 shared development. |

Setting the Batteries comparator to strict `<` matches raw branch choices,
but `[TotalBLE (<)]` is impossible on an inhabited strict-order type. The
guarded edge fields then become vacuous, so the resulting library `WF`
cannot stand in for source heap order. For a **single** link, reversing
operands to a non-strict Batteries merge reproduces the source result; it
does not automatically change the internally ordered links in `combine`.

A concrete valid tie witness is
`h₁=Hp 0 []`, `h₂=Hp 0 [Hp 1 []]`. Source strict link returns
`Hp 0 [Hp 0 [], Hp 1 []]`; usual Batteries non-strict merge decodes to
`Hp 0 [Hp 0 [Hp 1 []]]`. Both contain the multiset `{0,0,1}`, but their
root degrees are2 and1. Preserve this witness if using the library carrier
or operations. The full inspected file has size/structural/WF proofs but
no multiset/permutation, leastness, logarithmic-potential or amortized-cost
proofs. Complexity comments are not checked evidence.

Use `Search.PriorityInterface.ExactQueue` / `ExactLaws` for clients that
retain all occurrences; Chapter14's separate merge compatibility contract
supplies the missing binary operation. The keyed replacement interface
does not express this book's multiset priority queue.

## 23.1 Implementation and correctness: pp.257–259

Write `M h` for a rose tree's multiset, `MF hs` for the list sum of child
multisets, and `MH` for the optional-heap multiset. `H` is the rose-tree
heap predicate, `V` its optional lift. The source uses a linear order.

| ID | Source obligation | Exact algorithm or hypothesis |
|---|---|---|
| C23-001 | Nonempty rose tree `Hp x hs`, selector `hps(Hp x hs)=hs`, whole heap `Option Hp`. | No empty rose node may occur in the child list. Do not replace this by a datatype allowing empty interior children without a structural invariant and a checked adapter. |
| C23-002 | `M(Hp x hs)={x}+Σ(h in hs)M h`; `MH none=0`, `MH(some h)=M h`. | List sum retains every occurrence, including equal children/payloads. `M h≠0` and `MH q=0 ↔ q=none`. |
| C23-003 | `H(Hp x hs) ↔ ∀h∈hs,(∀y∈M h,x≤y)∧H h`. | Descendant-wise ordering; under transitivity it is equivalent to ordering against child roots plus recursively valid children. State a checked bridge if reusing local library edge predicates. |
| C23-004 | `V none=True`, `V(some h)=H h`. | Structural well-formedness and heap order remain separate concepts despite the lack of empty-child invariant. |
| C23-005 | `empty=none`; nonempty `getMin(some(Hp x hs))=x`; `isEmpty q ↔ q=none`. | The minimum outside the nonempty domain is unspecified. Reuse an `Option` result/domain witness and avoid a blanket payload inhabitant. |
| C23-006 | `link(Hp x xs)(Hp y ys)` returns `Hp x(Hp y ys::xs)` if `x<y`; otherwise `Hp y(Hp x xs::ys)`. | Strict test, second root on equality, loser prepended as first child. No rank/size restriction is required. |
| C23-007 | `merge q none=q`, `merge none q=q`, and two present heaps return `some(link h₁ h₂)`. | Nonrecursive operation; preserve ordered link operands. |
| C23-008 | `insert x none=some(Hp x [])`; on a present heap `h`, return `some(link(Hp x [])h)`. | Equal-key insertion keeps the old root and adds the new singleton as first child. |
| C23-009 | `pass1(h₁::h₂::hs)=link h₁ h₂::pass1 hs`; empty/singleton inputs are returned unchanged. | Adjacent pairs are processed left-to-right in the result; the final unpaired singleton keeps its position. |
| C23-010 | `pass2 []=none`; on `h::hs`, compute `pass2 hs`, return `some h` if empty and otherwise `some(link h tailResult)`. | Right-associated, right-to-left linking. A left fold or different link order need not give the same heap shape. |
| C23-011 | `delMin none=none`; `delMin(some(Hp x hs))=pass2(pass1 hs)`. | Actual pass2 consumes the actual result of pass1. The root is removed once; no separate `getMin` traversal occurs. |
| C23-012 | Pass1/fused recursion decreases child-list length by2, pass2 by1; all public operations terminate. | The heap's recursive datatype is finite. Constructor counts and payload order are not used as arbitrary termination assumptions. |
| C23-013 | On nonempty input, `getMin q∈M(the q)`. | `get_min_in`; requires no heap-order invariant. Replace the HOL partial `the` by a present-heap witness in Lean. |
| C23-014 | Nonempty `q`, `V q`, and `y∈M(the q)` imply `getMin q≤y`. | `get_min_min`; minimum leastness genuinely requires the heap-order predicate. |
| C23-015 | `M(link h₁ h₂)=M h₁+M h₂`. | `mset_link`; unconditional on raw nonempty rose trees. |
| C23-016 | `MH(merge q₁ q₂)=MH q₁+MH q₂`. | `mset_merge`; unconditional. Reusing the same immutable value twice adds two logical occurrences, even when physical storage is shared. |
| C23-017 | `MH(insert x q)={x}+MH q`. | `mset_insert`; unconditional occurrence addition. |
| C23-018 | `MF(pass1 hs)=MF hs`. | `mset_pass1`; no ordering invariant. |
| C23-019 | `MH(pass2 hs)=MF hs`. | `mset_pass2`; no ordering invariant. In particular pass2 returns none iff `hs=[]`. |
| C23-020 | `q≠none → MH(delMin q)=MH q−{getMin q}`. | `mset_del_min`; no heap-order hypothesis. The removed root is an occurrence even when it is not the least raw payload. |
| C23-021 | `H h₁ ∧ H h₂ → H(link h₁ h₂)`. | `php_link`; use linear order to show the winning root is below both child multisets. |
| C23-022 | Merge preserves `V` for two valid inputs; insert preserves it for one valid input. | `invar_merge`, `invar_insert`. |
| C23-023 | If every input child satisfies H, every pass1 output satisfies H, and pass2 returns a valid optional heap. | `invar_pass1`, `invar_pass2`. These standalone statements do not assume a common parent lower bound. |
| C23-024 | `V q → V(delMin q)`. | `invar_del_min`; combines both pass invariants. |
| C23-025 | All eight shared priority-queue laws and both merge laws. | Source interpretation `pairing:Priority_Queue_Merge`. Keep exact occurrences, valid-domain minimum and existing empty behavior through the project's interface adapters. |

## Exercise23.1 and actual selected-function costs: p.259, AppendixB.11

The source tariff counts recursive pass entries. Nonrecursive link, merge
and insertion have **zero** cost in this observation; that does not mean
zero comparisons/allocations or zero machine time. The deletion wrapper has
no extra tick. An empty/singleton pass base still costs1.

| ID | Source obligation | Exact recurrence or bound |
|---|---|---|
| C23-026 | Fused `mergePairs []=none`, `mergePairs[h]=some h`; on two heads, let `h12=link h₁ h₂`, recursively combine `hs`, and return `h12` if empty or `link h12 recursiveResult` otherwise. | This is the companion's `merge_pairs` and matches Exercise23.1's required pair-before-recursion result order. It returns an optional heap without an intermediate forest list. |
| C23-027 | `mergePairs hs=pass2(pass1 hs)` for every raw forest. | `pass12_merge_pairs` in the companion, oriented opposite to the exercise. Equality is of the whole labelled heap, so tie and operand order matter. |
| C23-028 | `Tpass1 []=Tpass1[h]=1`; on two heads, `Tpass1(h₁::h₂::hs)=1+Tpass1 hs`. | B-059. Therefore `Tpass1 hs=floor(length hs/2)+1`. Link has zero tariff. |
| C23-029 | `length(pass1 hs)=ceil(length hs/2)=(length hs+1)/2`. | Needed for exact cost and intermediate-spine bounds. Counts output trees, not total payload nodes. |
| C23-030 | `Tpass2 []=1`, `Tpass2(h::hs)=1+Tpass2 hs`; therefore `Tpass2 hs=length hs+1`. | B-060's residual option case contributes0 on either outcome; justify that simplification by exhaustive option cases. |
| C23-031 | `Tpass1 hs+Tpass2(pass1 hs)=length hs+2`. | Strong exact form of the book's displayed upper bound. Both empty base charges are present, including `hs=[]`. |
| C23-032 | Fused pass has base1 on empty/singleton and recursion `1+TmergePairs hs` after removing a pair; hence `TmergePairs hs=floor(length hs/2)+1`. | Use the same recursive-call-only tariff as the two passes. Counting each nonrecursive link invocation would be a different observation. |
| C23-033 | Exercise time theorem `TmergePairs hs≤Tpass1 hs+Tpass2(pass1 hs)`. | Derive from actual recurrences/checked measured erasure, not an assigned formula detached from code. The companion includes the value equality but does not expose this exercise-specific time theorem as an already completed Lean fact. |
| C23-034 | The fused program allocates no intermediate pass1 forest spine. | In an explicit list-spine allocation observation, pass1 allocates `floor(length hs/2)` new result cons cells; its singleton base reuses the supplied list. Fused recursion allocates0 such intermediate cells, while link-created heap-child cons cells still occur. State this resource distinction precisely. |
| C23-035 | Fused deletion inherits exact contents, validity, minimum removal and any upper bound proved for the slower two-pass cost. | Value equality and the time inequality are the separate required bridges. Do not claim identical costs. |
| C23-036 | Worst-case deletion can be linear in total heap size. | A valid star with root0 and k nonempty singleton children has size k+1 and exact two-pass work k+2. This witnesses the prose claim; it does not contradict the sequence amortized theorem. |
| C23-037 | Link, insertion and merge perform a bounded number of root comparisons/constructor operations. | State ordinary constant-time conclusions under constant primitive/structural-sharing assumptions, separately from their selected-call tariff0. Payload comparison cost itself is parameterized if the payload is nonconstant size. |

## 23.2 Sizes and potential: pp.260–262

Use distinct notation in implementation even though the source overloads
`sz` and Φ. Write `sF`, `sH`, `sQ` for forest, nonempty-tree and optional
heap sizes; `φF`, `φH`, `φQ` for potentials. `lg x` means real `logb 2 x`.
Natural sizes are cast to Real before subtraction and logarithms.

| ID | Source obligation | Exact equation or property |
|---|---|---|
| C23-038 | `sF []=0`, `sF(Hp x children::siblings)=sF children+sF siblings+1`; `sH h=sF(hps h)+1`; `sQ=Option.elim 0 sH`. | Counts Hp/payload nodes, not every list/option constructor and not payload-dependent `sizeOf`. `lift_hp` is just an optional eliminator. |
| C23-039 | `sF hs=Σ(h in hs)sH h`, `sH h=card(M h)`, `sQ q=card(MH q)`. | Establishes a common notion of queue size and the cardinality interpretation of the logarithmic bounds. |
| C23-040 | `sH(link h₁ h₂)=sH h₁+sH h₂`, hence its child size is the sum minus1. | `sz_hps_link`; its subtraction is safe because both trees are nonempty. |
| C23-041 | `sF(pass1 hs)=sF hs`, `sQ(pass2 hs)=sF hs`; insertion adds1, merge adds both sizes, nonempty deletion subtracts1. | `pass1_size`, `size_hps_pass2` and multiset consequences. Preserve total payload size separately from C23-029's forest-length reduction. |
| C23-042 | `φF []=0`; `φF(Hp x children::siblings)=φF children+φF siblings+lg(sF children+sF siblings+1)`. | The logarithm includes later siblings. It is generally **not** the sum of the individual nonempty-tree potentials. |
| C23-043 | `φH h=φF(hps h)+lg(sF(hps h)+1)`; `φQ none=0`, `φQ(some h)=φH h`. | Precisely the source's overloaded definitions and optional lift. |
| C23-044 | Forest, nonempty-tree and optional potentials are nonnegative on every raw shape. | Every logarithm argument at a node is at least1. Empty potential is0; no use of an unspecified real logarithm at0 is needed in the definition. Heap order is not required. |
| C23-045 | Size/potential observations ignore payload values. | Branch choices change tree shape, but the following link-potential formula is symmetric in the two child-forest sizes. This permits raw-shape analysis independently of heap validity. |
| C23-046 | Logarithmic AM–GM lemma: `x>0 ∧ y>0 → lg x+lg y+2≤2·lg(x+y)`. | `Lemmas_log.ld_sum_inequality`; derive from `(x-y)²≥0`, `4xy≤(x+y)²`, and monotonic log laws. Existing Mathlib logb laws supply primitives, not the complete heap lemma. |
| C23-047 | If `h₁=Hp x hs₁`, `h₂=Hp y hs₂`, with child sizes `n₁,n₂`, then `φH(link h₁ h₂)=φF hs₁+φF hs₂+lg(n₁+n₂+1)+lg(n₁+n₂+2)`. | The marked `(*)` equation on p.262; holds for both link branches and all payload values, including ties. |
| C23-048 | Insertion amortized bound: `Tinsert x q+φQ(insert x q)−φQ q≤lg(sQ q+1)`. | `A_insert`; Tinsert0. No H/V premise. Empty insertion yields potential0 and right side0. |
| C23-049 | Merge amortized bound: `Tmerge q₁ q₂+φQ(merge q₁ q₂)−φQ q₁−φQ q₂≤2·lg(sQ q₁+sQ q₂+1)`. | `A_merge`; subtract both input potentials. Empty operands are explicit cases; no heap-order premise. |
| C23-050 | Lemma23.2: `φF(pass1 hs)−φF hs≤2·lg(sF hs+1)−length hs+2`. | `ΔΦ_pass1`; all forests, including empty/singleton. The list length is cast to Real before subtraction. |
| C23-051 | For two heads with child sizes n₁,n₂ and suffix size m, exact potential difference is `lg(n₁+n₂+1)−lg(n₂+m+1)+φF(pass1 suffix)−φF suffix`. | This cancellation identity uses first-pass size preservation. It is the calculation connecting the recursive invariant to AM–GM. |
| C23-052 | Correct the AM–GM step in the proof of Lemma23.2. | Its `x+y` is `n₁+n₂+m+2`, not the printed `…+1`. At n₁=n₂=m=0 the printed transition would require2≤0. The companion has the correct +2; retain a checked arithmetic counterexample and the corrected proof step. |
| C23-053 | Lemma23.3: `hs≠[] → φQ(pass2 hs)−φF hs≤lg(sF hs)`. | `ΔΦ_pass2`; nonempty trees ensure `sF hs>0`. The empty case is deliberately excluded from this sharper form. |
| C23-054 | In the nonempty-tail proof, if `pass2 tail=some(Hp y hs₂)`, then `sF tail=sF hs₂+1` and the IH reduces to `φF hs₂−φF tail≤0`. | These are the source's key size cancellation and marked `(**)` inequality; they justify using the symmetric link formula. |
| C23-055 | Corollary23.4: `φQ(pass2 hs)−φF hs≤lg(sF hs+1)` for all hs. | Empty case gives0≤0; nonempty case follows from C23-053 and logarithm monotonicity. |
| C23-056 | Theorem23.1: `φQ(delMin(some h))−φQ(some h)≤2·lg(sF(hps h)+1)−length(hps h)+2`. | `ΔΦ_del_min`. Use pass1 size preservation and C23-055 to cancel the original root's logarithmic charge, then C23-050. No heap-order premise. |
| C23-057 | Final deletion bound: `TdelMin q+φQ(delMin q)−φQ q≤2·lg(sQ q+1)+4`. | `A_del_min`; for a present heap use the exact k+2 pass count with Theorem23.1, and monotonicity from `sQ q` to `sQ q+1`. |
| C23-058 | Empty and singleton boundary cases are explicit. | `TdelMin none=0`; deleting `some(Hp x [])` costs2 under the two-pass tariff, despite returning none. All potentials in both cases are0; logarithm arguments in the final bound are1 or2. |
| C23-059 | Instantiate the shared amortized framework with operation arities0 for empty,1 for insertion/deletion,2 for merge, and the listed upper charges. | Companion `pairing:Amortized` uses invariant `True` because these cost/potential bounds are shape-only. PQ validity remains a separate client invariant for semantic minimum operations. |
| C23-060 | Aggregate actual cost is bounded by summed amortized charges plus initial potential minus final potential, hence the usual nonnegative-potential upper bound. | Use Chapter19's Real-valued, multiple-input operation-history bridge. A unary trajectory theorem only applies when its actual state transition contains both consumed operands. |
| C23-061 | Insertion, merge and deletion have logarithmic amortized upper bounds in the displayed sizes. | Use `log(size+1)` to cover empty cases; merge's size is the combined input size. These are aggregate bounds on a properly accounted operation history, not per-operation worst-case logarithmic bounds. |

## 23.3 Binary representation: pp.262–263

Let `E` be the binary empty tree and `N left value right` a payload node.
The binary tree of a forest represents leftmost child and next sibling.
This is not an ordinary binary min-heap: a node is below its **left**
subtree, while its right subtree consists of siblings and need not be above
that node.

| ID | Source obligation | Exact correspondence |
|---|---|---|
| C23-062 | `trees []=E`; `trees(Hp x children::siblings)=N(trees children)x(trees siblings)`. | The displayed recursion must be preserved. Define whole-heap encoding `none↦E`, `some(Hp x children)↦N(trees children)x E`. |
| C23-063 | Every binary tree decodes to a unique forest of nonempty rose trees. | Prove mutually inverse encode/decode or an equivalent constructor-preserving representation theorem. The forest encoding needs no extra shape invariant. |
| C23-064 | Whole optional heaps correspond exactly to binary trees satisfying `isRoot E=True`, `isRoot(N l x r)↔r=E`. | A right sibling at the top denotes another heap in a forest, not part of the one-root optional carrier. Batteries `NoSibling` matches this condition. |
| C23-065 | `numNodes(trees hs)=sF hs`, and the whole-heap version equals sQ. | Gives the book's alternative definition of sizes and derives both forest recursion equations. |
| C23-066 | Binary payload multiset equals the corresponding forest/heap multiset. | Preserve multiplicity and prove the nested forest sum relation, not merely set equality. |
| C23-067 | Binary potential `φ E=0`, `φ(N l x r)=φ l+φ r+lg(numNodes(N l x r))` agrees with φF and φQ under the encodings. | This derives all overloaded source potential definitions from one structural recurrence. No log0 occurs at a node. |
| C23-068 | Source H/V corresponds to binary `pheap`: every payload in the left subtree is ≥ the root and both left/right subtrees recursively satisfy pheap, together with `isRoot` for a whole heap. | Right-sibling labels are not constrained by their left neighbour. Avoid substituting the ordinary binary heap property on both subtrees. |
| C23-069 | Preserve the two passes, link and public operations through the encoding, if the binary implementation is used. | The binary companion's `link` acts on two adjacent roots inside one forest; merge packages its two whole roots before linking. A value bridge must account for this arity change and strict tie rule. |
| C23-070 | Transfer sizes/potentials and corresponding measured pass counts through the representation, with explicit `NoSibling`/isRoot premises on whole-heap operations. | Equality of encodings alone does not prove arbitrary implementation costs. The companion tree theory's raw totalization discards malformed top siblings in deletion/merge. |
| C23-071 | Keep the binary whole-heap domain visible. | For `N E 0 (N E 1 E)`, raw binary deletion drops the top sibling as well as root; it is not multiset removal of0 from the encoded two-tree forest. The whole-heap invariant rules this out, and the counterexample prevents an unrestricted adapter claim. |
| C23-072 | Clarify the relation to the splay potential. | Both sum logarithms over binary subtrees, but this chapter uses the node count itself at each nonempty subtree. Any splay potential using a size offset needs an explicit equation/inequality rather than being renamed identically. |

## Cited mathematical improvement and cost-domain boundaries

The p.263 statement that later analyses improve the preceding logarithmic
amortized charges is mathematical and remains a coverage obligation. A
concrete sufficient witness is constant amortized insertion/meld while
retaining logarithmic deletion for the same two-pass pairing strategy.
This does not require adding the cited papers' separate decrease-key API.

Primary recovery reference: John Iacono, *Improved Upper Bounds for Pairing
Heaps*, author version <https://arxiv.org/abs/1110.4428v3>, January22,2014,
with preliminary SWAT2000 version cited by the book. PDF
<https://arxiv.org/pdf/1110.4428v3>, 367,579 bytes, SHA-256
`14d9d9481ce33defb74e60885b854c147d3fc2e5acef439b464b651c42157eb3`.
The arXiv license is nonexclusive distribution, not a BSD source license;
this reading copy is not a deliverable to redistribute as project source.

| ID | Required result or boundary | Precise scope |
|---|---|---|
| C23-073 | Formalize a genuine improved aggregate bound: constant amortized insertion and merge, logarithmic deletion, under a coherent common charging proof. | Preserve the book's asserted improvement rather than relabel it as historical discussion. It is a separate theorem from the explicit φQ bounds above; a different potential/aggregate argument is required. |
| C23-074 | Relate that improvement to the actual operation model used by the cited proof. | Iacono §3 concerns finite histories from an initially empty collection, consuming both meld inputs; its actual charge is number of pairings+1. Preserve the initial-state, ownership/history and tariff bridges to the functional two-pass implementation. Do not combine amortized charges from different analyses without a joint proof. |
| C23-075 | Handle possible dependence of the improved proof's potential on the whole history. | The cited analysis colors occurrences according to whether they survive the final history and allows intermediate negative total potential, using a nonnegative final-minus-initial condition. A nonnegative state-only φQ theorem is not the same argument. |
| C23-076 | Prove a cost bridge before transferring the improved bound. | For a present root with k children, pairing count is `max(k-1,0)` and the cited call tariff is that count+1; the book's two-pass count is k+2 and is at most the cited charge+2. Empty deletion and nonrecursive operations require separate cases. |
| C23-077 | Persistent reuse must not spend one potential contribution multiple times. | Operation trees may count repeated input occurrences separately, or a live-heap state may consume/update both operands. Repeatedly applying deletion to the same retained high-degree heap is not a single successive-state execution and does not inherit the unary telescope bound for free. |
| C23-078 | Keep library shape/tie and resource substitutions checkable. | Formalize the two-root equal-key witness above, prove whichever comparator/encoding adapter is chosen, and retain the source-vs-fused cost distinction. No Batteries documentation assertion closes the missing source potential proof. |

The improvement reference contains a proof-estimate gap worth preserving:
its §3.5 lists a rank-potential upper bound `42 lg(a+b)` and a heap-potential
drop of at least `36 lg(a+b)+8`; those displayed estimates with the other
listed terms do not by themselves imply its concluding nonpositive meld
charge. A tighter estimate must be proved rather than copied blindly. For
positive integer a,b, the elementary inequality `a+b-1≤ab` is the natural
route when expanding the two-root rank difference. This is a gap in the
printed calculation, not a claim that the improved theorem is false.

The empirical claim about outperforming Fibonacci heaps concerns the cited
Larkin–Sen–Tarjan2014 experimental study. It is not a universal mathematical
ordering of the two algorithms' times on all hardware/workloads. The book's
report of an open final analysis is edition-relative context, not an
instruction to solve an open problem or prove an impossibility theorem.

## Source defects and acceptance handoff

| Location | Evidence and required disposition |
|---|---|
| p.261, Lemma23.2 proof | PDF visibly uses `n₁+n₂+m+1` in the AM–GM step; `Pairing_Heap_List2_Analysis` uses +2. Two singleton heads give the printed intermediate transition2≤0. Correct the step, retain the counterexample, and prove the stated lemma unchanged. |
| Binary companion `mset_del_min` | Its nonempty side condition is written with unrelated variable `t≠Leaf`, while the deleted heap is `h`. Under `is_root h`, the multiset formula also holds for empty h because subtracting from the empty multiset is empty, so this is a redundant/misnamed source premise, not a hidden false theorem. State the intentional whole-heap theorem directly. |
| Potential comparison to splay trees | Similar shape does not establish identity with a size-offset potential. Preserve the explicit log-of-node-count definition. |
| Improved-analysis reference | Retain the §3.5 estimate gap and discharge a correct stronger bound in any formal reuse. No source axiom/admission is permitted to bridge it. |

Implementation should reuse generic carriers, exact priority interfaces,
measured erasure and the Chapter19 multiple-input Real potential framework.
Place algorithm-specific strict-link/pass equations and logarithmic lemmas
with the pairing realization. Exercise23.1 needs both whole-value equality
and the measured inequality/allocation distinction. The source and fused
variants may share clients only through those checked correspondences.

A complete chapter requires the source theorems and numerical constants,
all exercise parts, the binary representation correspondence, the cited
mathematical improvement with an explicit cost/history domain, and checked
source-error witnesses. It still requires both project review axes on the
same immutable candidate and applicable validation. This inventory grants
none of those implementation or acceptance milestones.
