# Ordinary list merge: bounded source preflight for proposed FDSA-XM01

Prepared 2026-11-02. **Source preparation only; no scope freeze, Lean
implementation, compiler result, final review, chapter activation or acceptance.**
Chapter 1 remains the prerequisite, with the coordinator's unchanged attempt-2
gate active. All chapter obligations and shared drafts remain unaccepted. The
sole output of this task is this report; all previous records remain unchanged.

## 1. Recommendation and evidence boundary

A small measured counterpart of the existing ordinary list merge has genuine
reuse in Chapter 2 and the chosen Chapter 14 exercise solutions. Keep the value
interface `List.merge` / `Applications.Sorting.mergeBy`, the existing source
adapter, ordinary lists and `Resources.Measured`. Do not create a general merge
framework or identify binomial forest merge with ordinary list merge.

The Chapter 2 algorithm and its comparison counter are prescribed. Chapter 14
Exercises 14.1 and 14.3 leave their implementations open: the sorted-list queue
and root-plus-merge enumeration described below are documented choices that
answer those exercises. The present shared unit can expose their common merge
component without implementing either complete exercise or activating Chapter 14.

This report reuses both complete retained readiness reports,
`mergesort-cost-readiness.md` and `mergesort-value-api-readiness.md`, alongside
the earlier mergesort plan/reuse plan and the relevant current inventory rows.
Their whole-sort reasoning is not redrafted here. The frozen Chapter 2
requirements still identify their historical 107-row snapshot; the current
inventory has 112 rows under `scope-reconciliation.md`. This proposed component
does not remove C02-108–112 or any original obligation. The companion
`ordinary-merge-api-preflight.md` owns the detailed current API/design search.

### Primary source identities

All paths below are relative to `/workspace/scratch/845aa1048b05`.
These are existing local reading copies; no remote source was retrieved.

| Source and exact relevant location | Version and SHA-256 |
| --- | --- |
| `book-source/functional_data_structures_algorithms.pdf`: Chapter 2 §2.4, printed pp. 17–18 / PDF pp. 23–24; §2.5–2.6 and Exercises 2.5–2.7 are downstream clients. Chapter 14 Exercises 14.1/14.3, printed pp. 180/181 / PDF pp. 186/187. | Official [FDSA PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf), version July 27, 2026; `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| `book-source/chapter02.txt`, lines 129–187: literal merge, content/order statements and handwritten comparison counter. `chapter14.txt`, lines 42–44 and 84–87: the two open-ended exercises. | Chapter 2 extraction `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`; Chapter 14 extraction `b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a`. These are locating aids for the pinned PDF. |
| `book-source/Sorting.thy`, lines 79–82, 94–95, 121–128, 147–155, 168–169: merge; multiset/set preservation; sortedness iff; comparison recurrence/bound; length. | Isabelle mirror `f86f290225eebcc52c1ae7dba2e098f405f51c21`, `src/HOL/Data_Structures/Sorting.thy`; `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. Author Tobias Nipkow. |
| `book-source/Heaps.thy`, lines 13–49 and 57–96: abstract heap/merge interpretations. It does not provide the two exercise implementations. | Same Isabelle revision, `src/HOL/Data_Structures/Heaps.thy`; `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`. Author Tobias Nipkow. |
| `book-source/Binomial_Heap.thy`, lines 167–175 and 480–524; Appendix B.7, printed p. 351, `appendix-b.txt:119–134`: excluded carry recurrence and its different tariff. | Same Isabelle revision, `src/HOL/Data_Structures/Binomial_Heap.thy`; `821d4236fb294b3b73b9c119a40f36225d3f16d4030b805c045da39dcf63210a`. Appendix B extraction `f809cfd567c764cf8a2f3660774617e1a43f7089f2d42e7874e6e1936bef1929`. |
| `book-source/LeanListSort-Basic.lean`, lines 18–47: verification-oriented ordinary recurrence; `LeanListSort-Lemmas.lean`, lines 149–195, 218–273: equations, length, membership, forward pairwise order and permutation. | Lean 4.35.0, revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, `src/Init/Data/List/Sort/{Basic,Lemmas}.lean`; hashes `a100c2a753aae0dda38a6e3afaca64f7ea70f4eba73d007ac29b5889fbf842ac` and `e04f8070b20080cdbcdd31a6d240e267363e308a5804fdaf6749c92a885547c0`. |
| `book-source/LeanListSort-Impl.lean`: runtime replacements, including `mergeTR`; relevant only to the value-versus-runtime boundary. | Same Lean revision, `src/Init/Data/List/Sort/Impl.lean`; `6db1a2a95fa6db3bebcd4197749fe3b5d21e3f80323e18e9047525264bcd3923`. |

The immutable Isabelle raw URL is
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`
followed by the table's path. The companion revision postdates the manuscript;
it is not claimed to be the PDF's build revision. The corresponding equations
were compared directly. The AFP natural-mergesort archive is not the provenance
of this ordinary merge definition or its `C_merge` counter.

`book-source/ISABELLE-COPYRIGHT`, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`,
contains the applicable BSD-3-Clause notice: copyright 1986–2026 University of
Cambridge, Technische Universitaet Muenchen and contributors. Any translated
source must retain the applicable attribution, conditions and disclaimer in
the project documentation/distribution. The Lean list sources identify Lean
FRO / Kim Morrison and Apache 2.0; imported dependencies retain their own
notices. The book remains a reference input, not a manuscript to redistribute.

### Inspected conaled source identities

These files were read in `conaled-ch01-cost-models`; the hashes identify actual
read bytes without inspecting or changing Git. They are source evidence, not
new validation or acceptance evidence.

| File under that checkout | Relevant declarations | SHA-256 |
| --- | --- | --- |
| `Applications/Sorting/Merge.lean` | `mergeBy`, `mergeBy_perm`, `merge_sorted_compatible_on`, `mergeBy_sorted`, `mergeBy_filter`, `mergeBy_stable`, `mergeBy_spec` | `79b35252d0f551b381ef63974497311336ea92a5d118691647825cade12a1338` |
| `Applications/Sorting/SourceMerge.lean` | Literal `sourceMerge`, its length-sum termination, `sourceMerge_eq_merge`, `mergeBy_source` | `bebd8eb2f06d92cc10e6f319c96b7965cdee36ff14c4a8b0b19e1351e8ebeaf2` |
| `Applications/Search/LeftistQueue.lean` | `mergeOn`/`toListQ` at 165–180; `mergeOn_sorted`, `toListQ_perm`, `toListQ_sorted` at 303–332 | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| `Applications/Resources/Measured.lean` | Existing value/observation pair, `bind`, `reweight`, erasure and additive transport | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | Explicit post-body invocation charge and actual argument/branch sequencing | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| `Applications/Resources/CallComparison.lean` | `add_entry_le` at 95 and `zero_cost_entry_matters` at 121: positive-cost and zero-cost boundaries for adding one entry | `8d6d9324aa9dc71ceeaeaa04073f0f2a4f721a309995f0b623650bb19f01b520` |

The retained cost/value readiness reports have respective hashes
`e36333a7e913fe0b11a1950f23c10a5fcb5975f37adb8c8d5405db2fe61a09a5`
and `8abaea795ad882785308d32b2187de32ee5398e036a07828a4f42f16f2da97ba`.
The Mathlib pin for the companion API search is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## 2. Exact eligible execution and distinct observations

For an arbitrary `cmp : α → α → Bool`, let `M` be the ordinary recurrence:

```text
M [] ys = ys
M xs [] = xs
M (x::xs) (y::ys) =
  if cmp x y then x :: M xs (y::ys)
             else y :: M (x::xs) ys.
```

Every nonterminal branch removes exactly one input head. The sum of input
lengths decreases, with no sortedness, comparator law, payload equality,
finiteness or inhabitant assumption. This is the pinned `List.merge`
recurrence. The source specializes `cmp x y` to `decide (x ≤ y)`; keyed reuse
uses `decide (key x ≤ key y)`, ordering keys rather than records. On equal
keys the source selects the left head, without suppressing either occurrence.

The source observation `CM` has zero empty-side bases and adds exactly one at
each nonempty/nonempty step, following the same selected recursive arguments.
It counts comparator invocations, not the implementation cost of an arbitrary
user-supplied comparator. `Sorting.thy:147–155` explicitly introduces this as
an element-comparison count. It is handwritten, **not** a generated
`time_fun merge` theorem. Constructor work, list traversal outside merge,
function entry and the terminal base case contribute no extra `CM` charge.

A separate declared observation `IM` counts each invocation of this recursive
merge, including its initial and terminal invocations. Its empty-side bases
are one, and a nonempty step adds one to the chosen recursive result. Thus,
for every comparator and both lists, including two empty lists,

```text
IM cmp xs ys = CM cmp xs ys + 1
CM cmp xs ys ≤ xs.length + ys.length
IM cmp xs ys ≤ xs.length + ys.length + 1.
```

The latter is a derived, deliberately loose bound. No tightness claim is
needed. There is exactly one terminal call, because the operation follows
one recursive branch at a time. This is why the additive one is exact.

For **both inputs nonempty**, the first comparison gives `1 ≤ CM`, so
`CM ≤ IM ≤ 2*CM`. This is a direct connected use of the existing Chapter 1
`Resources.CallCount.add_entry_le`. If either input is empty, `CM=0` and
`IM=1`; for every natural coefficient `K`, `IM ≤ K*CM` is false, exactly the
boundary recorded by `zero_cost_entry_matters`. Thus the positive-domain
multiplicative comparison must not be promoted to a uniform claim over all
inputs. This relates two declared observations; it does not reclassify the
book's comparison tariff as a recursive-call tariff.

A single actual execution with observation `(comparisons, invocations)` can
record `(0,1)` at either empty-side base and add `(1,1)` in the selected
nonempty branch. Its returned list must be constructed from that branch's
actual returned list. The first projection then witnesses the source `CM`,
and the second witnesses the separately declared `IM`; neither should be
attached to an independently chosen output without recurrence/erasure proof.
Existing product observations and `Measured` transport suffice. A separately
chosen scalar weighting is only an explicit additive reweighting; it does
not turn one tariff into the book's unspecified machine runtime.

The standard source says that `List.merge` is replaced at runtime by an
equivalent tail-recursive implementation. Its value equality does not identify
runtime calls, allocations, stack usage or timings with either observation.
XM01 needs no compiler-normalization or runtime-cost claim.

## 3. Source/claim table suitable for a later bounded scope

These are proposed claim handles, not frozen requirements or acceptance rows.
The direct Chapter 2 support is only C02-025, C02-027's merge portion,
C02-028/029/031/033/035/037. Other IDs below identify downstream consumers,
not additional coverage closures; all Chapter 14 obligations remain queued.

| Handle | Exact source requirement or shared claim | Existing reuse / bounded new work |
| --- | --- | --- |
| M1 | C02-025 and the merge portion of C02-027: the two bases, selected-head recurrence, left ties and termination. | Preserve `List.merge`, `sourceMerge_eq_merge` and `mergeBy_source`; connect the actual measured recurrence to them. Do not create a second public pure merge hierarchy. |
| M2 | C02-028/029/035, equations (2.10), (2.11), (2.13): output occurrence multiset is the sum; support is the union; length is the sum. | Reuse `merge_perm_append` / `mergeBy_perm`, `mem_merge`, `length_merge`, and ordinary permutation-to-multiset bridges. These need no order laws or decidable payload equality. |
| M3 | C02-031, equation (2.12): source merge is sorted iff both input lists are sorted. | Reuse existing forward sortedness; supply the output-to-input implication through order-free left/right sublists and existing `Pairwise.sublist`. Preserve the arbitrary-relation direction as described below. |
| M4 | C02-033/037, equation (2.15): actual source comparison recurrence and upper bound. | First observation of the branch-sensitive execution, exact source specialization, then the length-sum bound; no sortedness or distinctness premise. |
| M5 | Separate reusable invocation model: terminal call included and `IM=CM+1`. | Second observation of the same execution; prove the exact relation and derived bound, with the existing positive-cost comparison and empty-side counterexample as connected consequences. Label this as the declared invocation model, not a newly recovered printed `T_merge` for Sorting. |
| M6 | Keyed left ties / reusable ingredient of C02-107. | Use the actual key comparator and existing `mergeBy_filter`/`mergeBy_stable`/`mergeBy_spec` on sorted blocks. This does not complete the exercise's chosen whole sorter. |
| M7 | Chosen C14-033 enumeration body: prepend a node entry to the ordinary merge of its two child enumerations. | Connect one measured merge to the actual existing `toListQ` node equation for arbitrary raw nodes; expose only the merge's cost. C14-014 sorted-list queue is a further downstream client, not a new queue implementation here. |
| M8 | Meaningful boundary/consumer examples. | Actual full returned lists and both counts for the cases below, reusing the generic declarations. No new recursion, sort, heap or ADT framework is justified. |

### Sublist and sortedness converse: precise gap and assumptions

The complete retained value-readiness search found no exported each-input
sublist theorem for `List.merge` in the inspected pinned sort/list modules.
The present direct reread confirms that `List.pairwise_merge` (saved
`LeanListSort-Lemmas.lean:218`) is forward-only; the existing project merge
module is also forward-only. `sublist_mergeSort` and `pair_sublist_mergeSort`
at lines 461/490 concern a whole sort, not either operand of one merge.
The complementary current search also reports no matching input-sublist
declaration in the pinned Lean List Sort, Mathlib Data.List, Batteries
Data.List and local Sorting modules. This remains a scoped API-gap statement,
not a claim to have proved absence from every imported or archived file;
the companion API report records the detailed search. It confirms the
current constructors are `Sublist.cons_cons` and `Sublist.cons`, with
`Sublist.cons₂` deprecated at this pin.

The genuinely small missing observations are

```text
xs <+ List.merge xs ys cmp
ys <+ List.merge xs ys cmp
Pairwise R (List.merge xs ys cmp) → Pairwise R xs ∧ Pairwise R ys.
```

They hold for arbitrary `cmp`, arbitrary relation `R`, and arbitrary payload
universe. Each chosen-head branch preserves both input orders; the two
sublist constructors supply the induction. `List.Pairwise.sublist` already
exists (`book-source/LeanList-Pairwise.lean:47`), so a second pairwise theory
is unnecessary. Permutation or support alone would not establish this
ordered-occurrence implication.

Combining that implication with `mergeBy_sorted` yields the source keyed
iff under the existing linear-preorder/decidable-comparison assumptions;
the identity key gives the book's linear-order statement. The implication
from output to inputs needs none of those order assumptions. For forward
sortedness with an arbitrary comparator, retain the existing weaker
`merge_sorted_compatible_on` premise on actual cross-input members.

Stability is separate. Compatibility sufficient for sortedness does not
force left ties; a constant-false comparator on equal-key records can choose
the right record first. Existing key-filter stability assumes sorted input
blocks and the actual key comparator; its key equality decision belongs to
that filter contract, not to the raw operation, sublists, costs or payloads.
No claim of stable merging of arbitrary unsorted blocks is intended.

## 4. Exact Chapter 14 opportunity and its limit

Exercise 14.1, p. 180, requests a list-based mergeable queue with constant-time
minimum access/deletion and all ADT laws. Choosing sorted lists makes ordinary
merge an appropriate operation; head/optional-head and tail supply the intended
structural access. That is still a concrete representation and invariant proof
to build. Neither the current `exactList` implementation, which sorts during
removal, nor a generic occurrence contract discharges this exercise's costs.
The exercise does not prescribe an exact merge tariff.

Exercise 14.3, p. 181, requests a sorted list of a heap's occurrences and an
at-most-quadratic bound, with constants allowed. A chosen root-plus-merge
algorithm already has an actual conaled body:

```text
LeftistQueue.toListQ null = []
LeftistQueue.toListQ (PQ.fork k x p l r) =
  (x,p) :: LeftistQueue.mergeOn Prod.snd (toListQ l) (toListQ r).
```

`mergeOn` is the same `List.merge` by priority. A measured ordinary merge of
those **already obtained child lists**, followed by an uncharged cons, has
this body's value for every raw `k,x,p,l,r`. Cached-rank validity and heap
order are not needed for that equation. Its cost is only the executed merge;
the child `toListQ` computations have not thereby been instrumented or made
free in a complete cost theorem. Keep this body observation explicit.

The existing `toListQ_perm` is unconditional content evidence;
`toListQ_sorted` needs `Heap`, not `Ranked`. Completing the book exercise
still requires an ordinary node-labelled tree/carrier observation bridge,
the actual whole recursion and its value/cost correspondence. The retained
Chapter 14 plan's separate invocation recurrence is

```text
T(E)=1
T(N l a r)=T(l)+T(r)+IM(list l,list r)+1.
```

The proposed merge bound supplies only its local `IM` estimate. Whole-tree
induction, enumeration length/node-count correspondence and the resulting
quadratic bound remain downstream; they do not follow from one node body's
cost. This interpretation also distinguishes root construction/cons from
counting a whole enumeration entry. No complete Exercise 14.3 proof is
included in the proposed minimal shared scope.

## 5. Independent small cases for connected examples

The following are hand calculations from the actual recurrence, not a new
enumeration campaign or checked Lean results. Each should consume the eventual
public execution/observation theorem rather than merely compute an unrelated
number. Costs are ordered `(CM,IM)`.

| Inputs / actual observation | Expected value and counts | Boundary exercised |
| --- | --- | --- |
| `[]`, `[]`, with any comparator; also instantiate payload `Empty`. | `[]`, `(0,1)` | The initial base invocation exists even when there are no elements or inhabitants. |
| `[]`, `[3,1]`, and the reversed operand order. | `[3,1]`, `(0,1)` in both cases. | An arbitrary unsorted remainder is returned without any comparator call or traversal charge in these models. |
| Constant-true comparator, left `[2,0]`, right `[1,3]`. | `[2,0,1,3]`, `(2,3)` | Both input sublists and occurrence preservation hold without comparator/order laws; numerical sortedness does not. The generic theorem should quantify over every Boolean comparator. |
| Natural `≤`, left `[1,3]`, right `[2,4]`. | `[1,2,3,4]`, `(3,4)` | Both selected-head branches are executed before the one terminal call. |
| Key `Prod.fst`; left `[(1,10),(1,11)]`, right `[(1,20)]`. | `[(1,10),(1,11),(1,20)]`, `(2,3)` | Full record order and left-tie stability, with duplicates preserved. |
| Swap the preceding operands. | `[(1,20),(1,10),(1,11)]`, `(1,2)` | Same key multiset and identical untagged keys do not determine comparisons or full record order. No merge commutativity/cost-symmetry claim. |
| Raw `PQ.fork 99 () 9 l r`, where `l=PQ.fork 0 () 1 null null`, `r=PQ.fork 0 () 2 null null`; measure only the merge in its actual `toListQ` body. | Full body list `[((),9),((),1),((),2)]`; merge-only count `(1,2)`. | Rank caches are malformed and heap order is false. The body value bridge still applies; the list is not sorted. This must not be relabelled as the entire tree's cost. |

The tagged example also supplies a concrete stability consumer of the
existing merge contract. An arbitrary relation `R` in the sublist/converse
theorem must remain independent of the supplied comparator; forward sorting
needs its separate compatibility law.

## 6. Downstream obligations remain mandatory

The shared component does not implement the floor-left sorter, its strict
recursive-size decrease, source recurrence, permutation/stability, comparison
composition on actual sorted halves, all-length ceiling-log bound, printed
power-of-two theorem or real-log/asymptotic bridge. These remain in the complete
Chapter 2 plans. The standard ceil-left sort's value agreement cannot transfer
source costs. Bottom-up/natural passes, their actual run ordering and costs,
scanner/builders, alternating splitting and tail variants likewise retain
their original obligations. In particular, one merge's left ties do not prove
whole-sort stability after an algorithm changes the order of runs.

The complete sorted-list queue realization, direct constant-time access and
deletion, all source queue/merge laws, full heap-to-list traversal and its
quadratic theorem remain Chapter 14 work. The current XH01 observation/merge
draft is not a prerequisite for ordinary list merge and is not a substitute
for either concrete exercise.

Binomial merge remains separate. On equal ranks it consumes both heads,
merges both tails, then carries their linked tree through that actual result.
It changes the multiset of forest trees while preserving their payload
multiset. Two rank-zero singleton forests produce one rank-one tree, whereas
ordinary rank-list merge leaves two rank-zero entries. Under Appendix B.7's
tariff the binomial example costs three (outer merge, empty tail merge,
empty insertion), versus ordinary `CM=1`, `IM=2`. Its coupled work/output-length
lemmas, zero-cost `link`/`rank` convention, invariant preservation and
logarithmic forest-size conversion are not specializations of XM01.

No new false printed claim was found in this bounded source question. The
essential qualifications are prescribed versus chosen algorithms, occurrence
order versus set/multiset observations, comparisons versus invocations,
one-body versus whole-recursion work, and value equality versus runtime cost.
They require precise bridges, not a new general translator or mandatory
auxiliary framework. All original obligations outside this component remain
in their existing chapters and acceptance records.

Only this report was written. No repository source, prior report, requirement,
ticket, reference, cache or gate was changed. No compiler, Lake, project checker,
project hash helper, Git operation, remote request or acceptance action ran.
Ordinary file hashes above identify the inspected local bytes.
