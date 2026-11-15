# Ordered insertion observations — bounded source readiness

Date: 2026-11-03 UTC. Ticket: `FDSA-XI01`.

**Status: report-only preparation. No new source unit, implementation scope,
base, chapter activation, validation result or acceptance is selected here.**
Chapter 1 remains the sequential prerequisite. Its third attempt is the sole
authorized gate; this task neither observes nor controls that process. The
initial Chapter 2 integration prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

## 1. Disposition

The remaining observations in C02-009 and C02-094–098 are small statements
about the **existing** `List.orderedInsert` and `Sorting.insertionOn` operations.
Their essential ingredients are already in pinned Mathlib and conaled. The
negative and positive filtering equalities and the assembled sortedness iff
are not exported by the inspected conaled sorting modules. They remain
required source statements even though conaled proves the final stable-sort
contract by a different argument.

Ordinary insertion itself has genuine later consumers: Chapter 26 literally
inserts by cached tree weight, and the selected sorted-list implementation of
Chapter 14 Exercise 14.1 can use it. These inspected consumers need existing
length, permutation, mapping and forward-sortedness results. They do **not**
establish an additional consumer of the still-missing general filter equalities
or sortedness converse. Chapter 3 already justifies the separate X002 shared
insertion-sort cost draft; that does not newly justify XI01.

**Recommendation:** retain the thin missing observations as Chapter 2 work,
to be implemented when that chapter is active. Do not create another insertion
executor, carrier, cost model or generic framework. A later contrary decision
would need an actual additional consumer of the proposed new statements, not
merely another occurrence of the insertion recurrence. This conclusion does
not remove any source helper, source algorithm, exercise or cost obligation.

## 2. Reading boundary, identities and licensing

The complete XI01 ticket was read first. The complete 346-line reuse plan and
391-line current Chapter 2 inventory were read, as were the actual existing
sorting `Sort.lean`/`Stable.lean` modules and both X002 Lean files. Primary reads stayed within the
ordinary/keyed insertion and stability sections and the narrowly relevant later
consumer passages. The detailed API and independent-case reports are separate
preparation; this report does not claim their completion or final approval.

The reuse plan still opens with its historical **107**-obligation count.
The current inventory has **112** IDs. The frozen Chapter 2 requirements
intentionally retain the earlier 107-row snapshot; `scope-reconciliation.md`
explicitly preserves C02-001–107 and unpacks the already-required C02-088 into
C02-108–112. None of those files or requirements changes here. The six ID
groups examined below are unchanged by that reconciliation.

| Retained input | Identity and relevant location |
|---|---|
| Official book | July 27, 2026 PDF, <https://fdsa-book.net/functional_data_structures_algorithms.pdf>; `book-source/functional_data_structures_algorithms.pdf`, 1,742,029 bytes, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Chapter 2 ordinary insertion: printed pp.13–15; keyed insertion/stability: pp.26–27. |
| Chapter 2 reading copy | `book-source/chapter02.txt`, 28,337 bytes, SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`; lines 1–99 and 440–507. Extracted comparison glyphs are resolved against the formal theory, rather than guessed from text-extraction control characters. |
| Isabelle sorting companion | `book-source/Sorting.thy`, 14,846 bytes/435 lines, SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`; [pinned source](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy). Ordinary insertion and claims: lines 19–44; generated timing declarations/bounds: 49–74; keyed operations/helpers/stability: 346–405. |
| Huffman companion | <https://isa-afp.org/release/afp-Huffman-2026-10-26.tar.gz>, 549,876 bytes, SHA-256 `229ba4f3037d9f02dff7df8836d8a5a95f91c8463c8572cb0ae1a93dea2bfd77`. Main file `book-source/afp-Huffman-2026-10-26/Huffman/Huffman.thy`, 101,517 bytes/2,363 lines, SHA-256 `7bdc838bbdf7347fb78440a5b3c8dadaf6b7c228e6e3cae6f2d1fb49582837bf`. Relevant ranges: 828–873, 1723–1750 and 2052–2076. |
| Pinned list API | Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Data/List/Sort.lean`; inspected local file SHA-256 `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9`. This file owns `List.orderedInsert` and `List.insertionSort`; they are not a newly reconstructed executor. |

The Isabelle mirror revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It and the dated AFP archive
postdate the manuscript. They pin the inspected formal sources, **not an
asserted generating revision of the July PDF**. No source retrieval or new
paper campaign was performed.

`Sorting.thy` credits Tobias Nipkow; the book chapter credits Tobias Nipkow
and Christian Sternagel. Its applicable Isabelle BSD notice is retained at
`book-source/ISABELLE-COPYRIGHT` (1,673 bytes; SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`).
The Huffman theory credits Jasmin Christian Blanchette, 2008. Its applicable
AFP BSD notice is `book-source/AFP-LICENSE` (1,842 bytes; SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`),
corresponding to <https://isa-afp.org/LICENSE>. Any later source adaptation
must retain the applicable attribution and full notice. Mathlib's inspected
file carries its Apache-2.0 header and author credits. This original report
does not redistribute the whole manuscript or extracted chapters.

## 3. Exact operation and source claims

Write `I r x xs` for the **existing** `List.orderedInsert r x xs`, using a
decidable relation `r`. This notation in the report introduces no Lean
definition. Its actual recurrence, Mathlib `Sort.lean` lines 43–58, is:

```
I r x []       = [x]
I r x (y::ys)  = if r x y then x::y::ys else y::I r x ys
```

The book's ordinary operation specializes `r` to non-strict `≤` on a linear
order. Its keyed operation specializes `r a b` to `key a ≤ key b`, with a
linear order on keys and arbitrary payloads. Equality goes to the immediate
branch. Every old occurrence remains, and the new occurrence precedes an
existing equal-key head. The source sort recursively sorts the tail and
inserts the original head; Mathlib's right fold has these same nil/cons
equations (`Sort.lean` lines 61–66). Stable sorting refers to the order in
the original input list, not to an unspecified queue-arrival convention.

Both list operations are total, including empty input. They need no default
payload or `Inhabited` instance. A statement about inserting `x : Empty` has
no inhabitant to supply; sorting `List Empty` still has its genuine empty case.
Keys can identify different payloads. Neither insertion correctness nor
filter preservation requires injective keys or an order/equality decision
on payloads.

| Original ID and source | Exact mandatory observation | Existing reuse and remaining source connection |
|---|---|---|
| C02-009, (2.4), p.15; `sorted_insort1`, theory 40–41 | `sorted (insort1 a xs) ↔ sorted xs`, with no sorted-input assumption on the iff itself. | Forward direction is `List.Pairwise.orderedInsert`; converse uses `List.sublist_orderedInsert` and inheritance of pairwise order. Assemble the source iff, rather than replacing it by only forward preservation. |
| C02-094, (2.35), pp.26–27; theory 357–371 | Whole keyed sort preserves the full-record multiset and sorts mapped keys. Supporting one-element statements preserve one occurrence/set membership and give the keyed sortedness iff. | `insertionOn_spec` supplies the whole-sort contract. `perm_orderedInsert`, `mem_orderedInsert`, the ordinary iff and the pairwise-map correspondence supply the supporting claims. The supporting claims are explicitly retained by the current inventory. |
| C02-095, (2.36), p.27; `insort1_is_Cons`, theory 376–377 | If every old key is at least `key a`, insertion returns exactly `a::xs`. | Nil/cons cases and `orderedInsert_cons_of_le` suffice. The displayed all-members premise is retained even though the nonempty operation only tests its head. |
| C02-096, (2.37), p.27; theory 379–381 | If `¬P x`, `filter P (I r x xs) = filter P xs`. | A thin exact list equality is missing from the inspected conaled exports. No sortedness or order law is needed. Filtering retains the full old subsequence in its original order. |
| C02-097, (2.38), p.27; theory 383–385 | If `xs` has sorted keys and `P x`, `filter P (I r x xs) = I r x (filter P xs)`, for the same keyed insertion relation. | The sorted-input premise is substantive. A generic transitive-relation proof is possible; the book's linear-key instance remains the required specialization. This is a different equality from C02-096. |
| C02-098, Lemma 2.11, p.27; `sort_key_stable`, theory 387–405 | Filtering the sorted output by any one key gives exactly the corresponding filtered original list. | `(Sorting.insertionOn_spec key xs).stable k` has the exact observation after the recurrence/key bridge. Its existing proof is reusable; it does not waive C02-095–097. |

These displayed helpers are statements in §2.8, not numbered exercises.
Exercises 2.1 and 2.2, all other Chapter 2 algorithms/exercises and the
reconciled natural-run claims remain in their original scope.

## 4. Hypotheses that must remain visible

For the general relation reading, `r : α → α → Prop` needs `DecidableRel r`
to execute insertion. Filtering can use a Bool predicate, as the Lean list
API does, or a proposition with an explicit decision. Arbitrary filtering
does not require `DecidableEq α` or `DecidableEq` on keys. The existing
equal-key `Stable` contract separately uses a decision for key equality.

**Sortedness iff.** Every old list is an actual sublist of its insertion
result, for arbitrary `r`. Thus output pairwise order implies input
pairwise order, even for an independently specified observation relation.
The canonical forward theorem has `[Std.Total r] [IsTrans α r]`; it needs
neither antisymmetry nor a payload linear order. Those hypotheses suffice
for the source's `≤` specialization. Do not generalize the forward direction
to an arbitrary decision procedure merely because the converse is law-free.

**Immediate cons.** On `y::ys`, only `r x y` is evaluated. The all-members
premise in (2.36) implies that head fact and also handles the empty case.
It is sufficient, not necessary: inserting `2` into `[2,0]` under Nat `≤`
returns `[2,2,0]` immediately, although `2 ≤ 0` fails. Sortedness of the
old list is not needed for this observation.

**Negative filtering.** If the inserted value does not pass the predicate,
the old list's filtered value is unchanged on every branch, including an
unsorted old list. The theorem is an equality of lists with multiplicities
and payloads, not only a set or permutation assertion.

**Positive filtering.** A useful generic theorem needs `xs.Pairwise r`,
`IsTrans α r`, and a passing inserted value. Totality is not needed for
this helper. The delicate branch is an insertion that stops at a head later
discarded by the filter. Pairwise order relates that head to each retained
tail element; transitivity then makes insertion stop before the filtered
tail too. These are sufficient generic hypotheses, not a claim that global
transitivity is logically necessary for every individual input.

Two independently calculable boundaries make the distinction concrete:

- For Nat `≤`, insert `2` into the unsorted `[3,0]` and filter even values.
  Filtering afterward gives `[2,0]`; inserting into the filtered old list
  `[0]` gives `[0,2]`. A lawful linear order and `P 2` do not remove the
  sorted-input requirement.
- Let the three labels be `A,B,C` and let `r` be equality together with
  `A r B`, `B r C`, `C r A`. This relation is total but not transitive.
  The input `[B,C]` is pairwise ordered. Inserting `A` gives `[A,B,C]`.
  Filtering to `A,C` gives `[A,C]`, whereas insertion into `[C]` gives
  `[C,A]`. It also shows why forward pairwise preservation cannot simply
  drop transitivity. The input-sublist converse remains true.

The companion proof of stability applies the positive helper to the
**recursively sorted tail**, not to arbitrary original `xs`, and then uses
the all-members helper on an equal-key filtered list. Reusing the existing
sublist-based stability proof is mathematically sound; retaining those
displayed intermediate statements is a separate coverage requirement.

## 5. What the existing declarations already provide

Pinned Mathlib `Sort.lean` has `orderedInsert_nil`, `orderedInsert_cons`,
`orderedInsert_cons_of_le`, `orderedInsert_of_not_le`,
`orderedInsert_length`, `mem_orderedInsert`, `perm_orderedInsert`,
`sublist_orderedInsert`, and `List.Pairwise.orderedInsert` at lines
47–58, 74–76, 90–106, 170–171 and 203–213. It also has
`List.Sublist.orderedInsert_sublist` at 177–197: under transitivity, inserting
the same value into a sublist of a sorted list preserves that sublist
relation. This is an especially close reusable ingredient for the positive
filter equality; it is not itself the exact source equality.

The equality helpers can therefore be thin observations of canonical
operations. For example, filter the appropriate insertion-sublist fact,
simplify the retained lower list using the predicate on the inserted value,
and combine with the filtered insertion permutation's length equality.
The negative helper similarly uses the filtered old-list sublist and the
filtered permutation. A direct induction on the existing recurrence is
also possible; neither route calls for a new recursive executor. The
separate API assessment checks the pinned elaboration-facing interfaces.

`List.map_orderedInsert` (94–97) already transports the actual insertion
value across `f : α → β`, under its two stated input-local relation
equivalences involving the inserted value and each old element. Retain
those actual API premises when using it; do not replace the pinned theorem
with an imagined weaker signature. This is a value law, not a running-time
law for evaluating `f`, keys, comparisons or maps.

Current conaled `Applications/Sorting/Sort.lean` defines `insertionOn` at
17–18 and proves `insertionOn_spec` at 94–110. Its hypotheses are
`[LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]`, with
arbitrary payload type. The actual proof combines standard sortedness and
permutation with `stable_of_sublist` and `List.sublist_insertionSort`.
It does not export the one-element negative/positive filtering helpers.
`sortOn_eq_insertionOn` at 113–115 is stable-output agreement under the
stronger linear-order contract; it does not equate the executions or costs
of different sorting algorithms.

### Existing X002 cost draft is separate, reusable and unaccepted

The X002 ticket records base `1aabd512284fe86254278ac631eda061d311050b`
and candidate `697bcf242ce65d74815b5639bddb1c6e754dd10f`, with historical
focused builds and complete verification/reviews still pending. This task
read the retained worktree files and records their bytes below; it did not
recheck Git identity or rerun validation. No acceptance follows from the
ticket's earlier focused evidence.

`Resources.InsertionSort.insertRun` is the actual branch-sensitive measured
insertion, with erasure `insertRun_value`. `insertRun_cost_bounds`,
`insertRun_cost_of_head`, `insertRun_cost_of_all` and
`insertRun_cost_of_all_not` retain the immediate-head and exhausted-tail
distinction. `sortRun` invokes insertion on the **actual recursively sorted
tail result**. It has value/length bridges, an exact cons cost equation,
lower bound `2*n+1`, triangular upper bound `(n+1)*(n+2)/2`, the weaker
source square bound, attained sorted/reversed-range cases, and
`sortRun_stable` using the existing stable contract. Its existing examples
include the tied-head/unsorted-tail case, arbitrary payloads, equal-key
order, occurrence ranks and the sorting-only small-input budget.

These declarations do not already state the sortedness iff or the two
filter equalities. In particular, `insertRun_cost_of_all` is a **cost**
statement; it is not the displayed value equation (2.36). Its value equation
can be connected through erasure and the existing head/nil insertion laws.

The source `Sorting.thy` does have `time_fun insort1` and `time_fun insort`
at 49–50. X002 retains their recursive-invocation interpretation, including
the empty insertion call and the actual sort/insert composition. The keyed
helper subsection does not introduce a separate timing declaration for
each semantic lemma. Reusing a generic measured relation here does not
price an arbitrary key or predicate evaluator or prove Lean machine time.

In particular, this insertion counter is not uniformly comparisons plus
one: empty input has one invocation and zero key comparisons, while an
immediate nonempty insertion has one invocation and one comparison. A scan
that reaches nil has a terminal invocation. Do not transfer the ordinary
merge's different universal `entries = comparisons + 1` identity here, or
claim that X002 directly proves Chapter 26's comparison tariff.

## 6. Actual sharing, and superficially similar operations

| Consumer and exact retained passage | What is genuinely shared | What does not follow |
|---|---|---|
| Chapter 2, source claims above | Canonical ordinary/keyed insertion, raw value observations, sortedness/filter statements and existing stable-sort contract. | Existing final stability does not remove source helper coverage. No extra XI01 cost executor is needed. |
| Chapter 3 pp.36, 38, 40; `chapter03.txt` 212, 287 and 346; C03-027/028/032 | Full insertion sort for small groups and the `≤20` selection base case, with X002 value/call bounds. | Selection indexing, actual median/partition recurrences and their costs are separate. This does not establish a use of the missing general filter-insertion equalities. C03-049's bounded-prefix selector remains its own exercise/client choice. |
| Chapter 14 p.180, Exercise 14.1; `chapter14.txt` 42–44; C14-014 onward | The inventory selects sorted lists with ordinary insertion, sorted merge, head minimum and tail deletion. Existing permutation/forward order lemmas support insertion. | The book asks for a list implementation with constant minimum/deletion, not a prescribed `orderedInsert` algorithm. The selected complete ADT, validity, merge and actual cost obligations remain queued. Current `exactList` appends and sorts on removal, so it is not already that exercise solution. |
| Chapter 26 pp.308–309, literal `insortTree`; C26-018/019 | Exact `List.orderedInsert` recurrence with `r u t := cachedWeight u ≤ cachedWeight t`; new tied trees precede old ones. Length/nonempty/permutation observations already have canonical support. | Computed tree weight is not a raw cache. Whole Huffman recurrence, ties, optimality, termination and runtime need their own bridges. Existing leftist Huffman is not automatically the literal list algorithm. |
| Chapter 26 Lemma 26.6 support; C26-067/078 | `cachedWeight_splitLeaf` and source insertion/forest-transform commutation, theory 2052–2076. The existing insertion-map law is a useful route with the stated forest hypotheses. | This transform is not filtering. Symbol-membership, consistency and frequency premises in the source remain. No need for C02-096/097 has been established by these lemmas. |
| Chapter 5 p.64; `List_Ins_Del.thy` 39–48 | A different strict-sorted-list set refinement. | `ins_list` tests `<`, suppresses a duplicate on `=`, and then recurses. Ordinary insertion always adds one occurrence. Their values and costs are not interchangeable without additional, proved domain premises. |
| Chapter 17 p.198; `chapter17.txt` 111–118 | A rank-ordered binomial forest insertion with carrying. | On equal ranks, `ins_tree` replaces the inserted tree by `link t1 t2` and consumes the head. It is not ordinary insertion, and source invariants/carry/cost lemmas remain chapter-specific. |

The actual current `Huffman.SourcePriority` file was read in full. It
specializes the existing generic exact queue to a leftist queue and proves
that specialization's step/loop/output correspondence. It does not implement
the manuscript's cached-tree list insertion. Similarly, actual
`Search.PriorityInterface.exactList` has `add := fun xs q => q ++ xs` and
`remove := listRemove` (`ExactPriority.lean` 123–129). Shared minimum/multiset
semantics do not identify those tie-selected raw outputs with the source.

### Chapter 26's cache premise is already retained, not a new gap

The formal `insortTree` at 836–839 compares `cachedWeight`. The formal
`sortedByWeight` at 1729–1733 uses recursively computed `weight` and adjacent
ordering. Its insertion lemma at 1747–1750 assumes sorted input **and**
`height t = 0` **and** `height_F ts = 0`: all involved trees are leaves.
Under that domain caches and computed weights agree. A more general run
invariant must prove the appropriate cache-accuracy and sortedness bridge;
raw consistency of symbols alone is not sufficient.

This is already explicitly covered by the retained inventory:

- **C26-026**, current line 167: computed/cached distinction, leaf-only
  source lemma, separate cache-accuracy and actual-run preservation.
- **C26-081**, line 237: the optimality induction must retain a shorter
  consistent **leaf-only sorted forest**; its summed-leaf insertion uses
  that exact source lemma.
- **C26-027** and **C26-083** retain the initial nonempty, leaf,
  consistency/disjoint-symbol and computed-sortedness premises.
- **C26-067/078** separately retain the cache-preserving split/map route;
  C26-088 separately retains the list-insertion comparison bound within
  the shrinking actual Huffman execution.

Thus no new inventory omission is reported for this qualification, and no
inventory is changed. A future cached-key specialization can reuse the
existing operation immediately, but cannot silently replace these source
premises with a stronger global invariant on every mathematical tree
transformation or with an unproved cache/value identification.

## 7. Smallest justified future boundary and handoff

When Chapter 2 becomes active, a small source-coverage step can:

1. Assemble ordinary sortedness iff from the existing forward theorem and
   old-input sublist, then specialize it to keyed mapped-list sortedness.
2. Expose the source all-members immediate-cons equation using the existing
   nil/head equations, alongside the existing one-occurrence/set bridges.
3. Prove negative and positive filtering equalities as thin observations
   of canonical insertion, keeping their different premises visible.
4. Connect the existing final keyed stability theorem to the source
   recurrence, preserving the displayed helpers as independent statements.
5. Retain meaningful empty, tied-payload, arbitrary-relation, unsorted-input
   and missing-transitivity cases. Use the existing X002 erasure only for
   measured clients that actually need it; semantic helpers need not depend
   on that unaccepted resource draft.

This is a proposed Chapter 2 implementation route, not a frozen API, new
review loop or authorization to write Lean now. The separate API assessment
may refine the economical proof route; source domains and all six ID groups
remain fixed. There is no reason here to add a second sorter or insertion
wrapper solely to restate the source equations.

All 112 Chapter 2 obligations remain mandatory. In particular, the other
sorting algorithms, their actual recurrences/stability/termination, the
comparison and recursive-call models, exact/asymptotic cost proofs, natural
run/builder claims and all exercises remain. Chapter 3 selection, the
chosen Chapter 14 sorted-list queue, Chapter 26's cached-tree Huffman proof
and cost obligations, Chapter 5's duplicate-suppressing refinement and
Chapter 17's carrying forest remain queued on their original terms. This
report supplies no chapter completion or final review evidence.

## 8. Exact inspected local identities

Paths are relative to `/workspace/scratch/845aa1048b05`. These ordinary
SHA-256 identities record reading inputs, not compiler output, Git/index
verification or proof acceptance.

| File | Bytes / lines | SHA-256 |
|---|---:|---|
| `fdsa-control/tickets/FDSA-XI01.md` | 2,571 / 44 | `3fa60ef644bcfad90930520e055e1e3a6d97d687d5715c7e0d714ef0349578fb` |
| `fdsa-control/research/chapter02-reuse-plan.md` | 31,586 / 346 | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `fdsa-control/research/chapter02-obligations.md` | 42,539 / 391 | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `fdsa-control/reviews/chapter02-requirements.md` | 12,034 / 189 | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `fdsa-control/research/scope-reconciliation.md` | 14,441 / 151 | `21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87` |
| `fdsa-control/tickets/FDSA-X002.md` and byte-identical `fdsa-control/reviews/insertion-requirements.md` | 3,257 / 60 each | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `conaled/Applications/Sorting/Sort.lean` | 5,922 / 128 | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `conaled/Applications/Sorting/Stable.lean` | 3,704 / 87 | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `conaled-insertion-costs/Applications/Resources/InsertionSort.lean` | 7,257 / 178 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| `conaled-insertion-costs/Examples/InsertionCosts.lean` | 3,862 / 101 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |
| `conaled/Applications/Huffman/SourcePriority.lean` | 2,142 / 58 | `de80cc229d7854a18efcf6901cc166a41a258d7371ddfef54ac603884eb9af4c` |
| `conaled/Applications/Search/ExactPriority.lean` | 5,912 / 139 | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| `fdsa-control/research/chapter26-obligations.md` | 47,897 / 405 | `c1803a540a887977be6bf2a75e3291a6f1665ea7167786939b04a40b0b8ecb61` |
| `book-source/List_Ins_Del.thy` | 5,321 / 142 | `988921eb88b03519ec3dd365ec90e5fdcead0736065e188e99fc47f7bf206af3` |
| `book-source/chapter03.txt` | 26,538 / 527 | `e46c195c97462bd3266b360aeeb336a8a14f2a9049410ca1ae4b2615ac2fcac8` |
| `book-source/chapter05.txt` | 32,466 / 605 | `b00475b2893cf76a66a5c164a63ee99e065772fffa7ae56054359b278c5c4b1e` |
| `book-source/chapter14.txt` | 4,808 / 102 | `b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a` |
| `book-source/chapter17.txt` | 14,444 / 285 | `6bc8d098bdeaebf83053419e830d17f23646bbbc6eddf4e504549d3f78c20a08` |
| `book-source/chapter26.txt` | 19,706 / 520 | `ed82113d19a24fb4eaf5b4ea808900b258c7cfbae63287218ed2e4ec6512d42e` |

No prior source, inventory, requirement, ticket, worktree, ref or cache was
modified. No compiler, project checker/hash helper, remote action or new
acceptance loop was run. This sole report is the permitted preparation
artifact; root owns any later assessment, checkpoint and source release.
