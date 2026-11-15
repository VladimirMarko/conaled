# FDSA-XI01 — independent ordered-insertion case preflight

Prepared 2026-11-03 UTC. Status: **report-only preparation; no source scope,
implementation base, new executor, cost model, or acceptance is selected**.
The sole owned artifact is this report. Chapter 1 attempt3 remains the sole
authorized validation gate. All 112 current Chapter 2 obligations remain;
the exact initial C2 prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847` and follows repaired Chapter 1
acceptance. This report neither changes that prefix nor adds a prerequisite.

## 1. Recommendation and what the cases establish

The remaining observations are useful, thin Chapter 2 mathematics over
**existing** insertion. The cases below distinguish their actual hypotheses
and connect them to existing full-record sorting clients. They do not identify
a missing shared operation or resource model. Defer implementation of this
remainder until Chapter 2 activation, unless a later separately assessed
consumer supplies a concrete need for one of these still-missing laws.

There is a genuine later recurrence consumer: Chapter 26's `insortTree` is
ordinary left-on-`<=` insertion using cached tree weights. Its inspected
length, permutation/forest observations, forward order, and comparison-
preserving transformation needs are covered by existing insertion mathematics
or require Chapter 26's own semantic bridges. That recurrence reuse does not
establish a new consumer of C02-009's converse or C02-096/097's filter laws.
Chapter 3's existing sorting/rank/budget clients likewise use the already
retained X002 execution and sorting contract, rather than those missing laws.

This conclusion leaves the displayed Chapter 2 helper obligations intact.
The fact that `insertionOn_spec` already proves stability by another route
does not waive the source's displayed (2.36), (2.37), or (2.38).

## 2. Exact inputs and inspected identities

Paths in the first table are relative to `/workspace/scratch/845aa1048b05`.
Byte identities were read with ordinary SHA-256, not a project hash helper.
Git reads used the pinned Nix environment and `git show`; no ref/index or
source mutation was involved. Using the existing tree-leftmost checkout to
enter that environment does not select it as an XI01 implementation base.

| Ref | Input and inspected scope | Bytes / lines | SHA-256 |
| --- | --- | --- | --- |
| T | `fdsa-control/tickets/FDSA-XI01.md`, complete ticket read first | 2,571 / 44 | `3fa60ef644bcfad90930520e055e1e3a6d97d687d5715c7e0d714ef0349578fb` |
| O | `fdsa-control/research/chapter02-obligations.md`, complete current inventory, including C02-108–112 and scope reconciliation | 42,539 / 391 | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| R | `fdsa-control/research/chapter02-reuse-plan.md`, complete reuse plan | 31,586 / 346 | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| S | `book-source/Sorting.thy`, directly read 1–75 and 338–410 | 14,846 / 435 | `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca` |
| B2 | `book-source/chapter02.txt`, directly read 440–507, printed pp.26–27 plus the start of p.28 | 28,337 / 563 | `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1` |
| H | `book-source/afp-Huffman-2026-10-26/Huffman/Huffman.thy`, directly read 826–859, 1720–1757, 2045–2077 | 101,517 / 2,363 | `7bdc838bbdf7347fb78440a5b3c8dadaf6b7c228e6e3cae6f2d1fb49582837bf` |
| B26 | `book-source/chapter26.txt`, directly read 150–190, printed pp.308–309 | 19,706 / 520 | `ed82113d19a24fb4eaf5b4ea808900b258c7cfbae63287218ed2e4ec6512d42e` |
| L | Pinned `Mathlib/Data/List/Sort.lean`, directly read 1–241 and searched its insertion declarations | 35,291 / 901 | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| SP | `fdsa-control/research/ordered-insertion-source-preflight.md`, complete stopped report read for final correspondence | 27,603 / 363 | `42ad87047a0f9debbdf8729e9fa0ff9158ef1d9486115fe752c52e5ec6219ab5` |
| AP | `fdsa-control/research/ordered-insertion-api-preflight.md`, complete stopped report read for final correspondence | 30,616 / 483 | `ebe0dde61d1a3839df747b78d678cf673b307f13e2046149b2c5658d5e1aca84` |

S belongs to retained Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. O/R pin the July 27, 2026
manuscript, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`,
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The companion revision
postdates that edition; it is not asserted to be its generation revision.
B2/B26 are retained research extracts with control-character artifacts; the
literal Isabelle statements resolve the comparison/implication notation.
The manuscript or its long extracted prose is not reproduced here.

The following exact files were read completely through `git show` at the
unchanged prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847`:

| Ref | Path | Bytes / lines | SHA-256 |
| --- | --- | --- | --- |
| V1 | `Applications/Sorting/Stable.lean` | 3,704 / 87 | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| V2 | `Applications/Sorting/Sort.lean` | 5,922 / 128 | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| E1 | `Examples/StableSorting.lean` | 5,041 / 124 | `c894760e594cdc31d9dda54553eeff666156c81f7903dea82738c8a95faaf193` |
| X1 | `Applications/Resources/InsertionSort.lean` | 7,257 / 178 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| E2 | `Examples/InsertionCosts.lean` | 3,862 / 101 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |

X1/E2 are retained, unaccepted X002 work. Their source comments do not supply
a new validation result. R's opening historical count is 107; O's appended
scope clarification explicitly retains all 112 current IDs. No earlier
inventory or frozen requirement was rewritten for this report.

## 3. Operation identity and distinct hypothesis boundaries

In this report `I_r(a,xs)` abbreviates the existing
`List.orderedInsert r a xs`; it is notation for analysis, not a proposed new
definition. Its literal branches are singleton at nil, `a :: b :: ys` when
`r a b` holds, and `b :: I_r(a,ys)` otherwise. It stops at the **first** true
comparison. `List.insertionSort r` is the existing right fold of that
operation, and `Applications.Sorting.insertionOn key` uses
`r a b := key a <= key b`. [L:43–67; V2:17–18; S:19–26,346–352]

Write `F_P xs` for `List.filter P xs`, with `P : α → Bool`; the source's
propositional predicates have the ordinary decidable-predicate adapter.
Thus `P a` below means `P a = true`, and its negative means false. No predicate
implementation or observer tariff is selected by this notation.

| Obligation/observation | Exact applicable hypotheses | Existing anchor or remaining thin statement |
| --- | --- | --- |
| C02-009, reverse direction | Any `r : α → α → Prop` with `DecidableRel r`; no totality or transitivity | `xs` is an actual sublist of `I_r(a,xs)` by `List.sublist_orderedInsert`; `List.Pairwise.sublist` inherits output pairwise order. In fact the observed relation may be arbitrary and independent of r. |
| C02-009, forward direction | Pairwise `r` input and the pinned API's `[Std.Total r] [IsTrans α r]` | `List.Pairwise.orderedInsert`. Combine with the previous direction for the source iff; do not put these laws on the raw converse. |
| C02-094, one insertion | No order laws for full-record permutation, membership, or length | `List.perm_orderedInsert`, `mem_orderedInsert`, `orderedInsert_length`; keyed sortedness iff is C02-009 for the pulled-back relation. |
| C02-094, complete keyed sort | The existing `insertionOn_spec` assumptions are on keys: `LE`, `DecidableLE`, `Std.IsLinearPreorder`, `DecidableEq` | Its `.sorted` and `.perm` fields, plus `List.pairwise_map`, give the source mapped-key/full-record observations. The complete stable contract has a key equality decision; ordinary permutation does not need one. |
| C02-095/(2.36), cons | `∀ b ∈ xs, r a b`; no sorted-input or global relation law | Nil/cons cases and `orderedInsert_cons_of_le`. On a nonempty input the immediate branch only needs the actual head comparison; the source's stronger all-members premise is sufficient, not necessary. |
| C02-096/(2.37), negative filter | `P a = false`; arbitrary input, decidable relation and supplied predicate | `F_P(I_r(a,xs)) = F_P xs`. No totality, transitivity, input sorting, key/payload equality, or predicate monotonicity is needed. |
| C02-097/(2.38), positive filter | `P a = true`, `xs.Pairwise r`, and transitivity of the **same** insertion relation | `F_P(I_r(a,xs)) = I_r(a,F_P xs)`. Totality is not required for this helper. The source instantiates linear key order, which supplies the needed transitivity. |
| C02-098/Lemma 2.11 | The existing keyed stable-sort contract | `(Applications.Sorting.insertionOn_spec key xs).stable k` is the exact equal-key full-record filter equality. It is not equality of arbitrary filtered subsequences. |

The ordinary source statement S:40–41 uses a linear element order. Its keyed
analogue S:367–368 concerns sorted **mapped keys**, not a new order on full
records. B2 and S:376–405 explicitly supply the all-members, negative-filter,
and positive-filter helpers used in the displayed stability proof. The three
helpers are not additional exercises. [O:C02-009,094–098]

The most delicate positive-filter branch is an inserted element which stops
before a head that the predicate removes. For every later retained `c`, sorted
input gives `r head c`; transitivity with `r a head` then gives `r a c`. This is
why insertion into the filtered tail may put `a` first. The source requires
no predicate monotonicity; with an arbitrary P, the raw recurrence alone does
not supply that argument.

## 4. Independently derived connected cases

All expectations in this section were obtained by following the displayed
recurrence and independently inspecting the resulting lists. They are not
compiler results. No new recursive program was written to generate them.
The families are grouped to expose distinct claims; they are not a requirement
to add a new declaration or duplicate an existing example for every row.

### A. Nil, arbitrary universes, and the empty-type boundary

For arbitrary `α : Type u`, decidable `r`, supplied `P`, and an actual `a : α`:

- `I_r(a,[]) = [a]`.
- `F_P(I_r(a,[]))` is `[a]` when `P a` is true and `[]` when it is false.
- `List.insertionSort r [] = []`; insertion never needs a default element.

These same base observations disprove deleting the predicate premise from
either filter law. With `P a = true`, the negative law would equate `[a]` to
`[]`. With `P a = false`, the positive law would equate `[]` to `[a]`.

Every `List Empty` and `List (Nat × Empty)` is empty, so whole-sort value and
stability statements apply without an inhabitant or payload order. In contrast,
there is no nonvacuous `orderedInsert` call with an inserted `a : Empty`.
Do not manufacture that argument to claim a stronger domain test. The actual
`E2.key_contract` accepts an arbitrary `payload : Type u`, so its empty-payload
specialization already has the correct domain. V1/V2 explicitly separate record,
destination, and key universes; the intended generic observers need no equality
decision or order on semantic payloads.

### B. Cons is not sortedness, and a tied head does not inspect the tail

Use the raw numeric input `[2,0]` with the ordinary nonstrict relation:

| Inserted value | Literal branch/result | Distinction |
| --- | --- | --- |
| `0` | `0 <= 2`, so `I_≤(0,[2,0]) = [0,2,0]` | The C02-095 all-members premise holds (`0<=2`, `0<=0`) although the input is unsorted. The cons conclusion does not imply sortedness. |
| `2` | `2 <= 2`, so `I_≤(2,[2,0]) = [2,2,0]` | The all-members premise fails at0, yet the same cons conclusion holds. This is the exact retained `E2.tied_head_ignores_tail` value, with existing insertion subcount1. |

Both outputs retain the input inversion `2 > 0`. The unconditional sublist
converse explains why insertion cannot repair that inversion. For a positive
sorted/tie observation, reuse `E2.immediate_insertion`: inserting2 into `[2,3]`
gives `[2,2,3]`; repetitions are allowed by nondecreasing order and multiplicity
increases by one. The new iff witness should consume the public forward and
sublist laws, rather than replace these actual operation observations.

### C. Negative filtering on an unsorted semantic-payload input

Let records be `Nat × Bool`, compare only first projections, and let
`P(k,v) := v`. Insert `a=(2,false)` into

```text
xs = [(1,true), (3,false), (0,true)].
```

The comparison with key1 is false, and the comparison with key3 is true.
The operation therefore returns

```text
[(1,true), (2,false), (3,false), (0,true)].
```

Filtering that result gives `[(1,true),(0,true)]`, exactly `F_P xs`.
The input is unsorted (`3 > 0`), and the retained result is also unsorted
(`1 > 0`). The inserted semantic false value is removed by the **chosen
predicate**, not interpreted as absence by insertion. This one case tests a
recursive step, a stopping step, an arbitrary payload predicate, and the lack
of an input-sorting requirement in C02-096.

The law is not limited to a lawful ordering comparator. At the two raw extremes,
an always-true relation returns `a::xs`, and an always-false relation returns
`xs++[a]`; if `P a` is false, either result has filtered observation `F_P xs`.
Those are specializations of the same generic operation, not alternative source
sorters or proposed new comparators for the keyed sorting contract.

### D. Positive filtering with a discarded stopping head

Again compare `Nat × Bool` records only by keys, but take `P(k,v) := !v`.
Insert `a=(2,false)` into the sorted list

```text
xs = [(0,false), (1,true), (3,true), (4,false)].
```

The actual comparisons are `2<=0` false, `2<=1` false, `2<=3` true. Thus:

```text
I(a,xs)       = [(0,false),(1,true),(2,false),(3,true),(4,false)]
F_P(I(a,xs))  = [(0,false),(2,false),(4,false)]
F_P xs       = [(0,false),(4,false)]
I(a,F_P xs)  = [(0,false),(2,false),(4,false)].
```

Both a traversed prefix element (key1) and the actual stopping head (key3)
are filtered out. The last retained key4 is after key3 in the sorted input;
`2<=3` and `3<=4` justify `2<=4`. This is precisely the substantive positive
branch, with a predicate on semantic payloads rather than an equal-key-only
predicate. All record values remain explicit.

The existing X1 `insertRun` gives insertion subcounts **3** on `xs` and **2**
on `F_P xs`: each false comparison descends, each true stopping branch costs1.
Thus the positive **value** equality does not give equality of those measured
insertion observations. This calculation uses the existing X002 recurrence,
not a new tariff. No filter traversal, complete composed program, allocation,
or Lean runtime cost is included in those two numbers. Any future measured
value client must use `insertRun_value`; output equality alone is insufficient.

### E. The sorted-input premise cannot be dropped

Use ordinary Nat `<=`, `a=2`, `xs=[3,0]`, and the even-number predicate.
All relation laws and the positive predicate premise hold. Literal evaluation:

```text
I_≤(2,[3,0]) = [2,3,0]   because 2<=3
F_even [2,3,0] = [2,0]
F_even [3,0]   = [0]
I_≤(2,[0])    = [0,2]    because 2<=0 is false.
```

The two observations differ. The only failed positive-law premise here is
input sortedness. This is a genuine unsorted-input boundary, not a comparison
law failure, payload-equality issue, or exotic order example.

### F. One total nontransitive relation tests two laws

On three distinct labels `A,B,C`, define the decidable relation consisting of
equality and the three directed pairs `A R B`, `B R C`, `C R A`.
It is reflexive and total: each distinct pair has one of its two directions.
It is not transitive, since `A R B` and `B R C` hold but `A R C` does not.

The input `[B,C]` is Pairwise R. Inserting A stops at B and gives `[A,B,C]`.
This output is not Pairwise R, exposing the transitivity premise of the forward
C02-009 direction while retaining totality. The reverse direction is unaffected:
the original list is still an actual sublist.

Now let P retain A and C and remove B. Filtering that result gives `[A,C]`.
Filtering the input gives `[C]`; since `A R C` is false, inserting A there gives
`[C,A]`. Hence C02-097 also fails without transitivity, although the input is
Pairwise R, P A is true, and R remains total. One fixture supplies both
counterexamples; no additional relation framework is needed.

### G. Strict ties, totality, and stable full-record order

Reuse the exact records `a=(2,"first")`, `b=(2,"last")` from E1. With the
source nonstrict key relation, insertion of a into `[b]` yields `[a,b]`.
With the existing generic insertion instead instantiated at strict key `<`,
the comparison is false, so it yields `[b,a]`.

Strict key `<` is transitive but not total in the sense required by
`Std.Total r` (equal keys relate in neither direction). Its singleton input is
Pairwise r; the two-element output is not. This isolates the totality premise
of generic forward pairwise preservation, without challenging the raw converse.

At the same time, `[b,a]` is **nondecreasing by key** and a full-record
permutation of `[a,b]`. Its key list is still `[2,2]`. Nevertheless the key2
filtered full-record sequence is reversed. E1's existing
`sorted_permutation_not_stable` proves precisely this independent-observation
boundary. A right-fold insertion sorter with strict ties would produce that
reversal on `[a,b]`; changing the tie test is therefore not an acceptable
implementation of the source stable sorter.

No order on the strings was used. Projecting the result to keys would hide
the failure; preserving key lists, multisets, or sortedness alone does not
preserve semantic equal-key order.

### H. Reuse the actual signed-record client for the source proof connection

E1 supplies:

```text
input    = [(2,"first"),(-1,"negative"),(2,"last")]
expected = [(-1,"negative"),(2,"first"),(2,"last")].
```

The actual sorted tail is `[(-1,"negative"),(2,"last")]`. Inserting the
original first record compares `2<=-1` false and `2<=2` true, producing
`expected`. The source helper chain can be observed on this same execution:

- For key -1, the inserted record fails the key predicate; negative filtering
  leaves `[(-1,"negative")]` unchanged.
- For key2, the predicate is positive and the actual sorted tail supplies
  C02-097's premise. Filtering the output gives
  `[(2,"first"),(2,"last")]`.
- The filtered tail contains only `(2,"last")`; the all-members/equal-key
  condition from C02-095 inserts the earlier record at its head.

`E1.insertion_sort_records` already identifies the full actual output through
`insertionOn_spec` and the independently specified `expected_spec`.
`insertionOn_spec.sorted` and `.perm`, with `List.pairwise_map` and the ordinary
permutation/multiset adapter, witness C02-094's independent observations.
Its `.stable k` field supplies the quantified C02-098 observation, including
keys absent from the input. These are genuine existing public connections;
another sorter or another independent stable-sort contract would duplicate them.

An arbitrary-filter analogue of C02-098 would be false: taking P constantly
true on E1.input gives `expected`, whereas filtering the original input gives
`input`. The full-sort stability observation is specifically the equal-key
filtered sequence. This is separate from C02-097's arbitrary predicate and
its **single insertion into an already sorted input**.

## 5. Transport and generic-payload reuse already available

`List.map_orderedInsert` is existing value mathematics. Its actual interface
asks for both local comparison equivalences against the inserted value on
members of the input list; it does not require injectivity of the map.
Key-preserving maps satisfy those hypotheses for the pulled-back key relation.
Do not silently replace that inspected interface with a claimed stronger
one-way/local API. [L:94–97]

V1's `StableSort.map` works across distinct record/destination universes and
requires exact key preservation, with no injectivity requirement. E1's
`transformed_spec` already composes payload-length and parity maps. For its
literal strings, the transformed input is `[(2,1),(-1,0),(2,0)]` and the
transformed expected result is `[(-1,0),(2,1),(2,0)]` (lengths5,8,4 before
parity). This is an existing semantic-payload transport client, not evidence
that the original string values are unchanged. `sortOn_map` is also already
exported; a new insertion-specific payload framework is unnecessary.

Neither ordinary `map_orderedInsert` nor `StableSort.map` states a cost
identity for X1's execution, charges mapping the input for free, or preserves
unrelated payload invariants. No cost-transport theorem is inferred here.

## 6. Actual consumer assessment

### Existing conaled and Chapter 3

The source of V2's `insertionOn_spec` proves stability with
`stable_of_sublist`, `List.sublist_insertionSort`, and the equal-key filtered
sublist. It does not call the missing C02-096/097 helpers. The helpers remain
Chapter 2 display coverage, rather than prerequisites for repairing that proof.

E2's actual `sorted_result_has_rank` obtains `.sorted` and `.perm` from
`sortRun_stable`, then calls `Applications.Selection.pairwise_ranked`.
`small_rank_with_sort_budget` combines that result with the existing X002
bounded-size sorting budget. These are genuine shared clients of insertion
execution/correctness. They do not use a reverse sortedness implication or
filter/insertion commutation. Their cost is sorting subcost, not indexing or
the complete median-selection program. [E2:72–99; X1:170–176]

### Chapter 26's cached-weight tree insertion

H:836–839 and B26:175–179 use exactly the left-on-`<=` recurrence with
`key = cachedWeight`. A compact literal case is

```text
u = Leaf 5 false
v = Leaf 5 true
insortTree u [v] = [u,v].
```

The full trees remain distinct although their keys are equal. This needs the
existing cons-branch law, not a new filter observer. It is not a claim that
the complete Huffman construction is a stable sorting algorithm or chooses
a canonical optimum among tied weights.

The source also makes a substantive observation distinction: its later
`sortedByWeight` compares **computed** weight, whereas the insertion branch
compares cached weight. The inspected `sortedByWeight_insortTree` explicitly
requires the inserted tree and the forest to have height0 (all leaves).
A different domain would need its own correct cached/computed-weight bridge;
raw key sorting cannot supply that bridge. [H:1729–1750]

The inspected `splitLeaf` insertion commutations preserve cached comparisons
using `cachedWeight_splitLeaf`. They retain alphabet, consistency, and frequency
premises, and relate a forest/tree transformation to insertion. They are not
the C02 predicate-filter commutation. Existing comparison-preserving mapping
mathematics may help after the actual source transformation bridge is proved;
this report does not assert that those Chapter 26 lemmas are already formalized
or that their semantic premises can be discarded. [H:2052–2076]

Consequently, this later recurrence is genuine reuse evidence for the
**existing** `orderedInsert` operation and its existing laws. It does not
change the recommendation to defer XI01's missing thin observations to C2.
No new Huffman carrier, cache checker, forest transformation, source adapter,
or priority-queue implementation is selected by this investigation.

## 7. Small proof routes to retain for Chapter 2 activation

The API investigation corroborates routes that do not reimplement insertion:

1. **Sortedness iff:** combine `List.Pairwise.orderedInsert` with
   `List.sublist_orderedInsert` and `List.Pairwise.sublist`, keeping the raw
   converse separate from the forward relation laws. Specialize the relation
   to element `<=` or pulled-back key `<=`, and use `List.pairwise_map` for
   the book's mapped-key formulation.
2. **Cons:** nil/cons analysis and `orderedInsert_cons_of_le`, preserving the
   displayed all-members premise. The head-only existing cost observation
   remains a different statement.
3. **Negative filter:** filter the actual input-sublist witness. The filtered
   permutation from `perm_orderedInsert` gives equal lengths when P a is false;
   sublist plus equal length gives exact list equality, preserving order.
4. **Positive filter:** `List.Sublist.orderedInsert_sublist` applied to the
   filtered-input sublist and Pairwise input uses only `IsTrans α r`.
   Filtering that witness, retaining a because P a is true, and the filtered
   permutation/length observation yields the desired equality. The crucial
   sortedness/transitivity boundary is already present in that public theorem.
5. **Correctness/stability clients:** reuse V2's exact `insertionOn_spec`, the
   existing `Stable` definition, E1's signed records and counterexample, and
   X1's `insertRun_value`/`sortRun_value` if the already retained measured result
   is the chosen client. No fresh measured recursion is required.

These are future proof routes, not new exported declarations or a frozen file
layout. A future implementation may use a direct source induction where useful,
but must preserve the same statements, predicates, records, and assumptions.
The cases above do not justify making every helper a new framework component.

## 8. Assessment limits and unchanged gates

The complete stopped source report SP was read after the independent cases
were derived. Its exact helper statements, total-cycle and unsorted-input
boundaries, Huffman cache/domain distinction, and deferred-C2 recommendation
agree with this report. SP additionally records the selected Chapter 14
sorted-list consumer and distinguishes Chapter 5's duplicate-suppressing
insertion and Chapter 17's carrying insertion. Those are source-report
findings, not additional case families or a source scope selected here.

The complete stopped API report AP was then read. Its exact sublist/filter/
equal-length proof route, independent-relation converse, two local mapping
premises, and distinction between insertion values and the existing X002
counts agree with the cases and public-law connections above. Neither final
correspondence read found a concrete statement discrepancy or a new consumer
that would justify releasing a shared XI01 implementation now.

This is independent mathematical/source-level case preparation. There was no
Lean elaboration, compiler execution, test run, axiom audit, integrity check,
final Standards/Spec review, or acceptance action. Existing source equality and
these manually derived expectations are not a substitute for any such gate.

No source file, index, ref, worktree, dependency, ticket, scope record,
initial C2 prefix, Library object, or GitHub object was changed. No build-cache
inspection or intervention was performed. Only this report was authored.
All C02-001–112 remain mandatory under the user's
whole-book instruction, including the independently retained operational
claims C02-108–112. Chapter 2 activation and acceptance still follow the
existing Chapter 1 prerequisite and complete prescribed workflow.
