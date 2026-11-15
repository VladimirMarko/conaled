# Chapter 2 Exercise 2.3: independent three-way quicksort cases

Prepared 2026-11-03 for **C02-102**. This is bounded source-level mathematical
preparation, not implementation, a new shared unit, scope freeze, chapter
activation, final review or acceptance. Only this report is authored. The
coordinator retains sole ownership of the Chapter 1 full gate; this pass makes
no new liveness, build or terminal-status observation.

## 1. Literal operation and independent conclusion

The printed Exercise 2.3 supplies the three-way sorter itself. Its partition
is the three stable filters of the **tail**, with predicates `< pivot`,
`= pivot` and `> pivot`. The sorter recursively sorts only the strict sides
and places **one pivot followed by every equal tail occurrence** between them.
In mathematical notation, with parentheses making the middle block explicit:

```text
partition3 p tail =
  (filter (fun y => y < p) tail,
   filter (fun y => y = p) tail,
   filter (fun y => p < y) tail)

q3 [] = []
q3 (p :: tail) =
  let (L,E,G) = partition3 p tail
  q3 L ++ (p :: E) ++ q3 G
```

This is the displayed Exercise 2.3 operation on printed p.28 / PDF p.34,
`book-source/chapter02.txt:513–525`, under the chapter's linear-order
convention at lines 7–29. Unlike Exercise 2.2's accumulator worker, this
recurrence is supplied by the book. `q3` is mathematical shorthand here,
not a promise of a future Lean name. The retained `Sorting.thy:327–339`
supplies the earlier ordinary two-way sorter and its correctness; it is not
being cited as a companion implementation of this exercise.

Five compact inputs suffice for the identified risks: empty, singleton,
all-equal, mixed duplicates, and a pivot absent from a nonempty tail. The
mixed case exposes content and order separately, and the absent-tail case
shows exactly why the existing conditional partition-size theorem is not the
termination argument to apply without its premise. No extra cost model,
indexing observation, record-stability theorem or framework is needed.

## 2. Exact cases calculated from the source recurrence

These are independent direct calculations of finite lists, not Lean
evaluation results or proofs of a future implementation. There is no sorted
input or distinctness restriction. `L,E,G` below always partition the tail.
The nil branch does not choose a pivot or invoke a pivot-dependent partition.

| Input | Tail partition `(L,E,G)` | Exact expected `q3` output | Main distinction |
| --- | --- | --- | --- |
| `[]` | Not invoked | `[]` | Total base without a default element. |
| `[2]` | `([],[],[])` | `[2]` | The pivot occurs once even though it is absent from its empty tail. |
| `[2,2,2]` | `([],[2,2],[])` | `[2,2,2]` | Both strict recursive inputs are empty; the equal tail is retained directly. |
| `[2,3,1,2,0,3,2,1]` | `([1,0,1],[2,2],[3,3])` | `[0,1,1,2,2,2,3,3]` | Unsorted left side, repeated values in each region, and a nonempty equality block. |
| `[0,2,1]` | `([],[],[2,1])` | `[0,1,2]` | Pivot absent from the tail; the greater part equals the entire unsorted tail. |

### 2.1 Mixed input: actual children, middle block and multiplicities

Take `p=2`, `tail=[3,1,2,0,3,2,1]`. In source order the three filters yield

```text
L = [1,0,1]
E = [2,2]
G = [3,3].
```

Their lengths are `3,2,2`, summing to the tail length `7`. The unsorted list
`[1,0,1]` is actually sent to the left recursive call. It has pivot `1`,
tail `[0,1]`, and child/equality lists `[0],[1],[]`. Therefore

```text
q3 [1,0,1] = [0] ++ [1,1] ++ [] = [0,1,1].
```

The right recursive input `[3,3]` has empty strict sides and equality list
`[3]`, so its result is `[3,3]`. At the original root the middle block is
`2 :: [2,2] = [2,2,2]`, and the complete assembly is

```text
[0,1,1] ++ [2,2,2] ++ [3,3] = [0,1,1,2,2,2,3,3].
```

The multiplicities are exactly `0↦1`, `1↦2`, `2↦3`, `3↦2`, totaling `8`.
They agree with the input and are stronger evidence than equality of element
sets. Nondecreasing order is a separate observation of the resulting list.
The table does not replace the two universal correctness proofs.

### 2.2 All-equal and singleton boundaries

For `[2,2,2]`, the two strict recursive arguments are `[]` and `[]`. The
source body is

```text
q3 [] ++ (2 :: [2,2]) ++ q3 [] = [2,2,2].
```

There is no recursive call on `[2,2]` in this source body. This is an
execution-shape observation, without a numerical tariff for any call,
filter, constructor or append. The singleton similarly reduces to
`q3 [] ++ [2] ++ q3 [] = [2]`. A nonempty equality list is not a prerequisite
for processing a nonempty input.

The empty branch does not require an element of the payload type. The
general source specialization can retain `α : Type u` with `[LinearOrder α]`
and no `Inhabited` or finite-carrier premise. On an empty payload type the
only possible input is the empty list. The numeric fixtures do not restrict
the future theorem to naturals or add a global enumeration of values.

## 3. The precise conditional-size boundary

The actual existing theorem in `Applications.Selection.ThreeWay` is

```text
partition_strict_sizes p xs (hp : p ∈ xs) :
  (partition3 p xs).1.length < xs.length ∧
  (partition3 p xs).2.2.length < xs.length.
```

Its premise is substantive: the proof puts an occurrence of `p` in the
equality block and uses its positive length. The theorem is correct as
stated. Quicksort's pivot belongs to `p :: tail`; it need not belong to the
separately partitioned `tail`. There is no reason to add that premise to the
sorter, weaken the existing theorem, or switch the partition input merely
to make the theorem applicable.

For the selected `[0,2,1]` input, `0 ∉ [2,1]`. Its greater list is `[2,1]`,
so the proposed premise-free strengthening would assert `2 < 2`, which is
false. Its equality block is empty. Nevertheless the actual child has
length `2 < 3`, so it is strictly smaller than the **full** quicksort input.
The next call has input `[2,1]`, with lesser list `[1]`, empty equality and
greater lists, and returns `[1,2]`; the outer pivot yields `[0,1,2]`.

The universal termination route is simply

```text
L.length ≤ tail.length < (p :: tail).length
G.length ≤ tail.length < (p :: tail).length.
```

Use the literal filter-length bounds, or nonnegativity plus the existing
three-part length sum. Neither route needs `p ∈ tail`, input sortedness,
distinctness, a bound comparing the two children, or an output-length
theorem. The singleton already has strict children of length `0 < 1` even
though neither can have length strictly below its empty tail. The nonempty
absent-tail fixture exposes the same issue without relying only on zero.

## 4. Discriminating errors using the same mixed case

The following are **root-body changes with the correct child outputs fixed**
at `[0,1,1]` and `[3,3]`. Their exact lists are not asserted to be outputs of
a recursively modified algorithm at every node. This distinction keeps the
counterexamples focused on the actual assembly contract.

| Incorrect root assembly | Exact resulting list | Failed source observation |
| --- | --- | --- |
| Drop the pivot, retain only `E` in the middle | `[0,1,1,2,2,3,3]` | One occurrence of `2` is lost, although the result is sorted. |
| Drop `E`, retain only the singleton pivot | `[0,1,1,2,3,3]` | Two equal tail occurrences are lost, although the result is sorted. |
| Partition the whole input, then also prepend the pivot to its equality block | `[0,1,1,2,2,2,2,3,3]` | The root pivot is counted twice; the result has length `9`. |
| Move the pivot before the sorted left side, retaining all other values | `[2,0,1,1,2,2,3,3]` | Content is preserved, but the leading `2,0` violates nondecreasing order. |

The first three observations show why sortedness alone is insufficient;
the last shows why a permutation alone is insufficient. Set equality would
also miss the lost or extra equal copies in the first three rows.

### 4.1 Equal-block recursion can be invisible in final values

Replacing the untouched `E` by `q3 E` is a different recursion. On the mixed
case `E=[2,2]` and `q3 E=[2,2]`; on the all-equal case the same equality
holds. Thus it can retain every expected final value while adding a recursive
call that is absent from the source. This is an operation-identity failure,
not a claim that the resulting value theorem is necessarily false. The
actual defining body and recursive arguments must be inspected; no finite
collection of unlabelled output lists can certify that the recursive calls
match the source.

A different mistake is to recurse on the **whole** block `p :: E` instead
of emitting it. On `[2,2,2]` that argument is again `[2,2,2]`, the identical
input. Such a direct recursive call does not decrease the first-input
length. This observation concerns the proposed call itself, not a theorem
that a self-equality of values forces nontermination for every possible
definition. No execution or stack model is introduced.

### 4.2 The earlier two-way sorter is a different algorithm

For the mixed input, ordinary source quicksort sends `[1,0,1]` left and
`[3,2,3,2]` right. Three-way quicksort sends `[1,0,1]` and `[3,3]` to the
recursive calls and emits `[2,2,2]` between their results. On `[2,2,2]`,
two-way quicksort recurses on the right input `[2,2]`; the three-way source
has both strict inputs empty.

Their correctly sorted final lists can agree. That does not identify their
recursive calls, partition traversals or any cost observation. A call to
the existing library sorter, or to a future ordinary two-way sorter, cannot
stand in for implementing the displayed three-way recursion merely because
it returns the same values. Exercise 2.4's separate two-way time function
and the existing distinct-input probability preparations remain unchanged.

## 5. Existing public facts and general statement assessment

The complete current `conaled/Applications/Selection/ThreeWay.lean` was read.
Its partition definition uses two successive `List.partition` calls; the
public `partition3_eq_filters` proves equality to the literal triple of
source filters. The following existing declarations have direct roles:

| Existing `Applications.Selection` declaration | Actual use and limitation |
| --- | --- |
| `partition3_eq_filters p xs` | Identifies every returned list with the exact stable `<`, `=` and `>` filter. It supplies a value bridge, not a traversal/count identity. |
| `partition3_perm p xs` | The concatenation of the three buckets is a permutation of `xs`, retaining multiplicities. No pivot-membership premise. |
| `partition_left_mem`, `partition_equal_mem`, `partition_right_mem` | Give input membership and the exact relation to the pivot, for arbitrary `p` and `xs`. |
| `partition_lengths p xs` | Sum of all three bucket lengths equals `xs.length`; sufficient for non-strict child bounds on a tail. |
| `partition_strict_sizes p xs hp` | Strict bounds relative to the partition input, conditional on `hp : p ∈ xs`; it is not the unqualified quicksort-tail bound. |
| `sorted_partition p xs` | Expresses the standard `ordered xs` as sorted strict sides around the unchanged equal block. It is useful value structure, not an implemented `q3` or a selection-cost theorem. |

The actual `ordered` abbreviation is `Applications.Sorting.sortOn id`, with
`ordered_perm` and `ordered_pairwise` in `Selection/Rank.lean:52–61`. The
later selector, its pivot policies, fuel and positional dispatch are not
needed to define this sorter. Existing partition facts should be reused
through their independent interface, preserving the Selection adapters,
rather than making sorting import the complete selection implementation.

The coordinator and API author identified the already drafted XQ01 partition
extraction at `de5410286bbefd841dff50bef55c2e52d2ebbd2a`. It is uncompiled and
unaccepted; this task does not create another unit, choose its integration
base, or turn that draft into an accepted dependency. Final API correspondence
is recorded with the companion report below.

### 5.1 Universal content and order statements

The required content statement is a full permutation/multiset equality for
every input, including duplicates, not only equality of supports. For
`partition3 p tail=(L,E,G)`, the recursion and induction hypotheses give

```text
M(q3 (p :: tail))
  = M(L) + {p} + M(E) + M(G)
  = {p} + M(tail)
  = M(p :: tail).
```

Here `M` is mathematical multiset notation; the project already uses
`List.Perm`, so a new multiset carrier or sorting specification is unnecessary.
The middle contribution must be exactly one pivot plus the whole `E`.

For pairwise nondecreasing order, the strict child outputs inherit sortedness
from the induction hypotheses and membership from their permutation proofs.
The middle block consists entirely of values equal to `p`, including its
leading pivot. Thus it is pairwise ordered. Every left value is strictly
below `p`, and every right value strictly above it. These facts establish
the cross-block comparisons, including left-to-right comparisons by
transitivity. The existing pairwise-append specification can assemble these
pieces. Alternatively, a proved correspondence with the existing `ordered`
value may organize the same actual-recursion proof; neither route permits
replacing the algorithm by the reference sorter.

The exact source and current partition APIs assume `[LinearOrder α]`.
Trichotomy makes the three literal filters exhaustive and disjoint, and the
order laws justify the stated comparisons. This report does not weaken
that domain to unrelated arbitrary predicates or comparators. It also does
not add sorted-input, `Nodup`, pivot-in-tail, nonempty-type or finite-type
premises to the future source theorem. Keyed-record stability and semantic
payload transport are separate scoped work; unlabelled duplicate cases do
not establish either.

### 5.2 What the eventual statement/body read must check

The existing statement-review workflow should check the actual future
definition and public correctness claims together: quantification over all
inputs, exact tail partition and comparison directions, one explicit pivot,
untouched equal block, recursion only on strict sides, valid child decrease,
and both permutation and pairwise-order conclusions. Connected cases should
consume those real public equations/laws while retaining the independent
lists above. No theorem name, generated recursor or helper quota is promised.

The equal-block recursion example shows why output correctness alone cannot
certify source execution shape. Conversely, source-shaped equations alone
do not prove content and sortedness without the general arguments. This is
the ordinary existing assessment obligation, not a new acceptance loop.

## 6. Exact retained inputs and scope status

The governing Chapter 2 requirements were read completely. Current inventory
and historical reuse passages were read specifically for this exercise,
its neighboring obligations and the 112-row reconciliation. Their unchanged
historical 107-row requirement reference is
`edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
All original 107 obligations and all **112** current rows remain intact.
The exact initial C2 prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; no new source base is selected.

| Input | Ordinary content identity and inspection |
| --- | --- |
| `book-source/chapter02.txt` | 28,337 bytes / 562 LF lines; SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`. Read order convention 1–29, ordinary sorter 98–126 and exercises 508–542. Control-character extraction artifacts are not treated as new comparison operators. |
| `book-source/Sorting.thy` | 14,846 bytes / 435 lines; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. Read header 1–8 and ordinary quicksort 325–345; scoped source-name search. |
| `conaled/Applications/Selection/ThreeWay.lean` | 10,489 bytes / 226 lines; SHA-256 `bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52`. Complete source read, including the partition laws and separate selector. |
| `conaled/Applications/Selection/Rank.lean` | 3,713 bytes / 91 lines; SHA-256 `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965`. Narrow source read of `ordered` and its permutation/pairwise interfaces at 52–61. |
| `fdsa-control/reviews/chapter02-requirements.md` | 12,034 bytes / 189 lines; SHA-256 `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`. Complete frozen requirements read; unchanged. |
| `fdsa-control/research/chapter02-obligations.md` | 42,539 bytes / 391 lines; SHA-256 `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2`. Read 1–40, 227–238 and 352–391; C02-102 and all current rows retain their scope. |
| `fdsa-control/research/chapter02-reuse-plan.md` | 31,586 bytes / 346 lines; SHA-256 `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a`. Read 1–31, 44–59, 81–103, 277–296 and 310–325; historical planning remains distinct from acceptance. |
| `fdsa-control/research/quicksort-three-way-source-readiness.md` | 21,439 bytes / 324 lines; SHA-256 `d555fa3519e4f2eed6870f674f50a8bd205e00076291159bc186df1c4ce90946`. Complete stopped report read after the independent case calculations were settled. |
| `fdsa-control/research/quicksort-three-way-api-readiness.md` | 28,341 bytes / 476 lines; SHA-256 `e6b96c915cdeda4be1e3c8c2264624b40b3e05cf2f150c1437fd7d7cc0a4f092`. Complete stopped report read for final interface correspondence; its direct immutable-candidate/library reads are not new compiler evidence. |

The retained book edition is July 27, 2026, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The retained Isabelle revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
Chapter 2 is by Tobias Nipkow and Christian Sternagel; `Sorting.thy` is
attributed to Tobias Nipkow. This case pass reads retained text and source,
not a new remote edition or an Isabelle rebuild. The companion source report
owns the direct PDF/source-provenance correspondence.

The complete stopped source report agrees with the literal tail filters,
one-pivot/whole-equal-block assembly, strict-side-only recursion, order domain
and correctness targets assessed here. Its use of the absent-tail example
follows the independent case communication; that agreement is not a second
independent calculation or a formal proof. No source discrepancy was found.

The complete stopped API report directly inspected XQ01's small
`Applications/Sequences/Partition.lean`, namespace `Sequences.Partition`,
and its preserved Selection adapters. It confirms the partition laws and
tail-length argument used here, plus existing multiset and pairwise interfaces
for the general proof. Its quoted case values came from this independent
calculation; no additional independent execution is inferred. This case pass
did not query Git or independently reopen the saved candidate. The direct
content/order route in Section 5.1 needs neither the complete selector nor
its resource executor; discussing `sorted_partition` as value structure does
not recommend moving or copying another selector-dependent theorem. XQ01's
existing uncompiled/unaccepted status remains unchanged.

All list calculations were settled before the final companion correspondence.
No numeric time formula, random-pivot result, one-pass partition claim, stack
bound or new stability target is introduced. Exercise 2.2, Exercise 2.4,
ordinary quicksort and the later selection resource obligations keep their
separate algorithms and models.

## 7. Handoff limits

No mathematical obstruction has been identified. Actual `q3` implementation,
formal termination, universal correctness and connected Lean examples remain
future Chapter 2 work under its original prerequisite and acceptance sequence.
This report is not source release and does not close C02-102.

The complete final report was read back against the independent calculations,
actual source statements and stopped companion reports. Only retained
source/document reads and this report write were performed. No prior report,
inventory, tracker, project source, ref, index or worktree was changed. No
compiler/checker, project hash helper, cache/process/active-output inspection,
network operation or upload was performed. The ordinary byte/line/SHA-256
identity accompanies the stopped handoff; no formal validation is inferred
from that identity. All writes stop at that handoff.
