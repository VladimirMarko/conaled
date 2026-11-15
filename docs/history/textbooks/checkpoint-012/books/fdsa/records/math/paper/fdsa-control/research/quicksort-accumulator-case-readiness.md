# Chapter 2 Exercise 2.2: independent accumulator quicksort cases

Prepared 2026-11-03 for the existing **C02-101** obligation. This is bounded
mathematical and source-level preparation. It supplies no Lean implementation,
compilation, chapter activation, scope change, final review or acceptance.
Only this report is authored. Chapter 1 remains the active prerequisite and
sole authorized validator; the exact initial Chapter 2 prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847` with its existing integration and
acceptance gates.

## 1. Conclusion and exact source target

The proposed cons-only worker has a direct all-suffix value proof. A compact
set of empty, singleton, all-equal and mixed inputs exposes its essential
behavior when every nonempty-suffix case uses the same deliberately unsorted
suffix `[4,0,2]`. The mixed case independently yields

```text
q2 [2,1,2,3,0] [4,0,2] = [0,1,2,2,3,4,0,2].
```

The final three elements remain in their original order. They are not sorted,
merged with the prefix, reversed or deduplicated. The value specification
does not imply that this whole output is sorted.

The literal Exercise 2.2 is on printed p.28 / PDF p.34, retained
`book-source/chapter02.txt:508–512`. It asks for a two-argument `quicksort2`
that avoids append and accumulates through cons, and for the universal law

```text
quicksort2 xs suffix = quicksort xs ++ suffix.
```

It **does not print an accumulator recurrence**. The nested recurrence below
is our proposed exercise solution, already recorded as a proposal in C02-101
and the reuse plan. It is not an existing Lean declaration or a recovered
Isabelle solution. The inspected `Sorting.thy` defines only the ordinary
sorter at lines 327–329 and proves its multiset, set and sortedness facts at
331–339; a scoped search of that retained file finds no `quicksort2`.

The ordinary source convention is fixed by both printed p.16 / PDF p.22 and
the explicit companion symbols: the first element is the pivot, only its
tail is filtered, strict-less elements go left, and equal elements go right.
Both filters retain the order of their selected occurrences. With `q` naming
that actual ordinary recursion mathematically, write

```text
L_x(xs) = filter (fun y => y < x) xs
R_x(xs) = filter (fun y => x ≤ y) xs

q [] = []
q (x :: xs) = q (L_x(xs)) ++ [x] ++ q (R_x(xs))

-- Proposed cons-only solution of Exercise 2.2, not source-supplied code:
q2 [] suffix = suffix
q2 (x :: xs) suffix =
  q2 (L_x(xs)) (x :: q2 (R_x(xs)) suffix)
```

`y ≥ x` means `x ≤ y` here. It must not be replaced by strict `x < y`, a
three-way equality block, or the opposite tie convention used by another
quicksort source. This report assesses the literal two-way source operation.
The ordinary source retains its linear-order domain; the proof observations
below do not select a new comparator or partition framework.

## 2. Independent compact expectations

The following values were first calculated from the displayed recurrences,
then cross-checked with a temporary exact Python calculation. Its worker used
linked cons cells and the same stable tail filters. No script or calculation
artifact was saved outside this report. This is arithmetic/list evidence,
not execution or proof of a future Lean implementation.

| First input `xs` | Suffix | Ordinary `q xs` | Proposed `q2 xs suffix` | Discriminating observation |
| --- | --- | --- | --- | --- |
| `[]` | `[]` | `[]` | `[]` | Total empty base, without selecting a pivot. |
| `[]` | `[4,0,2]` | `[]` | `[4,0,2]` | Base returns the actual suffix unchanged. |
| `[2]` | `[4,0,2]` | `[2]` | `[2,4,0,2]` | Two empty first-argument children and one pivot cons. |
| `[2,2,2]` | `[4,0,2]` | `[2,2,2]` | `[2,2,2,4,0,2]` | Equal copies remain and use the right recursive branch. |
| `[2,1,2,3,0]` | `[4,0,2]` | `[0,1,2,2,3]` | `[0,1,2,2,3,4,0,2]` | Both children are nonempty; the left call consumes the actual right result. |

The chosen suffix is unsorted, overlaps the first input, includes a value
below some sorted-prefix values, and repeats the pivot value. No sortedness,
disjointness or distinctness premise on either list is needed for the suffix
identity. This single suffix tests these boundaries without adding separate
fixture families.

### 2.1 Main mixed trace and actual intermediate suffix

At the root of `[2,1,2,3,0]`, the pivot is `2` and the tail is `[1,2,3,0]`.
Literal filtering gives

```text
L_2([1,2,3,0]) = [1,0]
R_2([1,2,3,0]) = [2,3].
```

In particular the second occurrence of `2` is in the right list. Let
`s = [4,0,2]`. The right child and the actual suffix supplied to the left
child are

```text
q2 [2,3] s = [2,3,4,0,2]
2 :: q2 [2,3] s = [2,2,3,4,0,2].
```

Write the second list as `t`. The remaining recurrence is

```text
q2 [1,0] t
= q2 [0] (1 :: q2 [] t)
= q2 [0] (1 :: t)
= 0 :: 1 :: t
= [0,1,2,2,3,4,0,2].
```

This trace checks the actual dependency between recursive calls. Replacing
the left suffix by the original `s`, by a sorted suffix, or by a value chosen
independently of the right return would not be this operation.

The ordinary recursion independently gives `q [1,0]=[0,1]` and
`q [2,3]=[2,3]`, hence `q [2,1,2,3,0]=[0,1,2,2,3]`. Appending the unchanged
`s` therefore agrees with the independently calculated worker result.

### 2.2 Empty, singleton and equal-key details

The empty case makes no comparison and selects no head or default element.
For a singleton, both filters of its empty tail are empty, so the recurrence
reduces exactly to `q2 [] (2 :: q2 [] s) = 2 :: s`.

For `[2,2,2]`, each less-than child is empty. The successive right first
inputs are `[2,2]`, `[2]` and `[]`; unwinding conses exactly three copies of
`2` onto `s`. This is compatible with duplicates and does not rely on an
average-case distinctness assumption.

Unlabelled duplicate outputs alone cannot distinguish a left-tie sorter from
a right-tie sorter, since equal values are indistinguishable there. The
explicit filter observation in the mixed trace is the operation-identity
check. These cases claim neither a new keyed-payload stability theorem nor
an ordering on arbitrary semantic payloads.

The list/type parameters need no `Inhabited`, globally finite carrier,
chosen element or extra equality decision on complete lists. A payload type
with no elements has only empty lists, so the empty equation still applies
within the ordinary sorter's permitted domain. No nonempty `Empty` fixture
or default value is being assumed.

## 3. General arbitrary-suffix law and the required induction

The intended theorem quantifies the suffix after fixing each input:

```text
for every xs and every suffix, q2 xs suffix = q xs ++ suffix.
```

Use well-founded induction on the length of the **first** argument, with the
suffix generalized. Each filtered child has length at most the tail length,
which is strictly smaller than the length of `x :: xs`. With
`L = L_x(xs)` and `R = R_x(xs)`, the mathematical induction step is

```text
q2 (x :: xs) suffix
  = q2 L (x :: q2 R suffix)                    -- proposed defining equation
  = q L ++ (x :: q2 R suffix)                  -- IH for L at this actual suffix
  = q L ++ (x :: (q R ++ suffix))              -- IH for R at the original suffix
  = (q L ++ [x] ++ q R) ++ suffix             -- cons/append, associativity
  = q (x :: xs) ++ suffix.                    -- ordinary defining equation
```

The nil case is `suffix = [] ++ suffix`. The left induction hypothesis must
hold at `x :: q2 R suffix`; an induction hypothesis restricted to `[]`, or to
only the original suffix, does not supply that statement.

This value calculation uses matching filters in the two actual definitions,
their length bounds, and ordinary list equations. It does not use ordinary
quicksort sortedness or permutation, complementarity of the filters, a bound
on suffix length, suffix sortedness or distinctness. The source comparison
domain and the ordinary sorter's separate correctness obligations remain in
force. Observing the weak premises of this simulation is not a proposal to
add a new public abstraction or to change the source's sort specification.

For future Lean use, the existing plan and companion API preparation identify
the ordinary `List.length_filter_le`, `List.cons_append`, `List.nil_append`
and `List.append_assoc` route. This report does not promise new declaration
names, a generated recursion principle, tactic success or an elaborated
definition. The actual implementation must expose and consume the real
ordinary quicksort and accumulator equations when Chapter 2 is activated.

### 3.1 The decreasing argument is not the combined list length

The mixed trace supplies a small independent termination boundary. Its root
has first-input length `5` and suffix length `3`, so their sum is `8`. The
outer left recursive call has first-input length `2` and actual suffix
length `6`, also summing to `8`. Thus the sum of both argument lengths need
not decrease, while the first-input length strictly decreases from `5` to
`2`. The right first-input length is also `2`.

This is a termination-measure observation, not a resource counter. The suffix
may grow without affecting the valid first-length measure. The right recursive
call sits inside an argument of the left call; an accumulator parameter by
itself therefore establishes neither tail recursion nor constant stack use.

## 4. Counterexamples to incomplete or incorrect formulations

### 4.1 Reversing the nested child order

Consider the incorrect mathematical proposal

```text
wrong [] suffix = suffix
wrong (x :: xs) suffix =
  wrong (R_x(xs)) (x :: wrong (L_x(xs)) suffix).
```

On the same mixed input and suffix, literal evaluation gives

```text
wrong [2,1,2,3,0] [4,0,2] = [3,2,2,1,0,4,0,2].
```

This still preserves the suffix and the multiplicity of input values, but
its prefix differs from `q [2,1,2,3,0]`. The selected case therefore detects
incorrect recursive order; a permutation theorem or base case alone would
not distinguish it.

### 4.2 Empty-suffix correctness is too weak

A logical countermodel to an incomplete specification is

```text
b [] suffix = suffix
b (x :: xs) suffix = q (x :: xs).
```

It satisfies both `b [] suffix = suffix` for every suffix and
`b xs [] = q xs` for every input. Yet the mixed nonempty-suffix case returns
only `[0,1,2,2,3]`, omitting `[4,0,2]`. Thus a correct base equation plus the
empty-suffix specialization does not prove Exercise 2.2. This countermodel is
not proposed as an implementation and does not claim to satisfy the nested
worker recurrence.

### 4.3 A value identity alone does not certify append-free implementation

Defining `q2_by_append xs suffix := q xs ++ suffix` would satisfy the target
value law immediately and pass every extensional case in this report. It
would fail the exercise's actual implementation restriction. If the future
worker uses the proposal assessed here, its body must implement those nested
recursive cons calls, without append or delegation to the ordinary sorter.
This assessment does not freeze the proposal as the only possible solution.

Append is appropriate in the theorem statement and proof. Even equivalent
recursive value equations cannot, on their own, certify that an underlying
implementation contains no append. Checking the actual future body is a
necessary source-level connection, separate from the mathematical value law.
No runtime, allocation or numerical work claim is inferred from syntax here.

### 4.4 Sorting the entire result is not the target

The required mixed result contains the descending adjacent pair `4,0` in its
unchanged suffix. Hence unrestricted `Sorted (q2 xs suffix)` is false. Even
a sorted suffix would also need an appropriate cross-boundary order to make
the entire concatenation sorted. The source's pairwise-append law explains
that boundary; no new sorted-suffix theorem is required for this exercise.

After ordinary quicksort correctness, the empty-suffix specialization is
sorted, and content preservation for a general suffix concerns `xs ++ suffix`,
not `xs` alone. Those are consequences of the universal law plus the ordinary
sorter's results, not replacements for implementing the worker or proving
its all-suffix identity.

## 5. Connections and preserved limits

The future connected cases should call the actual worker and its universal
correspondence, retaining the table's independent expected lists. The mixed
case should also expose the actual source filters/right result/left suffix,
because equal final sorted values can hide a different recursion. These are
meaningful observations of one exercise solution, not a per-helper test quota
or a new acceptance loop.

The ordinary quicksort implementation and source correctness C02-017–023
remain prerequisite Chapter 2 work. The existing reuse plan proposes an
ordinary sorting module, but this report selects no new file, public API,
base, worktree or shared component. A separate accumulator framework is not
needed to express this recurrence or its proof.

The full average-input proof plan and conditional-mean preparation concern
the actual ordinary execution on distinct-key inputs, with separate random
pivot and append-work qualifications. They are not evidence for a cost law
of `q2`. In particular their AFP comparison convention on the distinct domain
cannot silently replace the book's equal-right convention in these cases.

Exercise 2.3's three-way partitioning, Exercise 2.4's supplied time function,
the literal two-append work bridge, and the merge/tail-merge/difference-list
obligations remain separate. Exercise 2.2 asks for no displayed accumulator
time formula. Its motivation does not authorize an invented counter, a
linear-time claim, a stack claim, or a transfer of counts through the append
associativity used in the value proof.

The unchanged frozen Chapter 2 requirements use their historical 107-row
inventory, identity `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
The current inventory retains those rows and adds C02-108–112 to clarify
already-required C02-088 operational work. All **112** current obligations,
including C02-101 and the original initial prefix, remain intact. This
readiness report discharges none of them and changes no gate.

## 6. Inspected inputs and correspondence

All reads were of retained local files. Project-context reads used the pinned
Nix environment. Content identities below are ordinary SHA-256 values, not
outputs from a project verification or hash helper. Line references for the
reading copy count LF-separated physical lines; its extraction contains
control characters, whose comparison symbols were checked against the theory.

| Retained input | Exact identity and read extent |
| --- | --- |
| `fdsa-control/REQUEST.md` | 4,606 bytes / 80 lines; SHA-256 `b8968174e0f49888d519ae0069ac75ceb8b6b0916d69aa99c5033ef31a3b7c2c`; complete governing request read. |
| `book-source/chapter02.txt` | 28,337 bytes / 562 LF lines; SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`; order assumptions 1–28, ordinary quicksort 94–127, exercise context 504–536 read directly. |
| `book-source/Sorting.thy` | 14,846 bytes / 435 lines; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`; ordinary recurrence/correctness 325–340 read directly and whole-file accumulator-name search scoped. |
| `fdsa-control/reviews/chapter02-requirements.md` | 12,034 bytes / 189 lines; SHA-256 `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`; complete frozen requirements read. |
| `fdsa-control/research/chapter02-obligations.md` | 42,539 bytes / 391 lines; SHA-256 `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2`; current scope, ordinary quicksort, exercises and 112-row reconciliation read at 1–74, 102–114, 221–267 and 352–391. This was a targeted inventory read, not a new whole-chapter review. |
| `fdsa-control/research/chapter02-reuse-plan.md` | 31,586 bytes / 346 lines; SHA-256 `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a`; relevant plan/proof boundaries read at 1–115, 137–182 and 277–346. Its historical 107-row scope and planning anchor are not changed. |
| `fdsa-control/research/quicksort-average-proof-plan.md` | 18,013 bytes / 308 lines; SHA-256 `ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46`; complete plan read, preserving separate value/cost/probability bridges. |
| `fdsa-control/research/quicksort-conditional-mean-preflight.md` | 10,877 bytes / 223 lines; SHA-256 `464af5974d485823b7ecb76b7546ad793ed860fbf947afdb03ef11d91b25b66c`; complete note read; no probability draft or underlying Lean proof is newly assessed here. |
| `fdsa-control/reviews/quicksort-conditional-mean-source-preflight.md` | 3,753 bytes / 65 lines; SHA-256 `a268d4a74db81230a4fdb8b0350f7aaaebc379eb38a2439a18d86c0e0c868b55`; complete existing bounded assessment read, without inheriting it as compiler evidence. |
| `fdsa-control/research/quicksort-accumulator-source-readiness.md` | 18,282 bytes / 294 lines; SHA-256 `ce8c019bfe437bbdb71e5863119469a67c0f0d1a7961a3c0f879566731025eba`; complete stopped companion report read after the independent cases and calculations were settled. |
| `fdsa-control/research/quicksort-accumulator-api-readiness.md` | 21,912 bytes / 341 lines; SHA-256 `aeec34427e96f45ede40f9631a201a443f1eded796abf49a04fd861d17f4572f`; complete stopped API report read for final correspondence. No underlying Lean library or project declaration is newly validated by this case report. |

The primary edition is the retained July 27, 2026 book, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion is Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. This pass read the text/theory
passages directly; the source-readiness report supplies the corresponding
direct PDF reading and complete source notice. No new PDF rendering or remote
retrieval was performed here. Chapter 2 is by Tobias Nipkow and Christian
Sternagel; the theory header attributes its formal source to Tobias Nipkow.
The proposed exercise solution is not attributed to absent companion code.

The stopped source report agrees with the independently derived partition,
nesting, arbitrary-suffix, termination and scope boundaries. Its illustrative
input differs from the mixed fixture chosen here; neither result was used to
infer the other. The complete stopped API report confirms the matching-filter,
all-suffix induction route and ordinary list equations. It records the exact
pinned declarations and cites the independently supplied total-length example;
that agreement is not another independent calculation of the example or a
new implementation, frozen theorem name or compilation result.

## 7. Source-level assessment and stop condition

No concrete mathematical or source-convention obstruction was found. The
remaining C02-101 work is the actual cons-only implementation, the universal
proof against the actual ordinary sorter, and the connected observations,
followed by the existing chapter validation and review gates. All are future
work after the prerequisite sequencing; this note supplies no accepted Lean
claim, theorem type or computational validation.

The complete report was read back against its stated inputs and independently
calculated expectations. Only authorized retained-document/source reads,
ordinary temporary calculations and this report write were performed. No
project source, inventory, earlier report, ref, index or worktree was changed.
No compiler/checker, project hash helper, active-output/cache inspection,
remote action or upload was performed. The sole written artifact is this
report; authoring stops at the final ordinary byte/line/SHA-256 handoff to the
coordinator.
