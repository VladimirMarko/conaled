# Chapter 2 mergesort: source and cost readiness

Prepared 2026-11-02. **Bounded read-only preparation, not implementation,
validation, either final review axis, or chapter acceptance.** Chapter 1 remains
the strict sequential prerequisite; gate 80227 is unchanged. All shared drafts
and chapter obligations remain unaccepted. This note changes no earlier plan,
inventory, requirement, ticket, source, reference, or cache.

## 1. Evidence and unchanged scope

Read in full: `mergesort-proof-plan.md` (451 lines),
`chapter02-reuse-plan.md` (346 lines), and
`../reviews/chapter02-requirements.md` (189 lines). Read the relevant current
inventory rows C02-025–088 and C02-104–112, and the explicit Chapter 2
clarification in `scope-reconciliation.md`, lines 53–85. The separate
`mergesort-value-api-readiness.md` owns the detailed value, stability and
termination API assessment; this note concentrates on source observations and
their cost proofs.

The frozen requirements retain their historical **107-row** inventory snapshot.
The current inventory has **112 rows**: C02-108–112 clarify the already-required
natural-sort claims about sorted input, repeated append, builder construction,
builder invocation and actual scanner work. Both records must be read together.
The frozen requirements digest remains
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`;
the historical inventory digest remains
`edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
These are retained identities, not newly computed hashes. No scope is dropped
because the old reuse plan numbers only 107 rows.

Primary evidence inspected, using existing local reading copies:

| Evidence | Exact relevant location and role |
|---|---|
| July 27, 2026 FDSA PDF | Printed pp. 17–21, 25, 29; `book-source/chapter02.txt`, lines 129–277 and 539–564. Page 17 asserts the general `O(n lg n)` guarantee; pp. 18–19 prove the simpler power-of-two comparison bound. Exercises 2.5–2.7 retain their actual algorithms and stated scope. PDF SHA-256: `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Isabelle `Sorting.thy` | `book-source/Sorting.thy`, lines 77–215 for merge/top-down values and comparisons; 217–324 for bottom-up sorting. Mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, path `src/HOL/Data_Structures/Sorting.thy`; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. |
| AFP `Natural_Mergesort.thy` | Lines 9–40: general pass bound, preservation of total run length, and general merge-all ceiling-log bound. This is the separate Efficient-Mergesort archive dated 2026-10-26, not a theory at the Isabelle mirror revision. Theory SHA-256 `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`; archive SHA-256 `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`. |
| Isabelle `Time_Functions.thy` and Appendix B.1 | Entire saved theory read; append lines 38–40, length 49–58, map/filter 63–93, take/drop 103–110. Printed pp. 347–348 give the corresponding recursive-call model. These supply a different observation from the sorting comparison counters. |
| Lean 4.35.0 list-sort sources | Saved `LeanListSort-{Basic,Lemmas,Impl}.lean` at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; `splitInTwo_fst/snd` at Lemmas lines 44/48 and `mergeSort_append` at 283–305. The ordinary sort splits ceiling-left. Runtime implementation equalities are value statements. |
| Mathlib | Pin `56a005855ea17e0b0958f73ec801ae140b0a1679`, actual files under `conaled-permutation-placement/.lake/packages/mathlib/Mathlib/`; exact log/ceiling/asymptotic declarations below. |
| Saved conaled interfaces | Read `conaled-insertion-costs/Applications/Resources/ListCalls.lean`, `Examples/ListLibrary.lean`, `CallCount.lean`, the relevant `Measured.lean` and `SymmetricCosts.lean` definitions, and `Growth.lean`. These are inspected source contracts, not newly validated or accepted dependencies. |

The official PDF and later Isabelle/AFP pins are distinct evidence. Their
dates do not establish that the archive is the exact build used for the July
manuscript. Existing provenance and license records remain authoritative;
this task downloaded nothing and copied no manuscript into a deliverable.

## 2. Literal algorithm and observation

Write `n = xs.length`, `a = n / 2`, `ys = xs.take a`, `zs = xs.drop a`.
The source sorter returns `xs` for `n ≤ 1`; otherwise it recursively sorts
these **contiguous floor-left** halves and merges the returned lists. Merge
takes the left head when `x ≤ y`. Its comparison observation is

```text
CM [] ys = 0;       CM xs [] = 0
CM (x::xs) (y::ys) = 1 +
  if cmp x y then CM xs (y::ys) else CM (x::xs) ys
CS xs = 0                                      if n ≤ 1
CS xs = CS ys + CS zs + CM (M ys) (M zs)        otherwise.
```

`Sorting.thy` explicitly introduces these as element-comparison counts
(lines 147–164). They are **hand-written** `C_merge`/`C_msort` functions, not
the result of `time_fun merge` or `time_fun msort`. The theory does invoke
`time_fun` for insertion earlier, and imports `Time_Commands`; that fact does
not make all later cost functions use the insertion tariff.

`C_msort` binds the two halves before its base test and mentions the separate
value sorter inside the counter. Those are analytical dependencies. Charging
the execution of this counter program would count a different computation.
A connected measured sorter must sort each actual half, pass those measured
results' **values** to the measured merge, and then prove both value erasure
and equality to `CS`. It must not compute an independently chosen sorted list
and pair it with an unrelated recursive number.

The existing `Measured` pair/bind operations suffice. Unit comparison work
occurs only in the nonempty/nonempty merge branch; recursive merge entries,
sort entries, length/take/drop, cons and base cases have no additional charge
in this model. `CallCount.tick` may express a unit charge, but applying it at
every recursive entry would change the requested theorem. A generic Boolean
comparator can support the recurrence and its size upper bounds without an
order law. Sortedness, stable key order and correspondence to the source
comparison separately require the appropriate lawful comparator assumptions.

For `n ≥ 2`, prove once that `a + (n-a) = n`,
`1 ≤ a ≤ n-a ≤ a+1`, and both lengths are strictly below `n`.
The guard matters: at `n = 1`, the right half has length one and cannot be
used as a decreasing recursive call. The empty case is also a base case,
not a call on two empty halves.

The pinned standard split uses `(n+1)/2` on the left. Its
`List.mergeSort_append l₁ l₂ h₁ h₂` requires
`h₁ : l₂.length ≤ l₁.length` and
`h₂ : l₁.length ≤ l₂.length+1`; it does not supply the source odd floor-left
recurrence. Stable output equality, when proved under its proper hypotheses,
does not transport comparison counts between these recursion trees.

## 3. What the saved list-resource interfaces do and do not discharge

`ListLibrary` supplies ordinary list value observations, including
`List.take_append_drop`. It does not instrument a sort.
`ListCalls.takeRun/dropRun` are the two value projections of the saved
`SymmetricCosts.splitRun`, retaining that execution's cost. Their inspected source
equations are exactly the Appendix B take/drop recurrence under this declared
invocation model; this does not assert how Lean's compiler implements the
library list operations.

| Existing declaration | Inspected source contract |
|---|---|
| `SymmetricCosts.lengthRun_exact xs` | `(xs.length, xs.length + 1)` |
| `ListCalls.takeRun_exact k xs` | `(xs.take k, min k xs.length + 1)` |
| `ListCalls.dropRun_exact k xs` | `(xs.drop k, min k xs.length + 1)` |
| `ListCalls.take_drop_separate k xs` | Two separately sequenced calls on the original `xs` return the fused split's pair and pay twice its work. No sharing or common-subexpression elimination is inferred. |

If a later, explicitly separate full-call model instruments the literal
recursive sort branch, length plus the two separate half traversals contribute
`(n+1) + (a+1) + (a+1) = n + 2*a + 3`. This is only that preprocessing
subcost: it excludes sort-entry, comparison, merge and other separately chosen
charges. The base branch executes length but not take/drop in the literal
value algorithm. A fused split has the same pair of values and a different
cost; substituting it requires its own implementation correspondence.

That optional full-call sort extension is unnecessary for Lemma 2.4's
comparison theorem. This does **not** make C02-109–112 optional: those rows
retain separate, expressly asserted natural-run/builder operational claims.
Their declared append, creation and invocation observations must remain
separate from `CM`, `CS`, `C_merge_adj` and `C_merge_all`.

## 4. Remaining comparison proof chain and all-length asymptotics

The retained plan's proof chain is sound at the mathematical level:

1. Establish the actual measured merge recurrence, value erasure, and
   `CM xs ys ≤ xs.length + ys.length`. The source bound is deliberately
   loose, includes empty inputs, and needs neither sortedness nor distinctness.
2. Define the decreasing floor-left sorter and prove its value/length laws.
   Sequence its measured children and measured merge; prove exact agreement
   with `CS` before applying size inequalities to the actual returned lists.
3. Obtain `CS xs ≤ CS ys + CS zs + n` on the recursive branch. Strong induction
   gives the proposed all-length bound `CS xs ≤ n * Nat.clog 2 n`.
   Put `q = n-a = (n+1)/2`; both child ceiling logs are at most `clog 2 q`,
   and `clog 2 n = clog 2 q + 1` for `n ≥ 2`.
4. Specialize `n = 2^k` using `Nat.clog_pow`. This recovers the printed
   `k * 2^k` theorem, including `k=0` (a singleton), and then its real
   `n * log₂ n` rendering. The empty list is covered separately; it is not
   represented by a natural power of two.

The exact available Nat APIs are `Nat.clog_of_right_le_one hn b`
(`Data/Nat/Log.lean:351`), `Nat.clog_of_two_le hb hn` (412),
`Nat.clog_pow b k hb` (432), and `Nat.clog_mono_right b h` (444).
The two-le recurrence uses `(n+b-1)/b`; simplifying it at base two and
bridging `n-n/2 = (n+1)/2` remain ordinary arithmetic proof steps.

**Readiness clarification:** the general guarantee on printed p. 17 is not
proved merely by a bound on lengths `2^k`. The proposed all-length bound gives
a short explicit completion, without a new recurrence framework or a stronger
worst-case lower bound. The exact pinned real APIs are:

| Declaration | Inspected statement / use |
|---|---|
| `Real.natCeil_logb_natCast (b n : ℕ)` | `⌈Real.logb b n⌉₊ = Nat.clog b n`; `Analysis/SpecialFunctions/Log/Base.lean:412`. No premises, because the functions are totalized. |
| `Nat.ceil_lt_add_one (ha : 0 ≤ x)` | `(⌈x⌉₊ : ℝ) < x + 1`, specialized to reals; `Algebra/Order/Floor/Semiring.lean:357`. Its nonnegativity premise must be supplied. |
| `Real.logb_nonneg hb hx` | Under `hb : 1 < b`, `hx : 1 ≤ x`, concludes `0 ≤ logb b x`; `Base.lean:237`, within the `OneLtB` section. |
| `Real.logb_le_logb_of_le hb hpos hxy` | Under `1 < b`, `0 < x`, `x ≤ y`, concludes `logb b x ≤ logb b y`; `Base.lean:194`. |
| `Real.logb_self_eq_one hb` | `logb b b = 1` when `1 < b`; `Base.lean:65`. |
| `Asymptotics.isBigO_iff` | `f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`; `Analysis/Asymptotics/Defs.lean:96`. |

For `n ≥ 2`, cast the natural bound to reals. The log lemmas give
`1 ≤ logb 2 n`; the natural-ceiling equality and strict ceiling estimate give

```text
(Nat.clog 2 n : ℝ) < logb 2 n + 1 ≤ 2 * logb 2 n.
(CS xs : ℝ) ≤ 2 * n * logb 2 n.
```

Then `Filter.eventually_atTop` with threshold two and `isBigO_iff` with
constant two packages the asymptotic consequence. Nonnegative casts/logs
justify norm simplification. The comparison estimate is uniform over all
lists of that length; any length-indexed family inherits it. A new maximum
over all payload lists, finite payload type, or worst-input enumeration is
unnecessary. `Resources.isBigO_of_nat_bound` is also available for the
intermediate natural `n * clog 2 n` comparison; the final real-log target can
use the ordinary Mathlib interface directly.

This does not remove the power-of-two premise from the printed *unrounded*
theorem by fiat. It also does not assert an exact worst-case formula, a
matching lower `Θ` bound, or machine time. The actual recurrence, its resource
erasure, the all-length induction, casts and final asymptotic application
still require Lean implementation and validation.

## 5. Bottom-up and exercise obligations that cannot be inherited by name

For C02-040–057, preserve the actual adjacent-pair pass and its odd leftover,
then recurse on the **produced** run list. With `r = xss.length` and
`N = (xss.flatten).length`, the relevant facts are:

- Pass length is `ceil(r/2)`; it is strictly less than `r` for `r ≥ 2`.
- Total payload length is preserved. A pass costs at most `N`, independently
  of run sortedness, uniform sizes or evenness.
- Empty and singleton outer lists cost zero comparisons. A long singleton
  run is returned without a merge. Many empty inner lists can have `N=0`
  and zero comparison work despite nonzero structural traversal work.
- Uniform doubling of run size needs the stated even outer-length premise.
  Three singleton runs produce run lengths two and one, not two and two.
- The printed bound `m*k*2^k` for `2^k` runs of length `m` permits `m=0`;
  ordinary bottom-up sort then specializes to `m=1`.

The general `N * ceil(log₂ r)` result needed by C02-073–076 is in the separate
AFP `Natural_Mergesort.thy`, not the pinned `Sorting.thy` proof. Its source
theorem uses real logarithm and an integer ceiling with casts. The intended
natural `N * Nat.clog 2 r` form has convenient zero/singleton bases, but its
source correspondence still needs the ceiling/cast bridge. It follows from
the same total-length preservation, pass bound and ceiling-halving recurrence;
an additional sorting algorithm or a second logarithm library is unnecessary.

**Exercise 2.5 / C02-104.** The requested `halve` traverses once and alternates
elements into accumulating piles. The source example is
`halve [2,3,4] ([0],[1]) = ([4,2,0],[3,1])`.
These are reversed, noncontiguous piles, not `take`/`drop` halves, even when
their lengths match a standard balanced split. Prove its arbitrary-accumulator
content/length laws and decreasing recursive lengths; keep the explicit
empty/singleton sort bases. The exercise requires that actual one-pass
implementation, termination, multiset preservation and sortedness. It does
not state a separate numerical time formula, and different legitimate
per-element/per-pair implementations need not have identical entry counts.
Neither a numeric formula nor stability of these alternating piles should be
invented as an additional exercise obligation.

**Exercise 2.6 / C02-105–106.** The source permits a different order of produced
runs and explicitly prohibits append in the tail-recursive pass. For the
natural illustrative realization

```text
ma2 acc [] = acc
ma2 acc [xs] = xs :: acc
ma2 acc (xs::ys::rest) = ma2 (merge xs ys :: acc) rest,
```

the pass comparison count equals the ordinary adjacent pass's count, since
the old accumulator is not merged. The arbitrary-accumulator value laws add
its payload multiset and its outer length. Recursive merge-all uses an empty
accumulator, so the strict run-count decrease applies; arbitrary accumulator
growth is not a decreasing measure for the repeated algorithm.

**Exact pass equality does not imply exact total-sort count equality.** On
`[[0],[0],[0]]`, ordinary merging first produces `[[0,0],[0]]` at cost one,
then costs two more comparisons. The displayed prepending variant produces
`[[0],[0,0]]` at cost one, then costs one more: totals **3 versus 2** under the
same left-on-equality comparison rule. The altered next-pass operands explain
the difference. Both have the same general `N * clog 2 r` upper-bound route.
These are hand derivations of this explicit illustrative implementation,
not an assertion that the exercise uniquely prescribes that recurrence.
Tagged equal payloads also show why this reversal does not automatically
inherit keyed stability. Comparison-only costs cannot detect an illicit
append traversal of an outer list whose inner lists are all empty; retain
the requested append-free implementation as a separate source property.

**Exercise 2.7 / C02-107.** A selected source-faithful floor-left sorter can
supply the required keyed stable implementation. It does not require every
alternating-pile or reversed-pass variant to be stable. The companion value
note supplies the actual existing stable-filter APIs and their order premises;
those semantic results alone do not transfer resource observations.

## 6. Small connected cases and smallest remaining work

No enumeration was run. These independent recurrence calculations retain the
important boundaries and should connect to the eventual public execution and
resource theorems:

| Actual case | Expected observation and purpose |
|---|---|
| Empty or singleton top-down input | Return the input and comparison count zero; no recursive split call. |
| Merge with either empty input | Count zero for an arbitrary other list, including a long one. |
| Source sort `[0,1,2]` / `[2,1,0]` | Counts two / three. Standard ceiling-left recursion gives three / two. Equal values do not identify costs. |
| Merge `[0,0]` with `[0]`, then the swapped inputs | Counts two and one under left ties, despite the same unlabelled output list. |
| Three equal singleton runs | Per-pass agreement but total ordinary/prepending counts three/two, as above. |
| Several empty runs; an odd run list; a singleton nonempty run | Zero payload comparison budget; leftover preservation; zero single-run merge work, respectively. |
| Nonempty-accumulator `halve` source example | Detect alternating accumulation and reversed piles rather than contiguous splitting. |
| Equal keyed records spanning the actual floor split | Connect selected stable value theorem to distinct payload order, without changing its comparison tariff. |

The smallest implementation sequence remains the retained plan's: ordinary
floor-left value/termination laws using existing merge APIs; actual measured
merge and sort with erasure and exact counter equations; comparison upper
bounds and the short all-length/real-log completion; then actual adjacent and
repeated passes with their total-length and run-count invariants, followed by
the specified exercise variants. The companion value note retains the genuine
merge-converse gap (each input must be a sublist of the merged result) rather
than confusing it with `sublist_mergeSort`.

No false `Sorting.thy` comparison recurrence was found in this bounded read.
The concrete readiness cautions are the analytic-counter/execution distinction,
the odd split mismatch, the explicit all-length asymptotic bridge, the separate
AFP provenance/general bound, and the failure of per-pass count equality to
transfer through changed run order. Existing ordinary lists, measured binds,
stable-filter lemmas and Mathlib logs suffice; this work does not propose a
new sorting hierarchy, resource framework, translator, or mandatory auxiliary
statistic. All remaining original Chapter 2 obligations, including the later
natural-run operational clarifications, stay mandatory and queued.

Only this report was written. No Lean/Lake/compiler/checker/hash helper, Git,
remote operation, cache modification, gate change, or acceptance action ran.
