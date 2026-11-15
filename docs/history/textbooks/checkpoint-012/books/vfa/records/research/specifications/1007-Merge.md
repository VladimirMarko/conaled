# Local #1007 — VFA Merge: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1006 Selection is accepted.**
The predecessor chain remains Perm → Sort → Multiset → BagPerm → Selection → Merge.
This is bounded preparation inside the existing workflow. No new Lean file,
compiler run, algorithm implementation, chapter acceptance, ticket update, or
candidate change is authorized or supplied by this plan. Proposed APIs remain
pending elaboration and ordinary chapter review.

## Source and baseline

- VFA 2.1, release header `2026-08-24 10:11`, Coq/Rocq 9.0.0 or later:
  [Merge](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Merge.html).
- Complete inspected source: `reference/vfa/vfa/Merge.v`, 526 lines,
  17,839 bytes, SHA-256 `090c5afc3a95750336b8b57ed2169b8d77c790266f231bf096be55761c20378b`.
- `../source/Merge.inventory.json`: **17 records; six exercises**, four standard
  and two advanced. Records include one aborted true claim with an inadequate
  induction attempt and one transparent well-founded mergesort definition.
- Restore the pinned archive using `../source/SOURCE-RECOVERY.md` and its hash
  verification/changed-source policy. Archive SHA-256:
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Preserve `../source/VFA-LICENSE.txt`; do not bundle the book into the project.
- Inspected checkout: `1da24c77d10fe03296dbf117e4249283139f5021`, Lean 4.35.0,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its full candidate gate was
  ongoing. Record the actual accepted #1006 baseline before implementing Merge.

Use `1003-Sort.md`, `1004-1005-Multiplicity-plan.md`, `1006-Selection.md`,
`../source/SORTING-STABILITY-BOUNDARIES.md`, and
`../source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md`. The shared specification
draft is checked preparation; rely on the actual accepted predecessor APIs,
not an assertion that a staged proof has already closed chapter coverage.

## Reuse with exact boundaries

| Existing declaration and local source | Verified role / remaining source bridge |
| --- | --- |
| `sourceMerge` in `Applications/Sorting/SourceMerge.lean` | Direct nil/cons, left-tie merge with a sum-of-lengths termination measure; requires only `LE` and `DecidableLE`. It already expresses the source merge primitive's value recurrence. |
| `sourceMerge_eq_merge` in the same module | All-input equality to `List.merge xs ys (fun x y => decide (x ≤ y))`; no sortedness or order-law premise. It supplies a value bridge, not measured-cost correspondence. |
| `mergeBy_source` in the same module | Exact key-comparison bridge using local `LE α := key a ≤ key b` and its decision instance, requiring `LE κ`/`DecidableLE κ`. No payload order/equality is needed. |
| `mergeBy_perm` in `Applications/Sorting/Merge.lean` | `(mergeBy key xs ys).Perm (xs ++ ys)` without sortedness or order laws. Reverse orientation for the source exercise. |
| `mergeBy_sorted` in the same module | Under `LE κ`, `DecidableLE κ`, `Std.IsLinearPreorder κ`, two KeySorted inputs give KeySorted output. Transport through the source adjacent-sortedness and exact merge bridges. |
| `merge_sorted_compatible_on`, `merge_sorted_compatible` | Existing weaker comparator APIs use `Std.IsPreorder κ` and, on relevant cross-input pairs or globally, true-branch `key a ≤ key b` and false-branch `key b ≤ key a`. Reuse if needed; no new comparator framework. |
| `mergeBy_filter`, `mergeBy_stable`, `mergeBy_spec` | Stability is relative to **`xs ++ ys`**, for sorted blocks. The first two require key preorder/decidable order and `DecidableEq κ`; `mergeBy_spec` uses a linear preorder. This does not supply stability relative to the original alternated input. |
| `KeySorted`, `Stable`, `StableSort` in `Applications/Sorting/Stable.lean` | Reuse the independent observations. Generic source mergesort has ordinary permutation/order correctness, not a universal StableSort result. |
| `sortOn`, `sortOn_correct`, `sortOn_spec`, `sortOn_sorted_fixed`, `insertionOn_spec` in `Applications/Sorting/Sort.lean` | Existing standard sorting clients. `sortOn` uses `List.mergeSort` and contiguous `splitInTwo`/take/drop; do not replace the source's alternating algorithm with it. |
| `List.twoStepInduction`, Mathlib `Data/List/Induction.lean:145–154` | Nil/singleton/two-cons induction, polymorphic in a `Sort*` motive. Its step also receives `∀ y, motive (y::xs)`; adapt to the source schema by ignoring that extra hypothesis, and demonstrate the actual split proof. |
| `List.Perm.eq_of_pairwise'`, Mathlib `Data/List/Sort.lean:300–305` | Nat output agreement under antisymmetry of the element relation. It does not identify differently ordered equal-key records. |
| `Resources.Measured`, `bind`, `bind_erases`, `erasureSquare`, reweighting laws; `Resources.isBigO_of_nat_bound` | Instrument and erase the actual source recursion; then transport established Nat count bounds to standard asymptotics. No new resource framework is needed. |
| `Nat.clog_le_iff_le_pow`, `Nat.le_pow_clog`, Mathlib `Data/Nat/Log.lean:386,440` | For `1 < b`, respectively `clog b x ≤ y ↔ x ≤ b^y` and `x ≤ b^(clog b x)`. These give an existing natural ceiling-log interface for a proved binary recursion-height bound. |

Suggested extension: a small `Applications/Sorting/SourceMergeSort.lean`
containing alternating split, its induction/length/permutation facts, and the
source well-founded mergesort, reusing `SourceMerge.lean`. Put connected clients
in an appropriate Examples module and source instrumentation in a resource
module only if useful. Do not duplicate standard merge theory, introduce a
second generic sorter structure, or change the existing stable-sort contract.

## Required recurrences, termination, and observations

Write `A` for a **proposed** alternating split and `M` for the source mergesort;
`sourceMerge` below is the existing operation, specialized to Nat or pulled-back
key comparison. Preserve the equations, not just the final Nat sorted output.

```text
A [] = ([],[])
A [x] = ([x],[])
A (a :: b :: xs) = let (l,r) = A xs; (a :: l, b :: r)
sourceMerge [] ys = ys; sourceMerge xs [] = xs
sourceMerge (a :: xs) (b :: ys) =
  if a ≤ b then a :: sourceMerge xs (b :: ys)
           else b :: sourceMerge (a :: xs) ys
M [] = []; M [x] = [x]
M (a :: b :: xs) =
  let (l,r) = A (a :: b :: xs); sourceMerge (M l) (M r)
```

The source's nested local fixpoint for merge (`209–217`) and conaled's
sum-of-lengths recursion have the same displayed value equations. Document
this Lean adaptation and retain the source branch lemmas. It does not imply
equal compiler code, stack use, allocations, or measured cost without an
additional instrumentation bridge.

For `A xs=(l,r)` prove length sum, `l.length=(xs.length+1)/2`,
`r.length=xs.length/2`, and strict decrease of both lengths **when `2≤xs.length`**.
The source only asks for weak bounds; the stronger balanced lengths supply the
actual termination and complexity work. Empty/singleton equations show why the
naive recursion without base cases is not decreasing. Define `M` by the
length measure and expose its equations plus a function-induction interface
for `P input output`; a strong-length induction adapter is also acceptable.
No fuel parameter is present in the source Merge algorithm.

Split is polymorphic without any order or equality assumptions. Merge and sort
definitions, permutation, size, and erasure use executable comparison only.
Sortedness can reuse key `Std.IsLinearPreorder` and the accepted adjacent ↔
Pairwise/KeySorted bridge. Keep all local assumptions explicit rather than
requiring a linear order on records. The source's Nat contract is
`∀ xs, xs.Perm (M xs) ∧ Sort.sorted (M xs)`; counts/multiplicity matter.

## Complete record and exercise obligations

**Every row is pending chapter integration.** `Adj` is the accepted source
Sort adjacent-sortedness presentation. `E` marks a standard exercise; `AEx`
marks an advanced exercise. Existing reusable proofs still need their precise
source-facing connections and meaningful clients.

| Source inventory ID | Exact obligation / proposed treatment |
| --- | --- |
| `Merge.split@47` | Polymorphic alternating `A`, retaining odd/even placement and the singleton-left rule. A take/drop split is a different operation. |
| `Merge.split_len_first_try@63` | Aborted true statement: `A l=(l1,l2) → l1.length≤l.length ∧ l2.length≤l.length`. Cover by the successful theorem and explain the one-step induction mismatch; no admitted “first try” declaration. |
| `Merge.list_ind2_principle@87` | Exact schema for every type and list predicate: nil, singleton, and `(P xs → P (a::b::xs))` imply all lists. Use a proposition/statement adapter to the existing two-step eliminator. |
| `Merge.split_len'@99` | **Assuming that induction schema**, establish both weak split-length bounds. Retain this conditional statement and use its supplied principle; it is not a new axiom. |
| `Merge.list_ind2@118` | Prove the exact schema constructively. A small `List.twoStepInduction` specialization is sufficient; explain the source explicit local proof term and the extra Mathlib hypothesis being ignored. |
| `Merge.split_len@148` | Unconditional weak bounds by supplying the proved induction schema; connect the two-step induction client. |
| `Merge.split_perm@161` **E** | For arbitrary payload type, `A l=(l1,l2) → l.Perm (l1++l2)`; source two-step split recursion, preserving duplicates. |
| `Merge.merge@209` | Reuse existing `sourceMerge`; record exact left-tie branch equations and the nested-fixpoint-to-length-measure adaptation. |
| `Merge.merge2@258` | `x1≤x2 → sourceMerge (x1::r1) (x2::r2) = x1::sourceMerge r1 (x2::r2)`; a source-facing equation consequence, including equality/ties. |
| `Merge.merge_nil_l@286` | `∀ l, sourceMerge [] l = l`; use the actual source primitive, not merely a sorted-input result. |
| `Merge.mergesort@358` | Direct alternating `M`, both base cases, checked strict-length termination, public equations and usable function induction. |
| `Merge.sorted_merge1@461` **E** | `x≤x1 → x≤x2 → Adj (sourceMerge (x1::l1) (x2::l2)) → Adj (x::sourceMerge (x1::l1) (x2::l2))`. **No individual input-sortedness premises.** Prove by the source head branch and adjacent constructor; `mergeBy_sorted` alone does not match these hypotheses. |
| `Merge.sorted_merge@470` **E** | `Adj l1 → Adj l2 → Adj (sourceMerge l1 l2)` through the exact merge bridge and `mergeBy_sorted`, with both adjacent/Pairwise conversions. |
| `Merge.mergesort_sorts@481` **E** | `∀ l, Adj (M l)` via the actual well-founded recursion/induction adapter and sorted-merge result. |
| `Merge.merge_perm@501` **AEx** | `(l1++l2).Perm (sourceMerge l1 l2)` with no sortedness premise; source bridge plus symmetry of `mergeBy_perm` or the underlying list theorem. |
| `Merge.mergesort_perm@509` **AEx** | `∀ l, l.Perm (M l)`, composing split permutation, recursive permutations, append congruence, and merge permutation. |
| `Merge.mergesort_correct@516` | Combine the actual `M` permutation/sortedness claims into the accepted arbitrary-function Sort specification. |

All six exercises are included; the two advanced permutation proofs are not
optional omissions. Source hints favor list/nested induction, and
`mergesort_sorts` starts with function induction. Preserve the explanation and
an actual recursion-induction client. No explicit tactic prohibition applies.
The chapter expressly permits the accepted Multiset/BagPerm characterizations
for permutation proofs (`493–498`); a count route must still recover the exact
permutation theorem, not just equality of membership sets.

## Meaningful commands and failed approaches

| Source command/prose | Required Lean adaptation |
| --- | --- |
| Imports `Perm`, `Sort`, `Recdef` (`3–5`) | Accepted source specification/decision bridges, standard list theory, and Lean well-founded recursion. No Rocq runtime dependency. |
| Aborted split proof (`63–84`), explicit induction term (`118–143`) | Explain why the tail's IH misses a recursion on the tail of the tail. Provide the constructive source-schema adapter and use it for split bounds/permutation. |
| Naive merge recursion discussion (`176–207`), `Print merge` (`234`), local-fix simplification (`236–299`) | Explain the competing structural arguments and source nested fixpoint. Inspect/document the actual Lean definition and demonstrate nil/left/right branch equations; no requirement to reproduce Rocq's diagnostic or local-fix printed syntax. |
| Naive mergesort and missing base cases (`306–356`) | Empty and singleton splitting does not strictly decrease; retain these concrete boundary cases and the corrected measure proof. |
| `Function`, `Defined`, `Check mergesort_equation` (`358–420`) | Executable Lean definition with a proved one-level equation and checked source case. Explain the different transparency/elaboration mechanisms; do not promise a Rocq equation is Lean definitional equality. |
| `Check mergesort_ind` and its displayed type (`423–444`) | Expose or adapt a proved induction principle relating input and output and consuming both split recursive hypotheses. A displayed `#check` without a checked consumer is insufficient. |

## Stability, fixed points, and existing-sort agreement

The source sorts Nat values; tagged-record behavior refers to the explicitly
defined key generalization. For distinct records `A,B,C` all with key 0,
alternating split is `([A,C],[B])`, so the source recurrence gives
`M [A,B,C]=[A,C,B]` and `M [A,C,B]=[A,B,C]`. These remain **pending checked
cases**, independently hand-derived in `SORTING-STABILITY-BOUNDARIES.md`.
They expose failure of equal-key stability, fixing every key-sorted input,
and idempotence for records. Erasing to the Nat key list hides the failure.

`mergeBy_stable` remains correct: its input observation is the concatenation
of its two blocks, here `[A,C,B]`, not `[A,B,C]`. Do not use it to construct a
false `StableSort key originalInput result`. Likewise, `sortOn_sorted_fixed`
and `StableSort.unique` are not proofs of tagged source fixed points/equality.
For Nat outputs, pairwise sortedness, permutation, and antisymmetry do give
agreement with existing `sortOn`/`insertionOn`, and hence Nat fixed-point and
idempotence properties. Equality of mapped key outputs is a valid weaker
record observation. Neither equality establishes recurrence or cost identity.

## Measured work and source-prose obligations

The opening `Merge.v:7–32` claims an O(n log n) algorithmic bound and explains
why linear list splitting does not change it. Make the primitive model explicit:
head comparison has unit cost; a split element visit has unit cost. Arithmetic
representation, compiler execution, and physical allocation are separate.

1. Instrument the actual two-step split. Its independent visit recurrence is
   `V(0)=0`, `V(1)=1`, `V(n+2)=2+V(n)`, so `V(n)=n`; prove erasure and the
   count for the returned pair. Do not charge a constant-time array slice.
2. Instrument the actual merge branches. Comparisons are zero when either
   input is empty, and one plus the selected recursive branch otherwise.
   Prove erasure and the bound `comparisons≤m+n-1` (Nat subtraction), with
   early-exhaustion cases. This is a bound, not an equality for all inputs.
   `sourceMerge_eq_merge` alone says nothing about these observations.
3. Instrument the actual well-founded `M`: base cases perform no split or
   merge comparisons; a larger input executes split, both recursive sorts,
   and merge in the stated order. Retain separate split-visit and comparison
   observations, or an explicit additive weighting. The independent recurrence
   uses `p=(n+1)/2`, `q=n/2`; establish `p+q=n` and both recursive bounds first.
4. Prove by binary-height induction that if `n≤2^k`, each of total split visits
   and total merge comparisons is at most `n*k`. `Nat.le_pow_clog` at base 2
   yields the bound with `k=Nat.clog 2 n`, including n=0 and n=1. This bridge,
   the recurrence proof, and its actual measured erasure are pending work;
   balanced output sizes alone do not prove a cost bound.
5. If calling the result total primitive work, also account for dispatch and
   other constant local work. One simple additional observation counts sort
   calls: one for n=0 and `2*n-1` for n>0, proved from the nonempty balanced
   sublists. Constructor/dispatch costs must be explicitly bounded by these
   charged visits/calls; otherwise label the theorem comparison/visit cost
   only. Weighted counts then give an eventual constant multiple of
   `n * Nat.clog 2 n`. Use `Resources.isBigO_of_nat_bound` for each
   length-indexed input family, or an explicitly defined uniform size bound.
   Explain the ceiling-log convention and small-size cases in the prose.

The opening O(n) auxiliary-space statement describes the usual **imperative
array algorithm**. A Lean list-value/permutation theorem proves neither that
implementation nor heap peak, reuse, GC, or stack costs. Record that scope;
do not silently claim O(n) live Lean storage from a linear split or from
output length. Any extra list allocation/space claim needs an explicit
evaluation, sharing, and liveness model; total constructor requests, peak live
cells, and retained output are distinct. No new heap framework is required
merely to qualify the book's array-context statement accurately. No benchmark
or universal speed comparison is a named exercise in this chapter.

## Checked-case intentions, remaining gaps, and acceptance

- Check odd and even alternating splits, e.g. `[0,1,2,3,4]` goes to
  `([0,2,4],[1,3])`, with public length/permutation results; check empty and
  singleton failure of strict decrease outside its required premise.
- Exercise source merge nil, left, right, and tie branches. For sorted blocks
  `[1,3]` and `[2,4]`, verify output `[1,2,3,4]` and three comparisons; compare
  `[1,2]` with `[3,4]`, whose merge makes only two comparisons. Use the actual
  measured value/count theorems, not unrelated computations on `sortOn`.
- Connect a duplicate-rich Nat sort output (the earlier pi-prefix example is
  reusable) to `mergesort_correct`, contents/count preservation, and agreement
  with an existing sorter. Include empty/singleton/base and nontrivial recursive
  cases; connect the induction/equation API rather than only reducing numerals.
- Check the tagged instability/two-cycle above and the primitive's positive
  stability relative to block concatenation. These cases distinguish two
  correct APIs with different source-input observations.
- Consume the measured erasure through existing `Resources.erasureSquare`
  or ordinary composition, and specialize the size/log bound to a real input
  family. No new per-declaration test quota or synthetic workload is needed.

The concrete gaps are alternating split and its exact induction/size/permutation
facts; the direct well-founded source sort and usable equations/induction;
all source-facing wrappers, especially `sorted_merge1`'s weaker premises;
source instrumentation and a uniform logarithmic-height work proof; and the
connected cases/qualified prose. Existing stable library sorting theorems do
not close those gaps by themselves. Statement review must inspect comparator
branches, tie policy, all equality orientations, permutations with duplicates,
the `n≥2` decrease condition, exact length formulas, and the distinction between
ordinary correctness, stability, value transport, and measured observations.

After #1006 acceptance, use the existing implementation/example-driven loop,
source coverage ledger and independent Standards/Spec review. Integrate public
modules/examples and exhaustive audit roots. Run applicable focused checks
and the ordinary isolated `./check.sh --candidate HEAD` using the pinned Nix
environment/current coordinator-selected workers; retain failures and fixes.
Run `./check.sh --verify-candidate HEAD` immediately before acceptance, then
update local ticket/coverage/review evidence and capture/upload/expose a
durability checkpoint before moving to the next chapter. No admissions, new
proof axioms, unsafe substitutions, or native proof shortcuts are permitted.
This planning assignment starts no separate implementation/review loop.

## Read-only planning identities

The complete chapter/inventory and listed APIs were inspected as source. No
proposed Lean declaration or timing claim was checked by a new compiler run.
Relevant identities for drift checking before implementation:

| Inspected file | SHA-256 |
| --- | --- |
| `../source/Merge.inventory.json` | `9ff8e9c5a08fc8e781b81de5a3c505ac64270ba9746be6a6b109c16ecbc77861` |
| `conaled/Applications/Sorting/SourceMerge.lean` | `bebd8eb2f06d92cc10e6f319c96b7965cdee36ff14c4a8b0b19e1351e8ebeaf2` |
| `conaled/Applications/Sorting/Merge.lean` | `79b35252d0f551b381ef63974497311336ea92a5d118691647825cade12a1338` |
| `conaled/Applications/Sorting/Sort.lean` | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `conaled/Applications/Sorting/Stable.lean` | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| Pinned Mathlib `Data/List/Induction.lean` | `16f7725635c5a3d3614cc3bda36c3a3c7089fbd5a940d1fa61fac42ef29e47b4` |
| Pinned Mathlib `Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |

The predecessor/specification and measured-resource identities are also recorded
in the companion #1006 plan. Recheck changed inputs at chapter start; preserve
the original pinned source hashes and explicit migration rule.
