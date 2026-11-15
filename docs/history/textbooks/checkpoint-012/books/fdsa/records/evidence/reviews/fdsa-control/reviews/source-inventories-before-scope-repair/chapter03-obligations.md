# Chapter 3: Selection — source obligations and reuse

Research date: 2026-11-02. Local ticket: `FDSA-003`.

**State: queued, source inventory only.** This note neither implements Chapter 3
nor claims accepted coverage. Every proposed witness remains subject to a checked
statement review and the repository's build/audit/review gates. Root retains
chapter-order control. This inventory was prepared while Chapter 1 validation ran.

## Pins, provenance, and reading scope

- Book: July 27, 2026 version, Chapter 3, printed pp. 31–44 (PDF pp. 37–50),
  plus Appendix B.1–B.2, pp. 347–348, where the chapter locates its auxiliary
  time functions. PDF URL <https://fdsa-book.net/functional_data_structures_algorithms.pdf>;
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- The chapter's direct source is `src/HOL/Data_Structures/Selection.thy` in
  <https://github.com/isabelle-prover/mirror-isabelle> at
  `f86f290225eebcc52c1ae7dba2e098f405f51c21`, file SHA-256
  `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`.
  It imports `Complex_Main`, `HOL-Library.Time_Functions`, and `Sorting`.
  Its own heading notes overlap with the AFP Median-of-Medians entry; that
  other entry was not substituted for this chapter's source or audited here.
- License: Isabelle's pinned top-level `COPYRIGHT` is BSD-3-Clause. Author
  notice in `Selection.thy` names Manuel Eberl, TU München. Retain notices
  when translating source. Definitions and mathematical obligations below are
  original analytical summaries, not copied book prose.
- Existing conaled code inspected: `Applications/Selection/{Rank,ThreeWay,Consumers}.lean`,
  `Examples/RankSelection.lean`, and `docs/research/adwh-rank-selection.md`,
  at repository baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
  No fresh build of these files is asserted by this research.
- Source-error typography on printed pp. 37, 41, 43 was checked visually
  against locally rendered pages, in addition to text extraction.

The official PDF is mutable. Its page-2 version and full-byte digest identify
the inspected artifact, but no immutable official July-27-2026 PDF URL or
manuscript Git revision was located by this investigation. The 2025 publisher
DOI is a different edition, not a replacement pin. Preserve these mathematical
inventories and immutable theory revisions in checkpoints, without redistributing
the full manuscript in violation of the project's archive policy.

## Conventions and compatibility boundaries

`n = xs.length`; `M xs` denotes the multiset of occurrences. `Nlt xs a` and
`Ngt xs a` count occurrences strictly below and strictly above `a`. `S xs`
means pairwise nondecreasing order. All lists are finite; values have a linear
order, and duplicates remain significant. `ceilNat r` means the nonnegative
natural obtained from the integer ceiling of a real/rational `r`; it is not
floating-point arithmetic. Decimal coefficients 0.2 and 0.7 denote exact 1/5
and 7/10. Division and subtraction in list indices are natural division and
truncated subtraction.

Reuse labels: **R** = relevant existing declaration inspected; **P** = partial
reuse requiring a source/statement/cost bridge; **G** = gap in the integrated
interfaces inspected, not a claim of absence from all Mathlib/Std or archives.
None is a completion mark.

### Existing selection must keep its indexing and failure contract

The book uses zero-based `select k xs`, with correctness restricted to `k<n`.
HOL's list indexing is total but unspecified out of bounds. conaled's public
`selectWith` and `sortSelect` use **one-based** positive ranks and return `Option`;
rank zero and ranks above the length return `none`. Its independent `RankedAt`
predicate is already zero-based. Reuse this architecture and prove an explicit
bridge from book rank `k` to public rank `k+1`; do not change existing APIs or
identify valid rank zero with failure. An `Option` or bounded-index realization
avoids introducing an arbitrary inhabitant for empty Lean types.

`ranked_strict_counts` currently exposes exact strict counts only with `Nodup`.
The book instead needs weak count bounds for **all** inputs, including duplicates.
A bridge from `RankedAt` to the weak-count specification, and its converse, is
missing in the inspected interface. Preserve `RankedAt.map` and `selectWith_map`:
monotone maps need not be injective and can create more ties.

`partition3` currently uses `List.partition` twice, with proved equivalence to
three filters, permutation, membership, length, and strict-size laws. The book's
exact `Tpartition3 = n+1` refers to a different **single-pass recursive code
equation**. Extensional equality does not transport that cost to the two-pass
implementation. A measured source adapter or a proved cost relation is needed.

## Specification and elementary facts: pp. 31–32

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-001 | (3.1): for `k<n`, the selected `a` has `Nlt xs a <= k` and `Ngt xs a < n-k`. The second inequality is strict. | P: `RankedAt` has the required occurrence semantics, but the all-input weak-count equivalence is not exported. Do not add `Nodup`. |
| C03-002 | Theorem 3.1, assumptions (3.2): for `k<n`, any `a,b` satisfying both inequalities in C03-001 are equal. | P: `RankedAt.unique` after a count-specification equivalence. It identifies a value, not an occurrence among ties. |
| C03-003 | Proof step (3.3): if `a<b`, the multiset of entries `<=a` is a submultiset of entries `<b`; complementary `<=a`/`>a` counts sum to `n`. | R/P: standard multiset/filter monotonicity and partition; preserve these exact strict/weak relations in the uniqueness witness. |
| C03-004 | (3.4): `select k xs` is the `k`th element of any correct sorted result. | R/P: `ordered`, `ranked_iff_index`, `sortSelect`; zero/one-based and in-bounds bridges required. Output values may use existing canonical sort rather than a new sorter. |
| C03-005 | Theorem 3.2: C03-004 satisfies C03-001 for `k<n`. Helpers on sorted `ys`: entries `< ys[k]` form a submultiset of `take k ys`; entries `> ys[k]` form a submultiset of `drop (k+1) ys`. | P: sorted indexing and permutation already exposed. Source names `sorted_filter_less_subset_take`, `sorted_filter_greater_subset_drop`, `size_less_than_select`, `size_greater_than_select`. Validity `k<len ys` is required in the helpers. |
| C03-006 | Lemma 3.3, (3.5): equal input multisets imply equal sorted lists. | R: Chapter 2 pairwise-permutation uniqueness and `ordered_perm`/`ordered_pairwise`. |
| C03-007 | Lemma 3.3, (3.6): equal input multisets imply equal selections at the same index. Source `select_mset_cong`. | P: derive via C03-006. The book's totalized formula also applies out of bounds; an Option bridge can state the full all-index equality without arbitrary values. |
| C03-008 | Supporting facts: valid selection belongs to the input; on nonempty input `select 0 xs` is its minimum. Source `select_in_set`, `select_0`, `Min_set_sorted`, `hd_sort`. | R/P: membership follows `RankedAt`/valid sorted indexing. A tail-recursive minimum implementation is separately required by Exercise 3.1. |

## 3.1 Divide-and-conquer recurrence: pp. 34–36

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-009 | (3.8): if every value of `xs` is at most every value of `ys`, `sort (xs++ys) = sort xs ++ sort ys`. Inputs need not themselves be sorted. | P: existing sorting contracts and uniqueness suffice; source `sort_append`. |
| C03-010 | Lemma 3.4, (3.7): under the cross-list bound and `k<len xs+len ys`, selection from concatenation selects `k` in `xs` when `k<len xs`, else `k-len xs` in `ys`. | P: C03-009 plus standard append indexing; source `select_append` and `select_append'`. |
| C03-011 | `partition3 p xs` means the `<p`, `=p`, `>p` filters; it preserves the input multiset and total length. | R: `partition3_eq_filters`, `partition3_perm`, `partition_lengths`, and three membership iff results. |
| C03-012 | Theorem 3.5: for **arbitrary** pivot `p` and valid `k`, select from lower block if `k<len ls`, return `p` if `k<len ls+len es`, otherwise select rank `k-len ls-len es` in `gs`. | P: `sorted_partition`, `dispatch_value`. Existing dispatch indexes the equal block rather than directly returning `p`; prove equality to `some p` on the valid middle branch. No pivot-membership assumption belongs to this semantic theorem. |
| C03-013 | Termination boundary: a pivot in the input makes both strict blocks smaller; arbitrary pivots outside the range need not do so. | R: `partition_strict_sizes` and `PivotValid`. Source value recurrence alone does not establish termination. Existing fuel adequacy is useful but does not by itself implement the nested median-of-medians policy. |
| C03-014 | `median xs = select ((n-1)/2) xs`, the lower central occurrence for even positive `n`. On nonempty input it belongs to `xs`; `Nlt xs (median xs) <= (n-1)/2`, `Ngt xs (median xs) <= n/2`. | P: `lowerMedianWith`, odd/even index theorems, and C03-001 bridge. Existing exact-count median results assume `Nodup`; these inequalities do not. Empty input is handled explicitly by Option or a zero-count vacuity statement. |

The random-pivot worst-case, expected-time and tail assertions on p.35 are
**formal coverage obligations**, even though their proofs are cited rather
than developed in this chapter. An earlier version of this inventory
incorrectly classified expectations and tails as external context; the
probabilistic reconciliation below replaces that classification explicitly.
The concrete median-of-medians algorithm and all exercises remain in scope.
The practical comparison and unspecified Introselect hybrid on p.44 are
classified separately; a bibliography entry does not import an entire paper.

## 3.2 Chopping and the median of medians: pp. 36–38

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-015 | `chop 0 xs=[]`; `chop d []=[]`; with positive `d` and nonempty `xs`, prepend `take d xs` to `chop d (drop d xs)`. | G. Reuse any standard chunking only after matching the zero-size behavior and exact chunk boundaries. |
| C03-016 | Termination of `chop` by remaining length for positive chunk size; characterize empty output as `d=0 or xs=[]`. Source `chop_induct'`, `chop_eq_Nil_iff`. | G/P: standard take/drop size facts. |
| C03-017 | Every produced chunk is nonempty and has length at most `d`. `chop_elem_not_Nil`, `length_chop_part_le`. | G. No nonempty assumption on the original input is needed for the vacuous statements. |
| C03-018 | For `d>0`, chunk count is `ceilNat(n/d)`. `length_chop`. | G/P: natural ceiling-division bridge; avoid lossy division in naturals before ceiling. |
| C03-019 | For `d>0`, flattening chunks returns `xs`, their multisets sum to `M xs`, and the union of chunk sets equals `U xs`. (3.9) is the multiset instance at `d=5`. | G. Source `concat_chop`, `sum_msets_chop`, `UN_sets_chop`; ordinary list laws reusable. |
| C03-020 | Useful source-only chunk laws: append commutes with chopping when `d` divides the left length; chopping uniform length-`d` blocks recovers them for `d>0`; the corresponding replicate law. | G/P support: `chop_append`, `chop_replicate_dvd`, `chop_concat`. Needed only if chosen proofs/exercise families use them; not separate additional book algorithms. |
| C03-021 | Define the mathematical pivot `mom xs = median (map median (chop 5 xs))`; on nonempty `xs` it is an input value. | P: existing median/rank consumers and chunk membership can compose, but no integrated median-of-medians constructor was found. This is the specification pivot; the fast algorithm must not compute it by fully sorting all medians. |
| C03-022 | Let `m = ceilNat(n/5)`. For either relation `R` equal to `<` or `>`, partition the chunk multiset into `Y_R` where each chunk median bears `R` to `mom xs`, and its complement `Y_notR`. | G. The complementary relation is selected relative to `R`, not always the numerical `>=`. |
| C03-023 | (3.10) chunk multiset is `Y_R + Y_notR`; (3.11) `m = size Y_R + size Y_notR`. | G/P: standard multiset partition and cardinality. |
| C03-024 | Corrected (3.12): `size Y_R <= m/2` with natural division; hence at most real `m/2`. Source `size_median_of_medians_aux` uses this non-strict bound. | G. The PDF's strict `< m/2` is false for upper-oriented comparisons with an even chunk count; counterexample below. |
| C03-025 | (3.13): a chunk in `Y_R` contributes at most 5 entries satisfying `R(_,mom xs)`; a chunk in `Y_notR` contributes at most 2, using its own median count and length at most 5. | G. Summing gives `2*m + 3*size Y_R`, then the arithmetic bound in C03-026. |
| C03-026 | Theorem 3.6: `Nlt xs (mom xs)` and `Ngt xs (mom xs)` are each at most `ceilNat(7*n/10 + 3)`. | G. Source `size_median_of_medians_aux`, `size_less_than_median_of_medians`, `size_greater_than_median_of_medians`. Preserve multiplicities, the short final chunk, lower-median convention, and exact rounding. The empty-input count is zero independently of an unspecified pivot. |

## 3.3 The terminating algorithm: pp. 38–40

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-027 | `slow_select k xs` uses insertion sort and index `k`; `slow_median xs = slow_select ((n-1)/2) xs`. Their values equal `select` and `median`. | R/P: existing insertion sorter and Chapter 2 uniqueness; source `slow_select_correct`, `slow_median_correct`. Do not attach merge-sort cost to this insertion baseline. |
| C03-028 | `mom_select` uses the insertion baseline for `n<=20`. Otherwise form size-five chunks, map `slow_median`, recursively select rank `(ceilNat(n/5)-1)/2` among these medians, then use C03-012's three branches, with a second recursive call only in a strict block. | G. Preserve this **nested** recursion and the selected branch. The source uses equivalent integer formula `((n+4)/5-1)/2`. |
| C03-029 | Theorem 3.7: for `k<n`, if the nested computation terminates, its value equals `select k xs`. `mom_select_correct_aux`. | G/P: dispatch semantics reusable. A Lean total/dependent well-founded construction may combine partial correctness and termination instead of recreating Isabelle's domain predicate, provided the resulting recurrence and correctness are checked. |
| C03-030 | Theorem 3.8: for valid `k`, `mom_select` terminates. The first recursive list has `ceilNat(n/5)<n` in the recursive case; its correct median belongs to the original input, ensuring both later strict partitions are smaller. | G. Source actually proves `All mom_select_dom`, covering invalid outer indices too, then `mom_select_correct` for valid ones. Do not assume correctness circularly to discharge termination without a checked well-founded/dependent justification. |

## 3.4 Exact time functions and a scalar majorant: pp. 40–41

The metric is §1.5's nonprimitive function-call count, using specific recursive
equations, inlining conventions, and unit-cost primitive arithmetic/comparisons.
It is not elapsed Lean time. The source deliberately caches branch lengths and
charges the equal-block length only when execution reaches that branch.

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-031 | Partition code is one recursive pass: recursively partition the tail, then cons the head onto the `<`, `=`, or `>` output. Its exact call time is `Tpartition3 p xs = n+1`. | G/P: value bridge to existing `partition3` exists via filters, but the one-pass measured execution and its cost do not. Source `partition3_code`, `T_partition3`. |
| C03-032 | Appendix B.2: `Tslow_select = Tinsort xs + Tnth (insort xs) k`; for `k<n`, it is at most `n^2+3*n+1`. | G/P: reuse Chapter 2 insertion-time proof and Appendix B's valid-index `Tnth=k+1`; source `T_slow_select_le`. |
| C03-033 | Appendix B.2: `Tslow_median = Tlength xs + Tslow_select ((n-1)/2) xs`; for nonempty input, at most `n^2+4*n+2`. | G/P: source `T_slow_median_le`; no nonempty requirement should be dropped from the source bound derivation. |
| C03-034 | Appendix B.2: `Tchop 0 xs=1`, `Tchop d []=1`; positive/nonempty step adds `Ttake d xs + Tdrop d xs + Tchop d (drop d xs) + 1`; all `d,xs` satisfy `Tchop d xs <=5*n+1`. | G/P: source `T_chop_le`; chapter-1/list-time composition reusable. |
| C03-035 | Map-call time from Appendix B.1 counts the sum of the actual `Tslow_median` values on chunks, plus one traversal call per chunk and the base call. | P: standard list sum/map and resource composition; source bound needs every chunk nonempty and of size at most 5, making per-chunk median cost at most 47. |
| C03-036 | `Tmom_select` base branch is `1 + Tlength xs + Tslow_select k xs`. Recursive branch additionally pays the median-selection recursive time, chopping, mapped slow medians, one-pass partitioning, `Tlength ls`, and then only the selected branch's recursive/equal-length work. | G; full unambiguous recurrence recorded below. Source `T_mom_select_simps`. |
| C03-037 | Define scalar `F n`: `483` if `n<=20`; otherwise `F(ceilNat(n/5)) + F(ceilNat(7*n/10+3)) + 19*n + 54`. (3.15) is its recursive equation. | G. Source `T'_mom_select`; prove both recursive arguments smaller, `F n>=483`, and monotonicity (`T'_mom_select_ge`, `T'_mom_select_mono`) before using upper bounds on actual subproblem sizes. |
| C03-038 | (3.14): if `k<n`, `Tmom_select k xs <= F n`. `T_mom_select_le_aux`. | G. Base arithmetic is `n^2+4*n+3 <=20^2+4*20+3=483`; recurrence uses C03-026, all auxiliary costs, valid child ranks, and monotonicity of `F`. |

For C03-036, let `xss=chop 5 xs`, `ms=map slow_median xss`,
`idx=(ceilNat(n/5)-1)/2`, `p=mom_select idx ms`, and `(ls,es,gs)=partition3 p xs`.
For `n>20`, the exact source time is

```text
1 + Tlength xs + Tmom_select idx ms + Tchop 5 xs
  + Tmap Tslow_median xss + Tpartition3 p xs + Tlength ls
  + (if k < len ls then Tmom_select k ls
     else Tlength es
       + (if k < len ls + len es then 0
          else Tmom_select (k-len ls-len es) gs)).
```

The first recursive call is charged once. The equal branch pays no second
selection call. Extra traversals introduced by an alternate implementation need
their own cost relation; output correctness alone is insufficient.

## 3.5 Akra–Bazzi Light: pp. 41–44

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-039 | General scalar recurrence beyond cutoff `n0`: `f n = f(ceilNat(a*n+b)) + f(ceilNat(c*n+d)) + C1*n+C2`. The contraction coefficients are **a and c**, not a and b. | G/P: inspect available recurrence libraries before adding a reusable result; no such exact theorem was established in the inspected conaled modules. |
| C03-040 | (3.16): sufficient child-size conditions for nonnegative offsets are `n1 >= (b+1)/(1-a)` and `n1 >= (d+1)/(1-c)`, with `0<a,c<1` and `n>n1`. For arbitrary offsets replace them in these bounds with `max 0 b`, `max 0 d`. | G/P: source `akra_bazzi_light_aux1`. Natural ceiling requires the zero truncation case to be handled explicitly. |
| C03-041 | Corrected sufficient slope condition underlying (3.17): `C3 >= C1/(1-a-c)` makes `C3*(1-a-c)-C1` nonnegative. | G. PDF writes strict `>` but later chooses a maximum that can give equality. Non-strict suffices; the pinned proof uses it. Counterexample to the claimed strict choice is below. |
| C03-042 | (3.18): choose `n1 > (max 0 b+max 0 d+2)/(1-a-c)`, ensure all `n<=n1` have `f n<=C4`, and choose `C3 >= (C1*n1+C2+C4)/((1-a-c)*n1-max 0 b-max 0 d-2)` as well as C03-041. Then strong induction proves `f n<=C3*n+C4`. | G. Source `akra_bazzi_light_aux2`; positive denominator and nonnegative slope must be proved, not assumed by automation without appropriate premises. |
| C03-043 | Theorem 3.9, (3.19): for `f:Nat->Real`, `a>0`, `c>0`, `a+c<1`, `C1>=0`, and the recurrence for all `n>n0`, there exist real `C3,C4` bounding every `f n` by `C3*n+C4`. | G/P. `b,d,C2` may be arbitrary reals; neither `f>=0` nor `C2>=0` is an assumption. Source `akra_bazzi_light`. This is the sufficient direction; no converse theorem is required by the numbered statement. |
| C03-044 | Source natural-valued corollary: if `f:Nat->Nat` and `C1,C2:Nat`, natural bounding constants exist, using nonnegative ceilings of the real constants. | G/P: `akra_bazzi_light_nat`. Choose a useful general theorem and derive this specialization rather than duplicate the induction. |
| C03-045 | (3.20): instantiate the recurrence theorem with `a=1/5,b=0,c=7/10,d=3,C1=19,C2=54,n0=20` to bound `F n` linearly for every `n`. | G. Source `T'_mom_select_le'`; exact rational coefficients have sum 9/10. |
| C03-046 | Theorem 3.10: constants independent of `xs` and valid `k` satisfy `Tmom_select k xs <= C3*len xs+C4`. | G, composing C03-038 and C03-045. This is worst-case linear **source-model cost** uniformly over the rank, not a runtime benchmark or a proof about every pivot policy. |

## Exercises: complete scope

| ID | Exercise and obligations | Reuse and boundaries |
|---|---|---|
| C03-047 | Exercise 3.1, p.33: a tail-recursive single-pass `select0`, correct on nonempty lists. | P: existing minimum/rank facts can verify an accumulator implementation. The exercise explicitly does not require a linear-time theorem, but the implementation must actually have the requested traversal shape. |
| C03-048 | Exercise 3.2, p.33: adapt to a single-pass `select1`, correct at zero-based rank one when length>1; prove correctness after Exercise 3.3, as requested by the text. | G/P. Preserve duplicates: the second smallest occurrence can equal the minimum. |
| C03-049 | Exercise 3.3(1), p.33: tail-recursive, one-pass `select_fixed k xs`, correct for `k<n`, with per-step work linear in `k`; suggested bounded sorted prefix computes `take m (sort xs)`. | G/P: existing insertion and independent rank contracts are reusable; no integrated fixed-rank streaming selector was identified. One traversal of the input does not forbid traversing a bounded accumulator. |
| C03-050 | Exercise 3.3(2): prove the actual Exercise 3.2 implementation equivalent to `select_fixed 1`, then obtain correctness. | G; exact algorithm relation, not merely an unchecked shared comment. |
| C03-051 | Exercise 3.3(3): define an appropriate source time and exhibit constants `C1..C4` with `Tselect_fixed k xs <= C1*k*n+C2*n+C3*k+C4` for `k<n`. | G. This formulation includes `k=0`; do not replace it with `C*k*n`, which would falsely force zero work for minimum selection. Constants must be explicit witnesses or existentially proved independently of input/rank. |
| C03-052 | Exercise 3.4, pp.33–34: for `xs:List Int`, `Nodup xs`, `k<n`, and `i<n`, there exists an integer `z` such that replacing entry `i` by `z` changes selection at rank `k`. | G/P: `RankedAt` and index-update laws reusable. A useful helper is injectivity of `k -> select k xs` on **valid** indices for distinct input. This sensitivity theorem is the exact formal target; a fully formal machine/query lower bound needs an additional computation model and is not supplied merely by this statement. |
| C03-053 | Exercise 3.5, p.36: construct a nonempty list `reduce_select_median k xs` whose lower median equals `select k xs` under `xs!=[]` and `k<n`. | G/P. A possible future construction pads with copies of an input minimum or maximum so the selected occurrence becomes central; no global bottom/top elements should be required. Correctness must include output nonemptiness. |
| C03-054 | Exercise 3.5 cost: define its time and prove `Treduction k xs <= C1*n+C2` uniformly over valid `k`. | G. Charge finding extrema, original length, building padding, and concatenation; do not assume finding a minimum is free because its specification exists. |
| C03-055 | Exercise 3.6, p.40: determine the least cutoff replacing 20 for which the actual algorithm works, and explain the choice of 20. | G/analysis: least actual cutoff is 1: cutoff0 recurses from a singleton to the same singleton medians; cutoff1 permits strict first-child decrease for every larger input, with pivot membership ensuring the later decrease. This is an analytical target to prove, not a completed Lean result. The scalar majorant's separate size bound does not decrease at n=13 and does at all n>=14, so its minimum cutoff is 13; 20 safely accommodates it and the displayed simple base constant 483. Do not claim a uniquely established author motive beyond this evidence. |
| C03-056 | Exercise 3.7, p.41: define `f:Nat->List Nat` with strictly increasing lengths and, for every index, strictly more than 70% of its entries greater than `mom (f i)` with chunk size5. | G. Preserve strict `>7/10` and all-index nonzero denominator; an equivalent integer target is `10*Ngt (f i) (mom (f i)) > 7*len(f i)`. A single example or finite experiment does not satisfy the exercise. |
| C03-057 | Exercise 3.8(1), p.44: for arbitrary chunk size `l>=1`, prove a corresponding two-sided pivot bound generalizing Theorem 3.6, including rounding and a short final chunk. | G. A useful proof target before simplification is: with `q=floor(l/2)` and `m=ceilNat(n/l)`, each strict side has size at most `q*m + (l-q)*floor(m/2)`. It follows by the same two-group argument, works for both orientations with the lower median, and specializes to the chapter's `2*m+3*floor(m/2)` for l=5. Any simplified bound must be proved from this or an equally precise statement. |
| C03-058 | Exercise 3.8(2), p.44: analyze how general `l` changes correctness and running time and why five is useful; the book presents this as an on-paper exercise. | G/analysis: exact mathematical conclusions remain **Lean obligations** under the user's whole-book request and `DECISIONS.md`. Prove the crude fixed-size recurrence's fraction `1/l + (l+floor(l/2))/(2*l)` is strictly below1 exactly when `l-floor(l/2)>2` for positive natural l, and hence for odd l>=5 and even l>=6; prove the associated sufficient-case linear majorants with the rounding and offset hypotheses exposed. Prove the coefficient equals1 for l=3 or4 and characterize the self-recursive pivot call for l=1. Correctness/termination changes for the chosen generalized algorithm also need checked statements. Prose may explain why five is the smallest sufficient odd size for this argument and discuss practical tradeoffs, but Markdown arithmetic alone cannot close this row. Failure of this particular recurrence argument to give a linear guarantee is not an impossibility theorem for other grouping strategies. |

## Probabilistic and other pivot-policy claims: p.35 scope reconciliation

This section corrects the earlier scope omission. The book affirmatively
asserts a quadratic worst case, linear expectation and a small probability
of a large excess over linear work for random pivots. Those are mathematical
claims to prove, not fulfilled by a source citation or the deterministic
median-of-medians theorem. It does not specify a random-bit implementation
or a probability distribution on input lists. The faithful randomized
interpretation fixes an arbitrary input list and valid requested rank,
then draws a **uniform input occurrence** at each active recursive call.

| Additional research source | Precisely inspected scope |
|---|---|
| R. M. Karp, *Probabilistic recurrence relations*, JACM41(6),1136–1150,1994 | Book citation is §2.5, DOI <https://doi.org/10.1145/195613.195632>. Publisher PDF returned HTTP403 through both public retrieval routes; an author publication list and the book bibliography confirm the citation, but no readable original or author technical-report copy was recovered. The exact 1994 metric, rank premises and real-versus-integer parameter wording are **not directly verified**. |
| Yican Sun, Hongfei Fu, Krishnendu Chatterjee, Amir Kafshdar Goharshady, *Automated Tail Bound Analysis for Probabilistic Recurrence Relations* | Immutable version <https://arxiv.org/pdf/2305.15104v1>, May24,2023, 46 PDF pages, 1,338,348 bytes, SHA-256 `00838dc1f49ec407ec170a131d804bb8d306257c1204afee29cac9ba92952773`. AppendixB Example17, PDF p24, and AppendixG.2, PDF pp42–43, were read for the quickselect model and displayed Karp-method tail. |

The later primary research paper reproduces a strict-tail bound
`Pr[p(n)>4n+wn]≤(3/4)^w`. This corroborates the constants; it is not
direct inspection of Karp's §2.5. Its Example17 assumes distinct keys,
describes `n-1` comparisons, but charges `pre(n)` in its recurrence and
equates the remaining size with the larger partition. The recurrence is
a valid prospective **upper envelope**, not the exact comparison/branch
law for an arbitrary fixed target rank. C03-073 retains an independent
counterexample to that equality. Its discussion of a nonnegative real
tail parameter refutes a particular prefixed-point proof condition, not
the probability inequality itself. The bound proved by the elementary
route below uses natural `w` and the explicitly defined scan-volume
metric; it is not presented as a verbatim reconstruction of the
inaccessible original theorem.

The reading PDF/text/provenance are saved under
`book-source/Sun-Fu-Chatterjee-Goharshady-2023-probabilistic-recurrences-v1.*`.
Redistribution license was not established; these are reading inputs, not
delivered source-code translations. Mathlib's finite uniform measures,
conditional-expectation/finite-sum laws and Markov inequality
(`mul_meas_ge_le_integral_of_nonneg` in
`MeasureTheory/Integral/Bochner/Basic.lean`, or
`meas_ge_le_lintegral_div` in `Integral/Lebesgue/Markov.lean`) are reusable
foundations. No already-integrated randomized selection/tail proof was
identified. The separate quicksort probability plan is related foundation
work, not a proof of these rank-selected recurrences.

Let the state be the remaining list and its valid zero-based rank. After
the usual three-way partition, keep only the selected strict block with
the adjusted rank, or terminate when the requested occurrence is in the
equal block. All occurrences of the pivot value disappear from either
strict recursive block. Fresh draws are uniform conditional on the entire
prior execution; this is not a fixed deterministic pivot function and not
a uniform draw from the set of distinct values. On `[0,0,1]`, for example,
the initial pivot-value probabilities are `2/3` and `1/3`.

Every active call has positive length and the next length is strictly
smaller. Thus the random execution is a finite probability tree with at
most `n` active states. It can be defined with finite weighted outcomes
or an appropriate probability/kernel interface; no almost-sure termination
axiom is necessary. Every outcome returns the same correct selected
value, while the work observation varies. Invalid public ranks still use
the existing visible failure contract before these valid-rank statements.

### A precise work metric and a proof route

Put `X₀=n` and let `X_j` be the current list length at active step `j`,
with zero forever after termination. Define **scan volume**

```
W = sum_j X_j.
```

Equivalently, an active length-`m` call charges `m` and adds the scan
volume of its one selected recursive branch, if any. This metric records
the actual random branch recurrence. It is not automatically the
Chapter1 function-call tariff, comparisons, random bits or elapsed time.
To transport it, instrument the actual random selection implementation
and prove a bound such as `α W ≤ T ≤ β W+γ`, with fixed `α>0`, `β>0`,
`γ≥0`. Single-pass partitioning, list indexing to an occurrence, lengths
and the other bounded-number traversals are linear per active list.
Uniform draw is an explicitly specified abstract choice operation; an
unbounded rejection sampler for random bits would need its own resource
analysis and does not automatically satisfy a pathwise affine bridge.

For a chosen occurrence with stable sorted rank `r` among `m` occurrences,
the next strict-block size is at most `max(r,m-1-r)`. Break ties by occurrence
identity solely for this counting proof: strict lower and upper blocks are
no larger than the corresponding refined-rank sides. The chosen occurrence
is uniform, so its refined rank is uniform in `0,...,m-1`, even with duplicate
values. Consequently,

```
E[next length | current state] ≤
  (1/m) * sum_(r<m) max(r,m-1-r) ≤ 3m/4.
```

The selected side depends on the requested rank, and the middle branch
can terminate immediately. Therefore `max(r,m-1-r)` is a **majorant**,
not the exact recurrence for fixed-rank selection. On a distinct length5
list, requested rank0 and pivot rank1 keep a length1 block, while that
majorant is3. This distinction matters when importing a probabilistic
recurrence theorem or claiming equality of distributions.

Strong induction on the remaining length gives `E[W]≤4n`; the initial
scan gives `W≥n`, hence `n≤E[W]≤4n` for every fixed input and every valid
rank. There is no `Nodup` premise on this upper or lower bound. The
constants are independent of the rank and payload distribution.

An elementary tail proof retains the chapter's quantitative assertion
without depending on an unverified external theorem. Conditional drift
gives `E[X_j]≤(3/4)^j n`. Conditional on the state at step `j`, expected
remaining scan volume is at most `4X_j`, so its unconditional expectation
is at most `4(3/4)^j n`. For every integer `w≥0`, the first `w` scans
cost at most `wn`. Therefore

```
W ≥ (4+w)n  ⇒  remaining scan volume after w steps ≥ 4n,
Pr[W ≥ (4+w)n] ≤ (3/4)^w.
```

The last step is Markov's inequality, with `n>0` guaranteed by valid rank.
All executions are finite, so the necessary sums and integrability can
be proved directly. No independence of the successive remaining sizes is
claimed; they depend on the earlier choices. The conditional law is the
essential hypothesis.

Under the actual-cost bridge the corresponding bounds are
`αn≤E[T]≤4βn+γ` and
`Pr[T≥β(4+w)n+γ]≤(3/4)^w`. These are proof targets, not completed
Lean theorems. The tail is exponential in the **excess multiple** `w`.
For fixed `w`, its upper bound is a fixed number independent of `n`; it
does not by itself prove a fixed-constant `O(n)` bound with failure
probability tending to zero as `n` grows. Choosing a logarithmic excess
factor yields an `O(n log n)` high-probability consequence if desired,
but the book does not require replacing its expectation claim by that
different statement.

### Worst case and other pivot choices

Every occurrence-pivot execution has
`W≤n+(n-1)+...+1=n(n+1)/2`. On a distinct input and any valid target
rank there is a sequence of endpoint pivots that removes exactly one
non-target occurrence at each step until the target is alone: use minima
while the target rank is positive, then maxima. That particular sequence
has probability `1/n!` under uniform occurrence draws and attains the
quadratic scan volume. Thus the randomized algorithm has a quadratic
worst case over inputs/positive-probability choice paths, despite its
linear expected work on every fixed input. An all-equal list terminates
in one partition, so a quadratic lower bound does not hold separately
for every duplicate pattern.

The adjacent p35 pivot-policy examples also need exact quantifiers.
For distinct inputs, repeatedly choosing the minimum at target rank `k`
uses `k+1` active calls and scan volume
`(k+1)n-k(k+1)/2`; the quadratic instance is `k=n-1`, while fixed `k`
is linear in `n`. A pivot always strictly outside a nonempty input leaves
the valid selection state unchanged and yields an infinite recurrence
path unless another stopping rule is introduced. A pivot with each
strict side at most half the active length gives at most `ceil(log₂ n)`
**recursive edges**, not that many total function entries; with linear
pivot construction and partition work, the sum of active lengths is at
most `2n`, yielding the stated linear bound. These claims do not follow
for arbitrary pivot policies merely from value correctness.

### Reconciliation checklist

The following appended IDs preserve the original C03-001–C03-058
identities. They are queued obligations, with no acceptance/status change.

| ID | Source claim and exact assumptions | Reuse or gap |
|---|---|---|
| C03-059 | P35 random-pivot claim: fix a list of length `n>0` and zero-based `k<n`; at each nonempty recursive state draw an input occurrence uniformly conditional on prior execution, partition, and follow the rank-selected strict block or stop in the equal block. | G/P: reuse the deterministic partition/rank dispatcher but define an actual finite random execution; `selectWith` with one fixed pivot policy is not that probability law. |
| C03-060 | Uniform occurrence law with duplicates; `[0,0,1]` chooses values0 and1 with probabilities2/3 and1/3. | G/P: finite uniform-index distribution and checked index-to-value pushforward. Uniform distinct-value choice is a different algorithm and does not discharge this row. |
| C03-061 | All random outcomes terminate in at most `n` active calls, maintain valid child ranks, and return the same correct selected value. | P: `PivotValid`, strict partition sizes, existing correctness and public zero/one-based Option bridge; combine with the random recursion rather than postulate correctness of a distribution. |
| C03-062 | Define the actual scan-volume recurrence: charge the positive active length, add only the chosen recursive branch, zero after termination. | G/P: measured computation/value erasure can be reused. This is an explicit observation, not an assignment of desired complexity to an extensional selector. |
| C03-063 | Every occurrence-pivot choice path has scan volume at most `n(n+1)/2`. | G: strict length decrease and finite sum. This is the quadratic upper bound, uniformly over ranks and duplicates. |
| C03-064 | Quadratic worst-case witness: for each distinct input and valid target rank, a specified bad-endpoint sequence keeps the target until a singleton, has probability `1/n!`, and attains scan volume `n(n+1)/2`. | G: exact branch and probability witnesses. If working over arbitrary payload types, state the required distinct-input availability; natural/integer lists supply an unbounded worst-case family. |
| C03-065 | Preserve worst-case quantifiers and counterexamples: all-equal input terminates after its first full partition; rank0 with deterministic minimum pivot also stops immediately. | P/G: checked examples plus general all-equal behavior. Do not infer an Ω(n²) bound for every individual input or rank/policy pair. |
| C03-066 | Stable occurrence-rank coupling: chosen occurrence rank is uniform, and actual next size is at most `max(r,m-1-r)`; duplicates can only remove additional equal occurrences. | G/P: sorting/permutation occurrence machinery, no global `Nodup` premise. Establish this law for each conditional state. |
| C03-067 | Arithmetic and drift: `(1/m) Σ_(r<m) max(r,m-1-r)≤3m/4`, hence conditional expected next size≤3m/4 for `m>0`. | G/P: finite sums and exact rational arithmetic; handle parity and singleton cases explicitly. |
| C03-068 | P35 expected Θ(n): for every fixed input and valid rank, `n≤E[W]≤4n`. | G: inductive expectation proof using actual random recurrence and C03-067; lower bound is the initial scan. Constants do not depend on the input distribution or requested rank. |
| C03-069 | With absorbing zero after termination, `E[X_j]≤(3/4)^j n` for every natural `j`. | G/P: finite conditional expectation or direct finite probability-tree induction. Successive sizes are dependent; no false independence assumption. |
| C03-070 | Expected residual scan volume after `w` steps≤`4(3/4)^w n`, obtained by conditioning on the actual state and using C03-068. | G/P: tower/finite sum law. The result is stronger evidence than merely bounding the number of recursive calls. |
| C03-071 | P35 tail assertion: for all natural `w`, `Pr[W≥(4+w)n]≤(3/4)^w`, with `n>0` and the model above. | G: original elementary derivation via C03-070 and Markov. Preserve exact threshold, nonnegative integer parameter, conditional law and metric; do not silently claim verification of the inaccessible cited paper's full theorem. |
| C03-072 | Tail proof decomposition: first `w` scans cost≤`wn`; on the tail event, residual work is≥`4n`; residual work is nonnegative and integrable. | G/P: needed actual-cost decomposition and finite expectation/Markov correspondence, not a cost defined to satisfy the desired inequality. |
| C03-073 | Larger-side probabilistic recurrence is a majorant for fixed-rank quickselect, not generally its exact law. Witness `n=5,k=0,pivot rank1`: next size1 versus majorant3. | G/P: checked dominance bridge if importing the cited/reproduced PRR. A theorem about the majorant alone cannot be relabelled as equality for the rank-selected recursion. |
| C03-074 | Transport scan volume to the chosen source resource model by a checked pathwise affine bound `αW≤T≤βW+γ`, with fixed positive α,β and nonnegative γ. | G/P: charge actual pivot retrieval, full partition, required length scans and branch work. The existing two-pass partition and pinned one-pass tariff have distinct constants/recurrences. Abstract uniform-choice cost is explicit; no random-bit/runtime claim is automatic. |
| C03-075 | Actual-model expected and tail bounds: `αn≤E[T]≤4βn+γ` and `Pr[T≥β(4+w)n+γ]≤(3/4)^w`, plus transferred quadratic worst-case upper/lower witnesses. | G: apply the actual bridge rather than mixing comparison counts, scan volume and Chapter1 function calls. |
| C03-076 | Tail quantifiers: exponential decrease in excess multiple `w`; no automatic fixed-constant high-probability O(n) conclusion as `n` grows. | Formal statement review/analysis: keep the exact probability theorem. The weaker logarithmic-excess consequence is optional and does not replace the linear expectation. |
| C03-077 | Checked random-model examples: singleton, duplicate equal block, valid rank0, endpoint ranks, different pivot traces with the same output, and the positive-probability worst path. | P/G: instantiate existing failure/rank contracts and new distribution/cost proofs. Finite calculations alone do not establish the general expectation or tail theorem. |
| C03-078 | P35 deterministic minimum-pivot claim, corrected: distinct input and target rank `k` give `k+1` active calls and scan volume `(k+1)n-k(k+1)/2`; largest rank gives Θ(n²). | G/P: retain the true worst-case assertion and small counterexamples to the unqualified all-rank/all-duplicate wording. “n recursive calls” refers to active invocations in that worst path; recursive edges are one fewer. |
| C03-079 | P35 outside-range pivot claim: on a nonempty valid selection state, always choosing below all entries or above all entries preserves the state and never reaches the equal branch. | P/G: formal infinite-step/nontermination witness for the recurrence, or an equivalent fuel/iteration statement; such a policy does not satisfy the existing `PivotValid` termination interface. |
| C03-080 | P35 halving-pivot claim: strict sides≤`m/2`, positive initial length, valid rank, and linear pivot-construction/partition costs imply at most `ceil(log₂ n)` recursive edges and scan volume≤`2n`, hence Θ(n) in the stated tariff. | G/P: geometric sums and path-length facts. Include n1, where there are zero recursive edges but one active invocation; do not count searching for an arbitrary pivot as free. |

### Useful reduction arithmetic for Exercise 3.5

For a nonempty length-`n` input and valid zero-based `k`, padding with
`A=max(0,n-1-2*k)` copies of an input minimum and
`B=max(0,2*k+1-n)` copies of an input maximum gives an odd output length at
most `2*n-1`; its central rank is `k+A`. One of `A,B` is zero. Correctness
must allow repeated extrema and arbitrary original duplicates. These formulas
are proposed analytical guidance, not a formalized algorithm or accepted
exercise solution.

## Source-error register and independent counterexamples

These are part of future statement-review scope. Corrected theorems and the
small counterexamples should both be checked in Lean; none should be silently
erased from the chapter ledger.

1. **p.31 prose after (3.1):** “at most n-k” is weaker than the displayed strict
   `Ngt<n-k`. On `xs=[0,2]`, `k=1`, candidate `a=1` has one smaller and one
   greater value, so both weakened non-strict inequalities hold although the
   selected value is 2. Retain the strict bound in the actual specification.
2. **p.37, (3.12):** the displayed strict-half bound fails for `R=(>)` and an
   even number of chunks. For `xs=[0,1,2,3,4,5,6,7,8,9]`, the two chunk medians
   are `[2,7]`, their lower median is 2, and exactly one chunk median is greater:
   the claim would be `1<2/2`. The corrected `1<=floor(2/2)` is true. The
   pinned Isabelle proof uses `size Y_R <= m div 2` and establishes Theorem 3.6
   without the erroneous strict inequality.
3. **p.41, contraction letters:** after the general recurrence, the prose writes
   `0<a,b<1` and `a+b<1`, but the recursive coefficients are `a,c`; `b,d` are
   offsets. The theorem (3.19) and source use `a>0,c>0,a+c<1`. A mere offset
   change cannot change the contraction coefficient of the second recursive
   branch. Do not encode the mismatched-letter prose as an alternative theorem.
4. **p.43, (3.17) and the subsequent constant choice:** the text demands strict
   `C3>C1/(1-a-c)` and then defines C3 with `max`, which ensures only `>=`.
   Independent admissible example: `f(n)=0`, `a=c=1/4`, `b=d=C1=C2=0`, `n0=0`.
   The recurrence and theorem assumptions hold; the printed construction gives
   `C4=0`, `C3=0`, contradicting its asserted strict `0>0`. Nonnegative slope
   suffices for the inductive inequality, and the source correctly assumes `>=`.
   If a positive slope is desired, increase the chosen constant explicitly.
5. **p.35 median prose:** an even list need not have two distinct median values;
   `[1,1]` has two central occurrences but just one distinct value. Keep the
   lower **occurrence** convention and allow duplicates throughout.
6. **p.44 chapter notes:** “k-th largest” disagrees with the chapter's ascending,
   zero-based smallest-rank definition. `[1,3]` at rank0 distinguishes minimum1
   from maximum3. Preserve the formal smallest-rank specification.
7. **p.35 proof of Theorem 3.5:** `set es={pivot}` holds only if the equal block
   is nonempty. The middle-branch rank inequalities ensure that fact; without
   them `xs=[1]`, `pivot=2` has empty `es`. Preserve the branch premise instead
   of exporting unconditional singleton-set equality.

The paragraph on minimum pivots describes a genuine worst-case mathematical
claim with missing qualifications: it is not uniform over every rank and
duplicate pattern. Selecting rank0 returns at the first minimum pivot, and an
all-equal list has no recursive strict block. C03-078 retains the corrected
exact cost/call statement and its quadratic specialization. Random-pivot
expectations and tails are retained in C03-059–C03-077 rather than being
classified as discussion. Practical hybrid performance judgments remain
analysis; the text supplies no exact Introselect switching recurrence from
which a new universal runtime theorem could follow.

## Completion map and handoff

All eight exercises are inventoried, including their subparts. The exercise's
“on paper only” instruction does not waive formal coverage: C03-058's exact
coefficient inequalities, sufficient-case bounds, and algorithmic conclusions
need Lean witnesses; practical or explanatory judgments are separately analysis.
Named results map as follows: Theorem3.1 C03-002;
Theorem3.2 C03-005; Lemma3.3 C03-006/007; Lemma3.4 C03-010; Theorem3.5 C03-012;
Theorem3.6 C03-026; Theorem3.7 C03-029; Theorem3.8 C03-030; Theorem3.9 C03-043;
Theorem3.10 C03-046.

| Numbered displays | Inventory witnesses |
|---|---|
| (3.1), (3.2), (3.3), (3.4) | C03-001, C03-002, C03-003, C03-004 |
| (3.5), (3.6), (3.7), (3.8) | C03-006, C03-007, C03-010, C03-009 |
| (3.9), (3.10), (3.11) | C03-019, C03-023, C03-023 |
| (3.12), (3.13) | C03-024 with correction, C03-025 |
| (3.14), (3.15) | C03-038, C03-037 |
| (3.16), (3.17), (3.18), (3.19), (3.20) | C03-040, C03-041 with correction, C03-042, C03-043, C03-045 |

The p35 probabilistic assertions now map to C03-059–C03-077, and its
remaining pivot-policy complexity/nontermination assertions to
C03-078–C03-080. All eighty IDs remain queued. Direct access to Karp1994
is an explicit source-recovery limitation, not permission to drop the
asserted mathematics; the independent finite-execution proof targets
above can discharge the precise retained claims once checked in Lean.
Neither a bibliography citation nor these analytical arguments are a
formal acceptance result.

Useful checked examples later include duplicates, empty/failing calls, valid
zero rank, odd/even lower medians, chunk sizes0/1/5 and nonmultiple lengths,
cutoff boundaries20/21, equal blocks absorbing the requested rank, different
valid pivot policies with equal values but different costs, a small instance
of the infinite tightness family, and each source-error counterexample above.
Reuse existing public failure, pivot-adequacy, monotone-map, and tie examples.
No chapter/ticket status or Lean/source repository file was changed here.
