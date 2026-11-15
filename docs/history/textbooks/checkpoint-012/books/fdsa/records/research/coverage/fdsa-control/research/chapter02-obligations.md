# Chapter 2: source obligations and existing reuse

Research date: 2026-11-02. Local ticket: `FDSA-002`.

**State: future-source inventory only.** Chapter 1 remains the active formalization.
This document does not activate Chapter 2, add Lean declarations, certify existing
builds, or mark any Chapter 2 obligation complete. It records original analysis of
the pinned sources and existing integrated code so that implementation can proceed
in chapter order. Every checklist item remains subject to statement review,
implementation or an explicit reuse witness, and the applicable acceptance gates.

## Evidence and pins

| Source | Inspected identity and location |
|---|---|
| Book | *Functional Data Structures and Algorithms: A Proof Assistant Approach*, version July 27, 2026; Chapter 2, printed pp. 13–29, PDF pages 19–35. Official PDF: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Main Isabelle theory | `src/HOL/Data_Structures/Sorting.thy` in <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`. File SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. The PDF links the distribution's `HOL-Data_Structures/Sorting.html`. |
| Natural merge-sort source | The book links <https://isa-afp.org/entries/Efficient-Mergesort.html>. Inspected dated archive: <https://isa-afp.org/release/afp-Efficient-Mergesort-2026-10-26.tar.gz>, SHA-256 `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`. `Natural_Mergesort.thy` SHA-256 `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`; `Mergesort_Complexity.thy` SHA-256 `fe1f2c7037da3f95d3f62077b8653595c90efa887a3d0efc8280c18cd839bb06`; `Efficient_Sort.thy` SHA-256 `baccd818d8a1a5e0b74d433a47d9696fb6763be53e423db6245d720c9a5fae95`. The first two were declaration-inspected; the third is archived supporting source, not audited here. |
| License | Isabelle `COPYRIGHT` is BSD-3-Clause. The AFP entry expressly selects BSD; <https://isa-afp.org/LICENSE> supplies its terms. Retain notices if translated source is incorporated. The book itself is a reference input, not project source to redistribute. |
| conaled comparison | Source inspection at HEAD `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`: `Applications/Sorting/{Stable,Merge,Sort,SourceMerge}.lean`, `Examples/StableSorting.lean`, and their reconstruction/provenance notes. No new compile or audit result is asserted. |
| Library comparison | Local pinned `Mathlib/Data/List/Sort.lean`, corresponding to repository Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`. Standard Lean merge declarations were identified through actual conaled uses; their implementation has not been separately revision-audited in this inventory. |

Source files are research inputs under `book-source/`. The checkpoint-worthy
artifact is this original inventory plus the provenance manifest; do not include
the full book or large extracted prose in project deliverables. The source archive
postdates the book edition. Corresponding theorem statements were compared here;
that is not a claim that every source file is the exact July 2026 development.

## Conventions and meaning of reuse labels

In the tables below:

- `S xs` means pairwise nondecreasing order on a finite list.
- `M xs` is its multiset, `U xs` its element set, and `len xs` its length.
- `MM xss = M (flatten xss)` is the multiset obtained by summing the multisets of
  all component lists. This is the book's `mset_mset`.
- Ordinary sorting assumes a linear order on elements. Key sorting assumes an
  order on keys, not on records or payloads.
- `D f` means `forall xs ys, f (xs ++ ys) = f xs ++ ys`, the difference-list law.
- `L n` means the ceiling of the base-two logarithm used in the source. The source
  statements involving real logarithms and ceilings are interpreted in integers
  after coercing natural costs and lengths. If Lean uses `Nat.clog 2 n` instead,
  an explicit correspondence for positive `n` and the `n = 0` case is required.
- `R` identifies a reusable existing statement or implementation. A checked
  specialization/source correspondence still has to be named in the coverage
  ledger; it is not newly accepted Chapter 2 coverage.
- `P` identifies partial reuse: the mathematical result or component exists, but
  a source-specific algorithm, converse, cost model, or correspondence is missing.
- `G` identifies a gap in the integrated modules inspected here. It does not
  assert absence from all Mathlib, Std, or archived ADWH material.

All list operations must remain total, with kernel-checked termination. `Perm`
is an appropriate standard witness for the book's multiset equality, with a
checked bridge rather than a new duplicate permutation theory.

## Existing interfaces to preserve and reuse

| Integrated interface | Exact useful scope | Boundary |
|---|---|---|
| `Applications.Sorting.KeySorted` | `List.Pairwise` on the pulled-back key relation. | It is not a new sorting implementation. |
| `Stable`, `StableSort` | Equal-key filtered sequences; sortedness, permutation, and stability as separate fields. | Ordinary sorting correctness must not silently acquire a stability requirement. |
| `mergeBy`, `sourceMerge`, `sourceMerge_eq_merge`, `mergeBy_source` | Standard left-tie `List.merge` and an explicit source-recurrence bridge; only decidable comparison is needed for the bridge. | No cost theorem is present. |
| `mergeBy_perm`, `mergeBy_sorted`, `mergeBy_spec` | Permutation of concatenation; forward sortedness; stable sorting of two already sorted blocks. | The book also states a sortedness equivalence, requiring a converse. |
| `mergeBy_filter`, `mergeBy_stable` | Exact left-before-right equal-key observation. | Assumes the input blocks are sorted; an arbitrary compatible comparator is not proved stable. |
| `sortBy`, `sortOn` | Standard Lean merge sort, permutation, key sortedness, stability, and fixed points. | Source split recurrence and comparison counts still need an explicit connection; output equality alone does not establish cost equality. |
| `insertionOn`, `insertionOn_spec` | Mathlib insertion sort and independent stable-sort contract. | No insertion-call cost model or exact best/worst bounds is present. |
| `StableSort.unique`, `sortOn_eq_insertionOn` | Unique stable result, retaining distinguishable equal-key payloads; exact agreement of standard sorters. | The direct element-sorting uniqueness theorem has weaker requirements and is already supplied by Mathlib's pairwise-permutation uniqueness. |
| `StableSort.map`, `sortOn_map` | Key-preserving maps can discard or identify payloads while transporting the contract. | This should survive future source adapters; no need to duplicate it for each book sorter. |
| Local comparator theorems | `merge_sorted_compatible_on` and `sortBy_sorted_compatible_on` require laws only for actual input elements. | Preserve their weaker assumptions; do not globally replace them with `LinearOrder` constraints. |

The existing reconstruction note explicitly defers source partition/halving,
additional direct/tree/run sorters, and comparison accounting. Those archived
declarations are possible future evidence, not accepted implementations. Follow
their archive guide before reuse.

## Introductory definitions and specification: pp. 13–14

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C02-001 | Account for reflexive, transitive, antisymmetric, total `<=`, and the compatible strict comparison `<`. | R: standard order classes. Use the existing weaker operation/law split where it suffices, with a `LinearOrder` book specialization. |
| C02-002 | `S []`; `S (x :: xs)` iff every member of `xs` is at least `x` and `S xs`. | R: `List.Pairwise`, `List.pairwise_cons`; `KeySorted id`. |
| C02-003 | Correct sorting means both `S (sort xs)` and `M (sort xs) = M xs`, preserving multiplicities. | R: sortedness/permutation fields of local contracts, with a bridge to multiset equality. The always-empty output is an explanatory counterexample to sortedness alone, not an alternative algorithm to accept. |

## 2.2 Insertion sort: pp. 14–15

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-004 | `insort1 x [] = [x]`; on `y :: ys`, insert before `y` if `x <= y`, otherwise recurse into `ys`. | R: `List.orderedInsert (<=)` has this exact branch direction and tie behavior. |
| C02-005 | `insort [] = []`; `insort (x :: xs) = insort1 x (insort xs)`. | R: `List.insertionSort`, `insertionSort_nil`, `insertionSort_cons`; `insertionOn id`. |
| C02-006 | (2.1) `M (insort1 x xs) = {x} + M xs`. Isabelle `mset_insort1`. | R: `List.perm_orderedInsert`; multiset bridge needed. |
| C02-007 | (2.2) `M (insort xs) = M xs`. `mset_insort`. | R: `List.perm_insertionSort`; `insertionOn_spec`. |
| C02-008 | (2.3) `U (insort1 x xs) = {x} union U xs`. `set_insort1`. | R: `List.mem_orderedInsert` or permutation membership. |
| C02-009 | (2.4) `S (insort1 a xs)` iff `S xs`. `sorted_insort1`. | P: forward `List.Pairwise.orderedInsert`; converse follows from `List.sublist_orderedInsert` and pairwise inheritance and needs a named bridge. |
| C02-010 | (2.5) `S (insort xs)`. `sorted_insort`. | R: `List.pairwise_insertionSort`; `insertionOn_spec`. |
| C02-011 | `Tinsort1 _ [] = 1`; `Tinsort1 x (y :: ys) = (if x <= y then 0 else Tinsort1 x ys) + 1`. | G: instrument the actual ordered-insert branches. This is nonprimitive-call cost, not merely comparisons. |
| C02-012 | `Tinsort [] = 1`; `Tinsort (x :: xs) = Tinsort xs + Tinsort1 x (insort xs) + 1`. | G: recursive cost including the actual sorted tail value. |
| C02-013 | (2.6) `Tinsort1 x xs <= len xs + 1`. `T_insort1_length`. | G. |
| C02-014 | (2.7) `len (insort1 x xs) = len xs + 1`. `length_insort1`. | R: `List.orderedInsert_length`. |
| C02-015 | (2.8) `len (insort xs) = len xs`. `length_insort`. | R: `List.length_insertionSort` or permutation. |
| C02-016 | Lemma 2.1: `Tinsort xs <= (len xs + 1)^2`. `T_insort_length`. | G; preserve all `+1` costs, including empty input. |

## 2.3 Quicksort: p. 16

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-017 | `quicksort [] = []`; a nonempty list uses its head as pivot, recursively sorts the `< pivot` and `>= pivot` filters of its tail, and appends left result, pivot, right result. | G: no such integrated implementation found. Both filter lengths are bounded by the tail length, supplying termination. |
| C02-018 | (2.9) `M (quicksort xs) = M xs`. `mset_quicksort`. | G; standard filter/multiset lemmas reusable. |
| C02-019 | Unnumbered helper: `M (filter P xs) = filter P (M xs)`. | R: standard list/multiset library bridge; exact theorem must be selected during implementation. |
| C02-020 | Unnumbered helper: complementary predicates partition a multiset; `filter P M + filter Q M = M` if `P x` iff `not Q x` for every `x`. | R/P: standard filter partition law, with a checked instantiation for `< pivot` and `>= pivot`. |
| C02-021 | Unnumbered helper: `S (xs ++ ys)` iff `S xs`, `S ys`, and every member of `xs` is at most every member of `ys`. | R: pairwise-append characterization. |
| C02-022 | Unnumbered helper: `U (quicksort xs) = U xs`. `set_quicksort`. | G as an algorithm theorem; derive from C02-018. |
| C02-023 | Unnumbered theorem: `S (quicksort xs)`. `sorted_quicksort`. | G. |
| C02-024 | Formalize both stated `O(n log n)` claims: average cost of first-pivot quicksort under a uniform ordering of distinct keys, and expected cost with a uniformly chosen pivot occurrence at every recursive call on distinct-key inputs. | §2.3 pp.16–17. The authors omit the analysis from their exposition; the user's whole-book scope still includes the asserted mathematics. Prove the actual algorithm/distribution/cost correspondence, state lawful total-order and distinctness assumptions, retain the duplicate-key quadratic counterexample, and distinguish the exercise's uncharged-append metric from complete code costs. See `quicksort-average-proof-plan.md` for pinned AFP sources and the exact recurrence/metric bridges. Neither claim follows from deterministic Exercise2.4. |

## 2.4 Top-down merge sort: pp. 17–19

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-025 | `merge [] ys = ys`, `merge xs [] = xs`, and head comparison chooses the left head on ties. | R: `sourceMerge` and `sourceMerge_eq_merge`; preserve the exact recurrence. |
| C02-026 | `msort xs = xs` if `len xs <= 1`; otherwise split with `take (len xs / 2)` and `drop (len xs / 2)`, recursively sort, and merge. | P: standard `sortOn id` has the desired behavior and local proof unfolds a take/drop split, but a checked equality/recurrence at the exact pinned Std implementation is still required. Count equivalence cannot be inferred merely from sorting uniqueness. |
| C02-027 | Termination of `merge` by sum of lengths; of `msort` by strict decrease of both floor-half and complementary lengths when `len xs > 1`. | R/P: existing source merge termination; msort source recurrence must discharge its own obligations or use a proved standard recurrence. |
| C02-028 | (2.10) `M (merge xs ys) = M xs + M ys`. `mset_merge`. | R: `mergeBy_perm`, with multiset bridge. |
| C02-029 | (2.11) `U (merge xs ys) = U xs union U ys`. `set_merge`. | R: `List.mem_merge` or permutation membership. |
| C02-030 | Lemma 2.2: `M (msort xs) = M xs`. `mset_msort`. | P: `sortBy_perm` after the source bridge. |
| C02-031 | (2.12) `S (merge xs ys)` iff `S xs and S ys`. `sorted_merge`. | P: `mergeBy_sorted` gives the forward construction from sorted inputs. Reverse implication needs each input as a sublist of the merged output, or a direct source proof. It is stronger than the existing forward API. |
| C02-032 | Lemma 2.3: `S (msort xs)`. `sorted_msort`. | P: `sortOn_correct` after the source bridge. |
| C02-033 | `Cmerge [] ys = Cmerge xs [] = 0`; two nonempty lists cost one comparison plus the chosen recursive branch. | G: comparison counts, distinct from insertion's function-call metric. |
| C02-034 | `Cmsort xs = 0` for length at most one; otherwise the two recursive comparison counts plus `Cmerge` on the actual sorted halves. | G. Split traversal, append, constructor, and function-entry costs are not included. |
| C02-035 | (2.13) `len (merge xs ys) = len xs + len ys`. `length_merge`. | R: `mergeBy_perm` followed by length. |
| C02-036 | (2.14) `len (msort xs) = len xs`. `length_msort`. | P: `sortBy_perm` after source bridge. |
| C02-037 | (2.15) `Cmerge xs ys <= len xs + len ys`. `C_merge_ub`. | G. Do not silently replace the source bound with an exact count or claim the bound is tight. |
| C02-038 | Lemma 2.4: if `len xs = 2^k`, then `Cmsort xs <= k * 2^k`. `C_msort_le`. | G. The source theorem restricts length to powers of two; it includes `k = 0` (singleton), not empty input. Empty cost must be treated separately. |
| C02-039 | Supporting source corollary `C_msort_log`: under the same power-of-two premise, comparison count is at most `len xs * log 2 (len xs)` after coercion. | G/derived support. This is in `Sorting.thy`, not a separately numbered book theorem. An explicit coercion bridge may witness the book's informal `n log n` reading. |

## 2.5 Bottom-up merge sort: pp. 19–21

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-040 | `merge_adj [] = []`; singleton lists are unchanged; two leading runs are merged and prepended to the recursive pass over remaining runs. | G, reusing `mergeBy`. |
| C02-041 | Intended (2.16): `len (merge_adj xss) = (len xss + 1) / 2`. `length_merge_adjacent`. | G. The PDF accidentally prints the accumulator variant here; retain both intended basic theorem and the exercise's actual variant, as described in the correction register. |
| C02-042 | `merge_all [] = []`; `merge_all [xs] = xs`; otherwise recurse on `merge_adj xss`. Termination uses C02-041 and `len xss >= 2`. | G. |
| C02-043 | `msort_bu xs = merge_all (map singleton xs)`. | G. |
| C02-044 | Book abbreviation `mset_mset`: sum all inner multisets, equivalently multiset of `flatten xss`. | R/P: use standard multiset/list operations and establish the equivalence once. Avoid a second list-of-lists accounting foundation. |
| C02-045 | Intended unnumbered preservation: `MM (merge_adj xss) = MM xss`. `mset_merge_adj`. | G; PDF instead prints a tail-recursive accumulator statement, separately covered by C02-106. |
| C02-046 | Intended (2.17): `M (merge_all xss) = MM xss`. `mset_merge_all`. | G; PDF instead names `merge_all2`, separately covered by C02-106. |
| C02-047 | Unnumbered correctness: `M (msort_bu xs) = M xs`. `mset_msort_bu`. | G. |
| C02-048 | Unnumbered preservation: if every input run is sorted, every run in `merge_adj xss` is sorted. `sorted_merge_adj`. | G, composing C02-031 or existing forward merge result. |
| C02-049 | (2.18): if every run of `xss` is sorted, then `merge_all xss` is sorted. `sorted_merge_all`. | G. |
| C02-050 | Unnumbered correctness: `S (msort_bu xs)`. `sorted_msort_bu`. | G. |
| C02-051 | `Cmerge_adj` has zero empty/singleton cost and otherwise adds the first pair's `Cmerge` to the recursive pass cost. | G. |
| C02-052 | `Cmerge_all` has zero empty/singleton cost and otherwise adds `Cmerge_adj xss` to the cost of merging the next pass. | G. |
| C02-053 | `Cmsort_bu xs = Cmerge_all (map singleton xs)`. | G. |
| C02-054 | (2.19): if `len xss` is even and every run has length `m`, every run after `merge_adj` has length `2*m`. `length_merge_adj`. | G. Evenness is essential; an odd leftover run keeps length `m`. |
| C02-055 | (2.20): if all runs have length `m`, `Cmerge_adj xss <= m * len xss`. `C_merge_adj`. | G. No evenness premise is required here. |
| C02-056 | Lemma 2.5: all runs of length `m` and `len xss = 2^k` imply `Cmerge_all xss <= m*k*2^k`. `C_merge_all`. | G. Allow `m = 0`; retain the exact power-of-two premise. |
| C02-057 | Corollary 2.6: `len xs = 2^k` implies `Cmsort_bu xs <= k*2^k`. `C_msort_bu`. | G. |

## 2.6 Natural merge sort: pp. 21–25

### Algorithms and value laws

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-058 | Mutually recursive `runs`: empty gives no runs, singleton gives one singleton run, and a two-element prefix chooses descending iff the second element is strictly smaller. | G. Exact strictness matters for equal elements and future key stability. |
| C02-059 | `asc a f [] = [f [a]]`. On `b :: bs`, continue with accumulator `f compose (a :: ·)` and new head `b` when `not (b < a)`; otherwise emit `f [a]` and start `runs (b :: bs)`. | G. The source uses a difference-list accumulator, not an ordinary reversed list. |
| C02-060 | `desc a acc [] = [a :: acc]`. On `b :: bs`, continue with `a :: acc` when `b < a`; otherwise emit `a :: acc` and start `runs (b :: bs)`. | G. This reverses strictly descending runs. |
| C02-061 | Difference-list specification `D f`. Source support `ascP_Cons`, `ascP_comp_Cons`, `ascP_simp`: singleton-prefix functions satisfy it, composition with a singleton prefix preserves it, and `f [a] = f [] ++ [a]`. | P: standard append associativity is reusable. A representation/invariant bridge is needed if an existing sequence or fusion interface is used instead of raw functions. |
| C02-062 | Mutual termination and induction for `runs`, `asc`, `desc`, including restarting `runs` on `b :: bs`. | G. A common size measure may need phase offsets; no unproved termination assumption. |
| C02-063 | `nmsort xs = merge_all (runs xs)`. | G. |
| C02-064 | (2.21): `D f` implies `MM (asc x f ys) = {x} + M (f []) + M ys`. Source `mset_asc`. | G. The `D f` premise cannot be omitted for arbitrary functions. |
| C02-065 | (2.22): `MM (desc x xs ys) = {x} + M xs + M ys`. `mset_desc`. | G. |
| C02-066 | (2.23): `MM (runs xs) = M xs`. `mset_runs`. | G. C02-064 through C02-066 are a mutual-induction group. |
| C02-067 | (2.24): `M (nmsort xs) = M xs`. `mset_nmsort`. | G, composition of run and merge-all preservation. |
| C02-068 | (2.25): every run in `runs xs` is sorted. `sorted_runs`. | G. |
| C02-069 | Source support for C02-068: `D f`, sorted `f []`, and every member of `f [] <= a` imply every output of `asc a f ys` is sorted; sorted `xs` and `a <=` every member of `xs` imply every output of `desc a xs ys` is sorted. | G. These invariant premises are visible in `Natural_Mergesort.sorted_asc` and `sorted_desc`, though not displayed fully in the book. |
| C02-070 | (2.26): `S (nmsort xs)`. `sorted_nmsort`. | G. |

### Comparison counts and bounds

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-071 | Mutually recursive `Cruns`, `Casc`, `Cdesc`: no comparison for empty/singleton `runs` or empty worker tail; every tested adjacent pair costs one plus exactly the selected worker/restart branch. | G. Worker counts intentionally omit accumulators because their comparison decisions do not inspect them. |
| C02-072 | `Cnmsort xs = Cruns xs + Cmerge_all (runs xs)`. | G. Does not count the cost of applying a difference-list function. |
| C02-073 | (2.27): `Cmerge_adj xss <= len (flatten xss)`. Source `C_merge_adj'`. | G. No equal-length-run premise. |
| C02-074 | (2.28): `len (flatten (merge_adj xss)) = len (flatten xss)`. `length_concat_merge_adj`. | G, derivable from multiset/permutation preservation. |
| C02-075 | (2.29): for `n >= 2`, `L n = L ((n-1)/2 + 1) + 1`. Source uses `ceiling_log2_div2`. | G/P: arithmetic/logarithm library reuse; explicitly prove any natural-ceiling-log bridge. |
| C02-076 | Lemma 2.7: `Cmerge_all xss <= len (flatten xss) * L (len xss)`. `C_merge_all'`. | G. Handles arbitrary run lengths and counts, unlike Lemma 2.5. Empty and singleton lists must be separated to make logarithm conventions explicit. |
| C02-077 | (2.30), asc component: under `D f`, `len (flatten (asc a f ys)) = 1 + len (f []) + len ys`. `length_concat_asc`. | G. |
| C02-078 | (2.30), desc component: `len (flatten (desc a xs ys)) = 1 + len xs + len ys`. `length_concat_desc`. | G. |
| C02-079 | (2.30), runs component: `len (flatten (runs xs)) = len xs`. `length_concat_runs`. | G. |
| C02-080 | (2.31), asc component: `D f` implies `len (asc a f ys) <= 1 + len ys`. `length_asc`. | G. |
| C02-081 | (2.31), desc component: `len (desc a xs ys) <= 1 + len ys`. `length_desc`. | G. |
| C02-082 | (2.31), runs component: `len (runs xs) <= len xs`. `length_runs`. | G. |
| C02-083 | (2.32), asc component: `Casc a ys <= len ys`. `C_asc`. | G. |
| C02-084 | (2.32), desc component: `Cdesc a ys <= len ys`. `C_desc`. | G. |
| C02-085 | (2.32), runs component: `Cruns xs <= len xs - 1`, with natural truncated subtraction. `C_runs`. | G. Includes empty input. |
| C02-086 | Lemma 2.8: `len xs = n` implies `Cnmsort xs <= n + n * L n`. `C_nmsort`. | G. Preserve the actual source bound; its use of `n` rather than `n-1` is intentional weakening. |
| C02-087 | Source support: nonempty input gives nonempty `runs`; worker outputs are nonempty under the appropriate `D` condition; logarithm is monotone on positive arguments. `runs_ne` and `log2_mono`. | G/P: necessary side conditions for the source proof, not new book algorithms. |
| C02-088 | Formalize the pp.21–22 best-case and difference-list mathematical claims. For a sorted nonempty input, prove `runs xs=[xs]`, zero merge comparisons, and the exact scan/comparison specialization; retain a separate declared operational model for constant-time builder composition and linear materialization of the actual ascending-run builders. | G/P, mandatory. C02-108–112 unpack these existing source claims and the quadratic repeated-append alternative. The conditional operational theorems are distinct from the source's comparison counters and from Lean machine runtime. This is an explicit scope clarification of the frozen C02-088 requirement, not a change to the comparison tariff; see the reconciliation section below. |

## 2.7 Uniqueness: pp. 25–26

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-089 | Theorem 2.9: `M ys = M xs`, `S xs`, and `S ys` imply `xs = ys`. Source `sorting_unique`. | R: `List.Perm.eq_of_pairwise'` needs only antisymmetry of the element relation; reuse it and specialize to the book's linear order. |
| C02-090 | Corollary 2.10: any two functions satisfying the sorting specification for every input are pointwise equal and hence equal as functions. | R/P: derive once using C02-089 and function extensionality. Existing `sortOn_eq_insertionOn` is one stronger keyed/stable specialization, not the full quantified theorem. |
| C02-091 | (2.33) and (2.34) are induction-case premises: equal multisets and sortedness of two nonempty lists. Account for them as proof steps, not independent new theorem requirements. | Existing standard uniqueness proof can witness them without copying its implementation. |

## 2.8 Key sorting and stability: pp. 26–27

| ID | Source item and statement | Reuse or gap |
|---|---|---|
| C02-092 | Key-sort correctness preserves full-record multisets and sorts the mapped keys; stability preserves every filtered equal-key subsequence. | R: `KeySorted`, `Stable`, `StableSort`; prove the `map key`/pulled-back `Pairwise` correspondence. Payloads need neither order nor decidable equality. |
| C02-093 | `insort1_key` and `insort_key` are the insertion recurrences with comparisons on keys, selecting the newly inserted earlier record on ties. | R: `List.orderedInsert (fun x y => key x <= key y)` and `insertionOn key`. |
| C02-094 | Keyed insertion correctness: `M (insort_key f xs) = M xs` and (2.35) sorted `map f (insort_key f xs)`. Source `mset_insort_key`, `sorted_insort_key`. | R: `insertionOn_spec`, pairwise-map bridge. Supporting one-element multiset/set and sortedness-iff statements are the keyed analogues of C02-006, C02-008, C02-009, explicitly present as `mset_insort1_key`, `set_insort1_key`, `sorted_insort1_key`. |
| C02-095 | (2.36): if `f a <= f x` for every `x` in `xs`, then `insort1_key f a xs = a :: xs`. `insort1_is_Cons`. | R/P: elementary specialization of `orderedInsert_cons_of_le` after nil/cons cases. |
| C02-096 | (2.37): if `not P x`, filtering after inserting `x` equals filtering before insertion. `filter_insort1_key_neg`. | G/P: helper not exported by the inspected conaled modules; prove with standard insertion recurrence. It does not require sorted input. |
| C02-097 | (2.38): if keys of `xs` are sorted and `P x`, filtering after inserting `x` equals inserting `x` into the filtered list. `filter_insort1_key_pos`. | G/P: retain sortedness premise and the same key comparator. |
| C02-098 | Lemma 2.11: `filter (key = k) (insort_key key xs) = filter (key = k) xs`. `sort_key_stable`. | R: `(insertionOn_spec key xs).stable k` is exactly the independent observation after the recurrence bridge. A different proof method is acceptable; it does not remove C02-095 through C02-097 from statement coverage. |

## 2.9 Exercises: pp. 28–29

The chapter's seven numbered exercises are included in the user's requested
whole-book scope. They are not optional simply because `Sorting.thy` omits their
solutions. Open-ended Exercise 2.7 requires a documented concrete selection,
not every imaginable sorting algorithm.

| ID | Exercise and exact target | Reuse, derivation, and remaining gap |
|---|---|---|
| C02-099 | Exercise 2.1, optimal case: sorted `xs` of length `n` has `Tinsort xs = 2*n + 1`. Establish the corresponding global lower bound to justify “optimal.” | G: C02-011/012 plus insertion fixed point; `List.Pairwise.insertionSort_eq` is reusable. |
| C02-100 | Exercise 2.1, worst case: `Tinsort (reverse (range n)) = (n+1)*(n+2)/2`. Establish the triangular global upper bound to justify “worst,” stronger than Lemma 2.1. | G. The displayed range is `[0..<n]`, length `n`; the earlier prose `[n,...,0]` has length `n+1`. Retain this index distinction. |
| C02-101 | Exercise 2.2: define accumulating `quicksort2 xs ys` using only cons, with no append in its recursive implementation; prove `quicksort2 xs ys = quicksort xs ++ ys`. | G. A valid recurrence is `q2 [] ys = ys`, `q2 (x::xs) ys = q2 less (x :: q2 greaterEq ys)`. This is an implementation proposal, not a new accepted definition. |
| C02-102 | Exercise 2.3: `partition3 pivot xs` gives `<`, `=`, `>` filtered lists; `quicksort3` recursively sorts only the strict parts and places pivot plus equal list between them. Prove both sortedness and multiset preservation. | G. Termination follows filter-size bounds. Do not confuse this three-filter definition with the later selection chapter's separately costed partition implementation. |
| C02-103 | Exercise 2.4, both parts: use the supplied `Tquicksort` recurrence, prove exact quadratic cost on sorted inputs, and prove the same polynomial is a global upper bound. | G. With Appendix B.1's `Tfilter (fun _ => 1) xs = 2*len xs + 1`, the coefficients are **a=2, b=2, c=1**, so the target is `2*n^2 + 2*n + 1`. This arithmetic is an inventory derivation, not a Lean proof. See metric caveat below. |
| C02-104 | Exercise 2.5: define alternating, accumulating `halve`, matching `halve [2,3,4] ([0],[1]) = ([4,2,0],[3,1])`; define the displayed two-base-case `msort2`; prove sortedness and multiset preservation. | G. Necessary support: combined multiset preservation and strict lengths of both initially empty halves for input length at least two. Existing merge contract is reusable. The exercise does not request a numeric time theorem, but the splitter should make one traversal rather than call `length`, `take`, `drop`. |
| C02-105 | Exercise 2.6: define tail-recursive `merge_adj2 acc xss` without append, and `merge_all2`, `msort_bu2`; prove `M (msort_bu2 xs) = M xs` and sortedness. | G. Retain the same comparison complexity and prove termination. Intermediate equality `merge_adj2 [] xss = merge_adj xss` is explicitly not required. The natural prepending-accumulator version reverses run order and therefore cannot inherit keyed stability automatically. |
| C02-106 | Exercise 2.6 support, also accidentally printed in §2.5: `len (merge_adj2 acc xss) = len acc + (len xss + 1)/2`; `MM (merge_adj2 acc xss) = MM acc + MM xss`; `M (merge_all2 xss) = MM xss`. | G. Prove these for the actual chosen tail-recursive definition. A same-complexity witness can use comparison count equality with the ordinary pass, or its exact per-pair additive formula; do not infer source traversal cost from final sorting equality. |
| C02-107 | Exercise 2.7: adapt a stated selection of non-insertion algorithms to keys; prove correctness and stability. | R/P: existing top-down `sortOn` with `sortOn_spec` is one direct solution once its Chapter 2 recurrence bridge is established. Existing `mergeBy_spec` supplies the key merger. If more algorithms are selected, state their exact scope; natural runs must reverse only strictly decreasing keys, and tail-reversed bottom-up passes need care. This exercise does not ask for every variant to be stable. |

### Exercise 2.4 metric, independently checked arithmetic

The specified recurrence is:

```text
Tq [] = 1
Tq (x::xs) = Tq (filter (<x) xs) + Tq (filter (>=x) xs)
              + 2 * Tfilter (fun _ => 1) xs + 1.
```

Appendix B.1, pp. 347–348, gives `Tfilter TP [] = 1` and a cons step adding
`TP x + 1`. Thus a length-`m` tail has filter cost `2*m + 1`. On a sorted input
of length `n > 0`, one recursive side is empty and the other has length `n-1`,
so `Tq(n) = Tq(n-1) + 4*n`, with `Tq(0)=1`. Summing yields
`2*n*(n+1)+1`. For arbitrary partition lengths `l+r=n-1`, the gap between this
polynomial at `n` and the recurrence using the two polynomial bounds is `4*l*r`,
which is nonnegative.

This supplied recurrence **does not include append traversal cost**, despite
the direct quicksort implementation using append. Preserve it as the exercise's
explicit abstract metric. Do not describe it as the complete §1.5 function-call
count for the literal quicksort code without a separate corrected instrumented
implementation and a relation between the two metrics. C02-024 separately
retains the book's average-input and randomized-pivot claims, with explicit
distributions, distinct-key assumptions, and a checked connection to the
chosen resource observation. The deterministic calculation here does not
discharge either probabilistic obligation.

## Corrections and ambiguities requiring explicit treatment

1. **§2.5, p. 19, (2.16) and preservation statements:** the displayed code defines
   `merge_adj` and `merge_all`, but the text then prints `merge_adj2 acc` and
   `merge_all2`, which are introduced only in Exercise 2.6. The main
   `Sorting.thy` states the non-accumulator laws recorded as C02-041, C02-045,
   and C02-046. The intended basic laws are needed by the following proofs;
   the literally printed accumulator laws must additionally be accounted for
   in C02-106. Do not replace undefined functions with axioms.
2. **§2.7, p. 26, order discussion:** the prose claims that a non-linear order
   supplies distinct `x,y` with `x <= y` and `y <= x`. Failure of linearity
   alone does not imply this; it describes a failure of antisymmetry. The
   displayed uniqueness theorem is valid under its linear-order assumptions,
   and in fact needs only antisymmetry once both outputs are pairwise sorted.
   Reuse Mathlib's weaker theorem. For equal-key records the pulled-back
   relation can fail antisymmetry, making the separate stability observation
   essential; the existing `sorted_permutation_not_stable` example captures
   that distinction.
3. **Expository boundaries versus whole-book scope:** the chapter says it
   does not analyze quicksort running time in its main exposition, then
   assigns worst-case analysis as Exercise2.4 and states average/expected
   bounds with external citations. Full coverage includes the exercise
   and both mathematical average/expected assertions. The original version
   of this inventory incorrectly classified those assertions as excluded;
   that classification was corrected on 2026-11-02 under the governing
   whole-book request and `DECISIONS.md`. The cited papers do not thereby
   become whole-paper formalization goals. Preserve the distinct input-order
   and random-pivot distributions and their duplicate-key/cost limitations.
4. **Ceiling logarithm at zero and coercions:** the Isabelle natural-merge
   bounds use totalized real logarithm and integer ceiling. Preserve source
   meaning for zero/one explicitly when choosing Lean's natural logarithm
   interface; do not conceal a positivity premise by implicit coercion.
5. **Semantics versus measured algorithm:** all correct ordinary sorters have
   the same result, but that does not permit moving a comparison count from
   one recurrence to another. Each cost theorem must name its own execution
   or prove a cost-preserving correspondence.

## Completeness cross-check and implementation handoff

The checklist accounts for every section 2.1–2.9, all named results Lemmas
2.1–2.5, Corollary 2.6, Lemmas 2.7–2.8, Theorem 2.9, Corollary 2.10, and Lemma
2.11; all numbered displays (2.1)–(2.38); the displayed algorithm/cost
definitions; supporting unnumbered preservation and sortedness claims; and all
seven exercises. Displays (2.33)–(2.34) are proof premises rather than extra
standalone claims. The natural-merge source invariant and nonempty/logarithm
side-condition lemmas are included where the book elides them.

Numbered-display map:

| Displays | Checklist IDs |
|---|---|
| (2.1)–(2.5) | C02-006–C02-010 |
| (2.6)–(2.8) | C02-013–C02-015 |
| (2.9) | C02-018 |
| (2.10), (2.11), (2.12) | C02-028, C02-029, C02-031 |
| (2.13)–(2.15) | C02-035–C02-037 |
| (2.16), (2.17) | C02-041/C02-106, C02-046/C02-106 |
| (2.18)–(2.20) | C02-049, C02-054, C02-055 |
| (2.21)–(2.26) | C02-064–C02-068, C02-070 |
| (2.27)–(2.29) | C02-073–C02-075 |
| (2.30), (2.31), (2.32) | C02-077–C02-079, C02-080–C02-082, C02-083–C02-085 |
| (2.33), (2.34) | C02-091 |
| (2.35)–(2.38) | C02-094–C02-097 |

After Chapter 1 is accepted, a useful order is to connect existing sorting and
insertion/merge recurrences first, add their measured executions with separate
call/comparison observations, then quicksort and top-down costs, bottom-up
passes, natural runs and logarithmic bounds, and the exercise variants. That is
a dependency suggestion, not permission to skip any item or start the next
chapter early. Reuse existing resource composition/reweighting facilities and
the Chapter 1 cost interface rather than introducing independent per-algorithm
writer structures.

Checked applications should include empty/singleton inputs, repeated equal keys
with distinguishable payloads, ascending and strictly descending lists, odd and
even split lengths, odd numbers of runs, mixed ascending/descending runs,
equal-key boundaries in runs, non-power-of-two input lengths for natural merge
sort, and zero/one logarithm boundaries. Use these to test intended statements
and composition, not only to restate the implementation. Preserve existing
`Examples.StableSorting` counterexamples and payload-map transport.

No task status, ticket state, source repository, build configuration, Lean file,
or Library item was changed by this investigation.

## Scope clarification of C02-088: recorded 2026-11-02

This is the bounded reconciliation of CSW-01 in `coverage-scope-audit.md`.
The frozen `../reviews/chapter02-requirements.md` remains unchanged, including
its reference to the original 107-row inventory with SHA-256
`edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
That exact earlier inventory is preserved under
`../reviews/source-inventories-before-scope-repair/`.
All C02-001–107 obligations remain. The following rows unpack mathematical
claims already identified by C02-088 and printed on pp.21–22; they do not
silently replace the frozen specification or change the comparison counters.
Old/new hashes and the reason are recorded in `scope-reconciliation.md`.

The source's `Cruns`, `Casc`, `Cdesc` and `Cnmsort` continue to count only
comparisons. Closure creation/application, constructor work and list-copy
work, when used to prove the separate operational prose claims, receive a
distinct named tariff. Do not add these charges to the printed counters.
No theorem about compiler allocation, garbage collection, or Haskell/Lean
machine time is implied.

| ID | Required statement and source location | Exact model and remaining work |
|---|---|---|
| C02-108 | Sorted-input best case, pp.21–22: for nonempty sorted xs, `runs xs=[xs]`, `Cmerge_all(runs xs)=0` and `Cnmsort xs=length xs-1`. Empty input has zero comparisons. | Prove through the actual mutual recurrences. The supporting identities `Casc a ys=length ys`, `Cdesc a ys=length ys`, `Cruns xs=length xs-1` give the comparison lower bound for every length-n input as well as the attained best case; retain the source's weaker C02-083–085 statements as corollaries. The linear best-case conclusion concerns n tending to infinity, not a positive lower bound at n=0/1. |
| C02-109 | Repeated append versus cons/reverse, p.22: appending n singleton values to an initially empty ordinary-list accumulator has append-call subcost `n*(n+1)/2`; the full fixed-overhead builder therefore has quadratic worst-case time. Prepending those values and applying the verified accumulator reverse has linear work and the same ordered result. | The displayed sum uses `appendTime prefix [x]=length prefix+1`; state loop/wrapper costs separately. Reuse Chapter1's checked reverse/count bridge. This is a particular source-described construction, not a claim that every extensionally equivalent list builder is quadratic. |
| C02-110 | Difference-list append, p.22: creating the composed builder has constant local work independent of the represented list lengths, and its value is function composition with the correct append order. | Give an explicit abstract closure-construction/application observation or a checked equivalent measured builder interface. Creating a composition node does not execute its two stored functions. Prove the bounded creation tariff and the value correspondence separately; do not derive either cost from the extensional D invariant alone. |
| C02-111 | Difference-list materialization, p.22: applying a finite builder built from identity, singleton-prefix and composition to a suffix has work bounded linearly in its construction representation, with exact value equal to its represented prefix appended to that suffix. | Under a unit closure-entry model, application visits the construction nodes; use a proved recurrence/trace relation. Prove the actual asc-generated builder has representation size linear in its emitted prefix length. Arbitrary extensionally valid functions or arbitrarily many empty compositions need not have cost controlled by output length; retain that boundary instead of asserting unrestricted linearity from D. |
| C02-112 | The actual runs/asc/desc construction has `W_runs xs<=A*length xs+B` in the chosen closure/scanner model, with fixed constants, hence the single-run natural-sort execution has linear operational work as well as C02-108's linear comparisons. | Count scanner steps, creation and application of the actual ascending builders, descending cons construction, emitted-run list construction and the actual empty/single-run merge dispatch. Relate builder representation size to source execution. The arbitrary-D worker correctness theorems retain their full semantic generality; operational bounds on arbitrary worker inputs need a supplied builder-cost/representation contract. |

The unrestricted interpretation that every function satisfying D materializes
in time linear solely in the length of its output is not a consequence of the
source's value invariant. In a model that charges closure applications, a
construction history containing k nested compositions of identity builders
can have empty represented output and application work growing with k.
Preserve a checked model-level example or equivalent independence witness when
implementing C02-111. The faithful positive target is the actual finite builder
construction and its source-specific size relation. The book's comparative
performance opinion about particular functional languages remains analysis.

All 112 IDs remain queued; these research clarifications are not implementation
or acceptance evidence.
