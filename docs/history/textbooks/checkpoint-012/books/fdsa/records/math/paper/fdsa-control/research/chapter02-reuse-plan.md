# Chapter 2: exact reuse and implementation plan

Prepared 2026-11-02 for `FDSA-002`, while Chapter 1 remains under verification.
This is a read-only plan for the 107 obligations in
`chapter02-obligations.md`, not chapter activation, accepted coverage, a build
result, or either independent acceptance review.

## Evidence and conclusions

The integrated source inspected is conaled
`1aabd512284fe86254278ac631eda061d311050b`. Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries to
`66e469188fe07963e5cf666c7d4433f45b8131c5`. The separate insertion-cost worktree
is pending `FDSA-X002`, not an accepted dependency. Its current public names are
included below so those results need not be implemented again after acceptance.

Book and Isabelle/AFP identities are recorded in `chapter02-obligations.md`.
The book is the July 27, 2026 edition, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`,
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
For this plan the pinned Lean definitions were also inspected directly:

- Lean tag `v4.35.0` resolves to commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- [Sort/Basic.lean](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Sort/Basic.lean),
  SHA-256 `a100c2a753aae0dda38a6e3afaca64f7ea70f4eba73d007ac29b5889fbf842ac`.
- [Sort/Lemmas.lean](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Sort/Lemmas.lean),
  SHA-256 `e04f8070b20080cdbcdd31a6d240e267363e308a5804fdaf6749c92a885547c0`.
- [Sort/Impl.lean](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Sort/Impl.lean),
  SHA-256 `6db1a2a95fa6db3bebcd4197749fe3b5d21e3f80323e18e9047525264bcd3923`.

These Lean files carry Apache-2.0 notices. Reading copies and the source-tree
manifest are under `book-source/` and excluded from checkpoints; this original
plan preserves the recovery provenance. No installed Lean source tree was assumed.

**Substantial value-level reuse exists, but most source comparison analyses and
the additional sorting algorithms remain new work.** Four findings refine the
earlier inventory:

1. **The standard top-down split differs on odd lengths.** Lean's
   `List.MergeSort.Internal.splitInTwo` takes `(n+1)/2` elements on the left;
   the book and `Sorting.thy` take `n/2`. `splitInTwo_fst`/`splitInTwo_snd`
   confirm this. `List.mergeSort_append` likewise requires the first half to
   be the larger one, so it does not supply the book's odd-length recurrence.
   A floor-left source realization is needed for its source comparison model.
2. **The difference-list representation already exists.** `Batteries.DList`
   has `apply : List α → List α` and invariant `apply ys = apply [] ++ ys`.
   This is equivalent to the book's `D f`, and `DList.push f a` implements
   `f ∘ List.cons a`. Use the existing carrier and prove the source-law adapter;
   do not invent another difference-list structure.
3. **The logarithm recurrence already exists.** `Nat.clog_of_two_le` gives the
   ceiling-halving recurrence; `Nat.clog_mono_right`, `Nat.clog_pow` and
   `Real.natCeil_logb_natCast` supply its monotonicity, powers and real-log bridge.
   A new log definition or a wrapper that merely renames these is unnecessary.
4. **Three-way partition values already exist.** Selection's `partition3` and
   `partition3_eq_filters` give the exact three lists, with permutation,
   membership and length laws. The three-way quicksort itself is missing.
   Its use does not establish a one-pass partition cost; that is a later,
   separate source realization.

### Concrete split/cost witness

The following was independently evaluated with the displayed merge comparison
recurrence and the two split rules; it is not yet a Lean theorem:

| Input | Book floor-left output / comparisons | Lean logical ceil-left output / comparisons |
|---|---|---|
| `[0,1,2]` | `[0,1,2]` / 2 | `[0,1,2]` / 3 |
| `[2,1,0]` | `[0,1,2]` / 3 | `[0,1,2]` / 2 |

For the first row, the book sorts `[1,2]` with one comparison and merges `[0]`
in one more. Lean sorts `[0,1]` with one comparison and merges `[2]` using two.
Preserve this as a small checked counterexample to an invalid cost transfer.
Lean also replaces its logical definitions at runtime through proved value
equalities in `Sort/Impl.lean`; those replacements do not assert equality of an
external source cost observation.

## Proposed placement and dependency order

Keep the existing `KeySorted`, `Stable`, `StableSort`, `mergeBy`, `sortOn` and
`insertionOn` interfaces. Ordinary sorting contracts remain pairwise order plus
permutation; they must not acquire unnecessary key-stability hypotheses. The
following are proposed module groupings, not a mandate to create a file per row.

| Work family | Placement and reusable boundary |
|---|---|
| Ordinary/keyed insertion bridges | `Applications/Sorting/Insertion.lean`, importing the existing sorter and standard laws; no duplicate insertion implementation. Keep pending measured work in `Applications/Resources/InsertionSort.lean`. |
| Merge converse and standard observations | Extend `Applications/Sorting/Merge.lean`; retain `SourceMerge.lean` as the existing literal recurrence adapter. |
| Book floor-left top-down sorter | `Applications/Sorting/TopDown.lean`; exact recurrence, termination, ordinary/keyed contracts and value agreement with `sortOn`. Agreement is a value theorem only. |
| Two-way, accumulator and three-way quicksort | `Applications/Sorting/Quick.lean`; shared filter/partition facts. If sharing the existing partition implementation, extract its independent fragment to `Applications/Sequences/Partition.lean` and preserve Selection's public names by adapters. Do not make the sorting implementation depend on the entire selection algorithm. |
| Adjacent passes, repeated passes, tail variants | `Applications/Sorting/BottomUp.lean`; one ordinary pass and its accumulator realization, sharing standard merge and flatten/permutation observations. |
| Natural runs and their sorter | `Applications/Sorting/NaturalRuns.lean`; use `Batteries.DList` for the ascending worker, ordinary cons accumulation for the descending worker, and the shared bottom-up merger. |
| Alternating splitter and its sorter | `Applications/Sorting/Halve.lean`; actual one-pass alternating accumulator recurrence, not take/drop. |
| Comparison observations | `Applications/Resources/MergeSort.lean` for measured merge, floor-left sorting and merge-pass bounds; `Applications/Resources/NaturalSort.lean` for measured run scanning and composition. Split these only where size/dependencies justify it. |
| Supplied quicksort exercise metric | `Applications/Resources/QuickSort.lean`; retain the charged filter predicate and the explicit omission of append traversal. |
| Quicksort average and randomized assertions | Retain both as new mathematical obligations. Share the measured sorter/resource observation and the existing probability domain; detailed source, finite-distribution and cost correspondences are in `quicksort-average-proof-plan.md`. |
| Connected clients | `Examples/SortingSources.lean` and `Examples/SortingCosts.lean`, reusing `StableSorting` and pending `InsertionCosts`; exact source recurrences, distinct cost models, stable payload observations and selection composition. |

Implement shared bridges and measured merge first. The arbitrary-run-count
merge-all bound can then imply its uniform/power-of-two specializations, avoiding
duplicate asymptotic proofs. Natural runs depend on the ordinary merge-all
construction. The exercise variants consume those operations and observations.
No new Lake package, sorting specification, logarithm family or measured-value
framework is needed.

## Full obligation mapping

Labels: **R** = inspected exact reusable statement; **A** = small adapter or
missing theorem over an existing operation; **N** = new source operation or
resource proof; **P** = pending FDSA-X002; **D** = expository/proof correspondence
using the identified mathematical result, never an exemption for an asserted
mathematical claim. None of these labels means chapter acceptance. Namespace abbreviations
below are `Sorting = Applications.Sorting` and
`IS = Resources.InsertionSort` (pending).

### Specification and insertion

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-001 | R: standard `LinearOrder`; existing operations expose weaker capabilities. | Record the book specialization without strengthening generic comparator APIs. |
| C02-002 | R: `List.Pairwise`, `List.pairwise_cons`, `Sorting.KeySorted id`. | Name the direct source correspondence; do not substitute adjacent-only order without its bridge. |
| C02-003 | A: pairwise order plus `List.Perm`; `Multiset.coe_eq_coe`. | Bridge permutation to the book's multiset equality; no new sorting-spec record. |
| C02-004 | R: `List.orderedInsert`, `orderedInsert_nil`, `orderedInsert_cons`. | Instantiate `r=(<=)` and retain the left tie branch. |
| C02-005 | R: `List.insertionSort`, `insertionSort_nil`, `insertionSort_cons`; `Sorting.insertionOn id`. | Record its right-fold/source recurrence. |
| C02-006 | A: `List.perm_orderedInsert`; `Multiset.coe_eq_coe`, `Multiset.cons_coe`, `singleton_add`. | Convert to singleton multiset plus input. No payload equality decision is needed. |
| C02-007 | A: `List.perm_insertionSort` and `Multiset.coe_eq_coe`. | Convert the existing permutation witness to multiset equality. |
| C02-008 | R/A: `List.mem_orderedInsert`. | Set extensionality gives the source singleton-union equation. |
| C02-009 | A: `List.Pairwise.orderedInsert`, `List.sublist_orderedInsert`, `List.Pairwise.sublist`. | Assemble the iff; only the forward direction needs the sorting relation's totality/transitivity. |
| C02-010 | R: `List.pairwise_insertionSort`; `(Sorting.insertionOn_spec id xs).sorted`. | Prefer the ordinary standard result where the key-stability contract adds unused assumptions. |
| C02-011 | P: `IS.insertRun`, `insertRun_value`. | After X002 acceptance, record the cost projection's empty/conditional equations. |
| C02-012 | P: `IS.sortRun`, `sortRun_cons_cost`, `sortRun_value`. | Record the actual sorted-tail dependency, not a recurrence on an unrelated sorter. |
| C02-013 | P: upper component of `IS.insertRun_cost_bounds`. | Specialize to the source relation. |
| C02-014 | R: `List.orderedInsert_length`. | Exact length-plus-one statement. |
| C02-015 | R: `List.length_insertionSort` or `List.perm_insertionSort.length_eq`. | Pending `IS.sortRun_length` connects the measured value too. |
| C02-016 | P: `IS.sortRun_quadratic`. | Source square bound follows with empty input cost 1 retained. |

### Quicksort

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-017 | N; reusable `List.filter` and `List.length_filter_le`. | Implement the first-pivot `<`/`>=` recurrence and length-based termination; no matching integrated sorter was found. |
| C02-018 | N; `List.filter_append_perm` is already used by Selection. | Prove the new quicksort permutation by recursion, then apply the multiset bridge. |
| C02-019 | R: `Multiset.filter_coe`. | Exact list-filter/multiset-filter equality, with the standard decidable-predicate adapter. |
| C02-020 | R/A: `Multiset.filter_add_not`, `Multiset.filter_congr`. | Instantiate complementarity of `< pivot` and `>= pivot`; no new multiset partition theory. |
| C02-021 | R: `List.pairwise_append`. | Use the same source nondecreasing relation and both cross-list quantifiers. |
| C02-022 | A after C02-018: `List.Perm.mem_iff`. | Derive set preservation for the new quicksort. |
| C02-023 | N, using C02-021 plus filter membership and permutation. | Prove ordered left/pivot/right concatenation for the source recurrence. |
| C02-024 | N: two distinct probability/cost theorems; exact primary references and reusable APIs are mapped in `quicksort-average-proof-plan.md`. | Prove the stated `O(n log n)` average bound for first-pivot quicksort under a uniform ordering of distinct keys, and the expected bound for a uniformly chosen pivot occurrence at every recursive call on fixed distinct-key input. Preserve lawful total order, actual execution/distribution correspondence, duplicate-key limitations, and the explicit resource observation. Neither follows from deterministic Exercise 2.4. |

#### Scope correction for C02-024

The actual closing paragraph of §2.3 is on printed p. 16 (PDF p. 22) of the
pinned book. It states a quadratic worst case, an `O(n log n)` average-input
bound, and an `O(n log n)` expected bound with randomized pivots. The authors'
decision to leave the probabilistic analysis outside their exposition is not
a mathematical exclusion from the user's whole-book reconstruction. The
earlier `D` classification in this plan was therefore incorrect and was
corrected on 2026-11-02. This correction changes no chapter acceptance state.

The quadratic worst-case assertion remains connected to Exercise 2.4 on
printed pp. 28–29, C02-103: its exact supplied tariff has attained maximum
`2*n^2+2*n+1`. That exercise explicitly omits append traversal, so a statement
about the literal append-using execution also needs a proved cost bridge.
The two probabilistic claims remain additional obligations. The standard
precise models use a uniform input permutation of distinct totally ordered
keys, or uniform pivot-occurrence selection in every recursive subproblem
of a fixed distinct-key input, respectively. They are not an arbitrary
probability distribution on values and are not the same theorem merely
because their asymptotic conclusions agree.

Distinctness is substantive for the displayed two-way partition: an input
of n equal keys always leaves one recursive side of size n-1, regardless of
input permutation or which equal occurrence is selected as pivot. It has
the same quadratic exercise count; silently substituting three-way quicksort
would change the algorithm. The book's phrase qualifying its average-case
claim leaves these assumptions to the reconstruction; the stronger
unrestricted duplicate-input interpretation is false. The separate root
note `quicksort-average-proof-plan.md` pins AFP's probability proofs and
records the actual measured-execution, distribution and append-cost bridges.
It supplies the proof plan without making all results in the cited papers
new coverage milestones.

### Top-down merge sort

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-025 | R: `Sorting.sourceMerge`, `sourceMerge_eq_merge`, `mergeBy_source`; `List.merge`. | Already matches the source base and left-tie branches. |
| C02-026 | N/A: standard merge and sort contracts, but **not** the standard split. | Add an actual floor-left source recurrence; prove its value agreement with `sortOn` under appropriate order/stability laws. |
| C02-027 | R/N: `sourceMerge` already has sum-of-length termination. | For C02-026 prove both floor-half lengths strictly decrease; standard `take`/`drop` length laws and natural arithmetic suffice. |
| C02-028 | A: `Sorting.mergeBy_perm`, `List.merge_perm_append`, `Multiset.coe_eq_coe`, `Multiset.coe_add`. | Transport concatenation permutation to the source multiset sum. |
| C02-029 | R/A: `List.mem_merge`. | Set extensionality supplies the union equation. |
| C02-030 | N/A: source floor recursion plus `mergeBy_perm`. | Prove its permutation directly; later value agreement permits standard theorem transport but cannot replace this implementation. |
| C02-031 | A: `mergeBy_sorted` supplies construction from sorted inputs. | Add each input as a sublist of `List.merge` for arbitrary comparator, then inherit pairwise order for the converse. No matching sublist theorem was found in inspected pinned files. |
| C02-032 | N/A: `mergeBy_sorted`/`mergeBy_spec`, recursively. | Establish the source sorter's ordinary/keyed correctness; standard `sortOn_correct` alone is about the other split. |
| C02-033 | N over exact `List.merge`. | Measured merge charges zero on empty-side branches and one per head comparison; prove erasure and branch equations. |
| C02-034 | N over C02-026. | Measured floor-left sort uses the actual measured sorted halves; zero base count and no function-entry/split charges. |
| C02-035 | R: `List.length_merge`; alternatively `mergeBy_perm.length_eq`. | Source adapter specializes the exact sum-of-lengths law. |
| C02-036 | A after C02-030: permutation length. | The standard `List.length_mergeSort` only transports after a valid source value bridge. |
| C02-037 | N: induction on measured merge, standard length arithmetic. | Prove the stated length-sum comparison upper bound without adding sortedness premises. |
| C02-038 | N: induction on exponent, half-size arithmetic, C02-037. | Prove `k*2^k` for the source recurrence with length `2^k`; handle the singleton exponent-zero case. |
| C02-039 | A after C02-038: `Real.logb_pow`, `Real.logb_self_eq_one`. | Coercion/power-of-two conversion gives the real `n*log_2 n` statement. |

### Bottom-up merge sort

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-040 | N, reusing `List.merge`/`mergeBy`. | Implement the adjacent-pair pass with unchanged empty/singleton run lists. |
| C02-041 | N: structural induction on the pass. | Prove run count `(length xss+1)/2`; this is the corrected ordinary-pass statement. |
| C02-042 | N: C02-041 and a decreasing run count. | Implement repeated adjacent passes, with empty output `[]` and singleton output that run. |
| C02-043 | N: `List.map List.singleton` and C02-042. | Define the source singleton-run sorter. |
| C02-044 | A: `List.flatten`, standard list-to-multiset coercion/addition. | Use multiset of flatten as the observation; prove the equivalent sum of inner multisets once by list induction. |
| C02-045 | N: pass-level flatten permutation using `merge_perm_append`. | Convert to the corrected ordinary-pass multiset equation. |
| C02-046 | N: repeated-pass invariant from C02-045. | Prove output permutation of the flattened original runs. |
| C02-047 | A after C02-046: flatten of singleton-map. | Recover ordinary bottom-up multiset correctness. |
| C02-048 | N/A: `mergeBy_sorted`. | Prove every pass output run is sorted when every input run is sorted. |
| C02-049 | N: pass preservation and repeated-pass induction. | Preserve the quantified sorted-run premise. |
| C02-050 | A: C02-049 and `List.pairwise_singleton`. | Specialize to the singleton-run sorter. |
| C02-051 | N over measured merge. | Instrument each adjacent pair and add its actual comparison count; empty/singleton pass costs zero. |
| C02-052 | N over measured passes. | Accumulate each pass and recur on the runs that pass actually produced. |
| C02-053 | A after C02-052. | Specialize measured repeated merging to singleton-map. |
| C02-054 | N: pass recurrence and `List.length_merge`. | Prove length doubling with even run count; preserve the unmerged odd leftover case as a counterexample to dropping evenness. |
| C02-055 | A after C02-073 plus uniform inner lengths. | Derive `m*length xss`; evenness is unnecessary for this cost bound. |
| C02-056 | A after C02-076: uniform flatten length and `Nat.clog_pow`. | Derive `m*k*2^k`, retaining `m=0`; a second special-purpose induction is unnecessary. |
| C02-057 | A after C02-056, with `m=1`. | Recover the source power-of-two bound for bottom-up sorting. |

### Natural-run merge sort and general merge-all bound

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-058 | N; standard list recursion and chosen key comparison. | Implement exact empty/singleton/start-direction branches; descending starts only on a strict decrease. |
| C02-059 | N/A: `Batteries.DList.apply`, `singleton`, `push`. | Implement the ascending worker and prove its source raw-function recurrence under the D-law adapter. |
| C02-060 | N: ordinary cons accumulation. | Implement the descending worker and restart branch; preserve strictness and every duplicate occurrence. |
| C02-061 | A: `Batteries.DList.invariant`, `push`, `toList_push`; associativity. | Prove `D f` iff `forall ys, f ys=f []++ys`, then wrap any source `f` satisfying D, not just reachable initial builders. |
| C02-062 | N: well-founded mutual recursion. | Candidate common measure: `length xs` for runs, `length ys+1` for each worker. Every continuation/restart decreases this measure. |
| C02-063 | A after the new runs and existing-in-plan merge-all. | Define natural sort as their composition. |
| C02-064 | N: DList invariant, flatten permutation, mutual induction. | Prove the arbitrary-valid-builder multiset equation; do not remove D when stating it for raw functions. |
| C02-065 | N: descending recurrence and cons/permutation laws. | Prove its multiset equation for arbitrary accumulator and remaining input. |
| C02-066 | N: the same mutual-induction group. | Prove flattened runs preserve the original input multiset. |
| C02-067 | A: C02-046 and C02-066. | Compose natural-sort permutation/multiset correctness. |
| C02-068 | N: worker sortedness invariants and list pairwise laws. | Prove every produced run is sorted. |
| C02-069 | N: existing `Pairwise` append/cons rules. | Preserve both worker invariants: ordered prefix bounded above by current head, or ordered accumulator bounded below by it. |
| C02-070 | A: C02-049 and C02-068. | Compose natural-sort sortedness. |
| C02-071 | N over the exact mutual branches. | Charge each tested adjacent pair once; accumulator application does not affect the comparison count. |
| C02-072 | A/N: `Resources.bind` on measured run production and merging. | Prove the displayed sum at the actual produced runs, without charging DList application. |
| C02-073 | N: measured pass, C02-037 and flattened-length decomposition. | Prove pass comparisons at most total number of elements, for arbitrary run lengths/counts. |
| C02-074 | A: C02-045 flatten permutation and `.length_eq`. | Exact preservation of total number of elements across a pass. |
| C02-075 | R/A: `Nat.clog_of_two_le` (or `clog_of_one_lt`), base 2. | Rewrite `(n+1)/2=(n-1)/2+1` for `n>=2`; use `Real.natCeil_logb_natCast` for the book's ceiling. |
| C02-076 | N: C02-041, C02-073/074 and C02-075. | Induct on run count to prove `totalLength * Nat.clog 2 runCount`; empty/singleton cases are explicit. |
| C02-077 | A after C02-064: permutation length and the DList adapter. | Obtain `1+length(f [])+length ys`; do not count only the remaining input. |
| C02-078 | A after C02-065: permutation length. | Obtain `1+length acc+length ys`. |
| C02-079 | A after C02-066: permutation length. | Obtain total produced-run length equal to input length. |
| C02-080 | N: mutual worker/run-count induction. | Ascending output-run count at most `1+length ys`; the arbitrary prefix length is not part of this bound. |
| C02-081 | N: the same induction. | Descending output-run count at most `1+length ys`. |
| C02-082 | N/A from C02-080/081 and start cases. | Runs count at most original list length. |
| C02-083 | N: measured-worker mutual induction. | Ascending comparisons at most worker-tail length. |
| C02-084 | N: the same induction. | Descending comparisons at most worker-tail length. |
| C02-085 | N/A from C02-083/084 and start cases. | Whole scan comparisons at most `length xs-1`, using truncated natural subtraction. |
| C02-086 | A after C02-072/076/079/082/085; `Nat.clog_mono_right`. | Derive the printed `n+n*Nat.clog 2 n` bound; explicitly bridge its real-log form. |
| C02-087 | N/R: worker/run nonemptiness; `Nat.clog_monotone`/`clog_mono_right`. | Establish actual nonempty-output premises; standard log monotonicity needs no replacement theory. |
| C02-088 | N/D: sorted-input branch analysis and C02-071. | Prove one run for nonempty sorted input, scan count `n-1`, merge count zero. Keep machine-cost claims for closure composition/materialization conditional. |

### Uniqueness, keys and stability

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-089 | R: `List.Perm.eq_of_pairwise'` under `Std.Antisymm r`. | Use the ordinary multiset/permutation bridge; totality and stability are not needed once both lists are pairwise sorted. |
| C02-090 | A: C02-089 and function extensionality. | State pointwise/function equality for any two ordinary correct sorters, not only the existing keyed pair. |
| C02-091 | D/R: the preceding standard uniqueness proof. | Account for the displayed induction premises without redundant public wrappers. |
| C02-092 | R/A: `Sorting.KeySorted`, `Stable`, `StableSort`, `List.pairwise_map`. | Bridge pulled-back key order to pairwise order of mapped keys; preserve full-record permutation and filtered record sequences. |
| C02-093 | R: generic `List.orderedInsert` and `Sorting.insertionOn key`. | Same source recurrences after pulling back key `<=`; no payload order. |
| C02-094 | R/A: `insertionOn_spec`, permutation/membership of `orderedInsert`, C02-009 and pairwise-map. | Record both sorter correctness and the keyed one-element support statements. |
| C02-095 | A: `List.orderedInsert_cons_of_le`, with nil/cons split. | Establish insertion equals cons under the displayed forall-members premise. |
| C02-096 | A: induction on `List.orderedInsert` and `List.filter_cons`. | Missing filter-negative insertion law; no sortedness or order laws are required beyond the decidable relation/predicate. |
| C02-097 | A: insertion recurrence, pairwise order and transitivity. | Missing filter-positive insertion law. Preserve sorted-input premise; totality is not needed for this helper if relation transitivity is exposed directly. |
| C02-098 | R: `(Sorting.insertionOn_spec key xs).stable k`. | Exact equal-key filter theorem; use its existing proof while separately covering the book's displayed helpers. |

### Exercises

| ID | Exact reuse anchor | Remaining implementation or witness |
|---|---|---|
| C02-099 | P: `IS.sortRun_cost_of_pairwise`, `sortRun_cost_lower`. | Exact sorted-input optimum, including duplicates, empty and singleton. |
| C02-100 | P: `IS.sortRun_cost_reverse_range`, `sortRun_cost_le`. | Exact attained triangular worst case and uniform upper bound; retain range length `n`. |
| C02-101 | N: new quicksort, arbitrary-suffix induction. | Implement `q2 less (pivot :: q2 greaterEq suffix)` using cons only, then prove `q2 xs suffix = q xs ++ suffix`. |
| C02-102 | N/A: `Selection.partition3_eq_filters`, `partition3_perm`, side membership/length laws. | Implement quicksort3 and its correctness; preserve a shared partition API without importing the whole selector. Tail-filter bounds suffice for termination; pivot membership in the tail is unnecessary. |
| C02-103 | N: supplied cost recurrence, complementary filter lengths, arithmetic. | Prove exact sorted cost and global bound `2*n^2+2*n+1`; predicate tariff is 1 and append traversal is deliberately absent. |
| C02-104 | N: one-pass alternating splitter; merge correctness. | Preserve the specified accumulated order, both smaller halves, sortedness and multiset correctness of msort2. It is neither standard take/drop nor the source floor-left sorter. |
| C02-105 | N: accumulator adjacent pass and repeated pass. | Implement the append-free tail versions, prove ordinary correctness and the requested comparison-complexity preservation. Do not claim keyed stability from ordinary correctness. |
| C02-106 | N: accumulator invariants. | Prove length and flattened-multiset equations for arbitrary accumulator, plus merge-all2 preservation. A pass's comparison formula is reusable even though its run order reverses. |
| C02-107 | R/A/N: existing `mergeBy_spec`, `sortOn_spec`, `StableSort.unique`, `StableSort.map`. | Document a concrete non-insertion selection, preferably the source floor-left top-down sorter. Prove its stable contract from contiguous splits and left-tie merges; then relate it to standard `sortOn`. Other variants are not automatically stable. |

## Implementation choices that prevent rework

**Measure actual source branches.** `Resources.Measured` and `bind` already
provide value/cost sequencing. Insertion counts function calls; merge and natural
sort count comparisons. Keep the names and recurrence correspondence explicit,
even though both observations happen to use `Nat`. In particular, do not reuse a
function-entry tariff as an unstated comparison model. The quicksort exercise
has its own supplied tariff: `Tfilter (fun _ => 1)` is `2*m+1`, and its recurrence
omits append work. These are model choices to preserve, not costs inferred from
value equality.

**Reuse ordinary observation mathematics.** Prove new algorithm permutations
with `List.Perm`; use `Multiset.coe_eq_coe` for book multiset equations,
`Perm.mem_iff` for sets and `Perm.length_eq` for lengths. Use
`List.pairwise_append`, `pairwise_cons`, `pairwise_map` and inherited sublist
order. A new book-specific multiset/set/sortedness foundation would duplicate the
project and Mathlib APIs.

**Do not confuse nearby list algorithms.** `Applications.Subsequences.sourceMergeBy`
is a right fold of merging, not adjacent-pair rounds. `RunCompression.compress`
removes repeated adjacent elements, so it cannot implement natural-run sorting's
partition, which preserves multiplicities. `List.mergeSortTR₂` is a value-proved
runtime replacement, not the book's alternating `halve` or tail-pass exercise.

**Preserve the source defects and exercise restrictions.** The ordinary and
accumulator bottom-up laws both need coverage because the book prints some
accumulator names prematurely. The uniqueness discussion must distinguish
antisymmetry from totality. Accumulator quicksort/merge passes must actually use
cons without append; their final output equality alone does not satisfy those
implementation restrictions. Descending natural runs must remain strict, and
reversed run order in the tail-pass variant must not silently transport stability.

## Completion evidence to retain

Extend existing checked examples only to address distinct remaining risks:
odd-length floor/ceiling split counts; empty/singleton/power-of-two merge bounds;
odd run leftovers and zero-length runs; natural runs with ties at direction
changes; a raw valid difference-list function through its adapter; nonempty
sorted input producing one run; accumulator quicksort with a nonempty suffix;
the displayed alternating-halving example; arbitrary pass accumulators; and
equal-key records that distinguish ordinary correctness from stability.

Pending insertion examples already include a generic payload contract, head-only
tie behavior, occurrence-rank composition and a size-five sorting-only budget.
Reuse them after X002 acceptance; do not count the budget as a complete selection
cost, since the source also charges indexing and length traversal.

For chapter closure, every ID above needs an explicit checked declaration or
reuse/source-correspondence witness (or its stated D-class disposition), plus
statement review and applicable verification/audit at the frozen candidate.
Existing APIs being present, a pending implementation compiling, and the chapter
being accepted are different milestones. Both independent review axes and the
Chapter 1 prerequisite remain in force.

No Lean source, ticket state, repository index/ref, build configuration, Library
item or GitHub object was changed by this preparation.
