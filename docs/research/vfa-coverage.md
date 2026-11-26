# Verified Functional Algorithms: Lean reconstruction map

Current receiving status is owned by [CTB-78](../textbooks/CTB.json), with the
canonical [coverage catalog](../textbooks/coverage.json). The chapter sections
below retain their original mathematical scope and dated donor development
observations; their old pending stages and scratch receipt names are historical,
not a new task queue or evidence of current receiving acceptance. At donor072,
all17 VFA units are locally source-qualified; receiving integration is separate.

This work reconstructs Andrew W. Appel's *Verified Functional Algorithms*,
Software Foundations volume 3, in the existing conaled library. The user has
requested whole-book coverage in chapter order, including optional and advanced
mathematical exercises. This adds to the method-oriented toolkit objective of
upstream issue #174; it does not close that broader workstream or select one
canonical data structure.

The [preserved VFA records](../history/textbooks/checkpoint-012/books/vfa/README.md)
retain original specifications, mathematical work and review conclusions.
Historical ticket labels, including VFA and 1001/1002 labels, belong to those
records; the [exact commit registry](../history/textbooks/issue-lineages.md)
resolves old unqualified messages. No GitHub number range is reserved for them.
[Issue #558](https://github.com/VladimirMarko/conaled/issues/558) supplies upstream
receiving context. The current checkpoint's local CTB tracker owns chapter work,
review state and receiving obligations. This document owns the current VFA
mathematical correspondence; the immutable source inventory owns source records.

## Source identity and qualification boundary

- Author: Andrew W. Appel; editor: Benjamin C. Pierce.
- Edition: **2.1 (2026-08-24 10:11), Coq 9.0.0 or later**.
- [Versioned contents](https://softwarefoundations.cis.upenn.edu/vfa-2.1/toc.html).
- [Versioned source archive](https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz).
- Archive SHA-256: `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
- `Preface.v`: 6,815 bytes, 165 lines; SHA-256
  `b6a910ecf69bef7682ec6a3d1a3be1d5146ffd046789b254397f0d92db93c1fd`.
- `Perm.v`: 21,421 bytes, 630 lines; SHA-256
  `0d3ad2421a6bee80b987423b702e8688e59fe802cafa1efa9b98df71d619fd9f`.
- `Sort.v`: 10,864 bytes, 308 lines; SHA-256
  `aeaf646d3b7e4dd88cb5d6dba9d35ae5714e5451c154d90de499bb09a32a7d33`.
- [Source license notice](../licenses/vfa-MIT.txt): MIT, copyright 2026;
  SHA-256 `6fcd23f1728be522ac23586b7e8b066d272fa60d45aac298142afeaefddae4ec`.
- [Immutable aggregate source inventory](../history/textbooks/checkpoint-012/books/vfa/records/research/source/vfa-source-inventory.json),
  SHA-256 `fe9b0c8693c9e448617411c9b2fba48335f28f472e2007a3e947e1adaf5fb41d`.

The order is Preface, Perm, Sort, Multiset, BagPerm, Selection, Merge, Maps,
SearchTree, ADT, Extract, Redblack, Trie, Priqueue, Binom, Decide, Color.
The inventory is a lexical aid, not a Rocq parser or verification of upstream
proofs. Its chapter entries distinguish definitions, statements, exercises,
aborted attempts, tactics and administrative markers. Old references to separate
chapter inventories are historical navigation, not additional current owners.

For CTB-3/CTB-4, the exact archive was recovered and all 17 chapter identities
and the license checked against the preserved records. **The entire Preface and
Perm primary texts were freshly read**, including prose and exercise prompts.
That reading and the correspondence below use mathematical source base
`412e450cc7902296d5ed054a81fb5422237e114f`, on programme upstream pin
`c214fb0720ffc998951255a7e4b5f2e80a299186`. This qualification changes only this
document. The checkpoint records the later exact documentary candidate,
focused build/audit, statement assessment, both independent review axes and
final snapshot comparison; a source map alone does not establish acceptance.

The receiving environment still owns the guarded whole-library build,
exhaustive project audit, immediate candidate verification and final integration
acceptance under the user's programme exception. Focused chapter evidence is
separate from those gates. Other chapters keep their own source-reading,
implementation and acceptance obligations. No whole-book machine-checked claim
or percentage follows from this assessment.

## Preface: scope and adaptation

The Preface has no theorem or exercise package. Its complete prose has the
following dispositions; this does not discharge later chapters by implication.

| Source concern | Lean development and boundary |
|---|---|
| Purpose and functional-program verification | Preserve executable algorithms and precise specifications, with proofs checked by Lean. The source's claim about its machine-checked presentation is context for the Rocq book, not acceptance evidence for this Lean reconstruction. |
| Prerequisites and dependency guidance | The recommended Logical Foundations topics include induction, lists, polymorphism, tactics, logic, inductive propositions and maps, with proof objects/principles as further preparation. Use the pinned repository's README and existing Lean/Mathlib APIs for the corresponding environment and proof techniques. The source dependency diagram guides ordering; optional branches remain in the user's whole-book scope. |
| Exercise stars, optional/advanced labels and grading | All mathematical exercises remain obligations regardless of these teaching labels. A grading stub carries no proof. Complete prompts, negative examples and open-ended requests determine the work, not declaration counts. |
| Proof, compilation and execution | Distinguish kernel-checked Lean statements, evaluation of actual Lean definitions, and compiler/runtime or representation claims. The source's Gallina-to-ML and optional OCaml material requires an explicit Lean adaptation in Extract. Preface qualification supplies no extraction, compiler-correctness or runtime-cost theorem. |
| Installation and source identity | Coq 9 is the source requirement; this reconstruction uses the compiler and dependency versions pinned by conaled. The user's native-kit allowance does not change those versions. The versioned archive and hashes above identify this source rather than a course-customized download. Its README's obsolete VFA.v hint does not override the actual chapter order; the Preface footer's 09:43 timestamp does not replace the release cover's 10:11 identity. |
| Publication and license | Retain the MIT notice and the authors' request that exercise solutions not be made publicly searchable. The authorized workflow is local development and private recovery checkpoints; it does not authorize public publication. Downloaded primary research bodies stay outside deliverables under [ADR 0001](../adr/0001-modules-and-proof-dependencies.md); exact identity, provenance and meaningful findings are retained. |
| Lectures, contributions, citation and thanks | The 2017 lecture links are supplementary teaching material. Contributor instructions, the Appel/Pierce volume-3 citation (2026, version 2.1), acknowledgments and grant context are bibliographic/administrative information, with no additional mathematical theorem to invent. |

## Perm: comparisons and permutations

Implementation: `Applications/Sorting/FirstPair.lean`.
Checked specializations: `Examples/ComparisonPermutations.lean`.

The reusable `Applications.Sorting.compareSwap` conditionally exchanges the
first two entries and leaves the tail unchanged. Empty and singleton lists are
unchanged. It accepts an arbitrary Boolean comparator and always preserves
occurrence-sensitive `List.Perm` and the suffix after two entries. Comparator
asymmetry alone suffices for idempotence. A separate two-branch law relates that
comparator to any relation for first-pair ordering. The Nat specialization
proves both sufficient laws. No payload order, transitivity, heap model or
runtime-cost assumption is introduced by these generic contracts.

`compareSwap_map` permits independent source/target universes and transports
the operation along any comparison-preserving map. It needs neither injectivity
nor ordered payloads. The record specialization maps string payloads to lengths.
The generic owner remains independent of checking: the composition theorem
`Examples.ComparisonPermutations.compareSwap_checked_prefix` belongs with the
examples and consumes the existing checker through the precise prefix bridge.

### All source records

Each row uses the immutable source ID, including its original line. Unqualified
example names are in `Examples.ComparisonPermutations`; generic `compareSwap*`
and `FirstPair` names are in `Applications.Sorting`. This is the single current
map for all 30 lexical records. The four complete exercise prompts and surrounding
prose are accounted for in the following sections; counts are not proof evidence.

| Source ID | Lean witness or explicit disposition |
|---|---|
| `Perm.geb@72` | `geb`; reversed Nat non-strict comparison computed by `decide`, related to its proposition by `geb_reflect`. |
| `Perm.gtb@76` | `gtb`; reversed Nat strict comparison computed by `decide`, related to its proposition by `gtb_reflect`. |
| `Perm.lia_example1@86` | Aborted teaching attempt. The completed contract is `lia_example1` below; `truncated_subtraction` explains the natural-subtraction obstacle. No second unproved result is introduced. |
| `Perm.truncated_subtraction@112` | `truncated_subtraction`, refuting the universal claim with `k = 0`. |
| `Perm.lia_example1@124` | `lia_example1`, with the actual Nat hypotheses and truncated subtraction, proved using `omega`. |
| `Perm.lia_example2@147` | `lia_example2`, retaining the same `k > i` conclusion and Nat assumptions as the final `lia_example1`; its Lean proof reuses that theorem. |
| `Perm.lia_example_3@170` | `lia_example_3`, for arbitrary `f : Nat → Nat → Nat`; the function application and product remain opaque arithmetic expressions. |
| `Perm.maybe_swap@185` | `maybeSwap := compareSwap gtb`, preserving the source's two-entry recurrence. |
| `Perm.maybe_swap_123@191` | `already_ordered`, checking `[1,2,3]` unchanged. |
| `Perm.maybe_swap_321@195` | `first_calculation`, checking `[3,2,1]` becomes `[2,3,1]`. |
| `Perm.maybe_swap_idempotent@202` | Aborted Boolean/proposition teaching attempt; the final `maybe_swap_idempotent` consumes `compareSwap_idempotent` and proved `gtb_asymmetric`. |
| `Perm.eqb_reflect@249` | `eqb_reflect`, Boolean equality true iff Nat equality. |
| `Perm.ltb_reflect@255` | `ltb_reflect`, Boolean strict comparison true iff Nat strict order. |
| `Perm.leb_reflect@261` | `leb_reflect`, Boolean non-strict comparison true iff Nat non-strict order. |
| `Perm.gtb_reflect@267` | `gtb_reflect`, with reversed arguments exactly as in `gtb`. |
| `Perm.geb_reflect@273` | `geb_reflect`, with reversed arguments exactly as in `geb`. |
| `Perm.reflect_example1@284` | `reflect_example1`, the full two-branch bound for arbitrary Nat `a`. |
| `Perm.reflect_example1'@312` | `reflect_example1'`, retaining the alternate reflection example and its statement. |
| `Perm.bdestruct@345` | Tactic adaptation: `by_cases`, `simp` with comparison equivalences, and `omega`; the proof-carrying decision and both branches are described below. |
| `Perm.reflect_example2@355` | `reflect_example2`, with the same source branch condition and bound. |
| `Perm.maybe_swap_idempotent@369` | `maybe_swap_idempotent`; generic asymmetry is sufficient and `gtb_asymmetric` proves it for the source operation. |
| `Perm.manual_grade_for_Permutation_properties@454` | Administrative marker. The exercise's four supplied examples and three additional library properties are checked as specified below; the marker is not a theorem. |
| `Perm.butterfly@460` | `butterfly`, using append commutation and permutation composition with arbitrary Nat variables, including the repeated variable. |
| `Perm.permut_example@534` | `permut_example`, proving the source-admitted rearrangement for arbitrary `a b : List Nat`. |
| `Perm.not_a_permutation@548` | `not_a_permutation`, proving the source-admitted `[1,1]` versus `[1,2]` counterexample by kernel-checked `decide`. |
| `Perm.maybe_swap_perm@560` | `maybe_swap_perm`, through unconditional `compareSwap_perm`; no comparator law is needed. |
| `Perm.first_le_second@576` | `FirstPair (· ≤ ·)`, vacuously true for zero or one entry. |
| `Perm.maybe_swap_correct@582` | `maybe_swap_correct`, through `compareSwap_correct` and the proved two-branch `gtb_order_law`, combining permutation with first-pair order. |
| `Perm.inv@603` | Tactic adaptation: `cases`/`rcases`, substitution, constructor disjointness and injectivity supply inversion. |
| `Perm.Forall_perm@613` | `forall_perm` and `forall_perm_inductive` prove the source-admitted arbitrary-predicate transport; the representation and reused induction are explicit below. |

### Complete exercises and proof routes

| Exercise | Complete obligation and current treatment |
|---|---|
| `Permutation_properties` (430–455) | The four supplied properties are `permutation_length`, `permutation_symmetry`, `not_a_permutation` and `four_values_permuted`. The three additional choices are `permutation_reflexivity`, `permutation_transitivity` and `permutation_membership`. The requested library-discovery answers are respectively `List.Perm.refl`, the constructor `List.Perm.trans`, and `List.Perm.mem_iff`, which the actual proofs reuse. `permutation_occurrences` additionally reuses `List.Perm.count_eq`, making duplicate multiplicity explicit. |
| `permut_example` (518–538) | The theorem retains the exact arbitrary-list equation, including the leading `5`, and uses append commutation lifted under cons. It does not substitute one finite example for the universal statement. |
| `not_a_permutation` (540–552) | The duplicate-sensitive negative statement is proved in Lean, with no native evaluation shortcut. The proof is reusable as one of the properties exercise's supplied examples. |
| `Forall_perm` (605–618) | Arbitrary predicates, without a decidability requirement, transport along permutation. Both membership-quantified and Mathlib `List.Forall` statements are proved. The source's instruction to use induction is met by explicitly reusing the library induction described next. |

Rocq's source `Forall` is inductive. Pinned Mathlib's **`List.Forall` is a
recursive conjunction definition**: `True` on the empty list, `P x` on a
singleton, and `P x ∧ List.Forall P rest` on longer lists.
`List.forall_iff_forall_mem` proves its equivalence with universal membership by
recursion on the list. Lean core `List.Perm.mem_iff` proves transport by induction
on the permutation evidence, with nil, cons, swap and transitivity cases.
`forall_perm` consumes that result; `forall_perm_inductive` rewrites through the
bridge on both sides. The latter name refers to adapting the source contract;
it does not make Mathlib's definition an inductive datatype or claim a new
direct induction proof. Reusing the existing proofs retains the mathematical
contract and explains the induction choice without another public wrapper.

### Remaining prose and proof-assistant mechanics

The chapter's opening map, queue and sorting applications motivate later work;
Perm itself supplies comparison and occurrence-sensitive permutation techniques.
The arithmetic retains truncated Nat subtraction and the zero counterexample.
`omega` proves the actual displayed statements, with `f x y` and `a * b` treated
as expressions where appropriate; this makes no claim of general nonlinear
solver completeness or equivalence of Rocq and Lean tactics.

The five Boolean/proposition equivalences support both outcomes. The existing
`decidable_of_bool` adapter consumes a full equivalence and produces a
proof-carrying `Decidable` value. `reflectedLt`, `reflected_true_branch` and
`reflected_false_branch` check both constructors; `false_branch_reflect` states
the negative `gtb` branch. The displayed source `iff_reflect` type also requires
an equivalence; its nearby informal sentence must not be weakened to a single
implication. There is no need to introduce another reflection datatype.

Imports, notation and hint setup adapt to existing Lean/Mathlib owners. All
23 `Locate`/`Check`/`Print`/`Search` commands serve library discovery and are
accounted for by notation/source inspection, `#check`, `#print` and search.
The append proofs reuse associativity, commutation, cons and transitivity;
Lean rewriting and named intermediate expressions supply the roles of Rocq
`change`/`remember`. The `bdestruct` and `inv` rows give their tactic adaptations.
Two `Abort` attempts are teaching stages of later proved statements; the three
`Admitted` exercises have actual Lean proofs. No tactic/runtime bound, new
trusted axiom, unsafe mathematical definition or Lean admission is licensed by
the source presentation.

### Statement review and connected cases

The independent expectation `[3,2,1] ↦ [2,3,1]` connects to the general results
through `first_calculation_spec` and `first_calculation_idempotent`.
`empty_case`, `singleton_case` and `repeated_values` cover short lists and equal
heads. `unchanged_suffix` consumes `compareSwap_drop_two` on `[3,2,1,0]`, giving
exactly `[1,0]` after dropping the two-entry prefix. `not_whole_list_sorted`
refutes whole-list ordering of `[2,3,1]`. These distinguish the precise positive
contract from an invalid stronger one.

`certified_prefix` uses `compareSwap_checked_prefix`,
`OrderCertificate.adjacent_correct` and
`Applications.Sorting.firstPair_iff_chain_take_two` to certify exactly `take 2`.
No transitivity or suffix order is required. `positive_after_swap` composes
`forall_perm` with `maybe_swap_perm`. `record_map` checks the comparison-preserving
map law with different payload types and a non-injective map. The generic
FirstPair owner supports arbitrary universes; the current checked-predicate
examples and checker adapter have their actual `Type`-level signatures, not an
unclaimed universe generalization.

There is also an existing cross-book consumer in `Examples/TextbookSorting.lean`.
Its `sort_after_compareSwap` uses `compareSwap_perm` and
`Applications.Sorting.sorters_eq_at` for a sorter whose output is pairwise
ordered and a permutation. The relation is antisymmetric on the **observed
records**, and the preprocessing comparator is arbitrary. The existing
first-pivot and floor-split sorters then share the ordinary-list specification:
`preprocessedQuickSquare` and `floorSquare` use the existing exact squares;
`jointSquare` and `paired_outputs` use `Squares.synchronize` and
`Squares.synchronize_agrees` to retain both algorithms and establish agreement.
`mixed_duplicates` transfers an independently checked mixed-duplicate result.

This consumer observes complete lists, including payload order.
`equal_key_order_matters` and the related `Examples.SortUniqueness` boundary
cases show why antisymmetry of non-injective keys cannot replace antisymmetry
on records. These relations do not equate costs, recursion strategies or stable
orders of arbitrary equal-key records. They establish reuse of Perm in the
current library; Sort has its own source correspondence below and separate
receiving acceptance.

## Sort: source recurrence, indexed correctness and resource observations

Shared owners: `Applications/Sorting/Specification.lean` and
`Applications/Sorting/InsertionObservations.lean`.
Source specializations and applications: `Examples/InsertionSorting.lean`.
Existing stable sorting and measured execution remain in
`Applications/Sorting/Sort.lean` and `Applications/Resources/InsertionSort.lean`.
The refined resource execution is in `Applications/Resources/InsertionWork.lean`,
with checked clients in `Examples/InsertionWork.lean`.

CTB-79 began on upstream prerequisite `1f3be1333d6c3ffde8d83a1bc8dbd40a364dc945`;
CTB-80 and CTB-81 continue CTB-5 on `9b20498dffaeb8f60de18b2af902f267786f8b22`.
The complete primary Sort text was
read, including all eight exercise prompts and resource prose, and its identity
matches the immutable aggregate inventory. That inventory contains **17 lexical
records: six definitions, two source-proved claims and nine source admissions**.
These are source counts, not a theorem count or acceptance percentage. The local
CTB record owns the actual candidate, focused build/audit and independent review
outcomes; this correspondence does not assert those gates passed. The source
unit is qualified by the complete treatment below; receiving acceptance remains open.

### Recurrence, representations and assumptions

The source operations are aliases of the existing `List.orderedInsert` and
`List.insertionSort` at Nat `≤`. The explicit `insert_nil`, `insert_cons`,
`sort_nil` and `sort_cons` equations retain both insertion branches, left
insertion on equality, and sorting the actual tail before inserting its head.
They apply to every input list. Sortedness is a premise of sorted-output
preservation, not a restriction on execution, permutation or length.
The source Boolean Nat comparison is adapted to Lean's decidable Nat `≤`;
both outcomes and the equality branch retain their mathematical meaning.
The generic keyed equations already appear in
`Examples.InsertionObservations.keyed_insert_equations` and
`keyed_sort_equations`; no second sorting algorithm is introduced.

Source `sorted` is represented by `List.IsChain (· ≤ ·)`, with the source's
empty, singleton and adjacent-cons rules exposed as `sorted_nil`, `sorted_1`
and `sorted_cons`. It is not silently replaced by all-pairs ordering.
`Specification.Indexed` quantifies over Nat indices and two successful optional
lookups. `Specification.BoundedIndexed` retains `i < j` and `j < xs.length`;
these imply both indices are valid. Its optional-lookup/default presentation
is connected to ordinary `List.getD` by `boundedIndexed_iff_getD`.

`pairwise_iff_indexed`, `pairwise_iff_boundedIndexed`,
`indexed_iff_boundedIndexed` and `boundedIndexed_default_irrelevant` need no
laws on the relation. `adjacent_iff_indexed` and
`adjacent_iff_boundedIndexed` require transitivity for the adjacent-to-all-pairs
direction; totality, reflexivity and antisymmetry are unnecessary for these
bridges. `keySorted_iff_indexed` uses the actual existing `KeySorted` contract
and requires no order on payloads. Insertion correctness separately needs a
decidable, total, transitive relation. Operation and occurrence laws do not
inherit those extra correctness assumptions.

### All source records

Unqualified source-facing names below belong to `Examples.InsertionSorting`.
`Specification` abbreviates `Applications.Sorting.Specification`; the generic
lookup-origin and direct indexed insertion results are in `Applications.Sorting`.
All source IDs and original line numbers come from the immutable inventory.

| Source ID | Lean witness or explicit adaptation |
|---|---|
| `Sort.insert@30` | `insert`, the Nat alias of `List.orderedInsert`; `insert_nil` and `insert_cons` expose the source recurrence, including the non-strict left-tie branch. |
| `Sort.sort@36` | `sort`, the Nat alias of `List.insertionSort`; `sort_nil` and `sort_cons` expose the same tail-first recurrence as the source. |
| `Sort.sort_pi@42` | `sort_pi`, with the exact eleven-element input and output `[1,1,2,3,3,4,5,5,5,6,9]`; `pi_contract` and `pi_indexed` connect this calculation to the ordinary and independently indexed results. |
| `Sort.sorted@95` | `Sorted` uses `List.IsChain`, with `sorted_nil`, `sorted_1` and `sorted_cons` retaining the three source rules. The Pairwise correspondence requires the stated transitivity assumption. |
| `Sort.sorted''@131` | `GetDSorted` retains Nat indices, default `0`, and the valid upper-index bound in the source `List.getD` presentation; `getDSorted_iff_indexedSorted` connects it to successful optional lookups. |
| `Sort.sorted'@140` | `IndexedSorted` specializes `Specification.Indexed` to Nat `≤`, preserving both successful-lookup premises and `i < j`. |
| `Sort.is_a_sorting_algorithm@157` | `IsSortingAlgorithm` retains `∀ xs, xs.Perm (f xs) ∧ Sorted (f xs)`. This is input-to-output occurrence permutation and adjacent sortedness; stability is a separate observation. |
| `Sort.insert_sorted@174` | `insert_sorted`, the ordinary source-preservation route through standard insertion correctness and the adjacent/Pairwise bridge at Nat order. |
| `Sort.sort_sorted@187` | `sort_sorted`, using list induction and the source-facing `insert_sorted` on the actual sorted tail. |
| `Sort.insert_perm@198` | `insert_perm`, orienting `List.perm_orderedInsert` from `a :: xs` to the insertion result. No sorted-input premise is added. |
| `Sort.sort_perm@209` | `sort_perm`, using list induction, permutation under cons and `insert_perm` on the actual sorted tail, in the source input-to-output direction. |
| `Sort.insertion_sort_correct@219` | `insertion_sort_correct`, combining the source-oriented permutation and sortedness in `IsSortingAlgorithm`. |
| `Sort.sorted_sorted'@239` | `sorted_indexedSorted`, the Nat forward direction of `Specification.adjacent_iff_indexed`; the source's advanced obligation is retained. |
| `Sort.sorted'_sorted@250` | `indexedSorted_sorted`, the converse direction of that same correspondence, with successful indices still explicit. |
| `Sort.nth_error_insert@277` | `nth_error_insert`, specializing `getElem?_orderedInsert_origin`: the returned value equals the inserted value or occurs at an actual successful old index. No sortedness or order laws are required by the generic origin theorem. |
| `Sort.insert_sorted'@283` | `insert_indexedSorted`, specializing `indexed_orderedInsert`, whose positional induction is independent of ordinary sortedness and the specification equivalences. |
| `Sort.sort_sorted'@289` | `sort_indexedSorted`, specializing `indexed_insertionSort`, proved by list induction using direct indexed insertion. The source's `Qed` depends on an admitted insertion lemma; the dependency is retained as part of this proof route. |

### Complete exercises and the independent proof route

| Exercise | Complete obligation and adaptation |
|---|---|
| `insert_sorted` (169–180) | Preserve adjacent sortedness after insertion. Nat comparison cases supply the role of the source `bdestruct`; the existing generic insertion theorem and explicit IsChain correspondence supply the ordinary proof. |
| `sort_sorted` (182–191) | Obtain adjacent sortedness of every source-sort result by list induction and `insert_sorted`, retaining the requested ordinary insertion-preservation route. |
| `insert_perm` (193–203) | Preserve every occurrence of `a :: xs`, for arbitrary lists including unsorted inputs. Reuse the standard permutation theorem in the source direction. |
| `sort_perm` (205–213) | Preserve every occurrence of the original input under tail-first sorting, using list induction and `insert_perm` as the prompt requests. |
| `insertion_sort_correct` (215–224) | Establish both conjuncts of the exact source sorting contract; do not replace occurrence permutation with membership or add stability to the definition. |
| `sorted_sorted'` (238–247, advanced) | Relate adjacent sortedness to increasing successful optional indices. Reuse the shared transitive chain/Pairwise/index bridge; the source's suggested induction is an explanation of a proof technique, not a new datatype requirement. |
| `sorted'_sorted` (249–256, advanced) | Recover adjacent sortedness from the successful-index predicate. Both equivalence directions remain explicit. |
| `insert_sorted'` (275–287, optional) | Retain both the lookup-origin helper with an old-index witness and the independently positional insertion proof. The source's explicit prohibition on using ordinary correctness or the sortedness equivalence is part of this obligation. |

The optional route does not disguise ordinary insertion correctness behind the
generic bridges. `getElem?_orderedInsert_origin` uses successful lookup,
membership in `List.orderedInsert`, and an old successful-lookup witness.
`indexed_orderedInsert` then inducts on the input list and splits the queried
indices. Its stopping branch compares the inserted head with an old head or
later value, using the branch fact and transitivity. Its recursive branch uses
totality when the queried value is the inserted value, or the old indexed
premise when the origin witness identifies an old-tail value. Two positive
indices reduce to the appropriate shifted premise or induction hypothesis.
`indexed_insertionSort` uses this result by list induction on the tail-first
recurrence. This route uses neither Pairwise/IsChain insertion correctness nor
the specification equivalences. Its method is checked by reading the actual
derivation and helper dependencies, not by treating a source-name search as
proof of independence.

### Source prose and proof-assistant mechanics

| Source concern | Current treatment and remaining boundary |
|---|---|
| 3–17: complexity, small inputs and textbook references | The references are bibliographic context. Faster small-input execution is a qualified empirical observation, not a universal timing theorem. CTB-80 makes the quadratic insertion claim precise with a sharp triangular bound on executed comparisons, as described below. No benchmark, constant-time Nat comparison or proof of other algorithms' complexity is inferred from this unit. |
| 18–19 and 24–29: imports, lists and the insertion precondition | Use normal Lean imports and pinned dependencies; no source warning suppression is needed. Functional lists and the exact recurrence are preserved. The sortedness precondition belongs to sorted-output preservation, while insertion executes and preserves occurrences on every list. |
| 47–78: nondestructive execution, displayed insertion and sharing | `insert_source_tail` gives the displayed value calculation; `insert_suffix` preserves an arbitrary suffix after the stopping value. This is a value equation. The time, allocation, retained-root and garbage-collection statements require the separately named models below. |
| 83–103: adjacent constructors and constructor hints | `List.IsChain` with the three source-facing rules preserves empty, singleton and adjacent-cons meaning. Lean constructors, cases and rewriting replace the source hint database. |
| 105–147: total lookup, `nth`, `nth_error` and default irrelevance | The two `Check` commands map to `List.getD` and `xs[i]?`; the source `Compute` maps to `insert_source_tail`. The generic bridges retain optional success evidence or explicit bounds, and prove that valid indices never observe the default. |
| 149–161: choosing a sortedness specification and the sorting contract | Preserve all three presentations and occurrence-sensitive permutation. Their equivalence connects the specifications; none says that merely equal membership preserves duplicate counts or that sortedness plus permutation ensures record stability. |
| 165–256: ordinary proofs and specification validation | Ordinary correctness reuses the existing insertion laws. The two advanced exercises retain both directions of the alternate specification. Equivalence and connected applications support statement review; they cannot formally establish every aspect of the informal intent. The Perlis quotation is commentary, not a theorem to recreate. |
| 260–304: alternative proof, explicit restriction and proof difficulty | The positional route above respects the four forbidden source lemmas and excludes the equivalent generic shortcut. The final sort theorem uses the direct insertion result. Relative proof difficulty is a pedagogical observation, not a formal cost bound on proofs or tactics. |
| Source admissions and release footer | The nine admitted claims are mathematical obligations, not permission for Lean admissions. The final source theorem depends on one of them. There are no aborted attempts in Sort. The `2026-08-24 10:11` footer agrees with the pinned edition; it does not replace candidate-specific validation. |

### Connected applications and statement boundaries

`sort_pi` supplies the source's independent expected output. `pi_contract` and
`pi_indexed` apply the ordinary and direct indexed theorems to that same result.
`insert_suffix` proves
`insert 7 ([1,3,4,8] ++ tail) = [1,3,4,7,8] ++ tail` for arbitrary `tail`;
the tail need not be sorted for this execution equation. `unsorted_insertion`
and `source_ties` retain the unconditional occurrence and equality-branch
boundaries. `sorted_fixed` and `sort_idempotent` connect the recurrence to the
existing sorted-input fixed-point law and correctness.

`signed_indexed` and `signed_defaults` connect the bridge to `[-3,-1,2]` with
defaults `-999` and `999`. `index_bound_matters` uses the sorted singleton `[1]`
with default zero to refute omission of the upper-index bound.
`nontransitive_boundary` uses `[0,1,2]` and the relation `b = a + 1` to separate
adjacency from all-pairs ordering. These cases retain the assumptions that make
the positive bridges valid.

`records_indexed` uses the new direct indexed theorem on the existing
`Examples.StableSorting.input`. `records_expected_indexed` connects it to that
module's independently specified expected record order; `merge_records_indexed`
also uses the existing stable merge/insertion agreement. Distinct payloads at
the same key make equal-key order observable. `sorted_indexed_permutation_not_stable`
transports the existing stability counterexample through the new indexed bridge,
so the source sorting contract is not confused with the stronger stable contract.
The generic laws require order on keys, not on payloads; exact stable-result
agreement retains its separate key-antisymmetry hypothesis.

`measured_sort_spec` combines the existing FDSA execution's value erasure and
call bound with occurrence permutation and the new indexed observation of that
value. `measured_insert_stopping` records four insertion calls for the displayed
stopping example. These are clients of `Resources.InsertionSort`, not a new
generic comparison-count or heap model. The existing `Examples.InsertionCosts`
empty, singleton, duplicate, stopping and worst-case clients remain applicable.

### Executed comparison and constructor observations

`Resources.InsertionSort.insertRun` charges one call at nil as well as each
visited cons; `sortRun` also charges every sort entry. Its uniform triangular
bound is `(n+1)*(n+2)/2` calls, with an exact descending-range family. This does
not identify calls with comparisons. CTB-80 adds `insertMeasured` and
`sortMeasured` in the same `Resources.InsertionSort` namespace, using the
established `Resources.Measured`, `bind` and product-observation pattern also
used by ordinary merge. One execution records
`(head comparisons, recursive invocations, literal cons requests)`:

| Reached branch | Local observation |
|---|---|
| Insertion into nil, returning `[x]` | `(0, 1, 1)` |
| Successful head test, returning `x :: y :: ys` | `(1, 1, 2)` |
| Failed head test, returning `y :: actualChildResult` | Actual child observation plus `(1, 1, 1)` |
| Sorting nil | `(0, 1, 0)` |
| Sorting a cons | Actual sorted-tail observation, insertion into that returned value, and `(0, 1, 0)` for this sort entry |

`insertMeasured_calls` and `sortMeasured_calls` prove that reweighting the
invocation coordinate recovers the **whole** old measured result, including its
value. `insertMeasured_value`, `sortMeasured_value` and `sortMeasured_length`
then connect the refinement to the existing source algorithms. The invocation
model and its selection clients remain unchanged. None of these results infers
cost from output equality or evaluates an independent post-hoc cost oracle.

All comparison bounds require only a decidable relation. `insertComparisons_cons`
charges one at each tested nonempty head and stops at the first success;
`insertComparisons_nil` charges zero. `insertComparisons_le` bounds insertion by
input length, while `insertComparisons_of_head` and
`insertComparisons_of_all_not` give exact stopping and complete-traversal costs.
`sortComparisons_le` proves `C(xs) ≤ n*(n-1)/2`. The opposite-Pairwise theorem
`sortComparisons_of_opposite` proves equality when every earlier input rejects
every later input; membership preservation transports that premise to the
actual sorted tail. `sortComparisons_reverse_range` supplies a sharp family at
every Nat length, including zero and one. This precise formula strengthens the
source's informal quadratic discussion; it is not quoted as a source theorem.

`sortComparisons_lower` proves `n-1 ≤ C(xs)`, using natural truncated subtraction.
`sortComparisons_of_pairwise` attains it on `Pairwise r` input without global
order laws. `insertConstructors_eq` proves `Kinsert = Cinsert + 1`, and
`sortConstructors_eq` proves `Ksort = Csort + n`, by induction on the observed
branches. The constructor bound `n*(n+1)/2` and its descending equality family
are separate from the comparison and invocation bounds.

The checked `Examples.InsertionWork` clients include empty/singleton inputs,
equal-head stopping, complete traversal, duplicate best cases and the infinite
descending family. `source_comparisons`, `source_constructor_requests` and
`source_calls` establish four comparisons, five literal constructor requests
and four calls when inserting 7 into `[1,3,4,8] ++ tail`, for arbitrary `tail`.
`source_tariff` reweights these events by declared prices `c`, `e`, `k` to
`4*c + 4*e + 5*k`; it is not a theorem about elapsed time. `source_contract`
combines the comparison interval with occurrence permutation and the independent
indexed specification. `keyed_contract` transfers the old stable-sort contract
through the call projection, requiring no order on payloads.
`same_value_different_comparisons` separates equal sorted results from equal
comparison counts with ascending and descending three-element inputs.

### Shared roots and conditional live space

CTB-81 adds `Applications/Sequences/SharedList/Insertion.lean` using the existing
`Store`, `Root`, `Represents`, `allocate`, heap-extension and relational-square
interfaces. Its `insertRunFuel` reads actual heap links. A successful head test
allocates one cell pointing to the matched old root; a failed test recursively
inserts into the stored tail and copies the head around that returned result.
Nil allocates the inserted cell. Invalid lookup and insufficient fuel fail
explicitly; a represented input has enough fuel at the existing frontier.

`insertRun_path` proves the actual output is the copied passed prefix followed
by the inserted cell and the exact old stopping root. `insertRun_correct`
establishes source `List.orderedInsert` correspondence, heap extension, fresh
frontier increase equal to the existing invocation observation, and equal roots
reached by the original and result traversals. The observation pair retains
actual comparison and invocation counts. `insertMeasuredSquare` relates values
and both observations; `insertSquare` projects the value relation, and
`insertRun_head_correct` composes the existing optional-head observation. Heap
extension preserves every valid old root, including unrelated retained roots.

`Applications/Sequences/SharedList/Live.lean` owns a finite `liveCells` observer
using the existing `Reaches`/`ReachableFrom` graph and store frontier. A valid
root reaches exactly its list length of distinct cells. Immutable extension
preserves each old footprint; retaining roots takes unions, counting shared
cells once. `liveCells_prepend` separates the fresh address interval from the
shared suffix footprint. The insertion consequences establish:

| Retained roots / observation | Exact count |
|---|---|
| Result root alone | Input length plus one live element cell |
| Original root and result root | Input length plus the number of fresh insertion cells |
| Original cells unreachable from the result | Length of the copied old prefix |
| Fresh frontier growth | Passed-prefix length plus one, equal to insertion invocations |

`Examples.SharedInsertion.source_shared_root` applies this to inserting 7 into
`[1,3,4,8] ++ tail` for arbitrary `tail` and arbitrary representing store. It
proves four comparisons, four invocations, four fresh cells, the expected result,
and identity of the reused `8 :: tail` root after three old or four new links.
The suffix need not be sorted. `source_live_cells` proves three old prefix cells
become unreachable from the result, with net live growth one if only the result
is retained. Retaining the original root instead gives net live growth four.
`source_cell_price` recovers `(4-3)Y = Y` for any declared Nat price per abstract
live cell and checks the retained-root alternative `4Y`, alongside five literal
source constructor requests. `source_head` is a composed consumer; `loaded_source`
constructs valid inputs for every suffix. Nil, equal-head stopping, traversal to
null, exhausted fuel and missing lookup have separate checked cases.

This gives the source's memory discussion an explicit mathematical interpretation.
The store remains append-only: unreachable means eligible under the stated root
set, not actually reclaimed. Length, literal constructors, fresh allocation,
net live cells and peak space are different observations. The source's physical
word-size estimate, constant-time comparisons, elapsed time, compiler sharing
and garbage-collector behavior are external realization assumptions, not Lean
runtime theorems. The generic count laws do not charge unrelated old heap cells
or silently assume that other roots disappear.

CTB-79, CTB-80 and CTB-81 together supply the Sort source/exercise and mathematical
resource correspondence under CTB-5. This qualifies the complete source unit
with the explicit realization boundaries above. Exact-candidate focused checks,
statement review and independent reviews remain separate from receiving
whole-library build, exhaustive audit and integration acceptance. No whole-book
completion claim follows.

## Multiset and BagPerm: counts, permutations and sorting contracts

CTB-82 continues the canonical chapter identities CTB-6 and CTB-7.

### Source identity and denominators

VFA 2.1, release timestamp 2026-08-24 10:11, Coq 9.0 or later. The chapter
footers' 2026-08-24 09:43 timestamp does not designate a different edition.
Both primary files were read completely, including source prose and all exercise
instructions. The local primary bytes agree with the canonical source inventory
in checkpoint-012. The versioned identity below is authoritative; a mutable
`vfa-current` URL in an older inventory is not a replacement edition.

| Unit | Bytes | Lines | SHA-256 | Complete lexical denominator |
|---|---:|---:|---|---|
| Multiset.v | 10383 | 323 | `ecdc47863b68bbef0d0579f75f4b5537cfb9f99c00f9b2fcc154eadcfdc9ef95` | 22 source records: 7 definitions, 13 admissions, 1 supplied proved example, 1 grading record; 14 exercise headings: 13 proofs and 1 discussion |
| BagPerm.v | 5949 | 192 | `a11149100fcdf0a2c366267288dfbe6538ad0bbc5ba65e53e2c026e1ec8899a7` | 19 source records: 4 definitions, 11 admissions, 3 supplied proofs, 1 grading record; 9 exercise headings, including one four-proof group and one discussion |

These 41 records and 23 headings are source denominators, not an assertion that
all source items are equally difficult or that declaration counts measure book
completion. The supplied proofs and manual grading records remain accounted for.

### Public ownership and exact source adaptation

`Sequences.Multiplicity` in `Applications/Sequences/Multiplicity.lean` owns the
single generic `contents` observation, defined through `List.count`. It also
owns unrestricted `Counts α := α → Nat` and empty/singleton/union operations.
All source-facing names are specializations/aliases of these owners, not
independent list observers. Source recursive equations and all-input fold
correspondences establish the original constructions for every list.

The Multiset source's singleton compares query against stored value; BagPerm's
counter and `List.count` compare stored head against query. The generic
`contents_cons_by_query` and `contents_cons_union` explicitly require lawful
Boolean equality. Empty, stored-oriented cons, append, and pointwise algebra
need no occurrence laws. Forward permutation-to-contents preservation also needs
only `BEq`, since it reorders an arbitrary fixed Boolean query. `LawfulBEq` is
sufficient for the inverse occurrence bridge;
it is not asserted to characterize every admissible Boolean test.

`Applications/Sorting/Multiplicity.lean` owns only sorting-contract transport
and the contents-based reuse of existing sorter uniqueness. It imports the
unchanged ordering specification and uniqueness modules. The generic
`contract_equivalent P f` retains exactly the same output predicate `P` on
both sides, including the source's adjacent sortedness predicate.

Source aliases and full chapter proofs live in `Examples/MultisetSorting.lean`
and `Examples/BagPermutation.lean`. Actual cross-application clients live in
`Examples/MultiplicityClients.lean`. No sorter, queue or occurrence datatype is
reimplemented. No finite-support hypothesis is imposed on arbitrary function
multisets. Bags remain raw lists, with a separate count-equivalence relation.

### Complete Multiset record map

Names below are in `Examples.MultisetSorting` unless explicitly qualified.

| Source identity | Current declaration or disposition |
|---|---|
| Multiset.value@42 | `Value := Nat` |
| Multiset.multiset@44 | `Multiset := Sequences.Multiplicity.Counts Value`, unrestricted functions |
| Multiset.empty@48 | `empty`, using shared `empty_apply` |
| Multiset.singleton@53 | `singleton`, using shared query-oriented `singleton_apply` |
| Multiset.union@58 | `union`, using shared `union_apply` |
| Multiset.union_assoc@70 | `union_assoc`; generic proof uses function extensionality and natural addition |
| Multiset.union_comm@83 | `union_comm` |
| Multiset.union_swap@95 | `union_swap`, derived from the two preceding algebraic laws |
| Multiset.contents@122 | `contents`, `contents_nil`, `contents_cons`, `contents_eq_foldr` |
| Multiset.sort_pi_same_contents@131 | `sort_pi_same_contents`; `pi_fives` checks all three occurrences of 5 |
| Multiset.is_a_sorting_algorithm'@142 | `IsSortingAlgorithm`, same source adjacent sortedness |
| Multiset.insert_contents@163 | `insert_contents`, induction on the actual source insertion recurrence using union laws |
| Multiset.sort_contents@175 | `sort_contents`, induction on actual tail-first sorting using insertion preservation |
| Multiset.insertion_sort_correct@186 | `insertion_sort_correct` |
| Multiset.manual_grade_for_permutations_vs_multiset@210 | Proof-comparison discussion below; subjective grading metadata has no theorem |
| Multiset.perm_contents@240 | `perm_contents`, specializing generic induction on permutation evidence |
| Multiset.contents_nil_inv@257 | `contents_nil_inv`, preserving the source's zero-on-the-left hypothesis |
| Multiset.contents_cons_inv@263 | `contents_cons_inv`, exact occurrence split and residual count; `repeated_occurrence_decomposition` is a duplicate-sensitive use |
| Multiset.contents_insert_other@273 | `contents_insert_other` |
| Multiset.contents_perm@280 | `contents_perm`, specializing the generic inversion-based list induction |
| Multiset.same_contents_iff_perm@302 | `same_contents_iff_perm`, using both proved directions |
| Multiset.sort_specifications_equivalent@313 | `sort_specifications_equivalent`, arbitrary proposed sorter and unchanged adjacent-order observation |

All fourteen exercise headings are represented: `union_assoc`, `union_comm`,
`union_swap`, `insert_contents`, `sort_contents`, `insertion_sort_correct`,
`permutations_vs_multiset`, `perm_contents`, `contents_nil_inv`,
`contents_cons_inv`, `contents_insert_other`, `contents_perm`,
`same_contents_iff_perm`, and `sort_specifications_equivalent`.

### Complete BagPerm record map

Names below are in `Examples.BagPermutation`.

| Source identity | Current declaration or disposition |
|---|---|
| BagPerm.bag@21 | `Bag := List Nat`, retaining raw list equality separately |
| BagPerm.count@23 | `count`, `count_nil`, `count_cons`, `count_eq_foldr`; literal stored-head/query recurrence |
| BagPerm.bag_eqv@33 | `BagEquiv`, with `bagEquiv_iff_contents` connecting pointwise and function equality |
| BagPerm.bag_eqv_refl@40 | `bag_eqv_refl` |
| BagPerm.bag_eqv_sym@44 | `bag_eqv_sym` |
| BagPerm.bag_eqv_trans@48 | `bag_eqv_trans` |
| BagPerm.bag_eqv_cons@54 | `bag_eqv_cons` |
| BagPerm.is_a_sorting_algorithm'@67 | `IsSortingAlgorithm`, same source adjacent sortedness |
| BagPerm.insert_bag@76 | `insert_bag`, direct induction on source insertion and pointwise count arithmetic |
| BagPerm.sort_bag@84 | `sort_bag`, list induction using cons congruence and insertion preservation |
| BagPerm.insertion_sort_correct@90 | `insertion_sort_correct`, accounting for the supplied source proof |
| BagPerm.manual_grade_for_permutations_vs_multiset@112 | Proof-comparison discussion below; subjective grading metadata has no theorem |
| BagPerm.perm_bag@128 | `perm_bag`, specializing generic induction on permutation evidence |
| BagPerm.bag_nil_inv@141 | `bag_nil_inv` |
| BagPerm.bag_cons_inv@147 | `bag_cons_inv`, exact split and residual multiplicity |
| BagPerm.count_insert_other@157 | `count_insert_other` |
| BagPerm.bag_perm@164 | `bag_perm`, through the shared inversion-based reverse proof |
| BagPerm.bag_eqv_iff_perm@172 | `bag_eqv_iff_perm`, accounting for the supplied proof |
| BagPerm.sort_specifications_equivalent@181 | `sort_specifications_equivalent`, arbitrary proposed sorter and unchanged adjacent-order observation |

All nine exercise headings are represented: `bag_eqv_properties` with all four
subproofs, `insert_bag`, `sort_bag`, `permutations_vs_multiset`, `perm_bag`,
`bag_nil_inv`, `bag_cons_inv`, `count_insert_other`, and `bag_perm`.
`pi_bag` connects the actual source calculation; `equivalent_bags_need_not_be_equal`
exhibits unequal raw lists with equivalent bags.

### Proof routes and comparison exercises

The union proofs reason about arbitrary functions. Function extensionality
reduces them to natural-number algebra; `union_swap` then reuses the established
laws. Multiset insertion follows the actual left-on-ties branch recurrence and
uses union swapping in the recursive branch. Tail-first sort induction uses
that insertion result. BagPerm insertion follows the same source recurrence,
but proves the observation one query at a time using count arithmetic; its sort
proof composes cons congruence and insertion equivalence.

Permutation preservation can instead reuse permutation constructors directly.
In this adaptation that route has less pointwise arithmetic. The function
multiset route makes algebraic laws reusable, and the bag route exposes explicit
counts without requiring a quotient. Their relative simplicity depends on the
chosen observation and library support; no objective preference theorem or
pretend grading value is asserted.

Forward correspondence inducts on permutation evidence. The shared reverse
proof explicitly inducts on the left list: zero counts force the empty case;
a positive head count supplies a real occurrence split in the target; the
selected count and all other counts establish equality on the remainders;
the induction hypothesis and the existing middle-occurrence permutation rebuild
the conclusion. The proof consumes the three advanced inversion ingredients and
does not discharge every chapter exercise by wrapping `List.perm_iff_count`.

### Recovered draft material and actual library integration

The remaining useful multiplicity material from preserved
`math/drafts/sorting-specs/SortingSpecifications.lean` (SHA-256
`45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c`)
is integrated through the shared owner. Its already integrated ordering portion
remains in `Applications.Sorting.Specification` and existing examples. No second
ordering or multiplicity framework is created. The historical draft's checks
are provenance, not acceptance of this candidate.

The retained useful cases connect to public theorems:

- Actual `Occurrences.picks` membership gives a singleton-plus-remainder
  contents equation, exact decrease of the selected count, and preservation of
  other counts. The duplicate example retains another equal occurrence.
- Existing first-pivot quicksort and floor-left merge sort become interchangeable
  through `sorters_eq_of_contents` and the existing uniqueness theorem. Their
  implementations, costs and stable-record claims remain distinct observations.
- `ExactQueue.add_exact` gives pointwise addition of the inserted and old entry
  counts. Successful removal from a valid exact queue gives the actual selected
  pair plus residual counts. Real leftist insertion and list deletion examples
  retain duplicate pairs. The weaker keyed `Queue` is not given an unsupported
  exact insertion guarantee.
- An arbitrary proposed Int sorter can transport indexed ordering and contents
  to pairwise ordering and permutation without changing its implementation.

Boundary cases retain the chapter's meaning: set membership does not count
duplicates; raw list bags can be equivalent without being equal; the constant
one Nat function is outside the finite-list contents image; always-false Boolean
equality invalidates general permutation characterization; and the actual
library `Stable` relation can fail despite indexed ordering and equal contents.

No runtime performance theorem is claimed by these two chapters. Their use of
function extensionality adds no application-specific axiom. Their informal
implementation-efficiency remarks and proof preferences are mathematical
explanation rather than an invented execution model or grading proposition.

CTB-82 provides the complete source/exercise correspondence for both units.
Exact-candidate validation and independent reviews remain separate from receiving
whole-library build, exhaustive audit and integration acceptance.

## Selection: exact remainder, fuel and measured comparisons

CTB-8 is implemented by CTB-83 through
`Applications/Sorting/SourceSelection.lean`,
`Applications/Resources/SelectionSort.lean` and
`Examples/SelectionSorting.lean`. The exact VFA 2.1 archive was retrieved again,
its SHA-256 matched the edition identity above, and the entire `Selection.v`
primary text was freshly read, including prose and all optional exercises.
The chapter has 14,528 bytes and 462 lines; its SHA-256 is
`ff343099ae0fd551648a8fa2bf0adfe32bf5fb158389cee211ff8d1b32c28e11`.
Its 33 source records and 20 exercise headings agree with the immutable
inventory. The existing MIT notice applies; the primary body is not bundled.

### Executable owners and assumptions

`SourceSelection.select` compares the current candidate against the next tail
entry, recursively selects from the remaining tail, and reconstructs the
unselected entry in precisely the source position. It does not substitute a
minimum followed by erasure, an imperative swap, or an existing sorting routine.
The two source branches are exposed by the Nat `select_cons` Boolean/proposition
adapter and by checked true, false and tied cases. The returned pair, including
remainder order, is part of the contract.

`sortFuel` structurally decreases fuel; zero fuel returns the empty list even
for nonempty input. `sortWF` is an independent length-founded recursive
definition, with `select_length` discharging the decrease. Its one-level
equations are public and used directly by the nine-element source calculation.
`sortFuel_eq_sortWF` proves agreement by the recurrences when fuel is sufficient;
`sortFuel_prefix` identifies every smaller-fuel result as a prefix of the
well-founded output. `sortFuel_length` gives `min xs.length fuel`, and
`sortFuel_perm_iff` says occurrence preservation holds exactly when
`xs.length ≤ fuel`. `sortFuel_saturated` handles arbitrary excess fuel.

Execution, permutation, remainder length, membership and fuel laws need only a
decidable relation. Minimum and pairwise-order proofs additionally require
totality and transitivity. They require neither antisymmetry nor equality on
payloads. A pairwise-ordered input alone suffices for `select_of_lower`,
`sortWF_of_pairwise` and `sort_of_pairwise`; these fixed-point laws do not assume
global order properties. Under the ordering assumptions, `sort_idempotent`
follows by applying that input-local result to the ordered output.

Direct `select_contents` and `sortFuel_contents` induct on the executed
recurrences and use pointwise count addition. They do not use the permutation
proof or the permutation-to-count theorem. These generic observations need only
`BEq`; the source query-first singleton/union wrapper specializes lawful Nat
equality and uses the existing `contents_cons_union` law. The function-count
carrier and all occurrence observations remain owned by `Sequences.Multiplicity`.

### All 33 source records

Unqualified witness names below belong to `Examples.SelectionSorting`.
E1–E16 mark the sixteen ordinary exercises and O1–O4 the four optional exercises.
The labels enumerate this chapter's existing headings, not new ticket IDs.

| Source ID | Lean witness or explicit disposition |
|---|---|
| `Selection.select@41` | `select`, `select_nil`, `select_cons`; exact generic execution in `SourceSelection.select`. |
| `Selection.selsort@56` | Expected failed structural recursion. `reconstructed_remainder` proves `select 1 [0,2] = (0,[1,2])`; the remainder is not a structural tail. The successful fuel and length-measure definitions replace the failed attempt, with no admitted stub. |
| `Selection.selsort@77` | `selsort`, `selsort_zero`, `selsort_nil`, `selsort_cons`; zero fuel and empty input remain separate clauses. |
| `Selection.out_of_fuel@87` | `out_of_fuel`, connected to the general output-length law; `partial_output` computes `[1,1,3]`. |
| `Selection.extra_fuel@94` | `extra_fuel`, using the generic saturation theorem. |
| `Selection.selection_sort@102` | `selectionSort`, `selectionSort_eq`; fuel equals actual input length. |
| `Selection.sort_pi@105` | `sort_pi`, the exact eleven-element calculation; `pi_contract` connects it to permutation and adjacent sortedness. |
| `Selection.sorted@119` | `Sorted`, `sorted_nil`, `sorted_1`, `sorted_cons`; the accepted `IsChain` presentation has the source's three rules. |
| `Selection.is_a_sorting_algorithm@126` | `IsSortingAlgorithm`, reusing the arbitrary-function source contract from Sort: input-to-output permutation and adjacent order, with no stability field. |
| `Selection.pairs_example@139` | `pairs_example`; pair decomposition retains the source's universally quantified unused components as underscore-prefixed parameters. |
| `Selection.select_perm@153` E1 | `select_perm`; select equality gives input-to-output permutation, reversing the generic output-first theorem. |
| `Selection.select_rest_length@166` E2 | `select_rest_length`; the source's length orientation follows by permutation length and successor cancellation. |
| `Selection.selsort_perm@178` E3 | `selsort_perm`; retains `l.length = n`, using the stronger sufficient-fuel theorem. |
| `Selection.selection_sort_perm@189` E4 | `selectionSort_perm`. |
| `Selection.select_fst_leq@201` E5 | `select_fst_leq`; generic candidate-minimum bound. |
| `Selection.le_all@212` | `IsLowerBound` is `List.Forall`; `isLowerBound_iff` exposes the membership-wise lower-bound meaning. |
| `Selection.le_all__le_one@222` E6 | `isLowerBound_le_one`, consuming the explicit Forall/membership bridge. |
| `Selection.select_smallest@234` E7 | `select_smallest`; selected value is below every returned remainder entry. |
| `Selection.select_in@247` E8 | `select_in`; the selected value is an actual input occurrence. |
| `Selection.cons_of_small_maintains_sort@262` E9 | `cons_of_small_maintains_sort`; retains `n = bl.length` and transports the bound through fuelled permutation. |
| `Selection.selsort_sorted@278` E10 | `selsort_sorted`; source length premise retained. The generic theorem proves ordering even for truncated output, while occurrence preservation still requires enough fuel. |
| `Selection.selection_sort_sorted@289` E11 | `selectionSort_sorted`, bridging pairwise order to the source adjacent presentation. |
| `Selection.selection_sort_is_correct@300` E12 | `selectionSort_is_correct`. |
| `Selection.selsort'@329` | `selsort'`, independent `SourceSelection.sortWF`, length termination proof, `selsort'_nil` and `selsort'_cons`. |
| `Selection.selsort'_example@353` | `selsort'_example`, the distinct nine-element calculation through the well-founded equations; `wf_example_contract` connects the result to correctness. |
| `Selection.selsort'_perm@375` E13 | `selsort'_perm`; the redundant `n` and length premise remain in the source wrapper. |
| `Selection.cons_of_small_maintains_sort'@388` E14 | `cons_of_small_maintains_sort'`; no fuel premise is introduced. |
| `Selection.selsort'_sorted@401` E15 | `selsort'_sorted`; source quantifiers retained around the stronger generic result. |
| `Selection.selsort'_is_correct@411` E16 | `selsort'_is_correct`. |
| `Selection.select_contents@431` O1 | `select_contents`; source singleton/union equation from the independent direct contents proof. |
| `Selection.selection_sort_contents@440` O2 | `selectionSort_contents`; retains redundant `n` and length equality, and the output is full `selectionSort`, as in the source. |
| `Selection.sorted_iff_sorted@449` O3 | `sorted_iff_sorted`; both chapter presentations explicitly use the same accepted adjacent relation and constructor adapters. |
| `Selection.selection_sort_correct'@456` O4 | `selection_sort_correct'`; the shared Multiset sorting contract, direct contents preservation, and the explicit sortedness bridge. |

### Resource prose and cross-application clients

`Resources.SelectionSort.selectRun` executes the comparison decision as a
measured step, then binds the chosen recursive call and reconstructs its exact
pair. `selectRun_value` proves erasure, and `selectRun_comparisons` proves exactly
one comparison for every input-tail entry. `sortFuelRun` consumes that actual
returned pair and recurses on its returned remainder. It charges no comparisons
at zero fuel or empty input. These are comparison observations; function entries,
constructor requests and comparator implementation costs are not charged.

The separate size-only specification has equations
`T(m,0)=T(0,n)=0` and `T(m+1,n+1)=m+T(m,n)`.
`sortFuelRun_comparisons` proves actual execution agrees with it using the
remainder-length theorem. `sizeCost_double` gives `2*T(n,n)=n*(n-1)` at every
natural size, including zero and one; `sizeCost_exact` gives the division form.
`sizeCost_le_square` and `square_le_four_sizeCost` establish
`T(n,n) ≤ n² ≤ 4*T(n,n)` when `n ≥ 2`. Both real-cast asymptotic directions
reuse `Resources.isBigO_of_nat_bound`. These bounds concern the executed
comparison count through its proved size correspondence.

`sortFuelRun_saturated` proves equality of the whole measured result for enough
fuel. `sortFuelRun_same_length` makes independence from values, input order and
even the decidable relation explicit. `measured_select`, `measured_partial`,
`measured_full`, `measured_excess` and `measured_boundaries` exercise the public
laws. The source five-element example uses nine comparisons at fuel three and
ten at full or excess fuel. No cost theorem is assigned to `sortWF` merely from
its equal output; a separately instrumented well-founded execution would need
its own count bridge.

`insertion_comparisons_le_selection` combines the same unit-comparison
convention with CTB-80's actual insertion measurement. The generic insertion
upper bound is selection's exact count; `insertion_worst_matches_selection`
and `descending_comparison_equality` retain equality in the descending case.
`insertion_best_strict` proves strict comparison advantage on pairwise-ordered
inputs of length at least three, with ascending and all-equal families as checked
specializations. `same_values_different_comparisons` separates output equality
from measured comparison equality. This does not assert wall-clock superiority,
primitive Nat comparison complexity, or relative allocation behavior.

`minimum_agrees` connects the selected value to FDSA's existing
`FixedRank.select0_some_iff_min`; it does not identify the other algorithm's
remainder or resource model. `agrees_with_insertion` uses ordinary sorter
uniqueness for Nat outputs. `keyed_correct` admits arbitrary payloads with
linear-preordered keys; `key_lists_agree` uses antisymmetry only on the observed
keys. `record_output` computes `[(1,"c"),(2,"b"),(2,"a")]` from
`[(2,"a"),(2,"b"),(1,"c")]`. `record_contract` proves ordering and permutation,
and `tied_seed_retained` separately checks the selected payload on a tied head,
while `selection_not_stable` and `selection_records_ne_insertion` prove the
actual equal-key reversal and distinct record outputs. Thus ordinary
correctness and fixed-point behavior do not promise stability.
`equality_relation_boundary` shows why occurrence preservation alone does not
give ordering; `transitivity_boundary` supplies a total cyclic comparison whose
selection output fails pairwise order.

### Teaching commands, remaining boundaries and acceptance

Source warning options, imports, constructor hints and `<=*` notation become
pinned Lean imports, namespaces, explicit lemmas and the `IsLowerBound` adapter; no
global hint database or warning suppression is introduced. Induction suggestions
guide the direct recurrence proofs, while ordinary library lemmas handle pair
decomposition, permutation transport and adjacent/pairwise equivalence.
The Recdef/measure discussion is realized by `termination_by` and its checked
decrease proof. Rocq's `Defined`/`Qed` discussion is not treated as a rule about
Lean proof opacity. `Print` and `Check` commands have public equations and actual
equation-consuming clients; generated Rocq helper names need no artificial Lean
counterparts.

The source's expensive imperative swaps, usual small-input preference and
bubble-sort video are contextual advice, not universal functional runtime
theorems. This development does not execute in-place swaps and does not infer
physical sharing, byte size, peak space or garbage collection from logical list
reconstruction. The source-qualified status covers the complete mathematical
and prose correspondence above. Exact-candidate focused compilation, axiom and
signature checks and both independent review axes are recorded separately by
the checkpoint. Receiving whole-library build, exhaustive project audit and
integration acceptance remain open under the existing programme exception.

## Merge: alternating halves, ordinary correctness and measured work

CTB-9 and CTB-84 reconstruct the complete Merge chapter. The exact primary
`Merge.v` has 17,839 bytes and 526 lines, SHA-256
`090c5afc3a95750336b8b57ed2169b8d77c790266f231bf096be55761c20378b`.
All 17 declaration records, six exercises (four standard and two advanced),
three inspection commands and the complete surrounding prose are accounted for.
The source edition, archive and MIT notice remain the single owners above.

### Algorithms, assumptions and shared owners

`Applications.Sorting.SourceMergeSort.split` implements the source's two-step
recursion. It sends positions 0, 2, 4, ... to the left and positions 1, 3, 5,
... to the right, preserving order within each side. `split_lengths` gives
`((n+1)/2, n/2)`, `split_length_add` gives their sum, and `split_length_lt`
requires `1 < n` before claiming that both sides decrease. `split_perm`,
`split_sublists` and `split_map` preserve occurrences, internal order and mapping
without an order or equality test on elements. The constructive
`list_induction_two` proves the two-step induction schema used by the split proofs.
`halve_eq_reverse_split` relates the distinct FDSA splitter at arbitrary supplied
accumulators: its two results are the reversed VFA subsequences followed by
those respective accumulators. `split_accumulator_bridge` checks this law with
both accumulators nonempty; no equality of the intermediate split pairs is assumed.

`sortBy` is the separate executable, length-founded source sort. It returns
empty and singleton inputs unchanged; otherwise it recursively sorts the actual
alternating halves and passes their results to the shared ordinary merge.
`sortBy_step` and `sortBy_induction` expose the one-level equation and the
input/output induction interface. The induction interface has real correctness
consumers in `Examples.MergeSorting.mergesort_sorts` and `mergesort_perm`.

`Applications.Sorting.sourceMerge` already owns the source merge recurrence,
with its `sourceMerge_eq_merge` bridge to `List.merge`. The source's nested
structural fixpoints are represented by this checked sum-of-lengths recursion;
the bridge concerns values, not equality of compiled code or resource counts.
The new whole-sort wrapper does not substitute the library's contiguous or
reversed-pile merge sort for VFA's alternating algorithm.

Permutation, length and measured erasure require only an executable Boolean
comparator. `sortBy_sorted_compatible_on` assumes a preorder on observed keys
and comparison agreement only on actual input members. `sortOn_correct`
specializes to decidable non-strict linear-preorder keys, without any order or
equality instance on the payloads. Ordinary Nat sorting uniqueness gives
agreement with insertion, selection and stable sorting, and Nat fixed-point and
idempotence laws. These equalities do not equate their executions or costs.
For tagged records only the key lists agree under key antisymmetry; the payload
sequences can differ.

### All 17 source records

Names in the final column are in `Examples.MergeSorting` unless qualified.
The historical separate chapter inventory is superseded by the immutable
aggregate inventory linked above; all IDs below are checked against the exact
primary file.

| Source record | Lean correspondence or complete disposition |
|---|---|
| `Merge.split@47` | `split`, aliasing the exact generic source splitter and its empty/singleton/two-cons equations. |
| `Merge.split_len_first_try@63` | The true statement is supplied by `split_len`; the aborted ordinary-tail induction is explained below, without retaining an admission. |
| `Merge.list_ind2_principle@87` | The universe-polymorphic `TwoStepListInduction` proposition preserves all three cases and quantifiers. |
| `Merge.split_len'@99` | `split_len'` retains and actually uses its supplied induction-schema premise. |
| `Merge.list_ind2@118` | `list_ind2` proves the schema through the constructive generic principle. |
| `Merge.split_len@148` | `split_len` supplies the proved principle to the conditional theorem and retains both weak length bounds. |
| `Merge.split_perm@161` | `split_perm` retains the source split-pair premise and input-to-concatenation permutation direction. |
| `Merge.merge@209` | `merge`, the shared actual `sourceMerge`, with `merge_equation` and both nonempty branch laws. |
| `Merge.merge2@258` | `merge2` preserves its non-strict head premise, including ties, without sortedness assumptions. |
| `Merge.merge_nil_l@286` | `merge_nil_l`; the complementary `merge_nil_r` is also exposed. |
| `Merge.mergesort@358` | `mergesort`, the exact length-founded alternating sort, with `mergesort_equation` and `mergesort_ind`. |
| `Merge.sorted_merge1@461` | `sorted_merge1` uses only the two head inequalities and sortedness of the merged output; no sorted-input premise is added. |
| `Merge.sorted_merge@470` | `sorted_merge` transports source adjacent sortedness through the shared pairwise merge theorem. |
| `Merge.mergesort_sorts@481` | `mergesort_sorts` consumes the source-shaped input/output induction principle. |
| `Merge.merge_perm@501` | `merge_perm` gives input concatenation to actual output permutation with no order premises. |
| `Merge.mergesort_perm@509` | `mergesort_perm` consumes the whole-sort induction, split occurrence law and merge occurrence law. |
| `Merge.mergesort_correct@516` | `mergesort_correct` supplies the accepted arbitrary-function sorting specification for this exact source sort. |

All six exercised declarations in the table are proved. The source permits the
Multiset/BagPerm formulation as an alternative occurrence proof; the retained
proof uses `List.Perm`, so no set-only notion of contents replaces multiplicity.

### Executed resource observations and separating clients

`Resources.SourceMergeSort.splitRun` recursively computes the actual halves,
charging one abstract element visit per input element. `splitRun_exact` proves
both its returned pair and the exact count `n`, with base costs zero and one.
The whole `run` binds the single measured splitter result, both recursive sort
results and `Resources.ListMerge.run` on those results. Its observations are
`(split element visits, merge head comparisons)`. `run_step`, `run_value`,
`run_perm` and `run_length` connect execution, sequencing and source meaning.

`splitVisits_step` and `comparisons_step` expose exact recurrences for the
executed observations. `splitSizeCost` independently defines
`S(0)=S(1)=0` and `S(n)=n+S((n+1)/2)+S(n/2)` for `n >= 2`;
`splitVisits_eq_splitSizeCost` proves the execution realizes it. Equal-length
inputs therefore have equal splitter work even across different comparators
and element types. Merge comparisons remain value-dependent. The shared
`Resources.ListMerge.comparisons_le_pred` sharpens its bound to `m+n-1`, with
natural subtraction handling empty inputs and no comparator laws required.

`costs_le_clog` bounds each whole-sort projection by `n * Nat.clog 2 n`.
`work_le_clog` bounds their sum by twice that quantity. `work_le_real_log`
gives an explicit `4*n*log₂ n` bound from length two, and the three `IsBigO`
results use the existing Growth bridge for arbitrary input families of length
`n`. The costs exclude comparator internals, function-entry and length-test
overhead; the result is a bound for these declared visit/comparison observations.
There is no unqualified wall-clock or all-primitive-operations theorem.

The checked clients retain:

- Empty, singleton, even and odd splits, including `[0,1,2,3,4]` becoming
  `([0,2,4],[1,3])`; explicit differences from contiguous and reversed piles;
  and singleton failure of strict decrease without the recursive-case premise.
- A duplicate-rich pi-prefix Nat example connected to the source equations,
  ordinary correctness and existing sorter uniqueness.
- Tagged equal-key records `[A,B,C]` yielding `[A,C,B]`, then `[A,B,C]` on a
  second sort. `records_not_fixed`, `records_not_idempotent` and
  `records_not_stable` retain the three distinct failures. `blocks_stable`
  positively checks ordinary merge stability relative to the split-block
  concatenation; that concatenation has already reordered the original records.
- Standalone split `[3,1,2]` costing three visits. Sorting that input costs
  `(5,2)`, whereas sorting `[3,2,1]` costs `(5,3)` despite the same sorted value.
  Empty and singleton sorts have `(0,0)` because they do not invoke the splitter.
- Actual measured merges of interleaved and early-exhausting inputs, the sharp
  comparison bound, explicit source-merge erasure, and an `erasureSquare`
  client transporting the pi example through the measured execution.
- A false Boolean comparator producing an unsorted result, preserving the
  need for comparison compatibility in the ordering theorem.

### Recursion pedagogy and prose boundaries

The first split proof is aborted because ordinary tail induction supplies the
wrong recursive hypothesis, not because the length statement is false. The
conditional two-step theorem, proved schema and final application retain that
pedagogical dependency. The source merge changes which argument decreases;
Lean's measure and public branch equations replace the local-fixpoint unfolding
mechanics without recreating Rocq tactic diagnostics. `Print merge` and the two
`Check` commands are represented by those equations and inspected elaborated
interfaces with checked consumers.

The naive whole-sort recursion also omits the necessary base cases; the retained
small cases show the missing decrease, while the actual definition supplies it.
Lean's equation theorems and `termination_by` implement the source's
`Function`/`Defined` intent without transferring Rocq opacity conventions.
The recommendation to reason with generated equations and induction is realized
by the source-facing correctness proofs.

The opening linear auxiliary-space claim concerns the usual imperative array
algorithm. It supplies no physical heap, stack, sharing, garbage-collection or
peak-live-space theorem for this list program. Splitting a list is explicitly
linear in the charged visit model. The source-qualified mathematical/prose
correspondence remains separate from exact-candidate focused validation,
independent reviews and the receiving whole-library acceptance gates.

## Maps: total functions, optional bindings and update algebra

CTB-10 and CTB-85 cover the complete Maps chapter after Merge. The exact primary
`Maps.v` is 7,017 bytes and 220 lines, SHA-256
`19e79f4b7ac5bce3ffc246e19dd926b14fa5720b47d9618d2607d809d0504aea`.
All 23 source records and six standard exercises are accounted for. There are
no optional exercises, aborted proofs, grading stubs or inspection commands.
The chapter's source identity and license use the owners already linked above.

### Public operations and exact assumptions

`Examples.FunctionalMaps.TotalMap A` is exactly `Nat → A`; `totalEmpty value`
is the constant function at the supplied value. The type carries no hidden
default, membership operation, finite support or update-history representation.
`PartialMap A` is exactly `Nat → Option A`, with empty `none` and updates
writing `some value`. Empty and optional payload types remain valid.

`Applications/Search/OrderedMap/FunctionUpdate.lean` extends the existing
`Search.OrderedMap` owner with six small laws. `update_apply_written` proves
the written-key-first equality branch, and `update_nat_source` connects the
exact Nat Boolean test to `Function.update`. Keys need only `DecidableEq`,
with no key ordering, payload equality or inhabitance requirement. Key and
payload universes are independent. `write_shadow`, `write_eq_self_iff`,
`write_same` and `write_comm` apply the shared function algebra to the existing
partial-map write operation; they do not introduce another map carrier.

The six total-map exercise proofs consume Mathlib's update laws. The six
partial-map statements visibly specialize those total laws at `Option A`.
The source's variable-order distinction is retained: total `totalUpdate_neq`
writes `x₁` and queries `x₂`, whereas partial `update_neq` writes `x₂` and
queries `x₁`. The partial self-update law retains its successful-binding
premise. Function equality uses extensionality; no executable function-equality
test or new project axiom is introduced.

### All 23 source records

Targets below are in `Examples.FunctionalMaps` unless qualified. The four
original observations retain the write of `false` at key 1, even though that
value equals the empty map's default.

| Exact source inventory ID | Lean target and complete contract/proof route |
|---|---|
| `Maps.total_map@28` | `TotalMap`: exact `Nat → A`, at arbitrary payload universe. |
| `Maps.t_empty@34` | `totalEmpty value`: the constant function, requiring only its supplied value. |
| `Maps.t_update@42` | `totalUpdate := Function.update`; `totalUpdate_source` proves the exact written-key-first Nat Boolean branch as a whole-function equality through `Search.OrderedMap.update_nat_source`. |
| `Maps.examplemap@54` | `exampleMap`: exactly `totalUpdate (totalUpdate (totalEmpty false) 1 false) 3 true`; the default write at key 1 remains in the expression. |
| `Maps.update_example1@61` | `exampleMap_zero`: the exact source map at 0 is false; consumes the two distinct-key laws and constant-empty law. |
| `Maps.update_example2@64` | `exampleMap_one`: at 1 is false; consumes outer distinct-key lookup and inner same-key lookup. |
| `Maps.update_example3@67` | `exampleMap_two`: at 2 is false; consumes both distinct-key laws and constant-empty law. |
| `Maps.update_example4@70` | `exampleMap_three`: at 3 is true; consumes the latest same-key update law. |
| `Maps.t_apply_empty@83` | `totalEmpty_apply A x value`: constant map application equals the supplied value; reduction of the actual definition. Standard exercise 1/6. |
| `Maps.t_update_eq@94` | `totalUpdate_eq A m x value`: querying the written key returns the value, for arbitrary function `m`; directly `Function.update_self`. Standard exercise 2/6. |
| `Maps.t_update_neq@107` | `totalUpdate_neq X value x₁ x₂ m`: premise `x₁ ≠ x₂`; written key `x₁`, query `x₂`; directly `Function.update_of_ne (Ne.symm different)`. Standard exercise 3/6. |
| `Maps.t_update_shadow@123` | `totalUpdate_shadow A m first last x`: two writes at `x` equal the later write alone as complete functions; directly `Function.update_idem`. Standard exercise 4/6. |
| `Maps.t_update_same@135` | `totalUpdate_same X x m`: writing `m x` returns `m` as a complete function; directly `Function.update_eq_self`. Standard exercise 5/6. |
| `Maps.t_update_permute@146` | `totalUpdate_permute X v₁ v₂ x₁ x₂ m`: premise `x₂ ≠ x₁`; write `(x₂,v₂)` then `(x₁,v₁)` equals the reverse history, with exact source key/value order; directly `Function.update_comm different v₂ v₁ m`. Standard exercise 6/6. |
| `Maps.partial_map@161` | `PartialMap A := TotalMap (Option A)`: unrestricted optional-valued functions. |
| `Maps.empty@163` | `empty := totalEmpty none`: absence is `none`, without selecting a default payload. |
| `Maps.update@166` | `update m x value := totalUpdate m x (some value)`; `update_eq_write` relates it to the existing generic partial-map `write`. |
| `Maps.apply_empty@173` | `apply_empty A x`: returns `none`; explicitly `totalEmpty_apply (Option A) x none`. |
| `Maps.update_eq@179` | `update_eq A m x value`: returns `some value`; explicitly `totalUpdate_eq (Option A)`. |
| `Maps.update_neq@186` | `update_neq X value x₁ x₂ m`: premise `x₂ ≠ x₁`, written key `x₂`, query `x₁`; explicitly calls total `totalUpdate_neq (Option X) (some value) x₂ x₁`. |
| `Maps.update_shadow@195` | `update_shadow A m first last x`: explicitly total `totalUpdate_shadow (Option A)` at `some first`, `some last`. |
| `Maps.update_same@202` | `update_same X value x m`: retains `m x = some value`; rewrites by that premise and consumes `totalUpdate_same (Option X)`. Absence is not a stored default. |
| `Maps.update_permute@210` | `update_permute X v₁ v₂ x₁ x₂ m`: same exact ordering and `x₂ ≠ x₁` premise as the total law, explicitly specialized at optional values. |

### Connected clients and complete prose disposition

The exact four Bool observations are proved through the public update laws.
`same_key_different_writes` shows why distinct keys are required for commutation
by comparing two actual false/true write orders at one key. Generic Bool-key
commutation and repeated-write clients exercise the reusable partial laws
without adding payload assumptions.

`storedDefault_ne_empty`, `storedDefault_same_total_observation` and
`storedDefault_presence` use a concrete absent map and a map storing `false`
at key 3. The partial functions differ, their default-false observations agree,
and their presence bits differ. This retains the distinction between absence
and a stored default. `empty_payload`, `optional_payload` and
`unrestricted_partial_function` additionally check empty payloads, a stored
`none` yielding `some none`, and an actual function bound at every Nat key.

The exact source map is connected to the existing chronological two-write
`Search.TotalTable.setAll` client. `table_two_writes` consumes the shared laws
from any valid starting representation; `exampleMap_eq_list_client` connects
the source's function implementation to the actual association-list realization
through observation equality. No equality of list and function representations
is claimed.

`store_write_decode`, `store_write_shadow` and `store_distinct_writes` compose
the update algebra with the existing `Dijkstra.Store` vector implementation.
The source map has arbitrary Nat keys; this separate client explicitly has
finite keys `Fin n`. The concrete `[10,20,30]` client writes 99 and then 7 at
index 1, obtaining 7 there and preserving 10 at index 0 through public decoder
and shadowing laws. It adds no claim about Dijkstra's whole algorithm.

The introductory total/default versus partial/optional discussion is captured
by these observation boundaries. The higher-order representation remains
function-valued, and the source's informal `Id` wording does not change its
actual Nat keys. Lean Bool/Option/Nat and Mathlib function APIs adapt the Rocq
imports. The extensionality discussion is a proof principle, not an algorithm
for deciding arbitrary map equality. Partial-map reuse is explicit in every
partial theorem. Maps requests no runtime experiment, complexity theorem or
history interpreter; none is inferred from the functional representation.
Later Trie and extraction obligations remain separate.

All source quantifiers, written/query directions and latest-write precedence
are retained. Chapter qualification follows Merge; exact-candidate validation,
independent review and receiving integration remain separately recorded gates.

## SearchTree: raw search, canonical enumeration and independent models

CTB-11 and its mathematical child CTB-86 reconstruct the complete SearchTree
source scope after Maps. The exact primary `SearchTree.v` is 44,738 bytes and
1,325 lines, SHA-256
`44b9464a10e8c9e3222530f6f26be45bd44d1c0568deb1710417618706fae61d`.
Its release, archive and license are those identified above. The entire source,
including prose and exercise prompts, and the preserved
[SearchTree plan](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1009-SearchTree.md)
were read for this correspondence.

The map accounts for all **90 lexical records**: 27 definitions, 18
source-proved statements, 41 source admissions, two proof tactics, one grading
stub and one aborted false claim. All **35 exercises** are included, with
24 optional, 12 advanced and eight carrying both labels. The 11 inspection
commands and all substantive algorithmic, abstraction and efficiency discussions
have explicit dispositions below. These counts identify the source scope;
the checkpoint owns exact-candidate validation, independent reviews and final
acceptance.

### Existing carriers and public owners

| Owner | Role in this chapter |
|---|---|
| `Applications/Search/OrderedMap/Basic.lean` | Existing directed search/insertion, now with independent key and payload universes; raw structural shadowing, the explicit path decoder and unrestricted raw-tree map laws. |
| `Applications/Search/OrderedMap/Enumeration.lean` | Strict key order and key nodup of existing entries; directed lookup/membership; the function-valued accumulator traversal; exact key/value list insertion and enumeration after insertion. |
| `Applications/Search/OrderedMap/SourceModel.lean` | Head-wins list decoding, finite observed support, the enumerating abstraction, collision-removing union, independent structural decoding and insertion, final coherence and canonical enumeration. |
| `Applications/Resources/SearchTree.lean` | Executing measured lookup and insertion, short-circuit comparator work, input-local bounds/calibration, height and real-logarithmic consequences, and valid linear-path witnesses. |
| `Applications/Resources/TreeEnumeration.lean` | Actual source append executions, exact copy counts and shape families, and measured accumulator traversal with arbitrary suffix. |
| `Applications/Resources/UnaryComparison.lean` | Explicit lockstep unary ≤ model, strict adapter, exact comparison charges, corrected difference-only claim and existing measured-square clients. |
| `Examples/SearchTrees.lean` | Nat-key source wrappers, every mathematical source statement, negative examples, independent abstraction clients and the accepted shared table client. |
| `Examples/SearchTreeWork.lean` | Connected concrete executions and source-wrapper erasure clients using the public resource results. |

The carrier remains Mathlib's `BinaryTree`, with key/value pairs at internal
nodes. `Examples.SearchTrees.nil` and `Examples.SearchTrees.node` adapt the source
constructor interface; no second tree type is introduced. Source keys remain
Nat. Generic algorithms compare only keys and allow key and payload types in
independent universes; they impose no equality, order or inhabitance on payloads.
The source's inductive `ForallT`/BST interface is supplied by
`Examples.SearchTrees.forallT_node`, `Examples.SearchTrees.bst_node` and
`Examples.SearchTrees.bst_induction` over the existing recursive
`Search.OrderedTree.All` and `Search.OrderedTree.OrderedBy`. Both all-descendant
strict separator premises are retained. Ordering immediate children alone would
not establish this invariant.

`Search.OrderedTree.entries` continues to own enumeration and reuses
`Trees.inorder`. `Search.OrderedTree.entries_length` establishes
`length(elements t) = t.numNodes` on every raw tree. Strict pairwise key order
and key nodup in `Search.OrderedMap.ordered_entries_keys_pairwise` and
`Search.OrderedMap.ordered_entries_keys_nodup` need only a preorder on keys;
the Nat source sortedness result uses the already accepted
`Examples.InsertionSorting.Sorted` representation. Key order is not replaced
by lexicographic order or an order on payloads.

### Observation boundaries and the raw algebra

`Search.OrderedMap.pathObserve` is the optional result of directed search.
`Search.OrderedMap.pathObserve_bind` and `Search.OrderedMap.rawTrees_laws`
apply to every raw tree, since insertion and lookup make the same branch
decisions. They are separate from the existing whole-tree decoder
`Search.OrderedMap.observe` and from the two source model abstractions.
A misplaced binding can belong to the tree without being reachable by search.

| Statement family | Exact assumption boundary |
|---|---|
| Empty lookup, same/different-key lookup and bound after insertion, default-valued shadow/self/commutation | Arbitrary raw trees; commutation retains distinct written keys. The self-update theorem uses the same caller-supplied default on both sides. |
| All-node predicate after insertion | The old tree satisfies that predicate and the new pair satisfies it; no BST or predicate closure property. |
| Structural shadowing | Arbitrary raw trees, with latest-write precedence. Structural self-update and structural distinct-key commutation are false and have explicit witnesses. |
| Enumeration completeness | Presence=true and the returned value; no BST. The false source attempt that omitted presence is refuted even on E. |
| Enumeration soundness and inverse completeness | BST is retained. Membership implies the actual partial binding, hence both presence and the value at every supplied default. |
| Inverse correctness and `Examples.SearchTrees.bound_value` | No BST. The latter chooses one value before quantifying over every default. |
| Sorted keys, key nodup, enumeration after tree insertion, and model/search correspondences | BST is retained; the invariant has concrete empty and insertion-preservation witnesses. |
| Equality of canonical lists | Two valid trees with equal partial-map bindings. Equality of observations at one default is insufficient. |

`Examples.SearchTrees.rawTable` uses the existing
`Search.TotalTable.ofPartial` adapter, and
`Examples.SearchTrees.rawTable_laws` explicitly has validity predicate
`fun _ => True`. `Examples.SearchTrees.rawTable_two_writes` invokes
`Examples.FunctionalMaps.table_two_writes` for arbitrary raw starting trees.
`Examples.SearchTrees.rawTable_history_agrees` connects a complete write
history to the accepted function representation starting at the same observed
function. The exact Maps Bool history, including the stored default at key 1,
is connected by `Examples.SearchTrees.function_example_eq_tree_client` and
`Examples.SearchTrees.tree_client_agrees_with_list` to the function and
association-list clients. These are equalities of observations, with separate
BST premises where enumeration is used.

### All 90 source records

Every target below is qualified. Multiple source proof presentations may use
one checked theorem when their complete mathematical contracts agree. Tactics,
the grading placeholder and the false Abort have explicit dispositions.

| Exact source inventory ID | Lean target and complete contract/proof route |
|---|---|
| `SearchTree.key@38` | `Examples.SearchTrees.Key := Nat`; the generic owner is separately polymorphic in ordered keys. |
| `SearchTree.tree@44` | `Examples.SearchTrees.Tree V := BinaryTree (Nat × V)`, with `Examples.SearchTrees.nil` and `Examples.SearchTrees.node` constructor adapters; arbitrary raw trees remain representable. |
| `SearchTree.ex_tree@59` | `Examples.SearchTrees.exampleTree`: root 4→`"four"`, left 2→`"two"`, right 5→`"five"`. |
| `SearchTree.empty_tree@64` | `Examples.SearchTrees.emptyTree` is E, with no payload inhabitance assumption. |
| `SearchTree.bound@69` | `Examples.SearchTrees.bound` and `Examples.SearchTrees.bound_node`: the presence bit of directed optional lookup; query/root comparison precedes root/query comparison. |
| `SearchTree.lookup@80` | `Examples.SearchTrees.lookup` and `Examples.SearchTrees.lookup_node`: directed lookup with the caller's explicit default, preserving that comparison order. |
| `SearchTree.insert@91` | `Examples.SearchTrees.insert`, `Examples.SearchTrees.insert_empty` and `Examples.SearchTrees.insert_node` specialize `Search.OrderedMap.bind`, including value replacement at the equal key. |
| `SearchTree.Tests.bst_ex1@109` | `Examples.SearchTrees.insert_exampleTree`: inserting 4, then 2, then 5 into E yields the exact source tree. |
| `SearchTree.Tests.bst_ex2@113` | `Examples.SearchTrees.lookup_exampleTree_present`: lookup 5 with default `""` returns `"five"`. |
| `SearchTree.Tests.bst_ex3@116` | `Examples.SearchTrees.lookup_exampleTree_absent`: lookup absent 3 with default `""` returns that default. |
| `SearchTree.Tests.bst_ex4@119` | `Examples.SearchTrees.bound_exampleTree_absent`: presence of 3 is false. |
| `SearchTree.NotBst.t@141` | `Examples.SearchTrees.Malformed.exampleTree` retains root 4, misplaced left 5 and right 2, with the exact source payloads. |
| `SearchTree.NotBst.not_bst_lookup_wrong@149` | `Examples.SearchTrees.Malformed.lookup_hidden_key_misses`: directed lookup of 2 does not return the physically present `"two"`. |
| `SearchTree.ForallT@160` | `Examples.SearchTrees.ForallT` specializes `Search.OrderedTree.All` to key/value predicates; `Examples.SearchTrees.forallT_node` exposes the all-node constructor equation. |
| `SearchTree.BST@174` | `Examples.SearchTrees.BST` specializes `Search.OrderedTree.OrderedBy Prod.fst`; `Examples.SearchTrees.bst_node` and `Examples.SearchTrees.bst_induction` retain both all-descendant strict separators. |
| `SearchTree.is_BST_ex@188` | `Examples.SearchTrees.bst_exampleTree` checks the complete source example against the actual invariant. |
| `SearchTree.not_BST_ex@195` | `Examples.SearchTrees.Malformed.not_bst_exampleTree` proves the malformed source example violates that invariant. |
| `SearchTree.empty_tree_BST@206` | `Examples.SearchTrees.bst_emptyTree`: E is valid for every payload type. |
| `SearchTree.ForallT_insert@220` | `Examples.SearchTrees.forallT_insert` consumes `Search.OrderedMap.all_bind`: all old labels satisfy P and the new binding satisfies P; no BST premise. |
| `SearchTree.insert_BST@229` | `Examples.SearchTrees.bst_insert` consumes `Search.OrderedMap.ordered_bind` and preserves the full strict separator invariant. |
| `SearchTree.lookup_empty@290` | `Examples.SearchTrees.lookup_empty`: every query on E returns the supplied default. |
| `SearchTree.lookup_insert_eq@296` | `Examples.SearchTrees.lookup_insert_eq` derives the same-key observation from `Examples.SearchTrees.lookup_insert` on every raw tree. |
| `SearchTree.bdestruct_guard@311` | Proof-automation disposition: checked Lean proofs split comparison/equality cases with `by_cases` and simplify the resulting propositions; no new mathematical constant or tactic framework. |
| `SearchTree.bdall@320` | Proof-automation disposition: ordinary case splitting, `simp` and arithmetic proofs replace the repeated Rocq branch tactic. This carries no execution-cost claim. |
| `SearchTree.lookup_insert_eq'@323` | The identical mathematical contract uses `Examples.SearchTrees.lookup_insert_eq`. The alternative automation presentation does not require a duplicate theorem. |
| `SearchTree.lookup_insert_neq@333` | `Examples.SearchTrees.lookup_insert_neq`: written key differs from query, so the default-valued query is unchanged; no BST premise. |
| `SearchTree.manual_grade_for_bound_correct@356` | The administrative grading value is omitted. The full exercise is proved by `Examples.SearchTrees.bound_empty`, `Examples.SearchTrees.bound_insert_eq` and `Examples.SearchTrees.bound_insert_neq` on arbitrary raw trees. |
| `SearchTree.bound_default@364` | `Examples.SearchTrees.bound_default`: absence implies the supplied default is returned. `Examples.SearchTrees.bound_default_converse_fails` checks that the converse is false. |
| `SearchTree.lookup_insert_shadow@432` | `Examples.SearchTrees.lookup_insert_shadow`: the latest same-key write wins at every query/default, through the public raw lookup law. |
| `SearchTree.lookup_insert_same@443` | `Examples.SearchTrees.lookup_insert_same`: inserting the current value preserves observations at this same default. It does not assert presence or raw-tree equality. |
| `SearchTree.lookup_insert_permute@453` | `Examples.SearchTrees.lookup_insert_permute`: distinct written keys commute under every default/query observation; no BST premise. |
| `SearchTree.insert_shadow_equality@475` | `Examples.SearchTrees.insert_shadow_equality` consumes `Search.OrderedMap.bind_shadow`: structural equality retains the latest value, with old-then-new write order explicit. |
| `SearchTree.insert_same_equality_breaks@493` | `Examples.SearchTrees.insert_same_equality_breaks`: at every payload universe, an existential empty-tree/default-valued insertion changes the raw tree. |
| `SearchTree.insert_permute_equality_breaks@499` | `Examples.SearchTrees.insert_permute_equality_breaks`: distinct keys 0 and 1 inserted in opposite orders give different roots, even with equal payloads. |
| `SearchTree.elements@517` | `Examples.SearchTrees.elements := Search.OrderedTree.entries`; `Examples.SearchTrees.elements_node` states explicitly `elements left ++ ([(k,value)] ++ elements right)`. `Search.OrderedTree.entries_length` gives length = node count for every raw tree. |
| `SearchTree.elements_ex@523` | `Examples.SearchTrees.elements_exampleTree`: exactly [(2,`"two"`),(4,`"four"`),(5,`"five"`)] in inorder. |
| `SearchTree.elements_complete_broken_spec@554` | `Examples.SearchTrees.DefaultLookupImpliesMembership` retains the false universal proposition, including its BST premise and default-valued lookup antecedent. |
| `SearchTree.elements_complete_broken@567` | The source Abort is disposed of by `Examples.SearchTrees.not_defaultLookupImpliesMembership`, a proof of the proposition's negation using a valid empty tree. The false positive statement is not asserted. |
| `SearchTree.elements_complete_spec@577` | `Examples.SearchTrees.ElementsComplete` retains presence=true and lookup=value as separate antecedents, with no BST assumption. |
| `SearchTree.elements_complete@587` | `Examples.SearchTrees.elements_complete` uses `Search.OrderedMap.binding_iff`, directed successful-lookup membership and the shared entries/contains bridge. |
| `SearchTree.elements_correct_spec@596` | `Examples.SearchTrees.ElementsCorrect`: on a BST, binding membership implies both presence and the value at the caller's default. |
| `SearchTree.uncurry@626` | Pair projections in `Examples.SearchTrees.elements_preserves_forall` express exactly `fun binding => P binding.1 binding.2`. This elementary adapter introduces no second predicate or carrier. |
| `SearchTree.elements_preserves_forall@631` | `Examples.SearchTrees.elements_preserves_forall`: every listed pair satisfies the all-node predicate. Its membership-quantified conclusion is equivalent to `List.Forall` through `List.forall_iff_forall_mem`. |
| `SearchTree.elements_preserves_relation@652` | `Examples.SearchTrees.elements_preserves_relation` specializes the all-node theorem at an arbitrary key relation and a fixed second key; no relation laws or BST premise. |
| `SearchTree.elements_correct@667` | `Examples.SearchTrees.elements_correct` uses `Search.OrderedMap.lookup_eq_some_iff_mem_entries` under BST, then the precise presence/default equivalence. |
| `SearchTree.elements_complete_inverse@688` | `Examples.SearchTrees.elements_complete_inverse`: on a BST, absent presence excludes every listed value at that key. |
| `SearchTree.bound_value@703` | `Examples.SearchTrees.bound_value`: presence gives `∃ value, ∀ default, lookup default k t = value`; the witness precedes and is independent of the default, with no BST premise. |
| `SearchTree.elements_correct_inverse@710` | `Examples.SearchTrees.elements_correct_inverse`: exclusion of every value at a key from entries implies absence, on every raw tree; uses the preceding witness and completeness. |
| `SearchTree.sorted_app@731` | `Examples.SearchTrees.sorted_app` retains sorted left/right Nat lists and both strict separator predicates; the conclusion uses the accepted `Examples.InsertionSorting.Sorted` adapter. |
| `SearchTree.list_keys@745` | `Examples.SearchTrees.listKeys` is `List.map Prod.fst` on the actual binding list. |
| `SearchTree.sorted_elements@751` | `Examples.SearchTrees.sorted_elements` derives accepted non-strict Nat sortedness from `Search.OrderedMap.ordered_entries_keys_pairwise` and the BST premise. |
| `SearchTree.disjoint@772` | `Examples.SearchTrees.Disjoint` is the source membership condition `∀ x, x ∈ left → x ∉ right`, for arbitrary element types. |
| `SearchTree.NoDup_append@781` | `Examples.SearchTrees.nodup_append` consumes `List.Nodup.append` with nodup on each operand and cross-list membership disjointness. |
| `SearchTree.elements_nodup_keys@794` | `Examples.SearchTrees.elements_nodup_keys` consumes `Search.OrderedMap.ordered_entries_keys_nodup`; uniqueness concerns projected keys, not merely pairs. |
| `SearchTree.fast_elements_tr@814` | `Examples.SearchTrees.fastElementsAcc` specializes `Search.OrderedMap.fastEntriesAcc`; `Examples.SearchTrees.fastElementsAcc_node` exposes the nested right-then-left accumulator recurrence. |
| `SearchTree.fast_elements@821` | `Examples.SearchTrees.fastElements` specializes `Search.OrderedMap.fastEntries` at the empty suffix. |
| `SearchTree.fast_elements_tr_helper@829` | `Examples.SearchTrees.fastElementsAcc_eq_append` consumes `Search.OrderedMap.fastEntriesAcc_eq` for every raw tree and arbitrary suffix. |
| `SearchTree.fast_elements_eq_elements@835` | `Examples.SearchTrees.fastElements_eq_elements` specializes that arbitrary-suffix result to the empty suffix; no BST premise. |
| `SearchTree.fast_elements_correct@846` | `Examples.SearchTrees.fastElements_correct` rewrites the optimized list through its public equality and then invokes `Examples.SearchTrees.elements_correct`. The separate `Examples.SearchTrees.fastElements_sorted` transfers sortedness in the same way. |
| `SearchTree.elements_empty@874` | `Examples.SearchTrees.elements_empty`: E enumerates to [] for arbitrary payload types. |
| `SearchTree.kvs_insert@886` | `Examples.SearchTrees.kvsInsert` specializes `Search.OrderedMap.kvsInsert`: insert before a greater head, recurse after a smaller head, replace at equality. |
| `SearchTree.kvs_insert_split@902` | `Examples.SearchTrees.kvsInsert_split` consumes `Search.OrderedMap.kvsInsert_split` with both strict separator predicates. Its three source branches require neither list sortedness nor per-list nodup. |
| `SearchTree.kvs_insert_elements@918` | `Examples.SearchTrees.kvsInsert_elements` consumes `Search.OrderedMap.entries_bind` under BST: enumeration after actual tree insertion equals the exact list insertion. |
| `SearchTree.map_of_list@986` | `Examples.SearchTrees.mapOfList := Search.OrderedMap.listObserve`; `Examples.SearchTrees.mapOfList_empty` and `Examples.SearchTrees.mapOfList_cons` expose the empty and head-wins tail-update equations. |
| `SearchTree.Abs@992` | `Examples.SearchTrees.enumerationMeaning := Search.OrderedMap.SourceModel.enumAbs`, defined as the list decoder of the actual inorder entries for every raw tree. |
| `SearchTree.find@1007` | `Examples.SearchTrees.find` specializes `Search.OrderedMap.withDefault`: the result is V after `Option.getD`, with no extra `some` in the codomain. |
| `SearchTree.map_bound@1015` | `Examples.SearchTrees.mapBound` specializes `Search.OrderedMap.hasBinding` and returns the optional map's presence bit. |
| `SearchTree.in_fst@1036` | `Examples.SearchTrees.in_fst` consumes `Search.OrderedMap.SourceModel.in_keys_of_mem` for arbitrary pair types in independent universes. |
| `SearchTree.in_map_of_list@1043` | `Examples.SearchTrees.mapOfList_eq_some_of_mem` retains projected-key nodup plus actual pair membership; `Search.OrderedMap.SourceModel.listObserve_eq_some_of_mem` yields the stored value. |
| `SearchTree.not_in_map_of_list@1051` | `Examples.SearchTrees.mapOfList_eq_none_of_not_mem` consumes `Search.OrderedMap.SourceModel.listObserve_none_of_not_mem`; key absence needs no nodup premise. |
| `SearchTree.empty_relate@1057` | `Examples.SearchTrees.enumerationMeaning_empty`: the enumerating abstraction of E is the accepted optional empty map. |
| `SearchTree.bound_relate@1065` | `Examples.SearchTrees.enumerationMeaning_bound` uses `Search.OrderedMap.SourceModel.enumAbs_bound` under BST. |
| `SearchTree.lookup_relate@1075` | `Examples.SearchTrees.enumerationMeaning_lookup` uses `Search.OrderedMap.SourceModel.enumAbs_default` under BST, retaining the supplied default. |
| `SearchTree.insert_relate@1082` | `Examples.SearchTrees.enumerationMeaning_insert` uses `Search.OrderedMap.SourceModel.enumAbs_bind`: the enumeration-insertion theorem and list-decoder insertion law establish the first model route. |
| `SearchTree.elements_relate@1132` | `Examples.SearchTrees.mapOfList_elements` retains the source BST argument and is definitional. `Search.OrderedMap.SourceModel.enumAbs_elements` exposes the stronger unconditional equality separately. |
| `SearchTree.union@1154` | `Examples.SearchTrees.collisionUnion := Search.OrderedMap.SourceModel.collisionUnion`: exactly one present operand survives; two present operands cancel even if their payloads are equal. |
| `SearchTree.union_left@1167` | `Examples.SearchTrees.collisionUnion_left` uses `Search.OrderedMap.SourceModel.collisionUnion_left` when the right operand is absent at this query. |
| `SearchTree.union_right@1172` | `Examples.SearchTrees.collisionUnion_right` uses `Search.OrderedMap.SourceModel.collisionUnion_right` when the left operand is absent at this query. |
| `SearchTree.union_both@1178` | `Examples.SearchTrees.collisionUnion_both` uses `Search.OrderedMap.SourceModel.collisionUnion_both`: two present values yield none. |
| `SearchTree.union_update_right@1187` | `Examples.SearchTrees.collisionUnion_update_right` uses `Search.OrderedMap.SourceModel.collisionUnion_write_right`, requiring the left operand absent only at the written key; a whole-function equality. |
| `SearchTree.union_update_left@1193` | `Examples.SearchTrees.collisionUnion_update_left` uses `Search.OrderedMap.SourceModel.collisionUnion_write_left`, requiring the right operand absent only at the written key; a whole-function equality. |
| `SearchTree.map_of_tree@1204` | `Examples.SearchTrees.mapOfTree := Search.OrderedMap.SourceModel.mapOfTree`; `Examples.SearchTrees.mapOfTree_node` exposes root update over the collision union of independently decoded children. |
| `SearchTree.map_of_tree_prop@1211` | `Examples.SearchTrees.mapOfTree_prop` consumes `Search.OrderedMap.SourceModel.mapOfTree_prop`: an all-node predicate holds of every successfully decoded binding, with no BST premise. |
| `SearchTree.Abs'@1222` | `Examples.SearchTrees.structuralMeaning` aliases the direct structural `Examples.SearchTrees.mapOfTree`, not the enumerating abstraction. |
| `SearchTree.empty_relate'@1225` | `Examples.SearchTrees.structuralMeaning_empty`: the direct abstraction of E is the optional empty map. |
| `SearchTree.bound_relate'@1232` | `Examples.SearchTrees.structuralMeaning_bound` uses `Search.OrderedMap.SourceModel.mapOfTree_bound` under BST, through the independently proved structural lookup correspondence. |
| `SearchTree.lookup_relate'@1240` | `Examples.SearchTrees.structuralMeaning_lookup` uses `Search.OrderedMap.SourceModel.mapOfTree_default` under BST, retaining the supplied default. |
| `SearchTree.insert_relate'@1247` | `Examples.SearchTrees.structuralMeaning_insert` uses `Search.OrderedMap.SourceModel.mapOfTree_bind`, proved independently by structural induction, union-update laws and separator-derived absence. |
| `SearchTree.map_of_list_app@1258` | `Examples.SearchTrees.mapOfList_append` uses `Search.OrderedMap.SourceModel.listObserve_append_of_disjoint`. Only cross-list projected-key disjointness is required; either list may contain internal duplicate keys. |
| `SearchTree.elements_relate'@1266` | `Examples.SearchTrees.mapOfList_elements_eq_structuralMeaning` uses `Search.OrderedMap.SourceModel.enumAbs_eq_mapOfTree` under BST. This final coherence theorem follows the direct structural route rather than defining it. |

### All 35 exercise prompts

The original star counts and optional/advanced labels are retained solely as
source metadata. Every listed mathematical prompt is covered, including helper
lemmas and all parts of the open-ended exercises.

| Source exercise and lines | Stars; labels | Complete implementation |
|---|---|---|
| `empty_tree_BST`, 202–211 | 1; standard | `Examples.SearchTrees.bst_emptyTree`. |
| `insert_BST`, 213–234 | 3; standard | Both `Examples.SearchTrees.forallT_insert` and `Examples.SearchTrees.bst_insert`. |
| `bound_correct`, 346–357 | 3; standard, optional | All three raw laws: `Examples.SearchTrees.bound_empty`, `Examples.SearchTrees.bound_insert_eq`, `Examples.SearchTrees.bound_insert_neq`; the grading stub adds no theorem. |
| `bound_default`, 359–371 | 1; standard, optional | `Examples.SearchTrees.bound_default`, with the failed converse checked separately. |
| `lookup_insert_shadow`, 430–439 | 2; standard, optional | `Examples.SearchTrees.lookup_insert_shadow` via the public raw lookup law. |
| `lookup_insert_same`, 441–449 | 2; standard, optional | `Examples.SearchTrees.lookup_insert_same` at the same supplied default. |
| `lookup_insert_permute`, 451–461 | 2; standard, optional | `Examples.SearchTrees.lookup_insert_permute` with distinct written keys. |
| `direct_equalities_break`, 486–505 | 2; standard, optional | Both `Examples.SearchTrees.insert_same_equality_breaks` and `Examples.SearchTrees.insert_permute_equality_breaks`. |
| `elements_complete`, 583–591 | 3; standard | `Examples.SearchTrees.elements_complete` with presence and value; no BST. |
| `elements_preserves_forall`, 614–637 | 2; standard | `Examples.SearchTrees.elements_preserves_forall`, with the exact pair-predicate adapter for source `uncurry`. |
| `elements_preserves_relation`, 639–660 | 2; standard | `Examples.SearchTrees.elements_preserves_relation` for any relation. |
| `elements_correct`, 662–671 | 4; standard | `Examples.SearchTrees.elements_correct` with BST and pair membership. |
| `elements_complete_inverse`, 683–696 | 2; advanced | `Examples.SearchTrees.elements_complete_inverse` retaining BST. |
| `elements_correct_inverse`, 698–717 | 4; advanced | Both `Examples.SearchTrees.bound_value` with `∃ value, ∀ default` and `Examples.SearchTrees.elements_correct_inverse`, without BST. |
| `sorted_app`, 725–738 | 3; advanced | `Examples.SearchTrees.sorted_app` with both sorted-list and separator premises. |
| `sorted_elements`, 740–755 | 4; advanced | `Examples.SearchTrees.listKeys` and `Examples.SearchTrees.sorted_elements` through the accepted sorting API. |
| `NoDup_append`, 775–786 | 3; advanced, optional | `Examples.SearchTrees.nodup_append` with two nodup premises and cross-list disjointness. |
| `elements_nodup_keys`, 788–800 | 4; advanced, optional | `Examples.SearchTrees.elements_nodup_keys` on projected keys. |
| `fast_elements_eq_elements`, 824–840 | 3; standard | Both `Examples.SearchTrees.fastElementsAcc_eq_append` for arbitrary suffix and `Examples.SearchTrees.fastElements_eq_elements`. |
| `kvs_insert_split`, 901–915 | 3; standard, optional | `Examples.SearchTrees.kvsInsert_split`, all three branches and both separator premises. |
| `kvs_insert_elements`, 917–924 | 3; standard, optional | `Examples.SearchTrees.kvsInsert_elements` for actual tree insertion under BST. |
| `in_fst`, 1035–1040 | 2; standard, optional | `Examples.SearchTrees.in_fst` for arbitrary pair types. |
| `in_map_of_list`, 1042–1048 | 2; standard, optional | `Examples.SearchTrees.mapOfList_eq_some_of_mem` with projected-key nodup. |
| `not_in_map_of_list`, 1050–1055 | 2; standard, optional | `Examples.SearchTrees.mapOfList_eq_none_of_not_mem` without nodup. |
| `bound_relate`, 1063–1071 | 3; standard, optional | `Examples.SearchTrees.enumerationMeaning_bound` through the first abstraction. |
| `lookup_relate`, 1073–1079 | 3; standard, optional | `Examples.SearchTrees.enumerationMeaning_lookup` with the explicit default. |
| `insert_relate`, 1081–1092 | 3; standard, optional | `Examples.SearchTrees.enumerationMeaning_insert` through enumeration/list insertion. |
| `union_collapse`, 1166–1184 | 2; standard, optional | All three laws: `Examples.SearchTrees.collisionUnion_left`, `Examples.SearchTrees.collisionUnion_right`, `Examples.SearchTrees.collisionUnion_both`. |
| `union_update`, 1186–1198 | 3; standard, optional | Both `Examples.SearchTrees.collisionUnion_update_right` and `Examples.SearchTrees.collisionUnion_update_left` with only the written-key absence premise. |
| `map_of_tree_prop`, 1210–1217 | 3; advanced, optional | `Examples.SearchTrees.mapOfTree_prop` from an all-node predicate, without BST. |
| `bound_relate'`, 1231–1237 | 3; advanced, optional | `Examples.SearchTrees.structuralMeaning_bound` through independent structural lookup. |
| `lookup_relate'`, 1239–1244 | 3; advanced, optional | `Examples.SearchTrees.structuralMeaning_lookup` through independent structural lookup. |
| `insert_relate'`, 1246–1251 | 4; advanced, optional | `Examples.SearchTrees.structuralMeaning_insert` through independent structural insertion. |
| `map_of_list_app`, 1257–1263 | 3; advanced, optional | `Examples.SearchTrees.mapOfList_append` with cross-list projected-key disjointness only. |
| `elements_relate'`, 1265–1271 | 4; advanced, optional | `Examples.SearchTrees.mapOfList_elements_eq_structuralMeaning` proves the final BST-dependent decoder coherence. |

### Two independent models and canonical enumeration

`Search.OrderedMap.SourceModel.enumAbs` first enumerates the tree and then
uses the existing head-wins list decoder. A cons updates the decoded tail, so
a duplicate later binding may occur in the list yet fail to be its observed
value. `Search.OrderedMap.SourceModel.listObserve_eq_some_of_mem` therefore
retains projected-key nodup; the absence theorem needs only key nonmembership.
The first insertion correspondence
`Search.OrderedMap.SourceModel.enumAbs_bind` visibly uses
`Search.OrderedMap.entries_bind` and
`Search.OrderedMap.SourceModel.listObserve_kvsInsert`. The latter law works
on arbitrary raw lists, while the tree-to-list insertion theorem needs BST.
The separator lemma retains its two quantified strict bounds without adding
sortedness or uniqueness of the two list segments.

`Search.OrderedMap.SourceModel.collisionUnion` treats the four optional-value
cases exactly as the source does. When both operands have a binding, the result
is none, including equal-valued bindings. Its write laws need absence only at
the written key in the opposite operand. By contrast,
`Search.OrderedMap.SourceModel.listObserve_append_of_disjoint` requires
cross-list disjointness of projected keys, while allowing duplicates within
either operand. The collision operation is commutative but is not assumed to
be an unrestricted associative union; the concrete
`Examples.SearchTrees.collisionUnion_not_associative` witness distinguishes the two
parenthesizations.

`Search.OrderedMap.SourceModel.mapOfTree` is a separate structural recursion:
decode both children, remove their collisions, then write the root binding.
`Search.OrderedMap.SourceModel.mapOfTree_eq_lookup` is proved by structural
induction, using all-node separators to show that the discarded child cannot
contain the queried key. `Search.OrderedMap.SourceModel.mapOfTree_bind` is
also independently proved by structural induction and the union/write laws.
Neither insertion proof takes final model coherence as a premise or uses the
enumerating abstraction as its decoder. Only afterwards does
`Search.OrderedMap.SourceModel.enumAbs_eq_mapOfTree` connect the two models
under BST, using the list-append law and disjoint subtree keys. This preserves
the chapter's alternative model-based proof route.

`Search.OrderedMap.SourceModel.enumAbs_finite_support` and
`Search.OrderedMap.SourceModel.mapOfTree_finite_support` give a finite
containing list of keys for every decoded tree, including malformed trees.
`Examples.SearchTrees.enumerated_finite_support` and
`Examples.SearchTrees.structural_finite_support` expose the source
specializations. The unrestricted function carrier `Nat → Option V` also
contains maps bound at infinitely many keys; it is not made finite by these
representation theorems.

`Search.OrderedMap.SourceModel.entries_eq_of_enumAbs_eq` proves canonical
enumeration from two BST witnesses and equality of their partial-map
abstractions. Its generic key assumptions are a preorder and decidable equality;
the proof uses strict pairwise order, key nodup and actual pair membership, with
`List.Pairwise.eq_of_mem_iff`. The direct-lookup and structural-model variants
`Search.OrderedMap.SourceModel.entries_eq_of_lookup_eq` and
`Search.OrderedMap.SourceModel.entries_eq_of_mapOfTree_eq` use linear-order
keys. `Examples.SearchTrees.canonical_enumeration` retains the exact source
Nat specialization. A non-strict key relation would not justify antisymmetry
on arbitrary payload pairs.

### Executing search and insertion costs

`Resources.SearchTree.lookupWithRun` and
`Resources.SearchTree.insertWithRun` execute the actual branch recurrence
with a supplied callback returning a Bool and a Nat charge. Their work pair is
**(nonempty nodes visited, sum of comparator charges)**. At each node they run
query/root first and run root/query only if the first comparison is false.
Only the selected subtree executes recursively. Insertion returns the actual
reconstructed tree; `Resources.SearchTree.insertWithRun_work` proves that
its work pair equals lookup's pair along that old-tree path. Reconstructing a
value is not a physical allocation or pointer-sharing theorem.

`Resources.SearchTree.lookupWithRun_value` and
`Resources.SearchTree.insertWithRun_value` erase to the existing raw search
and insertion operations when the two callback directions return the correct
strict-comparison Booleans at labels in this input tree. This is an input-local
`Search.OrderedTree.All` premise; it does not require comparator calibration
on every possible key pair or a BST invariant. Cost bounds use a separate
input-local premise bounding both relevant charges by K. They do not assume
correct Boolean answers merely to count the executed path, and they allow K=0.

Writing h for `t.height`, v for nonempty visits and w for comparator work, the
checked bounds are v ≤ h and w ≤ 2Kv ≤ 2Kh. The exact unit callback in
`Resources.SearchTree.lookupRun`/`Resources.SearchTree.insertRun` costs one
per call, so a left step costs one comparison and a right/equality step costs
two. `Resources.SearchTree.lookupWithRun_constant` connects an actually
executed constant-K callback to K times that unit call count.
`Resources.SearchTree.lookupWithRun_weighted_bound` separately gives
`visitPrice * v + w ≤ (visitPrice + 2*K) * h`. These counts exclude physical
allocation and, in v, the terminal empty constructor. The separately exposed
`Resources.SearchTree.lookupInspections` adds that final inspection exactly
when lookup returns none, and is bounded by h+1.

`Resources.SearchTree.lookupWithRun_log_bound` and
`Resources.SearchTree.insertWithRun_log_bound` require the explicit height
contract `h ≤ H * Nat.clog 2 (n+1)` as well as the input-local comparator
bound, where n is the old tree's node count. They conclude
`w ≤ 2*K*H*Nat.clog 2 (n+1)`, including the empty case. The family theorems
`Resources.SearchTree.lookupWithRun_isBigO` and
`Resources.SearchTree.insertWithRun_isBigO` use exact size n, the stated
height contract and the per-input comparator bound at every index to prove
ordinary real `Asymptotics.IsBigO` at infinity against
`Real.logb 2 (n+1)`. Their conversion uses n≥1 and explicit constant
`2*(2*K*H)`; these conclusions are not merely informal notation for a
recurrence. SearchTree supplies no balancing algorithm. Logarithmic height
does not follow from BST alone.

`Resources.SearchTree.rightSpine` reuses the existing increasing Nat-key
spine and permits arbitrary payloads. Its order, size and height are proved.
`Resources.SearchTree.lookupRun_rightSpine` and
`Resources.SearchTree.insertRun_rightSpine` give exactly n visits and 2n
comparisons for a key above all n stored keys. The lookup misses and has n+1
constructor inspections. `Resources.SearchTree.rightSpine_linear_path`
packages this valid worst-case family. This witnesses linear paths without
claiming that every query in every skew tree is slow. The chapter's comparison
with linked lists and accumulated function updates remains dependent on their
chosen representations and workloads; an unrestricted function map has no
intrinsic update-history length or probability distribution.

### Exact source append work and accumulator work

The source recurrence is explicitly right-associated:
`elements left ++ ([(k,value)] ++ elements right)`.
`Examples.SearchTrees.elements_node` and the shared inorder definition give
the exact value bridge to `elements left ++ (k,value) :: elements right`.
Value equality alone does not transfer a primitive-operation count.
`Resources.TreeEnumeration.copyStep` actually executes both
`Resources.ListAppend.copies` calls: append the singleton to the returned
right list, then append the returned left list to that actual result.
`Resources.TreeEnumeration.copyRun` uses the existing
`Resources.TreeFold.run` with zero empty-tree cost to execute that step on
the actual subtree outputs.

One copy is charged per cell in each append's first operand. Singleton
construction, tree inspection and compiler allocation are outside this copy
measure. `Resources.TreeEnumeration.copyRun_value` and
`Resources.TreeEnumeration.copyRun_entries` prove value erasure. If C(t)
denotes its measured copy count and n denotes node count, the public
`Resources.TreeEnumeration.copyRun_node_copies` and
`Resources.TreeEnumeration.copyRun_copies` establish

- C(E)=0 and C(node(l,a,r))=C(l)+C(r)+l.numNodes+1.
- C(t)=`Trees.leftSizeSum t`+n.
- n≤C(t), C(t)≤n², and the sharper 2C(t)≤n(n+1).

The exact contrasting families are
`Resources.TreeEnumeration.leftChain_copies`, with n(n+1)/2 copies, and
`Resources.TreeEnumeration.rightChain_copies`, with n copies.
`Resources.TreeEnumeration.complete_numNodes` and
`Resources.TreeEnumeration.complete_copies` apply to **every**
`Trees.Complete` tree of height h: n=2^h−1 and C=h·2^(h−1).
The exponent uses Nat predecessor; h=0 yields n=C=0 and is checked explicitly.
The stronger equation 2C=h·2^h is
`Resources.TreeEnumeration.complete_twice_copies`. These shape theorems
make no assertion that arbitrarily repeated labels form a BST.

`Resources.TreeEnumeration.copies_le_height_mul_size` proves C≤h·n.
`Resources.TreeEnumeration.almostComplete_copies` derives
C≤n·`Nat.clog 2 (n+1)` from the existing almost-complete height theorem.
`Resources.TreeEnumeration.copyRun_isBigO` gives the real-cast discrete
n·clog₂(n+1) bound for exact-size families with an explicit height contract.
`Resources.TreeEnumeration.copyRun_log_isBigO` separately gives ordinary
real O(n log₂ n): for all n beyond a specified N, the family has node count
at most n and height at most H·`Nat.clog 2 n`. Its size parameter can
therefore be an upper bound such as an external-leaf count. The conversion
uses the standard real-logarithm growth API, with small n removed by the
eventual threshold. `Resources.TreeEnumeration.copyRun_quadratic_isBigO`
gives the unconditional quadratic family upper bound for exact node count n.

`Search.OrderedMap.fastEntriesAcc` reuses the common function-valued
`Trees.fold` traversal. At a node the actual right traversal produces the
suffix passed under the new pair to the left traversal.
`Search.OrderedMap.fastEntriesAcc_eq` proves for **arbitrary** suffix xs
that the returned list is `entries t ++ xs`; the empty-suffix equality follows
afterwards. `Examples.SearchTrees.fastElements_correct` and
`Examples.SearchTrees.fastElements_sorted` transport membership correctness
and ordering through this public value equality.

`Resources.TreeEnumeration.accumulatorRun` instruments that same recurrence
using the existing `Resources.TreeAccumulator.nodeRun`. Its work pair counts
**(constructor visits including empty children, result-list cons operations)**.
`Resources.TreeEnumeration.accumulatorRun_value` and
`Resources.TreeEnumeration.accumulatorRun_fastEntriesAcc` prove the returned
value for every suffix. `Resources.TreeEnumeration.accumulatorRun_work`
proves exactly (2n+1,n), independent of suffix length; the returned length is
n+xs.length by `Resources.TreeEnumeration.accumulatorRun_length`.
`Resources.TreeEnumeration.accumulatorRun_visits_isBigO` supplies ordinary
linear growth for exact-size families. The suffix is unchanged in the list
value model. The source's “tail-recursive” description does not prove constant
stack space: the nested right traversal must finish before the left call can
use its result. No physical sharing, heap, peak-space, garbage-collection or
stack theorem is inferred from these equations.

### Qualified unary comparison model

`Resources.UnaryComparison.unaryLERun` executes an explicit lockstep unary
≤ comparator and charges one pattern-call step, including the terminal call.
`Resources.UnaryComparison.unaryLERun_spec` proves both the Boolean answer
and the exact charge `min n m + 1`. Equal inputs n,n cost n+1 despite having
absolute difference zero. The general
`Resources.UnaryComparison.no_difference_only_bound` and
`Resources.UnaryComparison.equal_inputs_beyond_threshold` make the source's
difference-only complexity claim false in this model, rather than adopting it
as an axiom or a cost assumption.

For strict comparison, `Resources.UnaryComparison.unaryLTRun n m` executes
the ≤ model on n+1,m. Its erased answer is `decide (n < m)` and its exact
pattern-call charge is `min (n+1) m + 1`. Successor construction is explicitly
uncharged. `Resources.UnaryComparison.strict_no_difference_only_bound`
retains the equal-input obstruction for this adapter. These are declared
models with proved values; they are not identified with Rocq's `Nat.ltb`,
extracted arithmetic, or native Lean Nat execution. The source's runtime and
extraction realization questions remain for Extract.

`Resources.UnaryComparison.unaryLESquare` and
`Resources.UnaryComparison.unaryLTSquare` use the existing
`Resources.erasureSquare`. The composed
`Resources.UnaryComparison.compareBothWays` executes both directions
unconditionally and sums their actual charges; the search interpreter instead
retains its short-circuit branch condition. In
`Examples.SearchTreeWork.unary_right_search`, the actual four strict
comparison callbacks on the concrete three-node tree total 11 steps.
`Examples.SearchTreeWork.unary_local_bound` supplies K=3 only for the
relevant key/input labels, `Examples.SearchTreeWork.unary_calibrated_erasure`
proves their correct values, and
`Examples.SearchTreeWork.unary_weighted_height_bound` gives 11≤12.
No impossible global constant bound on all unary comparisons is assumed.

### Connected examples, commands and remaining prose

`Examples.SearchTrees.malformed_update_still_observed` applies the raw
same-key update theorem to the source's misplaced tree.
`Examples.SearchTrees.explicit_default_and_absence` and
`Examples.SearchTrees.bound_default_converse_fails` distinguish a stored
false from absence despite equal default-false lookups.
`Examples.SearchTrees.duplicate_member_is_shadowed` checks a later
duplicate-key list member whose value is not observed.
`Examples.SearchTrees.raw_abstractions_disagree` gives the concrete
key-0 collision in both children of a key-1 root: inorder decoding preserves
the left binding while structural decoding cancels both. Its failed BST
witness is explicit in `Examples.SearchTrees.not_bst_collisionTree`.
`Examples.SearchTrees.collisionUnion_cases` includes equal-valued collision
removal; `Examples.SearchTrees.collisionUnion_update_without_absence_fails` checks
the missing-premise counterexample.

`Examples.SearchTrees.key_zero_replacement` consumes structural shadowing.
`Examples.SearchTrees.raw_partial_writes_commute` uses the public raw path
decoder and accepted function-update algebra.
`Examples.SearchTrees.distinct_shapes_same_canonical_list` has different
raw insertion shapes but equal canonical lists, through valid insertion and
partial-map equality. `Examples.SearchTrees.disjoint_append_with_internal_duplicates`
checks the intentionally weak hypotheses of the list-append law.
`Examples.SearchTrees.function_payload`,
`Examples.SearchTrees.empty_payload` and
`Examples.SearchTrees.high_universe_payload` check the payload assumption
and independent-universe boundaries.

The resource examples exercise empty/singleton cases, the three distinct
left/right/equality paths, missing lookup, actual replacement output and a
nonempty accumulator suffix. In the concrete three-node tree,
`Examples.SearchTreeWork.left_search`,
`Examples.SearchTreeWork.right_search` and
`Examples.SearchTreeWork.root_search` have work pairs (2,3), (2,4) and (1,2).
`Examples.SearchTreeWork.missing_search` additionally has three constructor
inspections. `Examples.SearchTreeWork.two_source_appends` has four copies;
`Examples.SearchTreeWork.nonempty_accumulator` has work (7,3).
The chain and all-height perfect-tree clients use the public family theorems;
`Examples.SearchTreeWork.all_perfect_heights` does not assume its repeated
labels are ordered keys. `Examples.SearchTreeWork.ordered_linear_family`
supplies a separate valid search-tree family.
`Examples.SearchTreeWork.weighted_right_search` executes four constant-7
callbacks for total work 28. The unary clients check zero, equality, both
unequal directions, large equal inputs, square erasure and composed charges.

All six source-wrapper erasure bridges in `Examples.SearchTreeWork` are
explicit: `Examples.SearchTreeWork.source_lookup_erasure` retains any
default, `Examples.SearchTreeWork.source_bound_erasure` the presence bit,
`Examples.SearchTreeWork.source_insert_erasure` the actual new tree,
`Examples.SearchTreeWork.source_elements_erasure` the source enumeration,
`Examples.SearchTreeWork.source_accumulator_erasure` any suffix, and
`Examples.SearchTreeWork.source_fast_elements_erasure` the empty suffix.
They hold on arbitrary raw source trees and retain arbitrary payload universes.
`Examples.SearchTreeWork.source_ex_tree_runs`,
`Examples.SearchTreeWork.source_nonempty_suffix` and
`Examples.SearchTreeWork.source_default_lookup_client` connect the exact
source examples to these public erasure results and independently specified
values/counts.

| Source inspection commands | Lean disposition |
|---|---|
| Check at 383/386, 392/395 and 402/406 | Inspect the paired tree and accepted Maps empty, same-key and different-key lookup statements. Their checked specializations preserve written/query direction and the explicit default. |
| Check at 413, 416 and 419 | Inspect accepted Maps shadow, self-update and distinct-key commutation, then the raw-tree observational consequences. Function equality and raw-tree shape equality remain separate. |
| Check at 612 | The source `Forall_app` interface is supplied by `List.forall_append`; `List.forall_iff_forall_mem` relates that predicate to the membership-quantified preservation theorem. |
| Print at 766 | Use the existing `List.Nodup` predicate and inspected `List.Nodup.append` interface. No duplicate no-repetition definition or theorem is introduced. |

Rocq sections, modules, notation, hints and comparison tactics are adapted to
Lean namespaces, explicit parameters, propositions/decidable comparisons and
ordinary proof automation. The source's admitted exercises are actual proved
Lean statements here; the false aborted statement is refuted. The algebraic
and model-based presentations demonstrate different proof routes, without a
new axiom or theorem measuring proof effort. The lookup diagram is read with
`find` returning V after default selection, not an unjustified extra optional
wrapper. Optimized correctness is transferred by the public enumeration
equality, not by repeating every proof for an unrelated algorithm.

Persistent source equations preserve the old value as a mathematical input;
they certify no native pointer behavior or compiler/runtime cost. Formal work
models are possible and are explicit above. The source's absence of an
internal runtime model is not an impossibility claim. Extraction, realized
primitive costs and compiler execution remain separate later obligations.

This section records source correspondence and the assessed statement
boundaries. Exact-candidate entrypoint integration, proof-audit regression,
focused validation, both independent review axes, immediate candidate
verification, receiving whole-library gates and checkpoint acceptance remain
owned by their separate records. This document alone does not mark CTB/BOOKS
accepted or authorize the next chapter.

## ADT: interfaces, represented values and source queue behavior

This correspondence covers the complete VFA 2.1 `ADT.v` chapter, including
its optional and advanced prompts, repeated module implementations,
deliberately failing commands, and the limits of its efficiency discussion.
The primary source is the `vfa/ADT.v` member of the
[authenticated VFA 2.1 archive](https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz).
The archive SHA-256 is
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`;
the 45,447-byte, 1,492-line member SHA-256 is
`87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2`.
The complete primary body stays outside this repository payload. Existing VFA
attribution and license handling continue to apply to the derived implementations.

The canonical inventory contains 254 declaration records: 78 interface
requirements, 78 definitions, 44 source-proved statements, 43 source
admissions, five expected declaration failures, two grading records, three
transparent proved definitions and one proof-term definition. There are also
12 complete exercise prompts, 39 module or module-type records, and 11
inspection/failure commands. Four exercises are optional and three are
advanced, with two in both categories. The false unrestricted raw-tree
soundness admission is refuted and the intended BST-qualified contract is
proved; expected elaboration failures are demonstrated as failures. Neither
category is converted into an axiom.

The implementation retains the existing table, partial-map, tree, list,
FIFO, measured-execution and growth owners. The source-facing clients use Nat
keys and the requested concrete defaults. Reusable table owners keep key,
payload and state universes independent; source queue operation/law records
keep payload and state universes independent. Pair-list updates require only
decidable key equality; ordered-tree instances retain their linear-order
premise. Payloads need no equality, ordering or global default instance.
Type-valued clients check that these are actual universe-generic interfaces.

| Current owner | Role |
|---|---|
| `Applications/Search/OrderedMap/EnumeratedTable.lean` | Separate unconditional table laws, validity-qualified enumeration laws, strengthened observations, and the exact seven-law model contract; raw list/tree and intrinsic-validity instances. |
| `Applications/Search/OrderedMap/AssociationListEnumeration.lean` | Exact unique-key pair-list subtype, first-key replacement, and proof bridges to existing `AList` operations through the pair/Sigma equivalence. |
| `Applications/Sequences/SourceQueue.lean` | Exact default-valued queue signatures, actual list and all-raw two-list operations, six versus four laws, counterexamples, and existing FIFO simulation/clients. |
| `Applications/Resources/SourceQueue.lean` | Actual source-structural and separately named linear reversal realizations, enqueue/dequeue potential accounting, and reachable repeated-peek counterexamples. |
| `Applications/Resources/ListErase.lean` | Actual first-match erasure and unique-list update with explicit predicate-call counts. |
| `Examples/AbstractDataTypes.lean` | Complete source specializations, examples, module-language adaptations, constructive subtype/vector definitions, and connected table/queue clients. |
| `Examples/AbstractDataTypeWork.lean` | Actual measured source bridges, boundary cases, arbitrary histories, and unbounded reachable queue/list-update families. |

### The contracts are distinct

| Source contract | Checked Lean contract and exact boundary |
|---|---|
| Table | `Examples.AbstractDataTypes.Table` uses `Search.TotalTable.Ops`. `Examples.AbstractDataTypes.TableLaws` instantiates the existing law family with validity `True`: empty/default, same-key, and distinct-key observations hold on every represented state. |
| First ETable attempt | `Search.OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws` adds both unrestricted membership directions to the unconditional table laws. The contract has valid-carrier instances, but `Examples.AbstractDataTypes.raw_tree_unrestricted_enumeration_fails` refutes the supplied raw-tree attempt. |
| ETable | `Search.OrderedMap.EnumeratedTable.Laws` keeps all Table laws and the three presence laws unrestricted. Its two membership directions alone require the separate validity predicate; valid empty and update preservation are additional fields. |
| Strengthened elements exercise | `Search.OrderedMap.EnumeratedTable.StrongElements` distinguishes validity-qualified absence-implies-no-entry from raw no-entry-implies-absence, and separately proves strict projected-key order and projected-key nodup. The source Nat client also supplies the requested non-strict ordering. |
| ETableAbs | `Search.OrderedMap.EnumeratedTable.ModelLaws` has exactly seven fields: valid empty, update preservation, empty decoding, and validity-qualified presence, get, update and enumeration refinements. It neither inherits raw membership soundness nor asserts finite support for every ambient optional function. |
| ETableSubset | `Search.OrderedMap.EnumeratedTable.SubsetLaws` is the same enumeration contract with validity `True` on an intrinsically valid carrier. The tree and unique-list carriers expose the source laws without an external representation premise. |
| Queue | `Sequences.SourceQueue.Ops` supplies empty, Boolean emptiness, queue-first enqueue, dequeue, and default-first peek. `Sequences.SourceQueue.Laws` has all six source algebraic equations, including literal state equality for dequeue/enqueue. |
| QueueAbs | `Sequences.SourceQueue.AbsLaws` has exactly the four unguarded empty, enqueue, default-peek and dequeue decoder equations. It imposes no validity predicate and no law for its supplied empty test. |

A total default observation can forget whether a binding exists.
`Examples.AbstractDataTypes.table_default_forgets_presence` gives actual
trees with equal default-valued observations and different presence bits.
The optional decoder is therefore retained wherever the source uses bound
or an abstraction function. The source update orientation is also explicit:
the model law states abstract write of the old decoder equals the decoder
after concrete set; its enumeration law states the decoder equals the
head-wins observation of the returned entries.

### All 254 source declaration records

The IDs below are the unchanged canonical inventory IDs. The constrained
implementation header at line 675 was lexically misclassified as an alias:
`ADT.TreeETableEncapsulated` is an actual module implementation.
Consequently the ten canonical IDs `ADT.rep_ok@679` through
`ADT.elements_correct@729` retain their original spelling here, while their
obligations and actual owner are assigned to that module. Repeated source
implementations reuse the same checked Lean provider and the separately
demonstrated abstract-client typing boundary.

| Canonical source record | Qualified checked implementation and disposition |
|---|---|
| `ADT.Table.table@54` | `Examples.AbstractDataTypes.Table`. Abstract state parameter T, independent of payload universe. |
| `ADT.Table.key@57` | `Examples.AbstractDataTypes.Table`. The source specialization fixes keys to Nat. |
| `ADT.Table.V@60` | `Examples.AbstractDataTypes.Table`. Arbitrary payload parameter V; no payload order, equality or inhabitance. |
| `ADT.Table.default@63` | `Examples.AbstractDataTypes.TableLaws`. Explicit supplied default parameter d, separate from operation data; no global default typeclass. |
| `ADT.Table.empty@66` | `Search.TotalTable.Ops.empty`. Existing operation field, specialized by `Examples.AbstractDataTypes.Table` to Nat keys; source argument order retained. |
| `ADT.Table.get@69` | `Search.TotalTable.Ops.get`. Existing operation field, specialized by `Examples.AbstractDataTypes.Table` to Nat keys; source argument order retained. |
| `ADT.Table.set@73` | `Search.TotalTable.Ops.set`. Existing operation field, specialized by `Examples.AbstractDataTypes.Table` to Nat keys; source argument order retained. |
| `ADT.Table.get_empty_default@78` | `Search.TotalTable.Laws.get_empty`; `Examples.AbstractDataTypes.TableLaws`. Unconditional source law through validity=True; any internal trivial validity argument imposes no state restriction. |
| `ADT.Table.get_set_same@81` | `Search.TotalTable.Laws.get_set_same`; `Examples.AbstractDataTypes.TableLaws`. Unconditional source law through validity=True; any internal trivial validity argument imposes no state restriction. |
| `ADT.Table.get_set_other@84` | `Search.TotalTable.Laws.get_set_other`; `Examples.AbstractDataTypes.TableLaws`. Unconditional source law through validity=True; any internal trivial validity argument imposes no state restriction. |
| `ADT.ValType.V@101` | `Examples.AbstractDataTypes.functionTable`. Ordinary payload/default parameters represent this type requirement; no redundant module or typeclass. |
| `ADT.ValType.default@102` | `Examples.AbstractDataTypes.functionTable`. Ordinary payload/default parameters represent this chosen value requirement; no redundant module or typeclass. |
| `ADT.FunTable.V@113` | `Examples.AbstractDataTypes.functionTable`. The supplied arbitrary payload type is retained. |
| `ADT.FunTable.default@114` | `Examples.AbstractDataTypes.functionTable`. The supplied default is explicit. |
| `ADT.FunTable.key@115` | `Examples.AbstractDataTypes.functionTable`. Keys remain Nat. |
| `ADT.FunTable.table@118` | `Examples.AbstractDataTypes.functionTable`. Actual function carrier Nat → V. |
| `ADT.FunTable.empty@120` | `Examples.AbstractDataTypes.functionTable`; `Search.TotalTable.Ops.empty`. Constant supplied-default function. |
| `ADT.FunTable.get@123` | `Examples.AbstractDataTypes.functionTable`; `Search.TotalTable.Ops.get`. Application to the queried Nat key. |
| `ADT.FunTable.set@126` | `Examples.AbstractDataTypes.functionTable_set_source`. Exact written-key-first Nat Boolean update branch, connected to Function.update. |
| `ADT.FunTable.get_empty_default@132` | `Examples.AbstractDataTypes.functionTable_laws`; `Search.TotalTable.Laws.get_empty`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.FunTable.get_set_same@136` | `Examples.AbstractDataTypes.functionTable_laws`; `Search.TotalTable.Laws.get_set_same`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.FunTable.get_set_other@140` | `Examples.AbstractDataTypes.functionTable_laws`; `Search.TotalTable.Laws.get_set_other`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.StringVal.V@149` | `Examples.AbstractDataTypes.StringPayload.Value`. Exactly String as in the source. |
| `ADT.StringVal.default@150` | `Examples.AbstractDataTypes.StringPayload.default`. Exactly the empty String as in the source. |
| `ADT.FunTableExamples.ex1@159` | `Examples.AbstractDataTypes.stringFunctionTable_empty`. get 0 empty = empty String. Proof consumes the public function-table law. |
| `ADT.FunTableExamples.ex2@162` | `Examples.AbstractDataTypes.stringFunctionTable_same_key`. get 0 after writing (0,"A") = "A". Proof consumes the public function-table law. |
| `ADT.FunTableExamples.ex3@165` | `Examples.AbstractDataTypes.stringFunctionTable_other_key`. get 1 after writing (0,"A") = empty String. Proof consumes the public function-table law. |
| `ADT.ListsTable.V@191` | `Examples.AbstractDataTypes.listTable`. The supplied arbitrary payload type is retained. |
| `ADT.ListsTable.default@192` | `Examples.AbstractDataTypes.listTable`. The supplied default is explicit. |
| `ADT.ListsTable.key@193` | `Examples.AbstractDataTypes.listTable`. Keys remain Nat. |
| `ADT.ListsTable.table@194` | `Examples.AbstractDataTypes.listTable`. Actual raw List (Nat × V), allowing duplicates. |
| `ADT.ListsTable.empty@196` | `Examples.AbstractDataTypes.listTable`; `Search.TotalTable.Ops.empty`. The empty pair list. |
| `ADT.ListsTable.get@198` | `Examples.AbstractDataTypes.listTable`; `Search.TotalTable.Ops.get`. Existing first-match optional lookup followed by the supplied default. |
| `ADT.ListsTable.set@201` | `Examples.AbstractDataTypes.listTable_set_source`. Prepend the new pair; older duplicates remain shadowed. |
| `ADT.ListsTable.get_empty_default@204` | `Examples.AbstractDataTypes.listTable_laws`; `Search.TotalTable.Laws.get_empty`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.ListsTable.get_set_same@209` | `Examples.AbstractDataTypes.listTable_laws`; `Search.TotalTable.Laws.get_set_same`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.ListsTable.get_set_other@214` | `Examples.AbstractDataTypes.listTable_laws`; `Search.TotalTable.Laws.get_set_other`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.StringListsTableExamples.ex1@229` | `Examples.AbstractDataTypes.stringListTable_empty`. get 0 empty = empty String. Proof consumes the public list-table law. |
| `ADT.StringListsTableExamples.ex2@233` | `Examples.AbstractDataTypes.stringListTable_same_key`. get 0 after writing (0,"A") = "A". Proof consumes the public list-table law. |
| `ADT.StringListsTableExamples.ex3@237` | `Examples.AbstractDataTypes.stringListTable_other_key`. get 1 after writing (0,"A") = empty String. Proof consumes the public list-table law. |
| `ADT.TreeTable.V@253` | `Examples.AbstractDataTypes.treeTable`. The supplied arbitrary payload type is retained. |
| `ADT.TreeTable.default@254` | `Examples.AbstractDataTypes.treeTable`. The supplied default is explicit. |
| `ADT.TreeTable.key@255` | `Examples.AbstractDataTypes.treeTable`. Keys remain Nat. |
| `ADT.TreeTable.table@256` | `Examples.AbstractDataTypes.treeTable`. Existing raw source tree, without a BST subtype restriction. |
| `ADT.TreeTable.empty@258` | `Examples.AbstractDataTypes.treeTable`; `Search.TotalTable.Ops.empty`. The existing source empty tree. |
| `ADT.TreeTable.get@261` | `Examples.AbstractDataTypes.treeTable`; `Search.TotalTable.Ops.get`. Existing directed search with the supplied default. |
| `ADT.TreeTable.set@264` | `Examples.AbstractDataTypes.treeTable_set_source`. Exactly the existing source insertion on every raw tree. |
| `ADT.TreeTable.get_empty_default@271` | `Examples.AbstractDataTypes.treeTable_laws`; `Search.TotalTable.Laws.get_empty`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.TreeTable.get_set_same@277` | `Examples.AbstractDataTypes.treeTable_laws`; `Search.TotalTable.Laws.get_set_same`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.TreeTable.get_set_other@283` | `Examples.AbstractDataTypes.treeTable_laws`; `Search.TotalTable.Laws.get_set_other`. The complete source empty/same/other-key law on all represented states; no BST or unique-key premise. |
| `ADT.ETable_first_attempt.bound@308` | `Search.OrderedMap.EnumeratedTable.Observations.bound`. Existing total-table operation data is extended with this separate observation. |
| `ADT.ETable_first_attempt.elements@309` | `Search.OrderedMap.EnumeratedTable.Observations.elements`. Existing total-table operation data is extended with this separate observation. |
| `ADT.ETable_first_attempt.elements_complete@311` | `Search.OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws.elements_complete`. Unconditional membership requirement, with unrestricted base Table laws. The signature is realizable on valid carriers; its raw-tree soundness attempt fails. |
| `ADT.ETable_first_attempt.elements_correct@316` | `Search.OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws.elements_correct`. Unconditional membership requirement, with unrestricted base Table laws. The signature is realizable on valid carriers; its raw-tree soundness attempt fails. |
| `ADT.TreeETable_first_attempt.bound@336` | `Examples.AbstractDataTypes.RawTreeTable.bound`. Reuse the existing raw source operation. |
| `ADT.TreeETable_first_attempt.elements@339` | `Examples.AbstractDataTypes.RawTreeTable.elements`. Reuse the existing raw source operation. |
| `ADT.TreeETable_first_attempt.elements_complete@342` | `Examples.AbstractDataTypes.RawTreeTable.elements_complete_raw`. Presence and get=value imply actual entry membership on every raw tree. |
| `ADT.TreeETable_first_attempt.elements_correct@351` | `Examples.AbstractDataTypes.raw_tree_unrestricted_enumeration_fails`; `Examples.AbstractDataTypes.malformed_tree_member`. The deliberately false raw soundness admission is refuted using the exact malformed predecessor tree; the corrected theorem retains BST. |
| `ADT.ETable.rep_ok@379` | `Search.OrderedMap.EnumeratedTable.Laws`. Separate Valid parameter, used by closure and membership laws only. |
| `ADT.ETable.bound@380` | `Search.OrderedMap.EnumeratedTable.Observations.bound`. Public observation alongside the existing unconditional Table operations. |
| `ADT.ETable.elements@381` | `Search.OrderedMap.EnumeratedTable.Observations.elements`. Public observation alongside the existing unconditional Table operations. |
| `ADT.ETable.empty_ok@385` | `Search.OrderedMap.EnumeratedTable.Laws.empty_valid`. Actual valid-empty requirement. |
| `ADT.ETable.set_ok@387` | `Search.OrderedMap.EnumeratedTable.Laws.set_valid`. Preservation of the supplied validity predicate by actual set. |
| `ADT.ETable.bound_empty@392` | `Search.OrderedMap.EnumeratedTable.Laws.bound_empty`. Unconditional empty absence. |
| `ADT.ETable.bound_set_same@395` | `Search.OrderedMap.EnumeratedTable.Laws.bound_set_same`. Unconditional same-key presence after set. |
| `ADT.ETable.bound_set_other@398` | `Search.OrderedMap.EnumeratedTable.Laws.bound_set_other`. Unconditional distinct-key presence preservation. |
| `ADT.ETable.elements_complete@403` | `Search.OrderedMap.EnumeratedTable.Laws.elements_complete`. Validity, presence and returned value imply entry membership. |
| `ADT.ETable.elements_correct@409` | `Search.OrderedMap.EnumeratedTable.Laws.elements_correct`. Validity and entry membership imply both presence and the default-valued get result. |
| `ADT.TreeETable.rep_ok@420` | `Examples.AbstractDataTypes.RawTreeTable.Valid`. The actual BST predicate on raw source trees. |
| `ADT.TreeETable.bound@423` | `Examples.AbstractDataTypes.RawTreeTable.bound`. Existing directed presence observation on every raw tree. |
| `ADT.TreeETable.elements@426` | `Examples.AbstractDataTypes.RawTreeTable.elements`. Existing inorder entry list on every raw tree. |
| `ADT.TreeETable.empty_ok@429` | `Examples.AbstractDataTypes.RawTreeTable.empty_valid`. Valid empty through the source BST proof. |
| `ADT.TreeETable.set_ok@434` | `Examples.AbstractDataTypes.RawTreeTable.set_valid`. BST preserved by actual insertion. |
| `ADT.TreeETable.bound_empty@440` | `Examples.AbstractDataTypes.RawTreeTable.bound_empty`. Raw empty-tree absence; no BST argument. |
| `ADT.TreeETable.bound_set_same@446` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_same`. Raw same-key presence; no BST argument. |
| `ADT.TreeETable.bound_set_other@452` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_other`. Raw distinct-key preservation with written-key ≠ query; no BST argument. |
| `ADT.TreeETable.elements_complete@458` | `Examples.AbstractDataTypes.RawTreeTable.elements_complete`. Retains the source BST premise; the stronger raw completeness theorem remains separately available. |
| `ADT.TreeETable.elements_correct@470` | `Examples.AbstractDataTypes.RawTreeTable.elements_correct`. Retains BST and returns both presence and the get value. |
| `ADT.StringTreeETableExample.ex1@491` | `Examples.AbstractDataTypes.string_tree_elements_example`. The exact (0,"A") membership after writing (1,"B") then (0,"A"), proved through validity, get, bound and membership laws. |
| `ADT.exposed_trees_ex@508` | `Examples.AbstractDataTypes.treeTable_singleton_lookup`. Exact exposed raw-tree lookup at key 0 returns "A". |
| `ADT.TreeETableFullyEncapsulated.rep_ok@530` | `Examples.AbstractDataTypes.RawTreeTable.Valid`. The actual BST predicate on raw source trees. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.bound@533` | `Examples.AbstractDataTypes.RawTreeTable.bound`. Existing directed presence observation on every raw tree. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.elements@536` | `Examples.AbstractDataTypes.RawTreeTable.elements`. Existing inorder entry list on every raw tree. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.empty_ok@539` | `Examples.AbstractDataTypes.RawTreeTable.empty_valid`. Valid empty through the source BST proof. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.set_ok@544` | `Examples.AbstractDataTypes.RawTreeTable.set_valid`. BST preserved by actual insertion. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.bound_empty@550` | `Examples.AbstractDataTypes.RawTreeTable.bound_empty`. Raw empty-tree absence; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.bound_set_same@556` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_same`. Raw same-key presence; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.bound_set_other@562` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_other`. Raw distinct-key preservation with written-key ≠ query; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.elements_complete@568` | `Examples.AbstractDataTypes.RawTreeTable.elements_complete`. Retains the source BST premise; the stronger raw completeness theorem remains separately available. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.TreeETableFullyEncapsulated.elements_correct@580` | `Examples.AbstractDataTypes.RawTreeTable.elements_correct`. Retains BST and returns both presence and the get value. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.OverlyEncapsulatedExample.ex1@601` | `Examples.AbstractDataTypes.abstract_empty_client`. Actual Lean rejection of a String literal at abstract V is checked inside the generic client; the result is then proved from the public empty law. |
| `ADT.SimpleTable.key@627` | `Examples.AbstractDataTypes.TableSignature.Key`. Ordinary abstract key type, not fixed to Nat; key/payload/state universes remain independent. |
| `ADT.SimpleTable.V@628` | `Examples.AbstractDataTypes.TableSignature.Payload`. Ordinary abstract payload type; key/payload/state universes remain independent. |
| `ADT.SimpleTable.default@629` | `Examples.AbstractDataTypes.TableSignature.default`. Ordinary abstract supplied value at that payload type; key/payload/state universes remain independent. |
| `ADT.SimpleTable.table@630` | `Examples.AbstractDataTypes.TableSignature.Carrier`. Ordinary abstract state carrier; key/payload/state universes remain independent. |
| `ADT.SimpleStringTable1.key@635` | `Examples.AbstractDataTypes.stringTreeSignature`; `Examples.AbstractDataTypes.TableSignature.Key`. Concrete Nat/String/empty-default/tree package; its Lean definition is transparent. Abstract exposure is demonstrated by generic clients, not asserted as sealing. |
| `ADT.SimpleStringTable1.V@636` | `Examples.AbstractDataTypes.stringTreeSignature`; `Examples.AbstractDataTypes.TableSignature.Payload`. Concrete Nat/String/empty-default/tree package; its Lean definition is transparent. Abstract exposure is demonstrated by generic clients, not asserted as sealing. |
| `ADT.SimpleStringTable1.default@637` | `Examples.AbstractDataTypes.stringTreeSignature`; `Examples.AbstractDataTypes.TableSignature.default`. Concrete Nat/String/empty-default/tree package; its Lean definition is transparent. Abstract exposure is demonstrated by generic clients, not asserted as sealing. |
| `ADT.SimpleStringTable1.table@638` | `Examples.AbstractDataTypes.stringTreeSignature`; `Examples.AbstractDataTypes.TableSignature.Carrier`. Concrete Nat/String/empty-default/tree package; its Lean definition is transparent. Abstract exposure is demonstrated by generic clients, not asserted as sealing. |
| `ADT.SimpleStringTable2.key@647` | `Examples.AbstractDataTypes.stringSignature`; `Examples.AbstractDataTypes.TableSignature.Key`. Payload is exposed as String while default remains a parameter; the source concrete package instantiates key/carrier/default to Nat/tree String/empty String. |
| `ADT.SimpleStringTable2.V@648` | `Examples.AbstractDataTypes.stringSignature`; `Examples.AbstractDataTypes.TableSignature.Payload`. Payload is exposed as String while default remains a parameter; the source concrete package instantiates key/carrier/default to Nat/tree String/empty String. |
| `ADT.SimpleStringTable2.default@649` | `Examples.AbstractDataTypes.stringSignature`; `Examples.AbstractDataTypes.TableSignature.default`. Payload is exposed as String while default remains a parameter; the source concrete package instantiates key/carrier/default to Nat/tree String/empty String. |
| `ADT.SimpleStringTable2.table@650` | `Examples.AbstractDataTypes.stringSignature`; `Examples.AbstractDataTypes.TableSignature.Carrier`. Payload is exposed as String while default remains a parameter; the source concrete package instantiates key/carrier/default to Nat/tree String/empty String. |
| `ADT.SimpleStringTable3.key@662` | `Examples.AbstractDataTypes.emptyStringSignature`; `Examples.AbstractDataTypes.TableSignature.Key`. Payload and empty-String default are exposed; key/carrier remain parameters until the source Nat/tree specialization. |
| `ADT.SimpleStringTable3.V@663` | `Examples.AbstractDataTypes.emptyStringSignature`; `Examples.AbstractDataTypes.TableSignature.Payload`. Payload and empty-String default are exposed; key/carrier remain parameters until the source Nat/tree specialization. |
| `ADT.SimpleStringTable3.default@664` | `Examples.AbstractDataTypes.emptyStringSignature`; `Examples.AbstractDataTypes.TableSignature.default`. Payload and empty-String default are exposed; key/carrier remain parameters until the source Nat/tree specialization. |
| `ADT.SimpleStringTable3.table@665` | `Examples.AbstractDataTypes.emptyStringSignature`; `Examples.AbstractDataTypes.TableSignature.Carrier`. Payload and empty-String default are exposed; key/carrier remain parameters until the source Nat/tree specialization. |
| `ADT.rep_ok@679` | `Examples.AbstractDataTypes.RawTreeTable.Valid`. The actual BST predicate on raw source trees. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.bound@682` | `Examples.AbstractDataTypes.RawTreeTable.bound`. Existing directed presence observation on every raw tree. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.elements@685` | `Examples.AbstractDataTypes.RawTreeTable.elements`. Existing inorder entry list on every raw tree. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.empty_ok@688` | `Examples.AbstractDataTypes.RawTreeTable.empty_valid`. Valid empty through the source BST proof. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.set_ok@693` | `Examples.AbstractDataTypes.RawTreeTable.set_valid`. BST preserved by actual insertion. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.bound_empty@699` | `Examples.AbstractDataTypes.RawTreeTable.bound_empty`. Raw empty-tree absence; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.bound_set_same@705` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_same`. Raw same-key presence; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.bound_set_other@711` | `Examples.AbstractDataTypes.RawTreeTable.bound_set_other`. Raw distinct-key preservation with written-key ≠ query; no BST argument. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.elements_complete@717` | `Examples.AbstractDataTypes.RawTreeTable.elements_complete`. Retains the source BST premise; the stronger raw completeness theorem remains separately available. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.elements_correct@729` | `Examples.AbstractDataTypes.RawTreeTable.elements_correct`. Retains BST and returns both presence and the get value. This checked component is reused by the generic abstract-client presentation described below. |
| `ADT.NicelyEncapsulatedExample.ex1@748` | `Examples.AbstractDataTypes.abstract_carrier_empty_lookup`; `Examples.AbstractDataTypes.treeTable_empty_lookup`. Generic get-empty proof uses the law and checks failed reflexivity; its concrete String/tree instantiation preserves the source result. |
| `ADT.NicelyEncapsulatedExample.ex2@758` | `Examples.AbstractDataTypes.abstract_carrier_empty_lookup`. Actual Lean rejection of a raw tree constructor at abstract carrier T; no false mathematical theorem is introduced. |
| `ADT.map_update@794` | `Examples.AbstractDataTypes.mapUpdate`. Existing partial write, with source argument order key,value,map and some-value binding. |
| `ADT.map_find@798` | `Examples.AbstractDataTypes.mapFind`. Explicit-default getD observation with source default,key,map order. |
| `ADT.empty_map@800` | `Examples.AbstractDataTypes.emptyMap`. The none-valued function. |
| `ADT.ETableAbs.table@808` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Independent concrete state parameter T. |
| `ADT.ETableAbs.key@809` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Source specialization retains Nat keys. |
| `ADT.ETableAbs.V@810` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Arbitrary payload parameter. |
| `ADT.ETableAbs.default@811` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Explicit supplied default used only when forgetting absence. |
| `ADT.ETableAbs.empty@813` | `Search.TotalTable.Ops.empty`. The same concrete total-table operation data, without inheriting a stronger membership contract. |
| `ADT.ETableAbs.get@814` | `Search.TotalTable.Ops.get`. The same concrete total-table operation data, without inheriting a stronger membership contract. |
| `ADT.ETableAbs.set@815` | `Search.TotalTable.Ops.set`. The same concrete total-table operation data, without inheriting a stronger membership contract. |
| `ADT.ETableAbs.bound@816` | `Search.OrderedMap.EnumeratedTable.Observations.bound`. The concrete observation field; its refinement is one of the separately proved model laws. |
| `ADT.ETableAbs.elements@817` | `Search.OrderedMap.EnumeratedTable.Observations.elements`. The concrete observation field; its refinement is one of the separately proved model laws. |
| `ADT.ETableAbs.Abs@819` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Separate decoder T → (Nat → Option V). |
| `ADT.ETableAbs.rep_ok@820` | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Separate Valid parameter; no raw entry soundness is assumed. |
| `ADT.ETableAbs.empty_ok@822` | `Search.OrderedMap.EnumeratedTable.ModelLaws.empty_valid`. Valid empty. |
| `ADT.ETableAbs.set_ok@825` | `Search.OrderedMap.EnumeratedTable.ModelLaws.set_valid`. Valid input is preserved by set. |
| `ADT.ETableAbs.empty_relate@828` | `Search.OrderedMap.EnumeratedTable.ModelLaws.empty`. Abs empty is the none-valued map, unconditionally. |
| `ADT.ETableAbs.bound_relate@831` | `Search.OrderedMap.EnumeratedTable.ModelLaws.bound`. Under Valid, optional model presence equals concrete bound. |
| `ADT.ETableAbs.lookup_relate@835` | `Search.OrderedMap.EnumeratedTable.ModelLaws.get`. Under Valid, forgetting absence with the supplied default equals concrete get. |
| `ADT.ETableAbs.insert_relate@839` | `Search.OrderedMap.EnumeratedTable.ModelLaws.set`. Under Valid, write key value (Abs t) = Abs (set key value t), in the source orientation. |
| `ADT.ETableAbs.elements_relate@843` | `Search.OrderedMap.EnumeratedTable.ModelLaws.elements`. Under Valid, Abs t = listObserve (elements t), in the source orientation; raw member soundness does not follow. |
| `ADT.ListETableAbs.V@856` | `Examples.AbstractDataTypes.ShadowingListModel.Carrier`. Ordinary supplied payload/default parameters and Nat keys, with the source argument positions. |
| `ADT.ListETableAbs.default@857` | `Examples.AbstractDataTypes.ShadowingListModel.get`. Ordinary supplied payload/default parameters and Nat keys, with the source argument positions. |
| `ADT.ListETableAbs.key@858` | `Examples.AbstractDataTypes.ShadowingListModel.Carrier`. Ordinary supplied payload/default parameters and Nat keys, with the source argument positions. |
| `ADT.ListETableAbs.table@859` | `Examples.AbstractDataTypes.ShadowingListModel.Carrier`. Raw List (Nat × V), including shadowed duplicates. |
| `ADT.ListETableAbs.empty@861` | `Examples.AbstractDataTypes.ShadowingListModel.empty`. Actual empty pair list. |
| `ADT.ListETableAbs.get@864` | `Examples.AbstractDataTypes.ShadowingListModel.get`. Actual first-binding lookup followed by the explicit default. |
| `ADT.ListETableAbs.set@867` | `Examples.AbstractDataTypes.ShadowingListModel.set`. Prepend the pair, retaining old entries. |
| `ADT.ListETableAbs.bound@870` | `Examples.AbstractDataTypes.ShadowingListModel.bound`. isSome of the actual first-match lookup. |
| `ADT.ListETableAbs.elements@873` | `Examples.AbstractDataTypes.ShadowingListModel.elements`. Identity on the stored raw pair list. |
| `ADT.ListETableAbs.Abs@876` | `Examples.AbstractDataTypes.ShadowingListModel.meaning`. The existing head-wins listObserve decoder. |
| `ADT.ListETableAbs.rep_ok@879` | `Examples.AbstractDataTypes.ShadowingListModel.Valid`. Exactly True; all represented lists are valid for this model contract. |
| `ADT.ListETableAbs.empty_ok@882` | `Examples.AbstractDataTypes.ShadowingListModel.empty_valid`. Proves True for empty. |
| `ADT.ListETableAbs.set_ok@886` | `Examples.AbstractDataTypes.ShadowingListModel.set_valid`. Proves True is preserved. |
| `ADT.ListETableAbs.empty_relate@891` | `Examples.AbstractDataTypes.ShadowingListModel.meaning_empty`. Empty decoder = empty optional map. |
| `ADT.ListETableAbs.bound_relate@896` | `Examples.AbstractDataTypes.ShadowingListModel.meaning_bound`. Model/concrete presence equality, retaining the trivial source validity argument. |
| `ADT.ListETableAbs.lookup_relate@902` | `Examples.AbstractDataTypes.ShadowingListModel.meaning_lookup`. Source-oriented default lookup equality. |
| `ADT.ListETableAbs.insert_relate@908` | `Examples.AbstractDataTypes.ShadowingListModel.meaning_set`. Source-oriented abstract write = decode after prepend. |
| `ADT.ListETableAbs.elements_relate@914` | `Examples.AbstractDataTypes.ShadowingListModel.meaning_elements`. Source-oriented decoder = decoded identity enumeration; no nodup or raw member soundness asserted. |
| `ADT.manual_grade_for_TreeTableModel@935` | `Examples.AbstractDataTypes.treeTable_enumeration_model`; `Examples.AbstractDataTypes.treeTable_structural_model`. Grading metadata is omitted. Both optional full seven-law model realizations are proved, with distinct enumeration and direct structural decoders. |
| `ADT.Queue.V@979` | `Examples.AbstractDataTypes.Queue`. Independent payload and state parameters of the source-shaped five-operation bundle. |
| `ADT.Queue.queue@980` | `Examples.AbstractDataTypes.Queue`. Independent payload and state parameters of the source-shaped five-operation bundle. |
| `ADT.Queue.empty@981` | `Sequences.SourceQueue.Ops.empty`. Exact source operation type and argument order; peek takes its default at each call. |
| `ADT.Queue.is_empty@982` | `Sequences.SourceQueue.Ops.isEmpty`. Exact source operation type and argument order; peek takes its default at each call. |
| `ADT.Queue.enq@983` | `Sequences.SourceQueue.Ops.enqueue`. Exact source operation type and argument order; peek takes its default at each call. |
| `ADT.Queue.deq@984` | `Sequences.SourceQueue.Ops.dequeue`. Exact source operation type and argument order; peek takes its default at each call. |
| `ADT.Queue.peek@985` | `Sequences.SourceQueue.Ops.peek`. Exact source operation type and argument order; peek takes its default at each call. |
| `ADT.Queue.is_empty_empty@986` | `Sequences.SourceQueue.Laws.isEmpty_empty`. Empty is marked empty. The actual list realization proves this requirement. |
| `ADT.Queue.is_empty_nonempty@987` | `Sequences.SourceQueue.Laws.isEmpty_enqueue`. Enqueue produces a nonempty queue. The actual list realization proves this requirement. |
| `ADT.Queue.peek_empty@988` | `Sequences.SourceQueue.Laws.peek_empty`. Every default is returned on empty. The actual list realization proves this requirement. |
| `ADT.Queue.peek_nonempty@989` | `Sequences.SourceQueue.Laws.peek_enqueue`. The right-side peek default is the enqueued value. The actual list realization proves this requirement. |
| `ADT.Queue.deq_empty@990` | `Sequences.SourceQueue.Laws.dequeue_empty`. Literal equality of dequeue empty and empty. The actual list realization proves this requirement. |
| `ADT.Queue.deq_nonempty@991` | `Sequences.SourceQueue.Laws.dequeue_enqueue`. Literal state equality; the empty-test true branch is exactly the original q, not an abstract empty or decoded equality. The actual list realization proves this requirement. |
| `ADT.ListQueue.V@1002` | `Examples.AbstractDataTypes.ListQueue.Value`. Exact source Nat specialization. |
| `ADT.ListQueue.queue@1003` | `Examples.AbstractDataTypes.ListQueue.Carrier`. Actual List Nat. |
| `ADT.ListQueue.empty@1005` | `Examples.AbstractDataTypes.ListQueue.empty`. []. |
| `ADT.ListQueue.is_empty@1008` | `Examples.AbstractDataTypes.ListQueue.isEmpty`. List.isEmpty. |
| `ADT.ListQueue.enq@1011` | `Examples.AbstractDataTypes.ListQueue.enqueue`. Actual append-singleton, q ++ [value]. |
| `ADT.ListQueue.deq@1014` | `Examples.AbstractDataTypes.ListQueue.dequeue`. List.tail, total on []. |
| `ADT.ListQueue.peek@1017` | `Examples.AbstractDataTypes.ListQueue.peek`. List.headD at the caller default. |
| `ADT.ListQueue.is_empty_empty@1020` | `Examples.AbstractDataTypes.ListQueue.isEmpty_empty`. Proved from the actual generic list-law instance. |
| `ADT.ListQueue.is_empty_nonempty@1024` | `Examples.AbstractDataTypes.ListQueue.isEmpty_enqueue`. Proved for every list and enqueued Nat. |
| `ADT.ListQueue.peek_empty@1029` | `Examples.AbstractDataTypes.ListQueue.peek_empty`. Proved for every caller default. |
| `ADT.ListQueue.peek_nonempty@1034` | `Examples.AbstractDataTypes.ListQueue.peek_enqueue`. Retains the enqueued value as the right-side default. |
| `ADT.ListQueue.deq_empty@1039` | `Examples.AbstractDataTypes.ListQueue.dequeue_empty`. Literal empty-state equality. |
| `ADT.ListQueue.deq_nonempty@1044` | `Examples.AbstractDataTypes.ListQueue.dequeue_enqueue`. Literal source if equation, with q itself in the empty branch. |
| `ADT.QueueAbs.V@1058` | `Examples.AbstractDataTypes.Queue`. Same independent payload/state operation parameters. |
| `ADT.QueueAbs.queue@1059` | `Examples.AbstractDataTypes.Queue`. Same independent payload/state operation parameters. |
| `ADT.QueueAbs.empty@1060` | `Sequences.SourceQueue.Ops.empty`. Same concrete operation field. |
| `ADT.QueueAbs.is_empty@1061` | `Sequences.SourceQueue.Ops.isEmpty`. Same concrete operation field. The four-law signature supplies no law for this empty test. |
| `ADT.QueueAbs.enq@1062` | `Sequences.SourceQueue.Ops.enqueue`. Same concrete operation field. |
| `ADT.QueueAbs.deq@1063` | `Sequences.SourceQueue.Ops.dequeue`. Same concrete operation field. |
| `ADT.QueueAbs.peek@1064` | `Sequences.SourceQueue.Ops.peek`. Same concrete operation field. |
| `ADT.QueueAbs.Abs@1065` | `Examples.AbstractDataTypes.QueueAbsLaws`. Explicit decoder parameter Q → List V. |
| `ADT.QueueAbs.empty_relate@1066` | `Sequences.SourceQueue.AbsLaws.empty`. One of exactly four unguarded source decoder laws; no invariant or extra empty-test requirement. |
| `ADT.QueueAbs.enq_relate@1067` | `Sequences.SourceQueue.AbsLaws.enqueue`. One of exactly four unguarded source decoder laws; no invariant or extra empty-test requirement. |
| `ADT.QueueAbs.peek_relate@1068` | `Sequences.SourceQueue.AbsLaws.peek`. One of exactly four unguarded source decoder laws; no invariant or extra empty-test requirement. |
| `ADT.QueueAbs.deq_relate@1069` | `Sequences.SourceQueue.AbsLaws.dequeue`. One of exactly four unguarded source decoder laws; no invariant or extra empty-test requirement. |
| `ADT.TwoListQueueAbs.V@1079` | `Examples.AbstractDataTypes.TwoListQueue.Value`. Exact source Nat specialization. |
| `ADT.TwoListQueueAbs.queue@1081` | `Examples.AbstractDataTypes.TwoListQueue.Carrier`. Every raw pair of Nat lists, without a normalization invariant. |
| `ADT.TwoListQueueAbs.Abs@1085` | `Examples.AbstractDataTypes.TwoListQueue.decode`. Front ++ reverse back. |
| `ADT.TwoListQueueAbs.empty@1088` | `Examples.AbstractDataTypes.TwoListQueue.empty`. ([],[]). |
| `ADT.TwoListQueueAbs.is_empty@1091` | `Examples.AbstractDataTypes.TwoListQueue.isEmpty`. Actual empty/empty pattern; separate is_empty_relate proves its concrete correctness. |
| `ADT.TwoListQueueAbs.enq@1097` | `Examples.AbstractDataTypes.TwoListQueue.enqueue`. (front,value::back), with no normalization. |
| `ADT.TwoListQueueAbs.deq@1100` | `Examples.AbstractDataTypes.TwoListQueue.dequeue`. Exact empty/empty, reversed nonempty-back, and nonempty-front source branches. |
| `ADT.TwoListQueueAbs.peek@1111` | `Examples.AbstractDataTypes.TwoListQueue.peek`. Exact source branches, returning only the observed value with no state update. |
| `ADT.TwoListQueueAbs.empty_relate@1122` | `Examples.AbstractDataTypes.TwoListQueue.decode_empty`. Empty decoder law. |
| `ADT.TwoListQueueAbs.enq_relate@1126` | `Examples.AbstractDataTypes.TwoListQueue.decode_enqueue`. All raw pairs; decode after enqueue = old decode ++ [value]. |
| `ADT.TwoListQueueAbs.peek_relate@1131` | `Examples.AbstractDataTypes.TwoListQueue.peek_eq_headD_decode`. All raw pairs and defaults; actual peek = decoded headD. |
| `ADT.TwoListQueueAbs.deq_relate@1136` | `Examples.AbstractDataTypes.TwoListQueue.decode_dequeue`. All raw pairs; decode after actual dequeue = decoded tail. |
| `ADT.even_nat@1173` | `Examples.AbstractDataTypes.EvenNat`. Exactly {n : Nat // Even n}. |
| `ADT.two@1178` | `Examples.AbstractDataTypes.twoInline`. The actual failed bare-numeral construction is checked before explicitly providing the value and evenness proof. |
| `ADT.Even2@1183` | `Examples.AbstractDataTypes.even_two`. Constructive evenness witness 1 for Nat 2. |
| `ADT.two@1192` | `Examples.AbstractDataTypes.two`. Actual subtype package containing 2 and Even2. |
| `ADT.two'@1197` | `Examples.AbstractDataTypes.twoInline`. Executable proof-building definition of the same even value. |
| `ADT.plus_two@1211` | `Examples.AbstractDataTypes.plus_two`; `Examples.AbstractDataTypes.plus_two_coercion`. The exact unannotated 1+two expression is rejected in Lean; explicit Nat-typed addition permits its standard subtype coercion. Both behaviors are checked. |
| `ADT.plus_two@1215` | `Examples.AbstractDataTypes.plus_two`. Exactly 1+two.val=3. |
| `ADT.Even2'@1220` | `Examples.AbstractDataTypes.even_two_from_subtype`. The evenness theorem is the actual stored subtype property. |
| `ADT.SigSandbox.sig@1233` | `Examples.AbstractDataTypes.SubtypeExamples.Refinement`. Alias to existing Subtype, with a computational witness. |
| `ADT.SigSandbox.ex@1245` | `Examples.AbstractDataTypes.SubtypeExamples.WitnessExists`. Alias to existing Exists in Prop. |
| `ADT.SigSandbox.proj1_sig@1254` | `Examples.AbstractDataTypes.SubtypeExamples.value`. The actual subtype value projection. |
| `ADT.SigSandbox.proj2_sig@1259` | `Examples.AbstractDataTypes.SubtypeExamples.property`. The actual stored property of exactly the projected witness. |
| `ADT.SigSandbox.proj1_ex@1264` | `Examples.AbstractDataTypes.SubtypeExamples.exists_propositional_elimination`. Actual rejection of executable generic witness extraction from Exists, with valid propositional elimination proved separately; no classical-choice replacement. |
| `ADT.vector@1278` | `Examples.AbstractDataTypes.StoredLengthVector`. Exactly {p : List X × Nat // p.1.length=p.2}; no Array-vector substitution. |
| `ADT.a_vector@1289` | `Examples.AbstractDataTypes.exampleVector`. Concrete ([3,1,4],3) with a constructive length proof. |
| `ADT.vector_cons@1300` | `Examples.AbstractDataTypes.vectorCons`. Executable prepend with stored length old+1 and a proof of the invariant. |
| `ADT.list_of_vector@1306` | `Examples.AbstractDataTypes.vectorToList`. Projection of the stored list. |
| `ADT.vector_cons_correct@1309` | `Examples.AbstractDataTypes.vectorToList_vectorCons`. Exact list projection x::old, for every payload type, value and vector. |
| `ADT.vector_app@1320` | `Examples.AbstractDataTypes.vectorAppend`. Executable append with stored length first+second and its invariant proof. |
| `ADT.vector_app_correct@1326` | `Examples.AbstractDataTypes.vectorToList_vectorAppend`. Exact ordered append of both list projections, for every payload type. |
| `ADT.ETableSubset.bound@1348` | `Search.OrderedMap.EnumeratedTable.Observations.bound`. The same observation type; the concrete carrier stores its invariant. |
| `ADT.ETableSubset.elements@1349` | `Search.OrderedMap.EnumeratedTable.Observations.elements`. The same observation type; the concrete carrier stores its invariant. |
| `ADT.ETableSubset.bound_empty@1351` | `Search.OrderedMap.EnumeratedTable.SubsetLaws`; `Search.OrderedMap.EnumeratedTable.Laws.bound_empty`. Source law is unconditional on the subtype carrier. The internal True-validity witnesses add no public representation premise. |
| `ADT.ETableSubset.bound_set_same@1354` | `Search.OrderedMap.EnumeratedTable.SubsetLaws`; `Search.OrderedMap.EnumeratedTable.Laws.bound_set_same`. Source law is unconditional on the subtype carrier. The internal True-validity witnesses add no public representation premise. |
| `ADT.ETableSubset.bound_set_other@1357` | `Search.OrderedMap.EnumeratedTable.SubsetLaws`; `Search.OrderedMap.EnumeratedTable.Laws.bound_set_other`. Source law is unconditional on the subtype carrier. The internal True-validity witnesses add no public representation premise. |
| `ADT.ETableSubset.elements_complete@1360` | `Search.OrderedMap.EnumeratedTable.SubsetLaws`; `Search.OrderedMap.EnumeratedTable.Laws.elements_complete`. Source law is unconditional on the subtype carrier. The internal True-validity witnesses add no public representation premise. |
| `ADT.ETableSubset.elements_correct@1365` | `Search.OrderedMap.EnumeratedTable.SubsetLaws`; `Search.OrderedMap.EnumeratedTable.Laws.elements_correct`. Source law is unconditional on the subtype carrier. The internal True-validity witnesses add no public representation premise. |
| `ADT.TreeETableSubset.V@1373` | `Examples.AbstractDataTypes.ValidTreeTable.Carrier`. Ordinary payload/default parameters and the source Nat key specialization. |
| `ADT.TreeETableSubset.default@1374` | `Examples.AbstractDataTypes.ValidTreeTable.ops`. Ordinary payload/default parameters and the source Nat key specialization. |
| `ADT.TreeETableSubset.key@1375` | `Examples.AbstractDataTypes.ValidTreeTable.Carrier`. Ordinary payload/default parameters and the source Nat key specialization. |
| `ADT.TreeETableSubset.table@1378` | `Examples.AbstractDataTypes.ValidTreeTable.Carrier`. The existing OrderedMap.Tree Nat V, exactly a BST subtype of the source raw tree. |
| `ADT.TreeETableSubset.empty@1383` | `Examples.AbstractDataTypes.ValidTreeTable.empty`. Existing executable empty tree packaged with its BST proof. |
| `ADT.TreeETableSubset.get@1390` | `Examples.AbstractDataTypes.ValidTreeTable.get`. Raw lookup at t.val with the explicit default. |
| `ADT.TreeETableSubset.set@1393` | `Examples.AbstractDataTypes.ValidTreeTable.set`. Existing insertion packaged with the preservation proof; no second tree algorithm. |
| `ADT.TreeETableSubset.bound@1400` | `Examples.AbstractDataTypes.ValidTreeTable.bound`. Raw presence through the stored tree projection. |
| `ADT.TreeETableSubset.elements@1403` | `Examples.AbstractDataTypes.ValidTreeTable.elements`. Actual inorder entries through the stored tree projection. |
| `ADT.TreeETableSubset.get_empty_default@1406` | `Examples.AbstractDataTypes.ValidTreeTable.get_empty_default`. Unconditional carrier law through the proved empty construction. |
| `ADT.TreeETableSubset.get_set_same@1416` | `Examples.AbstractDataTypes.ValidTreeTable.get_set_same`. Reuses the stronger raw same-key law after projection. |
| `ADT.TreeETableSubset.get_set_other@1424` | `Examples.AbstractDataTypes.ValidTreeTable.get_set_other`. Reuses the stronger raw distinct-key law after projection. |
| `ADT.TreeETableSubset.bound_empty@1432` | `Examples.AbstractDataTypes.ValidTreeTable.bound_empty`. Actual empty presence=false. |
| `ADT.TreeETableSubset.bound_set_same@1438` | `Examples.AbstractDataTypes.ValidTreeTable.bound_set_same`. Raw same-key presence after projection. |
| `ADT.TreeETableSubset.bound_set_other@1446` | `Examples.AbstractDataTypes.ValidTreeTable.bound_set_other`. Raw distinct-key preservation after projection. |
| `ADT.TreeETableSubset.elements_complete@1454` | `Examples.AbstractDataTypes.ValidTreeTable.elements_complete`. Presence and returned value imply membership; no external validity argument. |
| `ADT.TreeETableSubset.elements_correct@1465` | `Examples.AbstractDataTypes.ValidTreeTable.elements_correct`. Membership implies presence and get=value; the existing subtype property supplies BST internally. |
| `ADT.manual_grade_for_ListsETable@1489` | `Examples.AbstractDataTypes.UniqueListTable.laws`; `Examples.AbstractDataTypes.UniqueListTable.elements_identity`; `Examples.AbstractDataTypes.UniqueListTable.elements_set`. Grading metadata is omitted. The complete unique-key pair-list subtype realization, identity enumeration and actual first-key replacement discharge the advanced exercise; measured work is mapped below. |

### All 12 complete exercise prompts

Every optional, advanced, unnamed and grading-only prompt remains in scope.
The original labels are source metadata, not acceptance evidence.

| Source exercise and lines | Stars; labels | Complete implementation |
|---|---|---|
| `NatFunTableExamples`, 170–180 | 2; standard, optional | `Examples.AbstractDataTypes.natFunctionTable`; `Examples.AbstractDataTypes.natFunctionTable_empty`; `Examples.AbstractDataTypes.natFunctionTable_same_key`; `Examples.AbstractDataTypes.natFunctionTable_other_key`; `Examples.AbstractDataTypes.natFunctionTable_repeated_write`. Nat payload/default zero, with empty, same, other and repeated-write clients. |
| `lists_table`, 185–243 | 3; standard | `Examples.AbstractDataTypes.listTable_laws`; `Examples.AbstractDataTypes.stringListTable_empty`; `Examples.AbstractDataTypes.stringListTable_same_key`; `Examples.AbstractDataTypes.stringListTable_other_key`. Actual raw pair list and prepend; all three Table laws and all three exact String observations. |
| `elements_spec`, 766–774 | 4; advanced, optional | `Search.OrderedMap.EnumeratedTable.StrongElements`; `Examples.AbstractDataTypes.strong_elements_client`; `Examples.AbstractDataTypes.strong_elements_inverse_raw`; `Examples.AbstractDataTypes.elements_spec`. Generic observation/law client and actual tree realization; both absence directions retain their distinct scopes, with accepted Nat sortedness and projected-key nodup. |
| `list_etable_abs`, 849–925 | 4; standard | `Examples.AbstractDataTypes.ShadowingListModel.laws`; `Examples.AbstractDataTypes.raw_list_shadowed_entry`. All operations and seven model laws with Valid=True, head-wins decoding and identity elements; shadowed entries remain legal. |
| `TreeTableModel`, 927–937 | 3; standard, optional | `Examples.AbstractDataTypes.treeTable_enumeration_model`; `Examples.AbstractDataTypes.both_tree_model_histories`. All seven laws through enumeration Abs, plus arbitrary write histories. The grading constant is omitted. |
| `TreeTableModel'`, 939–945 | 2; advanced, optional | `Examples.AbstractDataTypes.treeTable_structural_model`; `Examples.AbstractDataTypes.both_tree_model_histories`. All seven laws through independent structural Abs′; only elements coherence uses the established decoder agreement. |
| `list_queue`, 994–1051 | 3; standard | `Examples.AbstractDataTypes.ListQueue.ops`; `Sequences.SourceQueue.lists_laws`; `Examples.AbstractDataTypes.ListQueue.source_operations`. Actual Nat list operations and all six exact algebraic equations, including right-side value default and literal q branch. |
| `two_list_queue`, 1072–1143 | 3; standard | `Examples.AbstractDataTypes.TwoListQueue.ops`; `Sequences.SourceQueue.twoLists_absLaws`; `Examples.AbstractDataTypes.queue_source_client`. Every raw source pair branch, all four decoder equations, separate emptiness, actual optional-head client, raw-state counterexample and measured qualifications below. |
| `a_vector`, 1285–1293 | 1; standard | `Examples.AbstractDataTypes.exampleVector`; `Examples.AbstractDataTypes.exampleVector_append_data`; `Examples.AbstractDataTypes.exampleVector_append_length`. Nontrivial source-shaped list/stored-length package and checked projections. |
| `vector_cons_correct`, 1295–1314 | 2; standard | `Examples.AbstractDataTypes.vectorCons`; `Examples.AbstractDataTypes.vectorToList_vectorCons`; `Examples.AbstractDataTypes.vectorCons_length`. Executable construction, invariant proof, exact list and stored-length equations. |
| `vector_app_correct`, 1316–1332 | 2; standard | `Examples.AbstractDataTypes.vectorAppend`; `Examples.AbstractDataTypes.vectorToList_vectorAppend`; `Examples.AbstractDataTypes.vectorAppend_length`. Executable construction, invariant proof, exact ordered list append and stored-length addition. |
| `ListsETable`, 1478–1490 | 4; advanced | `Examples.AbstractDataTypes.UniqueListTable.laws`; `Examples.AbstractDataTypes.UniqueListTable.elements_set`; `Search.OrderedMap.AssociationListEnumeration.toAList_set`; `Resources.ListErase.setRun_value`. Complete unsorted unique-key pair-list subtype contract, identity enumeration, exact first-key erasure/AList update bridge and measured linear worst case below. |

### All 39 module and module-type records

Rocq functors, signatures and module aliases are represented by ordinary
Lean operation data, law records, explicit parameters and concrete instances.
A repeated module body reuses its checked provider. A namespace or transparent
definition does not itself implement Rocq sealing; the abstract typing
boundary is exercised by actual generic clients and rejected elaborations.

| Actual source module and header line | Kind | Checked implementation or interface boundary |
|---|---|---|
| `ADT.Table`, 50 | module type | `Examples.AbstractDataTypes.TableLaws`. Abstract state/payload with Nat keys, explicit default and three unconditional laws. |
| `ADT.ValType`, 100 | module type | `Examples.AbstractDataTypes.functionTable`. Payload and default are explicit parameters of the table construction. |
| `ADT.FunTable`, 111 | module | `Examples.AbstractDataTypes.functionTable_laws`. Actual total-function provider and its complete law instance. |
| `ADT.StringVal`, 148 | module | `Examples.AbstractDataTypes.StringPayload.Value`; `Examples.AbstractDataTypes.StringPayload.default`. String and the empty String. |
| `ADT.FunTableExamples`, 153 | module | `Examples.AbstractDataTypes.stringFunctionTable_empty`; `Examples.AbstractDataTypes.stringFunctionTable_same_key`; `Examples.AbstractDataTypes.stringFunctionTable_other_key`. All three exact observations use public laws. |
| `ADT.FunTableExamples.StringFunTable`, 155 | module alias | `Examples.AbstractDataTypes.stringFunctionTable`. Concrete String/empty-default function-table instance. |
| `ADT.NatFunTableExamples`, 176 | module | `Examples.AbstractDataTypes.natFunctionTable`; `Examples.AbstractDataTypes.natFunctionTable_empty`; `Examples.AbstractDataTypes.natFunctionTable_same_key`; `Examples.AbstractDataTypes.natFunctionTable_other_key`; `Examples.AbstractDataTypes.natFunctionTable_repeated_write`. Complete optional Nat/zero instance and clients. |
| `ADT.ListsTable`, 189 | module | `Examples.AbstractDataTypes.listTable_laws`. Raw pair-list prepend/first-match provider and all three laws. |
| `ADT.StringListsTableExamples`, 223 | module | `Examples.AbstractDataTypes.stringListTable_empty`; `Examples.AbstractDataTypes.stringListTable_same_key`; `Examples.AbstractDataTypes.stringListTable_other_key`. All three exact String clients. |
| `ADT.StringListsTableExamples.StringListsTable`, 225 | module alias | `Examples.AbstractDataTypes.stringListTable`. Concrete String/empty-default raw-list instance. |
| `ADT.TreeTable`, 251 | module | `Examples.AbstractDataTypes.treeTable_laws`. Existing raw source tree with all three unconditional table laws. |
| `ADT.ETable_first_attempt`, 300 | module type | `Search.OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws`. The complete unconditional first-attempt interface. |
| `ADT.TreeETable_first_attempt`, 326 | module | `Examples.AbstractDataTypes.RawTreeTable.elements_complete_raw`; `Examples.AbstractDataTypes.raw_tree_unrestricted_enumeration_fails`. The valid raw completeness direction is proved; the false soundness direction is refuted. |
| `ADT.ETable`, 375 | module type | `Search.OrderedMap.EnumeratedTable.Laws`. The exact split between unconditional algebra/presence and validity-qualified enumeration. |
| `ADT.TreeETable`, 416 | module | `Examples.AbstractDataTypes.RawTreeTable.laws`. Complete corrected raw-tree provider with BST validity. |
| `ADT.StringTreeETableExample`, 485 | module | `Examples.AbstractDataTypes.string_tree_elements_example`. Exact source membership observation through the public laws. |
| `ADT.StringTreeETableExample.StringTreeETable`, 487 | module alias | `Examples.AbstractDataTypes.RawTreeTable.laws`. String/empty-default specialization of the complete provider. |
| `ADT.TreeETableFullyEncapsulated`, 527 | module | `Examples.AbstractDataTypes.RawTreeTable.laws`; `Examples.AbstractDataTypes.abstract_empty_client`. Reuse the complete provider; the generic client demonstrates the fully abstract payload/carrier/default boundary. |
| `ADT.OverlyEncapsulatedExample`, 595 | module | `Examples.AbstractDataTypes.abstract_empty_client`. Actual failed String-literal elaboration at abstract payload, followed by a lawful abstract client. |
| `ADT.OverlyEncapsulatedExample.StringTreeETableFullyEncapsulated`, 597 | module alias | `Examples.AbstractDataTypes.abstract_empty_client`. Source String implementation is behind the abstract client signature; no transparent Lean namespace is claimed to seal it. |
| `ADT.SimpleTable`, 626 | module type | `Examples.AbstractDataTypes.TableSignature`. Key, payload, default and state fields remain explicit. |
| `ADT.SimpleStringTable1`, 634 | module | `Examples.AbstractDataTypes.stringTreeSignature`. Actual concrete package; abstraction is tested at the generic signature boundary. |
| `ADT.SimpleTable2`, 644 | module type alias | `Examples.AbstractDataTypes.stringSignature_payload`; `Examples.AbstractDataTypes.string_abstract_default_client`. The constrained presentation exposes String but retains default/key/carrier as parameters. |
| `ADT.SimpleStringTable2`, 646 | module | `Examples.AbstractDataTypes.stringSignature`. Its source specialization uses Nat, tree String and the empty String. |
| `ADT.SimpleTable3`, 657 | module type alias | `Examples.AbstractDataTypes.emptyStringSignature_default`. The constrained presentation exposes String and the empty String, retaining key/carrier as parameters. |
| `ADT.SimpleStringTable3`, 661 | module | `Examples.AbstractDataTypes.emptyStringSignature`. Its source specialization uses Nat and tree String. |
| `ADT.TreeETableEncapsulated`, 675 | module | `Examples.AbstractDataTypes.RawTreeTable.laws`; `Examples.AbstractDataTypes.abstract_carrier_empty_lookup`. Actual constrained-signature implementation, not an alias; complete provider and abstract-state client are both retained. |
| `ADT.NicelyEncapsulatedExample`, 742 | module | `Examples.AbstractDataTypes.abstract_carrier_empty_lookup`; `Examples.AbstractDataTypes.treeTable_empty_lookup`. Public-law proof, failed reflexivity and failed raw constructor at abstract carrier; concrete source instantiation. |
| `ADT.NicelyEncapsulatedExample.StringTreeETableEncapsulated`, 744 | module alias | `Examples.AbstractDataTypes.treeTable_empty_lookup`. Concrete String/empty-default provider consumed through the abstract-state client. |
| `ADT.ETableAbs`, 806 | module type | `Search.OrderedMap.EnumeratedTable.ModelLaws`. Exactly seven model laws, with the source orientations and validity guards. |
| `ADT.ListETableAbs`, 854 | module | `Examples.AbstractDataTypes.ShadowingListModel.laws`. Complete raw duplicate-permitting list model, identity entries and head-wins decoder. |
| `ADT.StringListETableAbs`, 923 | module alias | `Examples.AbstractDataTypes.ShadowingListModel.laws`; `Examples.AbstractDataTypes.model_repeated_history_checked`. Specialize the complete model to String/default empty; the connected repeated-history client uses that actual specialization. |
| `ADT.Queue`, 978 | module type | `Sequences.SourceQueue.Laws`. Exact five operations and six algebraic equations. |
| `ADT.ListQueue`, 1001 | module | `Examples.AbstractDataTypes.ListQueue.ops`; `Sequences.SourceQueue.lists_laws`. Actual source Nat list completion and all six equations. |
| `ADT.QueueAbs`, 1057 | module type | `Sequences.SourceQueue.AbsLaws`. Exactly four decoder laws; the empty test remains unspecified. |
| `ADT.TwoListQueueAbs`, 1078 | module | `Examples.AbstractDataTypes.TwoListQueue.ops`; `Sequences.SourceQueue.twoLists_absLaws`. Literal source pair operations on every raw state and all four decoder laws. |
| `ADT.SigSandbox`, 1229 | module | `Examples.AbstractDataTypes.SubtypeExamples.Refinement`; `Examples.AbstractDataTypes.SubtypeExamples.WitnessExists`; `Examples.AbstractDataTypes.SubtypeExamples.exists_propositional_elimination`. Existing computational subtype and propositional existential, with their distinct elimination behavior. |
| `ADT.ETableSubset`, 1342 | module type | `Search.OrderedMap.EnumeratedTable.SubsetLaws`. The full enumeration contract with intrinsic representation validity. |
| `ADT.TreeETableSubset`, 1371 | module | `Examples.AbstractDataTypes.ValidTreeTable.laws`. Complete existing BST-subtype provider and all source laws. |

### Inspection commands and intended failures

The source commands are pedagogical observations of types, visibility and
proof behavior. Their Lean dispositions retain those observations without
claiming identical Rocq and Lean elaborators.

| Source command | Checked Lean observation |
|---|---|
| Check at 334 | `Search.TotalTable.Ops.get`; `Examples.AbstractDataTypes.RawTreeTable.laws`. Inspect the included get type and the complete enriched provider; get remains default-valued. |
| Print at 615 | `Examples.AbstractDataTypes.abstract_empty_client`. The generic payload is abstract, so a String literal is unavailable even if the eventual implementation is String. |
| Print at 642 | `Examples.AbstractDataTypes.TableSignature.Payload`; `Examples.AbstractDataTypes.abstract_empty_client`. The signature exposes only a payload type; the concrete first package is transparent in Lean, while the client demonstrates abstraction. |
| Print at 654 | `Examples.AbstractDataTypes.stringSignature_payload`. The second presentation exposes its payload equality to String. |
| Print at 655 | `Examples.AbstractDataTypes.stringSignature_default`; `Examples.AbstractDataTypes.string_abstract_default_client`. The second presentation keeps default as a parameter; it cannot be identified with the empty String in the generic client. |
| Print at 669 | `Examples.AbstractDataTypes.emptyStringSignature`. The third presentation visibly has String as payload. |
| Print at 670 | `Examples.AbstractDataTypes.emptyStringSignature_default`. The third presentation fixes the default to the empty String. |
| Fail at 751 | `Examples.AbstractDataTypes.abstract_carrier_empty_lookup`. Actual failed reflexivity under abstract operations, followed by the public empty/get law. |
| Check at 1190 | `Examples.AbstractDataTypes.SubtypeExamples.pack`. Inspect the existing subtype constructor with a computational value and its property proof. |
| Check at 1213 | `Examples.AbstractDataTypes.SubtypeExamples.value`. Inspect the computational value projection used by the valid Nat addition. |
| Check at 1218 | `Examples.AbstractDataTypes.SubtypeExamples.property`. Inspect the stored property of exactly the projected value. |

| Expected declaration failure | Checked disposition |
|---|---|
| `ADT.OverlyEncapsulatedExample.ex1@601` | `Examples.AbstractDataTypes.abstract_empty_client` rejects a String literal as an arbitrary payload and proves the valid abstract result from the public law. |
| `ADT.NicelyEncapsulatedExample.ex2@758` | `Examples.AbstractDataTypes.abstract_carrier_empty_lookup` rejects a raw tree constructor as an arbitrary carrier. |
| `ADT.two@1178` | `Examples.AbstractDataTypes.twoInline` checks rejection of the bare numeral at the even-number subtype before constructing the value/proof pair. |
| `ADT.plus_two@1211` | `Examples.AbstractDataTypes.plus_two` checks rejection of the original unannotated addition expression. `Examples.AbstractDataTypes.plus_two_coercion` separately proves the explicitly Nat-typed expression, for which Lean supplies its subtype coercion. |
| `ADT.SigSandbox.proj1_ex@1264` | `Examples.AbstractDataTypes.SubtypeExamples.exists_propositional_elimination` checks that generic executable witness extraction from `Exists` is rejected, and proves elimination into a proposition. |

### Algebraic tables, independent models and complete clients

`Examples.AbstractDataTypes.functionTable` uses the existing function table and
an explicit default. `Examples.AbstractDataTypes.functionTable_set_source`
retains the source written-key-first Boolean conditional.
`Examples.AbstractDataTypes.listTable` uses the existing first-binding
list lookup; `Examples.AbstractDataTypes.listTable_set_source` is prepend.
`Examples.AbstractDataTypes.treeTable` uses the existing raw tree owner;
`Examples.AbstractDataTypes.treeTable_set_source` is the actual source insertion.
All three complete Table instances are unconditional. The raw repeated-list
shape and its new-value observation are checked by
`Examples.AbstractDataTypes.stringListTable_repeated_raw_shape` and
`Examples.AbstractDataTypes.stringListTable_repeated_lookup`.
`Examples.AbstractDataTypes.malformed_table_update` confirms that the raw
tree update laws do not silently acquire a BST premise.

The first raw-tree membership attempt is false: the exact malformed tree
contains an entry that directed lookup does not find. The checked
`Examples.AbstractDataTypes.malformed_tree_member` and
`Examples.AbstractDataTypes.raw_tree_unrestricted_enumeration_fails` preserve that
counterexample. Corrected `Examples.AbstractDataTypes.RawTreeTable.laws`
retains BST for both source membership directions while
`Examples.AbstractDataTypes.RawTreeTable.elements_complete_raw` exposes
the stronger direction that needs no BST. Presence laws remain raw.
The source elements example is proved by
`Examples.AbstractDataTypes.string_tree_elements_example` through the
public validity, lookup, presence and membership laws.

The strengthened optional exercise is complete:
`Examples.AbstractDataTypes.strong_elements_client` uses only the supplied
generic observations, strengthened laws and validity, and
`Examples.AbstractDataTypes.strong_elements_inverse_raw` retains the
stronger raw scope of the inverse absence result.
`Examples.AbstractDataTypes.elements_spec` connects those requirements
to the actual tree. The sorting conclusion compares projected keys, with
strict order in the reusable owner and the requested non-strict Nat order
in the source client; the no-duplicate statement also concerns keys.

`Examples.AbstractDataTypes.ShadowingListModel.laws` proves all seven model
requirements with validity `True`, identity enumeration and the existing
head-wins optional decoder. Thus a raw list can contain a shadowed entry
without satisfying membership soundness.
`Examples.AbstractDataTypes.raw_list_shadowed_entry` supplies the concrete
two-binding witness and `Examples.AbstractDataTypes.raw_list_unrestricted_enumeration_fails`
refutes the stronger first-attempt contract on that representation.

The two optional tree models are separately realized:
`Examples.AbstractDataTypes.treeTable_enumeration_model` uses the existing enumeration
decoder, and `Examples.AbstractDataTypes.treeTable_structural_model` uses the
independently proved structural decoder. The latter's insertion/presence/get
route uses the direct structural model laws; its enumeration field uses
the established valid-tree agreement. This is not a second proof that
silently defines both abstractions through the same enumeration.
`Examples.AbstractDataTypes.tree_models_agree_on_valid` and
`Examples.AbstractDataTypes.tree_models_differ_on_raw` show the exact
validity boundary. `Search.OrderedMap.EnumeratedTable.ModelLaws.totalTable_laws`
derives validity-qualified algebraic Table laws from a model contract;
it does not upgrade that contract to raw laws.
`Search.OrderedMap.EnumeratedTable.ModelLaws.finite_support` proves finite
support for each represented valid state, without restricting the ambient
type of optional functions.

Shared clients consume the existing interfaces and executors.
`Examples.AbstractDataTypes.table_two_writes` reuses the prior
`Examples.FunctionalMaps.table_two_writes` client.
`Examples.AbstractDataTypes.table_history_function`,
`Examples.AbstractDataTypes.table_history_empty` and
`Examples.AbstractDataTypes.three_raw_histories` connect arbitrary finite
write histories across functions, raw lists and raw trees.
`Examples.AbstractDataTypes.both_tree_model_histories` and
`Examples.AbstractDataTypes.raw_list_model_history` similarly consume all
seven model laws for arbitrary histories.
The connected `Examples.AbstractDataTypes.raw_client_results`,
`Examples.AbstractDataTypes.subset_client_results` and
`Examples.AbstractDataTypes.model_repeated_history_checked` use the same
repeated-write/default-valued query word across the three raw providers,
the two subtype providers and both tree models. The explicitly written
default remains distinguishable from absence by bound.

### Intrinsic validity and the unsorted unique-list exercise

`Examples.AbstractDataTypes.ValidTreeTable.Carrier` is the existing
`Search.OrderedMap.Tree` carrier. Empty and insertion reuse the actual
raw operations and their invariant proofs; get, bound and elements use the
stored tree projection. Its full
`Examples.AbstractDataTypes.ValidTreeTable.laws` and
`Examples.AbstractDataTypes.ValidTreeTable.unrestricted_enumeration_laws`
need no external BST premise. There is no second tree datatype or insertion
algorithm.

`Search.OrderedMap.AssociationListEnumeration.UniqueList` is exactly a
pair list whose projected keys are nodup. It does not impose sortedness.
`Examples.AbstractDataTypes.UniqueListTable.laws` supplies the complete final
interface, `Examples.AbstractDataTypes.UniqueListTable.elements_identity`
returns the stored list itself, and
`Examples.AbstractDataTypes.UniqueListTable.elements_set` gives the chosen
executable update: prepend the new pair after first-key erasure from the
old pair list. The source leaves this exercise implementation open; this
first-erasure update is the selected completion.

The actual pair/Sigma equivalence
`Search.OrderedMap.AssociationListEnumeration.aListEquiv` reuses
`Equiv.sigmaEquivProd` and the existing `AList` carrier.
`Search.OrderedMap.AssociationListEnumeration.toAList_set` proves that
the executed pair-list replacement corresponds to actual `AList.insert`;
`Search.OrderedMap.AssociationListEnumeration.lookup_toAList` relates
the actual first-match observations. Conversions are proof bridges: the
update executes directly on the pair list and does not traverse a converted
representation at runtime. The key list update and latest-write shadow law
are proved by `Search.OrderedMap.AssociationListEnumeration.set_keys`
and `Search.OrderedMap.AssociationListEnumeration.set_shadow`.
Only keys require decidable equality.

`Examples.AbstractDataTypes.unique_unsorted_is_legal` exhibits legal
keys `[2,0,1]`, proves their uniqueness and refutes strict sortedness.
`Examples.AbstractDataTypes.unique_replacement_entries`,
`Examples.AbstractDataTypes.unique_replacement_lookup` and
`Examples.AbstractDataTypes.unique_other_lookup` check exact replacement
order, same-key and other-key lookup.
`Examples.AbstractDataTypes.unique_update_aList_bridge`,
`Examples.AbstractDataTypes.unique_lookup_aList_bridge` and
`Examples.AbstractDataTypes.unique_aList_roundtrip` connect those actual
states to the common association-list owner.
`Examples.AbstractDataTypes.unique_repeated_write` checks literal latest
write wins. These instances complete the advanced prompt, including its
performance question under the measured choice below.

### Module-language adaptation, subsets and stored-length vectors

`Examples.AbstractDataTypes.TableSignature` keeps key, payload, default and
carrier abstract. The three simple String presentations expose progressively
more information: the first concrete package is transparent in Lean; the
second public presentation fixes String while taking default/key/carrier
as parameters; the third fixes String and its empty default while taking
key/carrier as parameters. The source's concrete instances are their
Nat/tree specializations. `Examples.AbstractDataTypes.stringSignature_payload`,
`Examples.AbstractDataTypes.stringSignature_default` and
`Examples.AbstractDataTypes.emptyStringSignature_default` make the exposed
equalities precise.

The generic clients are where abstraction matters.
`Examples.AbstractDataTypes.abstract_empty_client` has abstract payload,
carrier and default; `Examples.AbstractDataTypes.string_abstract_default_client`
exposes String while keeping the default abstract;
`Examples.AbstractDataTypes.abstract_carrier_empty_lookup` exposes String
and its empty default while keeping the state abstract.
Each valid result uses the supplied public table law. The relevant failed
literal, constructor, definitional-equality and reflexivity attempts are
checked with actual failed elaborations inside the proof. Their concrete
tree instantiation is `Examples.AbstractDataTypes.treeTable_empty_lookup`.
This expresses the source's information-hiding lesson without claiming that
a Lean namespace seals a transparent implementation.

`Examples.AbstractDataTypes.EvenNat` is the constructive even-number
subtype. `Examples.AbstractDataTypes.two` and
`Examples.AbstractDataTypes.twoInline` contain the concrete value 2 and its
evenness proof. Their value/proof projections remain executable/propositional
respectively; `Examples.AbstractDataTypes.even_two_from_subtype` uses the stored proof.
The SubtypeExamples aliases use the existing `Subtype` and `Exists`, with actual
constructors and projections. No second set type or classical-choice program
is introduced. The rejected generic extraction from an existential proposition
is distinguished from permitted propositional elimination and from the
computational witness already present in a subtype.

`Examples.AbstractDataTypes.StoredLengthVector` retains the exact source representation:
a pair of a list and a stored Nat, with a proof that the list length equals
that stored Nat. It is not replaced by an indexed vector with a different
carrier. `Examples.AbstractDataTypes.exampleVector` contains `([3,1,4],3)`.
`Examples.AbstractDataTypes.vectorCons` constructs a prepended list and
stored length plus one; `Examples.AbstractDataTypes.vectorAppend` constructs
ordered list append and the sum of stored lengths. The two correctness
theorems prove exact list projections, and
`Examples.AbstractDataTypes.vectorCons_length` and
`Examples.AbstractDataTypes.vectorAppend_length` prove the stored-length
equations. `Examples.AbstractDataTypes.vectorToList_length` connects
the stored count to actual length; the concrete combined example checks
both its full list and its stored count of seven. These are constructive
definitions with their invariant proofs, not existence-only replacements.

### Source-shaped queue laws and actual all-raw operations

The chosen list completion uses actual empty list, Boolean emptiness,
append-singleton enqueue, tail dequeue and default-valued head.
`Sequences.SourceQueue.lists_laws` proves all six algebraic laws.
In particular peek after enqueue equals peek on the old queue with the
enqueued value as its new default, and dequeue after enqueue has the exact
source conditional with the original queue in the true branch.
`Examples.AbstractDataTypes.ListQueue.source_operations` exposes all of
these actual operations at the source Nat specialization. The source leaves
the list implementation open; append-singleton is the selected completion.

The supplied two-list implementation is retained on every raw pair.
`Sequences.SourceQueue.twoListDecode` is front followed by reversed back.
Enqueue only pushes onto back. Dequeue and peek keep the source case order:
empty/empty, empty front with a nonempty back that is actually reversed, then
nonempty front. Dequeue returns the reversed tail paired with an empty back
in the middle case; peek returns only the observed value and leaves no
normalized state for the caller to retain.
`Sequences.SourceQueue.twoLists_absLaws` proves all four decoder equations
for all raw pairs and all defaults.
`Sequences.SourceQueue.twoListIsEmpty_decode` separately proves that the
actual empty test agrees with decoded list emptiness.

The separation between interfaces is witnessed by actual states.
`Sequences.SourceQueue.twoList_dequeue_enqueue_counterexample` uses
`q=([],[1])` and enqueued value 2: dequeue after enqueue is `([2],[])`,
whereas enqueue after dequeue is `([],[2])`. The source test is false, so
the literal Queue equation fails.
`Sequences.SourceQueue.twoList_counterexample_same_decode` proves that
both states still decode to `[2]`, and
`Sequences.SourceQueue.twoLists_not_laws` records failure of the complete
six-law contract.
Conversely `Sequences.SourceQueue.AbsLaws.with_isEmpty` proves that any
replacement empty test preserves the four decoder laws;
`Sequences.SourceQueue.model_empty_test_unconstrained` supplies one that
returns false even at empty. Thus no extra law is inferred from QueueAbs.

`Sequences.SourceQueue.twoListHead?` is an actual optional-head adapter
with the same source branches, not an independent queue representation.
`Sequences.SourceQueue.twoListPeek_eq_getD` relates it to default-valued
peek. `Sequences.SourceQueue.twoListFIFO` and
`Sequences.SourceQueue.twoList_simulation` instantiate the existing
`Sequences.AbstractFIFO.Ops` interface and simulation.
`Sequences.SourceQueue.twoList_run_decode`,
`Sequences.SourceQueue.twoList_client_eq`,
`Sequences.SourceQueue.twoList_representation_independent` and
`Sequences.SourceQueue.twoList_peek_run` reuse the existing arbitrary
command execution and clients. Exact enqueue-list and replicate equations
also establish concrete reachability.
`Examples.AbstractDataTypes.queue_source_client` and
`Examples.AbstractDataTypes.queue_source_peek_client` execute enqueue 7,
enqueue 8, delete, enqueue 9 through that common executor and observe 8.
The branch, raw-law and unconstrained-empty-test clients check the same
public contracts.

### Measured operations and the qualified efficiency claims

The resource models execute the represented operations and prove value
erasure; they do not assert native compiler timings. Every counted primitive
and reversal choice is explicit.

| Operation or realization | Actual counted work and checked result |
|---|---|
| Selected list enqueue | `Resources.SourceQueue.listEnqueueRun` executes actual singleton append through `Resources.ListAppend.copies` and charges one queue dispatch. `Resources.SourceQueue.listEnqueueRun_exact` gives the appended list and exactly `n+1` for a prefix of length `n`. This counts copied prefix cells plus dispatch, not a separate append-empty inspection. |
| Pair enqueue | `Resources.SourceQueue.enqueueRun` returns the actual pair with the new back head and costs one dispatch. |
| Empty/empty or nonempty-front peek/dequeue | Both reversal realizations cost one dispatch and do not execute the reversal callback. |
| Empty-front, nonempty-back source realization | `Resources.SourceQueue.peekRun` and `Resources.SourceQueue.dequeueRun` bind the actual output of `Resources.ListReversal.naiveRun` and add one dispatch. The structural reversal has `2R(n)=(n+1)(n+2)`, including `R(0)=1`. Thus nonempty-back cost `C` satisfies `2C=(n+1)(n+2)+2`. The truly empty queue still costs one because it takes the first branch. |
| Separate linear reversal realization | `Resources.SourceQueue.linearPeekRun` and `Resources.SourceQueue.linearDequeueRun` use `Resources.SymmetricCosts.reverseRun` with an empty accumulator. Their nonempty-back cost is `n+2`. The actual returned values agree with the source operations. |
| Selected unique-list replacement | `Resources.ListErase.setRun` executes the actual first-key erasure and prepends the new pair. One Boolean key-predicate call is counted per inspected element; predicate-internal work, empty inspection and new-head allocation are not included in this count. |

`Resources.SourceQueue.dequeueUsing` and `Resources.SourceQueue.peekUsing`
retain the three source branches and bind actual callback values.
Their generic erasure theorems require the callback's value to be list
reversal. The source and linear specializations discharge that premise;
value equality does not equate their costs.
`Resources.SourceQueue.peek_realizations_agree`,
`Resources.SourceQueue.linearPeekRun_cost_le` and
`Resources.SourceQueue.linearPeekRun_back_cost_lt` separate agreement
from the comparison of formal work.

For the linear realization, `Resources.SourceQueue.linearStep` measures
the existing enqueue/delete command type and
`Resources.SourceQueue.run_linearStep_potential` proves, for every raw initial
pair and command list,
`work + final back length ≤ initial back length + 2 * command count`.
The empty-start specialization gives zero initial credit.
`Resources.SourceQueue.linear_accounting` supplies the existing
`Resources.FIFOContracts.Accounting` interface;
`Resources.SourceQueue.linear_client_bound` uses its public abstract
budget. `Resources.SourceQueue.linear_sequential_bound` composes two
actual runs, consuming the first returned queue and spending initial credit
once. These are enqueue/dequeue contracts for the separately named linear
realization. The endpoint FIFO head observation is not charged, peek is not
a command in that executor, and no claim covers persistent branches that
reuse the same potential credit.

Peek has a different limitation in both realizations.
`Resources.SourceQueue.peekStepUsing` performs the actual observation and
returns its original queue. `Resources.SourceQueue.runPeeksUsing` wraps
the existing `Resources.run` on repeated unit commands.
`Resources.SourceQueue.run_peekStepUsing` and
`Resources.SourceQueue.runPeeksUsing_exact` prove return of the same queue
with exactly the number of repetitions times the single-peek cost.
`Resources.SourceQueue.EnqueueReachable` is defined through actual
enqueue commands in the existing FIFO executor, and
`Resources.SourceQueue.replicate_reachable` proves the required witnesses.

`Resources.SourceQueue.no_uniform_peek_charge` quantifies any Nat-valued
state potential; its change cancels because each peek returns the same
state. `Resources.SourceQueue.peeks_exceed_initial_credit` strengthens
this to any Nat-valued initial-credit function and any constant per-peek
charge: an actually enqueue-reachable queue and a positive repetition count
exceed the proposed total budget. Its source and linear specializations
supply the actual reversal lower bounds. The explicit default/value
parameters provide the inhabitant used to construct the witness family.
No unqualified constant-amortized bound for all source queue operations is
claimed.

The unique-list model measures the chosen completion's real traversal.
`Resources.ListErase.run_value` proves exact erasure to `List.eraseP`;
`Resources.ListErase.run_comparisons_le` gives the input-length upper bound.
`Resources.ListErase.run_absent` returns the unchanged list and exactly its
length in calls; `Resources.ListErase.run_first_hit` returns the actual
prefix/suffix with exactly prefix length plus one calls. First-match
erasure stops at the first matching key on a raw duplicated list.
`Resources.ListErase.pairSetRun_value`,
`Resources.ListErase.setRun_value` and
`Resources.ListErase.setRun_entries` connect actual measured outputs to
the pair-list and subtype operations.
`Resources.ListErase.setRun_toAList` relates the actual result to
`AList.insert` without executing a pair/Sigma conversion.
The erasure squares use the existing common resource square, not a second
executor or measurement framework.

The performance exercise has an unbounded family of actual legal inputs.
`Examples.AbstractDataTypeWork.uniqueRange` packages the pairs from
`List.range` with proved key uniqueness.
`Examples.AbstractDataTypeWork.unique_update_worst_case` inserts the
missing key equal to the range length, proves the full returned entries,
and gives exactly `n` predicate calls, including `n=0`.
`Examples.AbstractDataTypeWork.unique_update_no_uniform_bound` rules
out a constant bound, while
`Examples.AbstractDataTypeWork.unique_update_linear_growth` gives
ordinary real-cast asymptotic linear upper growth.
Front replacement costs one. Likewise
`Examples.AbstractDataTypeWork.list_enqueue_family`,
`Examples.AbstractDataTypeWork.list_enqueue_not_uniform` and
`Examples.AbstractDataTypeWork.list_enqueue_linear_growth` qualify
the selected append-singleton queue completion on actual unbounded lists.

The reachable `Examples.AbstractDataTypeWork.backFamily` uses a back
of length `n+1`.
`Examples.AbstractDataTypeWork.backFamily_source_double_cost` gives
the exact source formula;
`Examples.AbstractDataTypeWork.backFamily_source_quadratic_lower` and
`Examples.AbstractDataTypeWork.backFamily_source_quadratic_upper` give
natural quadratic bounds, and
`Examples.AbstractDataTypeWork.source_peek_quadratic_growth` states
ordinary real-cast `O(n²)`.
`Examples.AbstractDataTypeWork.backFamily_linear_cost` gives exactly
`n+3`, with `Examples.AbstractDataTypeWork.linear_peek_linear_growth`
stating ordinary real-cast `O(n)`. These are explicit execution families,
not arbitrary scalar costs attached to otherwise unrelated operations.

### Connected boundary cases and source erasure

The examples check empty/no-reversal dispatch, nonempty-front dispatch,
singleton source versus linear costs 4 versus 3, and an actually enqueued
back `[2,9,4]` whose front value is 4. Its source peek/dequeue cost is 11;
the linear cost is 5. Three repeated observations return the original pair
with costs 33 and 15.

The historical constructor tariff is recovered by
`Resources.ListReversal.constructorVisits` and
`Resources.SourceQueue.constructorPeekRun`. The exact law
`naiveRun_cost_eq_constructorVisits` removes the terminal reverse call and
one terminal append call per input element. For a nonempty back of length
`n`, `peekRun_cost_eq_constructorPeekRun` adds back `n + 2` terminal and
dispatch calls; other peek branches add one dispatch call. The history law
`run_peekStepUsing_cost_eq_constructor` derives the repeated difference through
`Resources.run`, preserving the unchanged queue state.
`Examples.AbstractDataTypeWork.three_back_constructor_peek`,
`repeated_constructor_peeks` and `reachable_peek_tariff_recovery` connect the
historical costs 6 and 18 to the current call costs 11 and 33 on the same
reachable three-enqueue state. These tariffs count different calls in the
same source execution; neither is a wall-clock cost.

`Examples.AbstractDataTypeWork.repeated_peeks_exceed_back_credit`
checks failure even after supplying the ordinary back-length credit.
`Examples.AbstractDataTypeWork.back_credit_is_required` checks why
arbitrary initial states need credit in the positive dequeue result.
`Examples.AbstractDataTypeWork.four_commands_budget_tight` retains
the final potential in a tight execution; the arbitrary-raw and sequential
history clients use the same public accounting result.
The front-hit, absent-hit, repeated-key, unsorted-unique, AList and
type-valued examples consume the same public operations and erasure lemmas.

All ten direct source/resource bridges are explicit in
`Examples.AbstractDataTypeWork.source_list_enqueue`,
`Examples.AbstractDataTypeWork.source_pair_enqueue`,
`Examples.AbstractDataTypeWork.source_pair_peek`,
`Examples.AbstractDataTypeWork.source_pair_linear_peek`,
`Examples.AbstractDataTypeWork.source_pair_dequeue`,
`Examples.AbstractDataTypeWork.source_pair_linear_dequeue`,
`Examples.AbstractDataTypeWork.source_history_peek`,
`Examples.AbstractDataTypeWork.source_unique_update`,
`Examples.AbstractDataTypeWork.source_unique_update_elements` and
`Examples.AbstractDataTypeWork.source_measured_update_lookup`.
They retain arbitrary raw queue inputs and defaults where applicable.
The last bridge proves source get and bound on the actual measured unique
update, including a stored value equal to the default.

The chapter's discussion of interfaces, representation choices, the
algebraic versus abstraction-function proof routes, type information and
subset-based validity is represented by these complete operations, laws
and consuming clients. Its ML/Rocq background references explain the
presentation; they do not add an unproved language-semantics claim.
Rocq tactic notation, hints, modules, sections and grading constants are
adapted to Lean's existing mechanisms. Transparent proof-building
definitions retain their actual projected data, and every grading-only
exercise receives the full requested implementation.

Comparative table efficiency continues to depend on the actual operation
and, for tree height bounds, the existing SearchTree hypotheses. This
chapter does not establish balance for arbitrary raw trees. The measured
models certify the specified primitive work and ordinary mathematical
asymptotics; they certify no physical sharing, machine allocation, constant
stack or native runtime identity. Extraction and realized machine operations
remain obligations of their later source chapters.

This section records the current checked source correspondence and precise
statement boundaries. Exact-candidate integration, proof-audit regression,
focused validation, both independent review axes, immediate candidate
verification, receiving whole-library gates and checkpoint acceptance are
tracked separately. This document does not itself mark CTB/BOOKS accepted.

## Remaining chapters

Preface, Perm, Sort, Multiset, BagPerm, Selection, Merge and Maps retain their
source-qualified treatments. SearchTree and ADT have complete current
correspondences recorded above, with validation and acceptance tracked
separately. The seven later units, Extract through Color, retain their complete
definition, exercise,
prose, source-algorithm, statement-review and acceptance obligations. The staged
sorting-specification draft's ordering and contents portions are now represented
through the current shared owners; its preservation
does not create a second current specification.

Existing sorting, selection, tree, queue, graph and resource libraries alone
do not establish chapter coverage. In particular, alternating-split mergesort
is not generally stable on equal-key payloads; default-valued tables differ
from optional finite maps; maximum priority queues differ from minimum or
key-deduplicating queues; and extraction assumptions need proved realizations.
The preserved source inventory and current local chapter tickets retain these
boundaries and the complete chapter sequence.

## Extract: comparison and sorting increment; chapter remains open

**This is a partial chapter correspondence. CTB-13 remains open.** The first
24 of the chapter's 34 declaration records have checked comparison/sorting
support below. The ten tree records, three remaining exercises, all fourteen
optional enumeration groups, resource/workload obligations and all thirteen
extraction/execution command obligations remain open. Existing checked
mathematical clients are not evidence of a standalone program run or native
performance. No full Extract, whole-book or receiving acceptance is asserted.

The complete VFA 2.1 primary `Extract.v` was read: 393 lines, 13,003 bytes,
SHA-256 `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d`.
Its auxiliary `test_searchtree.ml` was also read completely: 24 lines,
935 bytes, SHA-256
`109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279`.
The exact archive identity is recorded above. The immutable inventory counts
34 declaration records, four exercises and thirteen commands; the complete
[canonical Extract specification](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1011-Extract.md)
retains the unnamed prose, optional exercise and execution obligations.

### Current owners and mathematical boundaries

The current modules are `Applications.Representations.SignedComparison`,
`Applications.Sorting.DecodedInsertion` and `Examples.ExtractedPrograms`.
In the tables below, `SC` means namespace `Representations.SignedComparison`,
`DI` means `Applications.Sorting.DecodedInsertion`, and `EP` means
`Examples.ExtractedPrograms`. These abbreviations name actual declarations;
the recovery drafts described later are outside the project import closure.

The comparison interface uses ordinary parameters `W : Type u`,
`decode : W → Int`, and executable Boolean `ltb`/`leb`, with their exact
reflection laws. It introduces no new comparison class or arithmetic axiom.
`SC.strictDecision` and `SC.nonstrictDecision` retain the supplied Booleans.
Only `SC.linearOrder` and `SC.linearOrderOfStrict` require decoder injectivity
to obtain a lawful order on original values. The strict-only adapter derives
non-strict comparison by reversing and negating the strict comparison.

The order's explicit LT/LE decision fields, derived equality, min/max and
compare use these adapters. A fresh inferred `decide (a < b)` can unfold the
transported relation and select a decoded-Int comparison instead. The public
`SC.linearOrder_decide_lt`, `SC.linearOrder_decide_le` and
`SC.linearOrderOfStrict_decide_lt` therefore state their actual `Decidable`
field arguments explicitly. The executable sort receives only its Boolean
comparison, and the Int64 comparisons explicitly call `Int64.decLt`/`decLe`.
The native override remains an ordinary compiler/runtime trust boundary.
Proofs in `Prop` are erased; a decoder or specification function stored as data
in `Type`, including in a `Squares.Square`, is not erased merely by its name.

`DI.insert` and `DI.sort` call the existing `List.orderedInsert` and
`List.insertionSort`; their nil/cons equations preserve left insertion on ties
and tail-first recursion. Arbitrary-comparator permutation is on original
values, in source input-to-output direction. Decoded sortedness and stability
need comparison reflection, with **no injective-decoder premise** and no
payload equality, order, default or inhabitance assumption. `DI.Sorted` is the
source adjacent `List.IsChain` observation; `DI.sorted_iff_keySorted` uses
integer transitivity to connect it to all-pairs ordering. `DI.sort_spec` reuses
`insertionOn_spec`, and `DI.sort_eq_sortOn` relates the result to independent
stable merge sort without equating their work.

`DI.map_insert` and `DI.map_sort` retain independent source/target universes and
require only comparator compatibility. Decoder specialization gives insertion
and whole-sort equations. `DI.listRep`, `DI.insertSquare` and `DI.sortSquare`
package concrete `Type 0` list decodings through the existing same-universe
`Squares.Rep`; that packaging does not restrict the generic mapping theorems.

Three realizations stay distinct. Mathematical `Int` is unbounded. Signed
`BitVec w` uses `slt`/`sle`, preserving the ordinary unsigned global order;
`SC.word_representable_iff` and conversion laws retain positive-width and
range premises. `BitVec 63` has range `[-2^62,2^62)`. `Int64` has range
`[-2^63,2^63)`. Width zero has exactly the decoded image `{0}`, with strict
comparison false and non-strict comparison true. Neither finite decoder is
claimed surjective onto Int. `SC.word_add_modular` gives balanced remainder
modulo `2^w`; `SC.word_add_no_overflow` retains the actual no-overflow premise.
The checked 4-bit case decodes `7 + 1` to `-8` while the decoded inputs sum to
`8`; the positive guarded case decodes `2 + 1` to `3`. No addition law is
assumed by sorting.

### All 34 source records

“Supported” below means the comparison/sorting mathematics and source adapter
are present; it does not close the chapter's execution or acceptance gates.
“Open” retains the full original statement, including all raw-tree scopes.

| Source record | Current disposition and exact owner |
| --- | --- |
| `Extract.ins@26` | Supported: `EP.ins`, `EP.ins_nil`, `EP.ins_cons` reuse the accepted Nat insertion program with its exact natural non-strict test. |
| `Extract.sort@32` | Supported: `EP.sort`, `EP.sort_nil`, `EP.sort_cons`, `EP.sort_correct`; `EP.nat_sort_adapter` connects the Boolean adapter to that accepted program for every list. |
| `Extract.insZ@74` | Supported: `EP.insZ`, `EP.insZ_cons` specialize `DI.insert` at `SC.intLeb`. |
| `Extract.sortZ@80` | Supported: `EP.sortZ`, `EP.sortZ_cons`, `EP.sortZ_correct`, `EP.sortZ_stable`; the full correctness requested by prose is included. |
| `Extract.int@113` | Supported as ordinary carrier parameter `W`, with concrete Int, all-width signed BitVec and Int64 realizations in `SC`; no global source axiom. |
| `Extract.Abs@120` | Supported as ordinary decoder parameter; `DI.map_decode_insert` and `DI.map_decode_sort` prove compatibility, without surjectivity. |
| `Extract.Abs_inj@121` | Supported as an explicit hypothesis where needed, with `SC.int_decode_injective`, `SC.word_decode_injective`, `SC.int64_decode_injective`; sorting deliberately needs no such hypothesis. |
| `Extract.ltb@126` | Supported by the supplied strict Boolean and `SC.intLtb`, `SC.wordLtb`, `SC.int64Ltb`. |
| `Extract.ltb_lt@128` | Supported by explicit strict reflection and `SC.intLtb_true_iff`, `SC.wordLtb_true_iff`, `SC.int64Ltb_true_iff`. |
| `Extract.leb@130` | Supported by the supplied non-strict Boolean and `SC.intLeb`, `SC.wordLeb`, `SC.int64Leb`. |
| `Extract.leb_le@132` | Supported by explicit non-strict reflection and `SC.intLeb_true_iff`, `SC.wordLeb_true_iff`, `SC.int64Leb_true_iff`. |
| `Extract.int_ltb_reflect@162` | Supported: `SC.strictDecision`, `SC.decide_strictDecision`, `SC.strict_false_iff` retain both branches of supplied strict comparison. |
| `Extract.int_leb_reflect@168` | Supported: `SC.nonstrictDecision`, `SC.decide_nonstrictDecision`, `SC.nonstrict_false_iff`. |
| `Extract.Z_eqb_reflect@174` | Supported: `SC.intEqb_true_iff`, `SC.intEqb_false_iff`. |
| `Extract.Z_ltb_reflect@180` | Supported: `SC.intLtb_true_iff`, `SC.intLtb_false_iff`. |
| `Extract.Z_leb_reflect@186` | Supported: `SC.intLeb_true_iff`, `SC.intLeb_false_iff`. |
| `Extract.Z_gtb_reflect@192` | Supported: `SC.intGtb_true_iff`, `SC.intGtb_false_iff`, with reversed strict operands. |
| `Extract.Z_geb_reflect@198` | Supported: `SC.intGeb_true_iff`, `SC.intGeb_false_iff`, with reversed non-strict operands. |
| `Extract.bdestruct_guard@211` | Supported language adaptation: ordinary `by_cases`, reflection and `simp`, exercised by `EP.choose_minimum` and `DI.insert_eq_orderedInsert`; no custom tactic framework. |
| `Extract.bdall@225` | Supported proof-method adaptation: the same branch laws compose in `EP.comparison_equality_branch`, retaining injection for equality of originals; `EP.integer_reflection_orientations` separates comparison directions. |
| `Extract.ins_int@233` | Supported: `EP.decodedInsert` calls `DI.insert`; `DI.insert_nil`/`insert_cons` expose the exact supplied-Boolean recurrence. |
| `Extract.sort_int@239` | Supported: `EP.decodedSort` calls `DI.sort`; `DI.sort_nil`/`sort_cons` retain the source recursion. |
| `Extract.sorted@253` | Supported: `EP.sorted`, `DI.Sorted`, `DI.sorted_nil`, `DI.sorted_singleton`, `DI.sorted_cons`, `DI.sorted_cons_iff`, `DI.sorted_iff_keySorted`. |
| `Extract.sort_int_correct@270` | Supported: `EP.decodedSort_correct` retains original-value input-to-output permutation and adjacent decoded order for every input; `EP.decodedSort_stable` and `EP.sort_decode` strengthen and connect the result. |
| `Extract.key@282` | Open: reuse the same carrier as tree keys, with no added arithmetic structure. |
| `Extract.tree@284` | Open: specialize the existing `BinaryTree (W × V)` carrier with exact empty/node presentation and independent key/payload universes. |
| `Extract.empty_tree@291` | Open: specialize existing empty without requiring a payload default. |
| `Extract.lookup@293` | Open: retain caller default and the exact supplied query/root then root/query strict tests. |
| `Extract.insert@301` | Open: retain both tests, persistence and replacement by the newly supplied key/value on equality. |
| `Extract.elements_aux@309` | Open: actual fast accumulator traversal; prove the all-raw-tree arbitrary-suffix equation and map compatibility. |
| `Extract.elements@316` | Open: fast traversal at the empty suffix, connected to accepted inorder enumeration. |
| `Extract.lookup_empty@319` | Open: every carrier, payload, caller default and key; no BST premise. |
| `Extract.lookup_insert_eq@324` | Open: every raw tree; strict reflection supplies irreflexivity, without adding BST or decoder injectivity unnecessarily. |
| `Extract.lookup_insert_neq@332` | Open: every raw tree and distinct original keys, retaining the injection/comparison requirements; decoded inequality cannot simply replace the source premise. |

### All four exercises and the complete optional enumeration request

| Exercise and source lines | Current status |
| --- | --- |
| `sort_int_correct`, 263–275, three stars | Mathematical support present: `EP.decodedSort_correct`, Int/word/Int64 correctness and decoding clients, noninjective-decoder and labelled-payload cases. Chapter execution and acceptance remain open. |
| `lookup_insert_eq`, 323–329, one star | Open: exact universal raw-tree law, same-key replacement example and concrete comparison realization. |
| `lookup_insert_neq`, 331–337, two stars | Open: exact original-key inequality, justified injection dependency, universal raw-tree scope and connected distinct-key case. |
| `int_elements`, 339–345, four stars, optional | Open in full. The prompt has no named starter theorem; every group below is required, and the optional label waives none. |

The fourteen `int_elements` groups remain open independently of their draft
candidate names. They preserve the accepted SearchTree/ADT distinctions:

| Group | Required contract and boundary |
| --- | --- |
| IE01 — invariant and preservation | All-node `ForallT`, full-subtree decoded strict BST separators, valid empty, insertion preservation and all-node insertion transport. Immediate-child checks are insufficient. |
| IE02 — raw bound/search algebra | Empty, same-key and distinct-original-key lookup/bound laws and false-bound default lookup. No BST premise on these raw laws; injection remains where distinct originals require it. |
| IE03 — raw completeness | Successful lookup/bound gives the original query/value pair in enumeration on raw trees, with the relevant comparison and injection laws. |
| IE04 — guarded soundness | BST plus enumerated pair gives bound and lookup value for every caller default. Retain the invariant. |
| IE05 — predicate/relation transport | Arbitrary all-node predicates and relation-to-a-key forms transfer to enumeration without BST or comparison premises. |
| IE06 — both absence directions | False bound implies no entry under BST; no entry for any value implies false bound on raw trees, retaining the comparison/injection requirements of the relevant raw law. |
| IE07 — bound-value witness | Preserve `∃ value, ∀ default`, rather than a value chosen after the default. |
| IE08 — ordering | Strict projected decoded-key order and the source adjacent non-strict observation. |
| IE09 — uniqueness | `Nodup` of projected original keys under the strict decoded BST, not merely nodup of complete pairs. |
| IE10 — actual fast traversal | All raw trees and arbitrary suffixes; fast/inorder equivalence, empty result and map compatibility. No value equality is promoted to a cost equality. |
| IE11 — enumeration after update | Exact list insertion tests/replacement and separator split with both separator premises; the tree/enumeration update equation retains BST. |
| IE12 — list/enumeration partial model | Head-winning list meaning, actual optional presence/default boundary, lookup/bound/update refinement, complete existing ADT law records and finite-history use. |
| IE13 — independent structural model | Retain the independent collision-removing structural abstraction and its lookup/update route; prove coherence with enumeration under the original hypotheses. |
| IE14 — canonical enumeration | Valid trees with equal complete partial meanings have equal canonical inorder lists. Equality of one default-valued lookup is insufficient. |

Malformed-tree membership, stored-default bindings and distinct originals with
colliding decoded keys remain required connected tree cases. Raw structural
identity, map observation and physical sharing remain different claims.

### Connected sorting and representation clients

`EP.sortZ_signed_repeats_contract` connects the independently expected output
`[-3,-3,0,1,2]` to the universal contract for `[-3,2,-3,0,1]`.
`EP.sortZ_empty` and `EP.sortZ_singleton` use the public recurrence.
`EP.constant_decoder_not_injective` proves the Bool-to-zero decoder is not
injective, while `EP.constant_decoder_preserves_originals` and
`EP.constant_decoder_source_contract` preserve the original Boolean values
and stable result. `EP.labelled_payloads` quantifies over arbitrary payloads
in their own universe and keeps the earlier key-2 record before the later one.

`EP.four_bit_signed_sort` uses `EP.word_sort_decode` to obtain
`[-8,-1,-1,0,7]`, and `EP.four_bit_original_permutation` separately retains the
original words. `EP.zero_width_sort` uses generic sortedness/fixed-point laws.
`EP.word_upper_bound_unrepresentable` and `EP.word_decoder_not_surjective`
expose the finite boundary for every width. `EP.int64_signed_endpoints_sort`
uses the native-carrier decoding theorem at `-2^63`, `2^63-1`, -1 and zero;
`EP.int64_upper_bound_unrepresentable` excludes `2^63`. These are mathematical
clients of the actual definitions, with no standalone timing claim.

### All thirteen extraction/execution command obligations remain open

Lean's ordinary Bool, List and Prod and the checked callable sort definitions
supply mathematical prerequisites. Lean compilation/evaluation replaces the
source's Coq-to-OCaml workflow, but the full execution protocol still needs a
standalone driver, both verified execution paths and retained observations.
No row below is closed by kernel reduction alone.

| Source line and command role | Remaining execution obligation |
| --- | --- |
| 40 — extract Nat sort | Open: documented execution/inspection of the actual `EP.sort` specialization. |
| 47 — recursive Nat extraction | Open: record the corresponding executable dependency closure and execution path. |
| 58 — native Bool directive | Open as workflow evidence: use the existing actual Bool comparisons in the delivered runnable client. |
| 59 — native list directive | Open as workflow evidence: ordinary List interoperability in that client, without a duplicate carrier. |
| 60 — repeat recursive extraction | Open: demonstrate the same source sort through the ordinary native datatypes and closure. |
| 86 — recursive Int sort extraction | Open: run the actual `EP.sortZ` whose mathematical correctness is already proved. |
| 114 — inline integer carrier | Open: identify and execute the proved runtime realization, distinguishing unbounded Int, BitVec63 and Int64. |
| 127 — inline strict comparison | Open: verify the runnable client's actual chosen signed strict operation and dependency path. |
| 131 — inline non-strict comparison | Open: corresponding non-strict path, including tie behavior. |
| 245 — recursive abstract-word sort | Open: execute the actual finite-runtime specialization and retain result checks. |
| 349 — native pair directive | Open: ordinary Prod/payload preservation through the runnable tree enumeration. |
| 350 — recursive table extraction | Open: deliver and execute the complete source empty/insert/lookup/elements interface. |
| 358 — standalone tree extraction | Open: standalone Lean entry point, direct-runner and compiled-executable paths, reproducible workload protocol and retained outputs. |

Source imports, notation, hints, extraction-output-directory and IDE mechanics
are language adaptations, not additional mathematical assumptions. Proof/body
inspection does not establish the correctness of Lean's compiler, its native
overrides, or Coq extraction.

### Resource, workload and recovery-draft boundary

The source's unary comparison claim in terms of operand difference is corrected
by the existing `Resources.UnaryComparison` terminal-call-inclusive
`min n m + 1` model and its equal-input obstruction. That model is distinct from
Lean native Nat and from CPU time. Binary comparison needs a representation-size
cost model; fixed-width primitive charges require an explicit machine model.
Reflection alone establishes neither constant time nor constant allocation.
Full Extract resource/workload integration remains open: exact finite write/query
histories, actual-path measured erasure, consecutive-chain construction/search
counts, and finite signed-range transport. BST correctness alone proves no
logarithmic height or random-workload expectation.

The supplied ML program builds its tree before starting its CPU timer, then
times queries with key generation inside the loop. Its printed insertion/lookup
label is inaccurate and it discards the hit count. Random queries make fresh
draws, so they need not all hit; consecutive generated keys are increasing and
produce an unbalanced chain. The Lean driver must preserve this scope honestly,
check and consume results against an independent model, retain seed/generator,
size/range/list identity, clock/unit/mode and exact commands, and distinguish a
source-shaped RNG-in-query experiment from a controlled pre-generated list run.
Zero-size handling, invalid ranges, stored defaults, duplicates and misses,
negative/endpoint keys, deterministic replay and both actual execution modes
remain required. Historical source timings are not current Lean observations.
No such standalone execution or measurement is claimed by this increment.

Five **uncompiled recovery drafts** are preserved separately from the project
import closure. Their names describe proposals only:

| Preserved draft | Proposed continuation; current status |
| --- | --- |
| `Basic.lean` | Minimal raw LT/DecidableLT seam for the existing ordered map; proposed replacement only, not an applied change to the checked owner. |
| `DecodedKeys.lean` | Boolean-only tree wrappers, comparison-free mapping/traversal and weak decoding laws; uncompiled. |
| `DecodedKeysModels.lean` | Original-key raw laws, complete enumeration/ADT models and structural coherence continuation; uncompiled. |
| `Workload.lean` | Finite writes/queries, source consecutive family and model-based observations; uncompiled. |
| `SearchTreeWorkload.lean` | Measured source workload, exact erasure/counts and bounded-word transport; uncompiled. |

Their static inventories and recovery guides preserve useful mathematical work,
but no current compiler evidence, theorem acceptance, chapter progress closure,
resource claim or runtime result follows from their existence. Promotion requires
fresh elaboration, affected-import checking, complete statement assessment,
connected clients and the ordinary candidate workflow. This partial section
preserves the entire original Extract requirement; CTB-13 stays open before
Redblack. Exact-candidate proof audit, independent Standards/Spec reviews,
receiving whole-library acceptance and durable checkpoint publication are tracked
separately from this correspondence.

## Extract: tree models and finite workloads; execution remains open

This increment advances the tree and pure-workload portion of the preceding
Extract correspondence. The earlier comparison/sorting section remains an
unchanged historical account of checkpoint 036. Its first 24 source-record
dispositions continue to apply. The ten tree records and the three remaining
mathematical exercises now have the applications below, including every one of
the fourteen groups in the optional `int_elements` exercise. These mathematical
results do not complete Extract: the measured-workload refinement, standalone
execution, timing protocol and all thirteen extraction-command adaptations
remain open. CTB-13 remains open before Redblack.

The authoritative source is still the complete VFA 2.1 `Extract.v` and its
`test_searchtree.ml` companion, with the archive, source and canonical-plan
identities recorded above. This addition retains their full scope, including
unnamed prose obligations. It introduces no replacement tree carrier, recursive
search algorithm, list model, operation interface, comparator hierarchy or
compiler-correctness assertion.

### Applied owners and execution boundary

In this section, `OM` denotes `Search.OrderedMap`, `DK` denotes
`Search.OrderedMap.DecodedKeys`, `WL` denotes `Search.OrderedMap.Workload`, and
`ET` denotes `Examples.ExtractedTrees`. `DK` declarations reside in the separate
`DecodedKeys.lean` and `DecodedKeysModels.lean` owners. The existing
`Search.OrderedMap.EnumeratedTable`, `Search.OrderedMap.SourceModel` and
`Search.TotalTable` interfaces, the association-list observation owner, and
`Search.OrderedTree` retain their original contracts.

The change to `Applications/Search/OrderedMap/Basic.lean` separates the existing
`lookup`, `pathObserve`, `bind` and `all_bind` definitions/theorem into a section
requiring only `LT` and its supplied `DecidableLT`. Their recursive branch
bodies remain the existing algorithms. `OM.lookup_bind_self_of_irrefl` exposes
the exact weak same-key premise, `∀ key, ¬ key < key`, without BST, a linear
order or a key-equality decision. The existing linear-order laws and valid-tree
interface remain separately available.

`DK.lookup?`, `lookup`, `bound`, `insert` and `kvsInsert` receive the actual
Boolean strict comparison. A private ordinary `LT`/decision adapter interprets
its result as equality to `true`; their executable arguments contain no
decoder, reflection law or injection proof. Their equations retain the source
test order, first `ltb query stored`, then `ltb stored query`, and replacement
stores the newly supplied original key and payload. `lookup` applies the
caller's `getD` default to the optional result; `bound` observes `isSome`.
`elementsAux` and `elements` reuse the accepted fast traversal and require no
comparison at all.

The weak mapping/operation bridges use strict reflection alone. The complete
original-key table/model contracts additionally install the previously checked
`Representations.SignedComparison.linearOrderOfStrict` along an injective
decoder. The proofs explicitly select that order's `toDecidableLT` when invoking
the ordered implementation. This retains the decision-field distinction
established in checkpoint 036: a newly inferred `decide` after unfolding a
lifted relation is not evidence that the supplied comparator is being executed.
`DK.ops` packages the Boolean-only programs themselves; its recurrence-based
equalities to existing lawful operations are separate proofs. Generic `WL`
operations receive the actual abstract `LinearOrder` dictionary. The connected
Int workload uses the corresponding `DK` operation bridge. No global signed
BitVec instance is introduced.

Key and payload universes are independent throughout these tree, traversal,
model and workload contracts. `WL.bindAll_append` also retains an independent
state universe. Payloads require no equality, order or inhabitance. The
type-valued-payload clients below exercise this boundary; a source `V : Type`
presentation does not restrict every Lean payload to `Type 0`.

### Remaining ten source records

The first 24 records remain mapped by the comparison/sorting section. The
following table completes the mathematical mapping of all 34 inventory
records; it does not discharge the separate execution commands.

| Exact source record | Current declaration/application and preserved scope |
| --- | --- |
| `Extract.key@282` | `ET.Key W` is exactly the supplied carrier, with no additional arithmetic structure. |
| `Extract.tree@284` | `ET.Tree W V`, `ET.nil` and `ET.node` reuse `BinaryTree (W × V)`; `ET.node` preserves source left/key/value/right argument order and independent universes. |
| `Extract.empty_tree@291` | `ET.emptyTree` is `ET.nil`, without requiring a payload default. |
| `Extract.lookup@293` | `ET.lookup` aliases `DK.lookup`; `ET.lookup_nil`, `ET.lookup_node` and `DK.lookup?_node` expose the exact two Boolean tests and caller default on every raw tree. |
| `Extract.insert@301` | `ET.insert` aliases `DK.insert`; `ET.insert_nil`, `ET.insert_node` expose persistent insertion and the equality branch's replacement of both original key and value. |
| `Extract.elements_aux@309` | `ET.elementsAux` aliases `DK.elementsAux`; `ET.elementsAux_nil`, `elementsAux_node`, `elementsAux_eq` give the actual accumulator recurrence and `entries t ++ suffix` for every raw tree and arbitrary suffix. |
| `Extract.elements@316` | `ET.elements` aliases the fast traversal at `[]`; `ET.elements_eq` records that definition, while `DK.elements_eq` identifies it with the existing inorder list on all raw trees. |
| `Extract.lookup_empty@319` | `ET.lookup_empty` quantifies over any supplied Boolean comparison, key and caller default; no reflection, injection or invariant premise is added. |
| `Extract.lookup_insert_eq@324` | `ET.lookup_insert_eq` uses strict reflection on every raw tree, arbitrary payload and caller default. `DK.lookup_insert_self_of_irrefl` exposes the still weaker sufficient premise. No decoder injection or BST is required. |
| `Extract.lookup_insert_neq@332` | `ET.lookup_insert_neq` retains distinct **original** keys, arbitrary raw tree, payload and default. Decoder injection and strict reflection are explicit; the theorem has no BST premise. |

### All four exercises and the complete optional enumeration transfer

`decodedSort_correct` retains the original-value input-to-output permutation,
decoded adjacent sortedness, stable-key strengthening and concrete clients from
checkpoint 036. The current `ET.lookup_insert_eq` and `lookup_insert_neq`
discharge the two source tree admissions with the scopes just stated.
`ET.word_lookup_insert_eq`/`word_lookup_insert_neq` specialize them at every
BitVec width; `ET.int64_lookup_insert_eq`/`int64_lookup_insert_neq` use the
proved Int64 decisions. `ET.signed_history_last_write` and
`signed_history_lookup` connect same-key replacement, other-key retention and
absence on an actual signed history. None of these mathematical exercise
dispositions claims that a standalone program has run.

The unnamed four-star optional `int_elements` exercise is represented by every
group below. All entries are applications of the existing SearchTree and ADT
owners through the explicit comparison/invariant bridges; the exercise is not
reduced to a subset of convenient named source records.

| Group | Current declarations and exact premises |
| --- | --- |
| **IE01 — Full-subtree invariant and preservation** | `DK.ForallT`, `BST`, `bst_empty`, `bst_iff_mapKeys` and `bst_insert` use strict decoded separators for every node of both subtrees. `all_insert` preserves any all-node predicate for arbitrary supplied Boolean comparison. `bst_insert` needs strict reflection and the initial BST, but no decoder injection. |
| **IE02 — Raw bound/search laws** | `lookup_empty`, `lookup?_insert_eq`, `lookup_insert_eq`, `lookup?_insert_neq`, `lookup_insert_neq`, `bound_empty`, `bound_insert_eq`, `bound_insert_neq` and `bound_default` have no BST premise. Same-key laws use reflection; distinct-original-key laws additionally use injection. `bound_default` is valid for arbitrary Boolean comparison and every default. |
| **IE03 — Raw completeness** | `mem_elements_of_lookup?` turns successful optional search into membership of the exact original key/value pair, using injection and reflection but no BST. `elements_complete` retains both presence and the observed default-valued result, and likewise remains valid on every raw tree. |
| **IE04 — Guarded soundness** | `lookup?_eq_some_of_mem` and `elements_sound` assume decoded BST and actual pair membership. Strict reflection suffices without injection. Soundness includes `bound = true` and the same payload for **every** caller default. |
| **IE05 — All-node and relation transport** | `all_mapKeys`, `all_elements`, `forallT_elements_iff` and `relation_elements` transport arbitrary node predicates and relations to a key. These statements do not acquire a BST, comparison or injection premise. |
| **IE06 — Both absence directions** | `absent_no_entry` uses BST and reflection to infer no enumerated payload from false bound. `no_entry_absent` uses absence of every payload to infer false bound on an arbitrary raw tree, with injection and reflection. `strong_elements` packages these differently scoped fields in the accepted interface. |
| **IE07 — Default-independent witness** | `bound_value` states exactly `∃ value, ∀ default, lookup ltb default key t = value` from true bound. The witness precedes the default quantifier, and no order law, injection or BST is assumed. |
| **IE08 — Strict and source ordering** | `decoded_keys_pairwise` and `keys_pairwise` prove strict order of decoded projected keys under decoded BST; `keys_sorted` derives the source non-strict adjacent chain. None requires decoder injection or any comparison/order on payloads. |
| **IE09 — Original projected-key uniqueness** | `keys_nodup` proves `((elements t).map Prod.fst).Nodup` under decoded BST, even when the decoder is globally noninjective. It does not substitute nodup of whole pairs. `strong_elements` exposes the same interface field under the complete canonical parameters. |
| **IE10 — Actual fast traversal** | `elementsAux_empty`, `elementsAux_node`, `elementsAux_eq`, `elements_eq`, `elements_empty`, `entries_mapKeys`, `map_elementsAux` and `map_elements` cover every raw tree and arbitrary suffix. Mapping changes only keys and preserves payloads; comparison, injection and BST are absent. `elements_sound` applies to this actual fast enumeration with its original BST premise. |
| **IE11 — Exact enumeration update** | `kvsInsert_empty`, `kvsInsert_cons` and `kvsInsert_eq_ordered` preserve the two-test/replacement list recurrence. `kvsInsert_split` retains both strict decoded separator premises, including the source right-side condition. `elements_insert` states the exact fast-enumeration equality under BST. These complete-contract results retain the canonical injection/reflection parameters. |
| **IE12 — List/enumeration partial meaning and ADT laws** | `listAbs`, `listAbs_empty`, `listAbs_cons` reuse head-winning `listObserve`; `listAbs_kvsInsert` applies to every binding list. `enumAbs`, `enumAbs_empty`, `enumAbs_elements`, `enumAbs_lookup`, `enumAbs_bound`, `enumAbs_default` and `enumAbs_insert` preserve the optional-map/default seam and each BST guard. `ops`, `table`, `observations`, their existing-owner equalities, `table_laws`, `enumerated_laws`, `strong_elements` and `model_enum_laws` instantiate the existing contracts. Base-table validity is `True`; validity is retained for guarded enumeration/model fields. `enumAbs_setAll` handles arbitrary chronological histories. |
| **IE13 — Independent structural meaning** | `mapOfTree` reuses `SourceModel.mapOfTree`, whose child union removes collisions symmetrically. `mapOfTree_empty`, `mapOfTree_lookup`, `mapOfTree_bound`, `mapOfTree_default` and `mapOfTree_insert` transfer that independently proved structural route. Its lookup/update proofs invoke the structural owner directly, rather than deriving them from enumeration coherence. `model_structural_laws` and `mapOfTree_setAll` retain its seven-field interface and arbitrary histories. `enumAbs_eq_mapOfTree` and `elements_relate_structural` assert coherence under BST. |
| **IE14 — Canonical enumeration** | `elements_eq_of_enumAbs_eq`, `elements_eq_of_lookup?_eq` and `elements_eq_of_mapOfTree_eq` require both trees to satisfy BST and their complete partial meanings, or all optional lookups, to agree. Equality at one default-valued observation is insufficient. `ET.canonical_workload_histories` and `reordered_distinct_histories` consume this result for actual finite histories. |

The two `model_*_laws` results preserve the existing seven `ModelLaws` fields:
empty validity, insertion preservation, empty meaning, bound, get, set and
elements. In particular the field orientations remain
`write key value (Abs t) = Abs (set key value t)` and
`Abs t = listObserve (elements t)`. The separate generic history theorem
states the resulting abstraction after chronological `setAll` as `writeAll` of
the starting abstraction. The standalone update equations may expose the
symmetric equality without changing the interface orientation.

`lookup?_finite_support`, `listAbs_finite_support`, `enumAbs_finite_support`
and `mapOfTree_finite_support` give an explicit finite list containing every
key with a `some value` observation. They apply to the corresponding **raw**
finite tree/list input under the canonical injection/reflection parameters;
they require no BST. This is represented-state finiteness. The ambient
`Meaning κ ν = κ → Option ν` is still an unrestricted function type, and no
theorem claims every partial meaning has finite support.

### Pure finite workloads: all 43 declarations

`Applications/Search/OrderedMap/Workload.lean` supplies a pure reusable client
with 43 explicit declarations. `buildFrom` executes the existing chronological
`bindAll` over `rawTrees`; it returns the actual resulting tree. `model` is the
independent first-binding list lookup on the **reversed** write history, so the
last chronological write wins. It is not defined by tree lookup. `queryResults`
retains `Option` results, and `queryValues` applies the caller default afterward.

| Declaration group | Preserved contract |
| --- | --- |
| `model`, `listLookup_constant` | Independent reverse-history observation and the exact constant-payload membership equation; only `DecidableEq κ` is required. |
| `bindAll_append` | Arbitrary operations and initial state: execute the first history and then the second. Key, payload and state universes remain independent; no map laws are required for this execution identity. |
| `sourceWrites` | Preserve key order while assigning the source payload `Nat` value `1`. |
| `sourceIndices`, `sourceIndices_zero`, `sourceIndices_succ`, `sourceIndices_length`, `mem_sourceIndices`, `sourceIndices_consecutive` | Use `(List.range' 1 n).reverse`; zero gives `[]`, successor gives `(n+1) :: sourceIndices n`, length is `n`, and membership is exactly `0 < j ∧ j ≤ n`. The actual source generator maps this descending schedule to ascending `List.range n`: `map (fun j => n-j) (sourceIndices n) = List.range n`. |
| `expectedHits` | Count each query occurrence whose key belongs to the original insertion history. This independent checker needs only decidable key equality, with no order, tree, randomness or timing premise. |
| `buildFrom`, `build`, `buildFrom_nil`, `buildFrom_cons`, `buildFrom_append`, `build_snoc`, `buildFrom_eq_setAll` | Execute chronological histories through the existing map/total-table owners, including arbitrary initial raw trees, append and final-write laws, and exact equality with `TotalTable.setAll` for any default. |
| `queryResults`, `queryValues`, `buildFrom_lookup`, `build_lookup`, `queryResults_model`, `queryValues_model` | Observe the actual built tree. On an arbitrary starting raw tree, lookup is `writeAll` of its direct `pathObserve`; starting from empty gives the independent reverse-history model. Query order, duplicates, absence and arbitrary payload/default are retained. |
| `buildFrom_ordered`, `build_ordered`, `build_entries_lookup`, `build_entries_keys_nodup`, `build_entries_keys_sorted` | Preserve an assumed initial invariant, derive it from empty, identify enumerated pairs with exact model bindings, and prove strict order/nodup of projected keys. No payload equality/order is introduced. |
| `buildKeys`, `queryHits`, `hits` | Build payload-1 bindings and count actual default-0 query values equal to `1`; the independent checker is not used to compute these tree operations. |
| `buildKeys_lookup`, `buildKeys_ordered`, `buildKeys_bound`, `buildKeys_elements_mem`, `queryValues_source` | Actual lookup/presence/enumeration and the entire returned query list agree with membership in the original insertion history. Enumerated payloads are exactly `1`. |
| `hits_eq_expected`, `hits_all`, `hits_self`, `hits_le_queries` | Every finite workload agrees with the independent membership count. Full success requires the explicit per-query membership premise; querying the same history is a valid specialization, and hits never exceed query-list length. |
| `source_consecutive_hits`, `source_schedule_hits` | Both consecutive histories yield `n` hits, including zero size. The latter consumes the actual descending-index/generator equation before applying the existing workload client. It does not make a claim about independently generated random queries. |

These equalities preserve concrete returned values and chronological execution.
They do not count comparisons, prove a resource bound, validate a random
generator, establish an expected logarithmic height, or compare CPU times.
The `n-j` schedule has no silently substituted increasing execution loop:
its equality to the increasing key list is proved from the descending source
indices. The eventual finite-word workload must retain the checked range and
distinctness conditions before converting such a list; the unbounded Nat
schedule does not assert arbitrarily many distinct keys fit in a fixed word.

### Connected source-facing clients

`Examples/ExtractedTrees.lean` keeps the source API names and the operational
equations above, alongside the following connected applications. These reuse
the public universal results; concrete output equalities supplement those
contracts.

| Client family | What is checked and what remains distinct |
| --- | --- |
| `word_lookup_insert_eq`, `word_lookup_insert_neq`, `int64_lookup_insert_eq`, `int64_lookup_insert_neq`, `zero_width_replacement` | All-raw-tree source updates under the actual signed comparisons. Width zero collapses original keys and still supports replacement; original distinct-key statements retain their explicit inequality. |
| `decoded_history_step` | The actual inserted tree and any supplied suffix commute with key decoding and the existing Int insertion. Only strict reflection is needed; the suffix and payloads are preserved. |
| `type_payload_update`, `workload_type_payload` | Values may themselves be types in an independent universe. A repeated chronological write retains the final type-valued payload. |
| `signedHistory`, `signed_history_last_write`, `signed_history_lookup`, `signed_history_elements`, `signed_history_valid`, `signed_history_keys_unique`, `signed_history_sound`, `signed_history_models` | An actual negative/positive history replaces the earlier `-3` binding with `9`, keeps key `4`, misses `-1`, enumerates `[(-3,9),(4,8)]`, has unique original projected keys, and connects invariant-guarded soundness and both independent partial models. |
| `history_models` | Both independent abstractions of arbitrary chronological histories agree with the corresponding `writeAll`, starting from any valid original-key tree and with every caller default. |
| `ET.colliding_original_keys`, `DK.colliding_decode_reflects` | The first theorem combines noninjectivity of constant Boolean-key decoding with changed lookup at a distinct original key; the second separately proves that the false strict comparator reflects the constant decoder. Together they demonstrate why reflection alone cannot supply the distinct-original-key law. |
| `stored_default_not_canonical` | Empty and a table explicitly storing default `0` agree at every default-0 lookup but have different enumerations. Complete partial meanings retain this distinction. |
| `malformed_membership`, `malformed_not_valid` | A hidden key in an incorrectly placed subtree remains in enumeration while search misses it and bound is false. The tree is explicitly shown not to satisfy BST. |
| `four_bit_endpoints`, `int64_endpoints` | Signed minimum/maximum keys use the actual signed adapters; decoder/insertion/traversal transport preserves payloads and yields the stated ordered endpoints. The 4-bit and Int64 ranges remain distinct from unbounded Int and the earlier BitVec63 realization. |
| `source_workload_lookup`, `source_workload_default`, `source_workload_history` | The Boolean source operations connect to the actual Int workload and its independent reversed-write model, including optional/default observations and exact total-table history execution. |
| `canonical_workload_histories`, `reordered_distinct_histories` | Equality of complete independent partial meanings yields equal canonical enumerations for the actual built trees; one default view is not substituted. |
| `workload_empty`, `workload_empty_with_queries`, `workload_repeated_queries`, `workload_signed_queries`, `workload_presence_and_default`, `source_consecutive_schedule` | Empty histories, missing and repeated queries, signed keys, stored-default versus absent results, and the actual descending-index source schedule are connected to the universal workload contracts. The duplicate/missing example has three hits among five queries; the signed example has four hits among five. |

### Preserved drafts and remaining resource/execution obligations

The five sealed checkpoint-036 recovery drafts and their notes remain
unchanged as historical artifacts. The four corresponding current mathematical
owners—`Basic`, `DecodedKeys`, `DecodedKeysModels` and pure `Workload`—were
promoted through fresh current elaboration and statement inspection, with
source adjustments made in those owners. This supplies evidence for their
current checked versions, not a retroactive compilation claim about the old
draft bytes. The fifth draft, `Applications/Resources/SearchTreeWorkload.lean`,
remains uncompiled and outside the import graph. It supplies no current
resource theorem or acceptance evidence.

The existing accepted tree height/path and measured search results remain
available. The Extract-specific workload composition, exact cost erasure and
aggregate comparison/path bounds, including the consecutive chain and bounded
word-history transfer, still require their own checked promotion. The pure
workload equalities above do not imply equal allocation, stack use, physical
sharing or timing. The earlier unary-comparison correction and finite-width
overflow/range restrictions remain in force.

All thirteen command obligations at source lines **40, 47, 58, 59, 60, 86,
114, 127, 131, 245, 349, 350 and 358** remain open as execution adaptations.
The current library definitions, real dependency builds, Bool/List/Prod
interoperability, comparator equations and connected theorem clients supply
mathematical prerequisites. They are not recorded successful standalone
execution of those commands. Neither a direct runner nor a compiled workload
executable, reproducible generated workload, retained result checksum, timing
comparison or source-sized benchmark is claimed by this increment.

The pending driver must still preserve build-before-timer, fresh independently
generated query keys, payload/default `1`/`0`, and per-query hit counting. The
source's random queries are not guaranteed to occur in its insertion history;
`hits_all` has that premise explicitly. Reproducible ranges/seeds, the inclusive
Lean versus exclusive OCaml random-bound distinction, zero-size behavior,
signed-range checks, negative/end-point cases, identical controlled inputs for
later Redblack comparison, both execution paths, measured region/clock units,
raw logs and honest result checking remain required. The source's historical
timings and misleading insertion-and-lookup label remain qualified as recorded
in the prior section; current mathematical results establish no timing result.

This correspondence records a bounded mathematical increment, with all earlier
coverage and the complete canonical Extract requirements retained. Candidate
proof audit, the two independent review axes, receiving whole-library
acceptance and durable checkpoint publication remain separate from this
source map. Extract is not marked complete by the 34-record/four-exercise
mathematical mapping while its resource and execution obligations remain open.

## Extract: measured histories and signed prefixes; execution remains open

This increment adds resource observations to the actual tree programs and
finite histories mapped in the previous Extract sections. The mathematical
source-record and exercise coverage remains **34 records and four exercises**,
including all fourteen optional enumeration groups. The additional results
address resource/prose obligations; they do not add inventory records or
qualify Extract as complete. Runtime, timing and all thirteen source-command
execution obligations remain open, so CTB-13 remains open before Redblack.

The three current modules add **172 public declarations**: 62 generic measured-workload
declarations, 75 supplied-Boolean/signed-prefix declarations and 35 connected
theorem clients. Fresh source checks, parent exports and a combined exported
signature probe have passed. All 35 client statements were compared with their
actual elaborated types; the owner assessments cover all 62 and 75 declarations
and their operational bodies. This describes implementation evidence, not the
later independent review axes or whole-candidate acceptance.

The previous coverage text is retained unchanged as a historical account.
The formerly uncompiled resource draft now has a separately promoted current
owner with fresh evidence. Its sealed checkpoint036 bytes and README remain
unchanged historical artifacts; none receives retroactive compiler evidence.

### Observation, state and phase boundaries

`Resources.SearchTreeWorkload` (abbreviated `RW` here) uses the accepted
`Resources.SearchTree.lookupRun`/`insertRun` and `Resources.run`.
`Resources.DecodedSearchTreeWorkload` (`DW`) supplies the actual Boolean
comparison adapters. `Examples.ExtractedProgramWork` (`EW`) supplies the
connected source-facing clients. Existing `Search.OrderedMap.Workload` (`WL`),
`Search.OrderedMap.DecodedKeys` (`DK`), signed-comparison and unary-comparison
owners retain their accepted roles. The signed-comparison namespace is
`Representations.SignedComparison` (`SC` below).

Every measured return is an ordinary pair of its actual value and
`(nonempty node visits, primitive strict-comparator calls)`. Nil inspection,
allocation, pointer sharing, stack use, input generation, hit-counter
arithmetic, comparator internals and elapsed time are outside that pair.
Left branches call the comparator once; right/equality branches call it twice,
in source query/root then root/query order. Unit charges count invocations of
the supplied comparison, without asserting constant physical runtime for that
comparison or for arbitrary-precision integers.

`RW.buildRun_cons` and `buildRun_append` expose the existing measured bind:
the next write consumes the tree returned by the previous write. The final
state is not reconstructed by a separate unmeasured computation and then
annotated with a guessed cost. `queryStep` inspects the optional payload
actually returned by measured search and performs the source default-0/test-1
hit update. `sourceRun_work` exposes the build cost plus query cost on that
**actual completed build state**. Empty insertion has zero charge because its
allocation and nil inspection are outside this observation; singleton lookup
still visits and compares its root.

Keys and general lookup/insertion/build payloads retain independent universes.
They require no payload equality, ordering or default. The source hit-count
scan is intentionally the separate Nat-payload specialization with inserted
value 1 and caller default 0. Caller-default and presence laws for general
lookup remain projections of its optional result.

Construction finishes before the companion ML program starts its timer.
Separate build and query counts therefore remain visible. Their combined
count is a further mathematical observation and is never labelled as the
source's query-only time. Arbitrary insertion/query lists permit duplicates
and misses; complete success is not assumed for fresh random draws.

### Generic measured workload: all 62 declarations

The general execution family takes `[LinearOrder κ]`; payloads remain
unrestricted. The two finite-list representation lemmas
`encodedKeys_decode` and `encodedKeys_nodup` omit that order premise and
derive their conclusions from pointwise prefix representation alone.

| Source obligation | Declaration families and exact scope |
| --- | --- |
| Actual chronological measured writes | `buildRun`, `buildRun_nil`, `buildRun_cons`, `buildRun_append`, `buildRun_value`; existing `Resources.run`/`bind` pass each actual returned tree to the next insertion. Erasure is `Workload.buildFrom`, arbitrary initial raw tree and independent key/payload universes. |
| Source payload-1 construction | `buildKeysRun`, `buildKeysRun_value`, `buildKeysRun_snoc`; sourceWrites preserves chronological key order, followed by actual measured insertion. |
| Actual query observations | `queryStep`, `queryStep_work`, `queryRun`, `queryHits_cons`, `run_queryStep_value`, `queryRun_value`, `queryRun_work`; each hit test consumes the actual optional result with source default 0/test 1. Initial hit accumulator is arbitrary in `run_queryStep_value`. |
| Path/height bound | `queryRun_visits_le_height`, `queryRun_comparisons_le_height`: visits ≤ query length × actual tree height, comparisons ≤ twice that bound. No BST premise or logarithmic-height inference. |
| Separate and combined phases | `sourceRun`, `sourceRun_work`, `sourceRun_value`, `sourceRun_independent_count`: actual final build state is the query input; combined costs add those two phases, result equals independent membership count on arbitrary insertion/query lists. |
| Exact consecutive tree | `bind_rightSpine_next`, `buildKeys_range_eq_rightSpine`, `lookupRun_rightSpine_present`, `consecutiveBuildRun`, `consecutiveBuildRun_value`, `consecutiveBuildRun_succ`: actual build is rightSpine 1 0 n, and the next insertion adds `(n,2*n)`. |
| Exact construction costs | `consecutiveBuildRun_work_add`, `consecutiveBuildRun_double_visits`, `consecutiveBuildRun_comparisons`: `2*visits=n*(n-1)`, comparisons equal `n*(n-1)`, including n=0. |
| Successful/absent paths | `successful_consecutive_query`, `upper_missing_consecutive_query`, `last_consecutive_query`: k<n returns some1 and `(k+1,2*(k+1))`; upper missing n returns none and `(n,2*n)`; last successful n-1 needs positive n and returns some1 with the same full-path count. |
| Exact query and total costs | `consecutiveQueryRun`, `consecutiveQueryRun_value`, `sum_successful_steps`, `sum_successful_work`, `consecutiveQueryRun_work`, `consecutiveQueryRun_double_visits`, `consecutiveQueryRun_comparisons`, `sourceRun_consecutive`, `sourceRun_schedule`: scan result n, doubled query visits n*(n+1), query comparisons n*(n+1), combined result `(n,(n*n,2*(n*n)))`. Source schedule uses actual descending indices and accepted n-j/range equality. |
| Full measured decoder transport | `lookupRun_mapKeys`, `insertRun_mapKeys`, `buildRun_mapKeys`, `buildKeysRun_mapKeys`, `buildKeys_mapKeys`, `run_queryStep_mapKeys`, `queryRun_mapKeys`, `sourceRun_mapKeys`: compatible strict order preserves whole measured results/pairs, with decoded original returned trees and arbitrary histories. These are separate count proofs, not consequences of mere value erasure. |
| Finite-prefix representation | `encodedKeys`, `encodedBuildRun`, `encodedQueryRun`, `encodedKeys_decode`, `encodedKeys_nodup`: pointwise representation on k<n derives distinctness of the actual encoded list; no global inverse or unbounded finite-word family. |
| Encoded families | `encodedBuildRun_transport`, `encodedBuildRun_work`, `encodedQueryRun_transport`, `encoded_successful_query`, `encoded_upper_missing_query`, `encoded_last_query`, `sourceRun_encodedKeys_exact`: preserve actual decoded shape and all counts. Upper-missing query explicitly adds representation of encode n; last success uses only prefix representation plus positive n. |

The general query bounds are `visits ≤ queries.length * tree.height` and
`comparisons ≤ 2 * (queries.length * tree.height)`, on every raw tree. When a
query follows a measured build, that height belongs to its actual returned
tree. Neither BST validity nor a random sample supplies a logarithmic-height
premise.

### Consecutive source family and exact observations

Let `B n = RW.consecutiveBuildRun n` and
`Q n = RW.consecutiveQueryRun n`. The first returns the actual
`Resources.SearchTree.rightSpine 1 0 n`. The standalone query abbreviation uses
`WL.buildKeys (List.range n)`; `buildKeysRun_value` identifies that tree with
the return of the measured construction. The combined `sourceRun` itself
passes the measured build return directly through `Resources.bind`. Their
equations hold for every Nat n, including zero:

| Observation | Checked formula and owner |
| --- | --- |
| Actual constructed shape | `(B n).1 = rightSpine 1 0 n`, by `consecutiveBuildRun_value`. |
| Construction | `2 * (B n).2.1 = n * (n-1)` and `(B n).2.2 = n * (n-1)`, by `consecutiveBuildRun_double_visits` and `consecutiveBuildRun_comparisons`. |
| Successful query k<n | `(some 1, (k+1, 2*(k+1)))`, by `successful_consecutive_query`. |
| First absent upper key n | `(none, (n, 2*n))`, by `upper_missing_consecutive_query`. |
| Last successful key n-1, with 0<n | `(some 1, (n, 2*n))`, by `last_consecutive_query`. |
| Completed scan | `(Q n).1 = n`, `2 * (Q n).2.1 = n*(n+1)`, `(Q n).2.2 = n*(n+1)`, by the three `consecutiveQueryRun_*` result/count theorems. |
| Combined construction and scan | `RW.sourceRun (range n) (range n) = (n, (n*n, 2*(n*n)))`, by `sourceRun_consecutive`. |
| Actual descending source indices | `sourceRun_schedule` applies the same combined formula to both lists `map (fun j => n-j) (WL.sourceIndices n)`, using the accepted schedule/range equality. |

Doubled-visit formulas preserve Nat zero/subtraction behavior without an
implicit division convention. The successful last-key and upper-missing-key
results demonstrate a full linear search path; the full scan has quadratic
aggregate counts. These exact identities do not measure CPU time, impose a
runtime stack bound or prove a random expected-case theorem.

### Supplied Boolean comparisons and measured transport

`DW.unitBoolRun ltb a b = (ltb a b, 1)` retains the actual executable Boolean
answer. `lookupRun` and `insertRun` specialize the existing `SearchTree`
measured primitives with that operation. `buildRun`, `queryRun` and `sourceRun`
compose those steps through the existing measured executor and bind, with no
second recursive history algorithm.

`lookupRun_value`, `lookupRun_default`, `lookupRun_bound`, `insertRun_value`,
`buildRun_value` and `buildKeysRun_value` hold for **every** supplied Boolean
comparator and every raw tree, without reflection, injection or BST.
`queryRun_value` and `sourceRun_value` similarly identify the actual returned
hit counter with the fold over the actual Boolean source lookups. They do not
claim that an arbitrary comparator implements original-key equality.

Under injective decoding and strict reflection,
`unitBoolRun_eq_ordered` explicitly selects
`(SC.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT`.
It uses the established `linearOrderOfStrict_decide_lt` field equation.
`lookupRun_eq_ordered`, `insertRun_eq_ordered`, `buildRun_eq_ordered`,
`buildKeysRun_eq_ordered`, `queryStep_eq_ordered`, `queryRun_eq_ordered` and
`sourceRun_eq_ordered` then equate **whole measured results**, not just values.
The canonical `sourceRun_independent_count` consequently compares actual hits
with the original-history membership checker under those lawful parameters.
The checkpoint036 warning about freshly inferred `decide` remains relevant:
its expression alone does not establish that a supplied comparator executed.

The `RW.*_mapKeys` and `DW.encoded*` transfer results preserve the actual decoded
returned tree as well as its complete observation pair. Their count equality
is established through matching measured branches, unit charges and history
composition. It is not inferred solely from the earlier value-level decoder
squares or fast/slow traversal equality.

### Supplied-Boolean adapter: all 75 declarations

The names in the following table belong to `DW`. The source anchors refer to
the authenticated VFA 2.1 `Extract.v`, its companion `test_searchtree.ml`, and
the complete canonical Extract specification. No comparison, history or tree
algorithm is duplicated for a carrier.

| Requirement and primary-source anchor | Checked targets in `Resources.DecodedSearchTreeWorkload` | Scope |
| --- | --- | --- |
| Actual strict-comparison operation and interpretation separation; `external/Extract.v:110-137`, `canonical Extract requirements section 2`, `checkpoint038 requirements actual Boolean layer` | `unitBoolRun`, `unitBoolRun_eq_ordered`, `lookupRun_eq_ordered`, `insertRun_eq_ordered` | Actual operations contain only the supplied Boolean callback; order laws are explicit theorem parameters, and the exact selected decision field is inspected. |
| Source lookup branches, optional/default/presence observations; `external/Extract.v:293-299` | `lookupRun`, `lookupRun_empty`, `lookupRun_value`, `lookupRun_default`, `lookupRun_bound` | Reuses existing measured short-circuit search; arbitrary Boolean comparator and all raw trees. First branch query/root, second root/query; projected default is caller supplied. |
| Source insertion branches and actual state propagation; `external/Extract.v:301-307`, `external/test_searchtree.ml:2-4` | `insertRun`, `insertRun_empty`, `insertRun_value`, `buildRun`, `buildRun_value`, `buildKeysRun`, `buildKeysRun_value`, `buildRun_eq_ordered`, `buildKeysRun_eq_ordered` | Existing insertWithRun and Resources.run; chronological writes consume actual prior returned trees; no duplicated search or history recursion. |
| Source query hit test and independent count; `external/test_searchtree.ml:5-8` | `queryStep`, `queryRun`, `queryRun_value`, `queryStep_eq_ordered`, `queryRun_eq_ordered`, `sourceRun_independent_count` | Consumes actual optional results, getD 0, and equality to 1; lawful independent count uses original insertion-list membership. |
| Phase separation and full execution equality; `external/test_searchtree.ml:4-11`, `external/Extract.v:353-385` | `sourceRun`, `sourceRun_value`, `sourceRun_work`, `sourceRun_eq_ordered` | Separate actual build and scan phases; their mathematical sum is distinct from query-only timer. No clock observation or source command acceptance here. |
| Consecutive worst-case build shape, successful paths and exact pair formulas; `external/test_searchtree.ml:20`, `external/Extract.v:387-391`, `checkpoint038 required consecutive family` | `encodedBuildRun`, `encodedQueryRun`, `encodedSourceRun`, `encodedBuildRun_eq_ordered`, `encodedQueryRun_eq_ordered`, `encodedBuildRun_transport`, `encodedBuildRun_counts`, `encodedQueryRun_transport`, `encodedQueryRun_counts`, `encoded_successful_query`, `sourceRun_encodedKeys_exact` | Actual decoded returned rightSpine shape, separate n(n-1) and n(n+1) counts, and combined (n,(n²,2n²)); whole measured transport and pointwise finite representation. |
| Exact descending source schedule; `external/test_searchtree.ml:2-8,20`, `accepted Workload.sourceIndices_consecutive` | `encoded_source_schedule`, `word_source_schedule`, `int64_source_schedule` | The source schedule j=n,...,1 maps by encode(n-j) in both phases. Nat counters and subtraction are explicit. |
| Finite signed word and Int64 families with derived distinctness; `external/Extract.v:116-121,139-154`, `canonical Extract requirements section 3`, `checkpoint038 finite-prefix requirement` | `wordKeys`, `wordBuildRun`, `wordQueryRun`, `wordSourceRun`, `word_prefix_representable`, `wordKeys_nodup`, `wordBuildRun_transport`, `wordBuildRun_counts`, `wordQueryRun_counts`, `wordSourceRun_exact`, `word_successful_query`, `wordBuildRun_63_transport`, `wordBuildRun_63_counts`, `wordQueryRun_63_counts`, `wordSourceRun_63_exact`, `int64Keys`, `int64BuildRun`, `int64QueryRun`, `int64SourceRun`, `int64_prefix_representable`, `int64Keys_nodup`, `int64BuildRun_transport`, `int64BuildRun_counts`, `int64QueryRun_counts`, `int64SourceRun_exact`, `int64_successful_query` | Actual signed providers with non-strict finite-prefix bounds; width 63 is the bounded source model, Int64 is the distinct Lean 64-bit realization; no modular counter arithmetic assumption. |
| Full-prefix endpoint and first-absent-query boundary; `checkpoint038 finite-prefix and connected-boundary requirements` | `encoded_upper_missing_query`, `encoded_last_query`, `word_upper_missing_query`, `word_last_query`, `int64_upper_missing_query`, `int64_last_query` | Absent upper query requires its own representability (strict finite bound); last successful query uses original non-strict prefix bound plus positivity. `EW.four_bit_wrapped_missing` supplies the checked width-4 n=8 witness. |
| Width-zero singleton carrier; `canonical Extract requirements section 3`, `checkpoint038 zero-width requirement` | `zero_width_lookup_after_insert` | Separate all-raw arbitrary-payload theorem with (some value,(1,2)), without positive-width conversion claims. |

### Finite signed prefixes and the missing-key boundary

The exact representation premise is
`∀ k, k < n → decode (encode k) = (k : Int)`.
`RW.encodedKeys_decode` identifies the decoded generated list and
`encodedKeys_nodup` derives distinctness of its original encoded keys from this
finite premise. There is no assumption of an unrestricted decoder inverse or
an unbounded strictly increasing finite-word sequence.

`DW.wordKeys` generates `BitVec.ofNat w` encodings; `wordBuildRun`,
`wordQueryRun` and `wordSourceRun` execute `SC.wordLtb` on those keys. The
analogous `int64Keys` generates `Int64.ofInt (k : Int)` values, and
`int64BuildRun`, `int64QueryRun` and `int64SourceRun` execute `SC.int64Ltb`.
These definitions have no proof inputs;
the following mathematical contracts carry the needed range premises.

| Carrier and observation | Exact guard and checked contracts |
| --- | --- |
| Signed `BitVec w` prefix | `0 < w` and `n ≤ 2^(w-1)`. `word_prefix_representable` and `wordKeys_nodup` prove pointwise decoding and distinctness of the actual generated key list. `wordBuildRun_transport` retains the actual decoded returned tree and complete work; `wordBuildRun_counts`, `wordQueryRun_counts` and `wordSourceRun_exact` retain the separate and combined formulas. |
| Signed word queries | `word_successful_query` additionally needs `k<n`. `word_upper_missing_query` needs the strictly stronger `n < 2^(w-1)`. `word_last_query` needs `0<n` with the original non-strict prefix bound. `word_source_schedule` connects both encoded lists to the actual descending source indices. |
| Source-width model `BitVec 63` | `n ≤ 2^62`. `wordBuildRun_63_transport`, `wordBuildRun_63_counts`, `wordQueryRun_63_counts` and `wordSourceRun_63_exact` specialize the actual signed provider; the general word-query theorems give the same strict/non-strict boundary at width 63. The signed interpretation range remains `[-2^62,2^62)`. |
| Distinct runtime carrier `Int64` | `n ≤ 2^63`. `int64_prefix_representable`, `int64Keys_nodup`, `int64BuildRun_transport`, `int64BuildRun_counts`, `int64QueryRun_counts`, `int64SourceRun_exact` and `int64_source_schedule` retain the actual provider and finite generation. The signed interpretation range is `[-2^63,2^63)`. `int64_successful_query` needs `k<n`, `int64_upper_missing_query` needs `n<2^63`, and `int64_last_query` needs `0<n` with `n≤2^63`. |
| Width zero | `zero_width_lookup_after_insert` handles every raw `BitVec 0` tree and arbitrary payload universe: lookup of any width-zero query after the actual measured insertion returns `(some value,(1,2))`. This is the subsequent **lookup** observation; it does not include insertion work. No positive-width range theorem is invoked. |

A prefix may attain its positive representability bound because its largest
key is n-1. Querying the first missing upper key n additionally needs that key
to be representable. Thus the missing-query guard is strict, whereas the
build/full-scan guard is non-strict. At the full positive prefix use the last
successful key n-1, with 0<n, for the full linear-path formula. Encoding n at
the signed endpoint wraps and cannot inherit the Nat upper-missing path count.

Generation parameters, indices and observation counters remain Nat. No result
claims the counter n itself fits in the signed carrier at a full prefix or that
native wrapping arithmetic agrees unconditionally with Int arithmetic. Width
zero remains a separate singleton-key case, with no use of a positive-width
representation theorem.

### Connected measured clients

All 35 declarations below belong to `EW`. Their complete frozen source and
all 35 actual exported types were read after the combined 172-statement probe
returned exit 0. The descriptive assessment found no changed quantifier,
hidden payload restriction, missing range premise, reversed equality or
unintended cost phase. This remains separate from independent review.

| Connected client | Checked result and relevant boundary |
| --- | --- |
| `measured_history_queries` | Arbitrary chronological writes and independent queries return the independent reversed-write model on the actual measured build; key/payload universes remain independent. |
| `measured_decoded_history` | For a compatible strict order, decoded arbitrary-suffix enumeration and complete work of the actual history equal the Int history on mapped writes, initial raw tree and suffix. |
| `empty_workload` | No writes and no queries give `(0,(0,0))`. |
| `empty_with_queries` | No writes with queries `[0,0,7]` still give `(0,(0,0))`; nil inspection is outside the count. |
| `singleton_workload` | Insert/query `[0]` gives `(1,(1,2))`; root equality executes both strict comparisons. |
| `consecutive_four_build` | The actual build is `rightSpine 1 0 4`, with construction work `(6,12)`. |
| `consecutive_four_query` | Query phase returns `(4,(10,20))`, separately from construction. |
| `consecutive_four_total` | The combined actual range/range run returns `(4,(16,32))`. |
| `consecutive_four_found` | Key 2 in the actual four-key measured return gives `(some 1,(3,6))`. |
| `consecutive_four_missing` | First absent upper key 4 gives `(none,(4,8))`. |
| `consecutive_last_path` | For every `0<n`, successful key `n-1` gives `(some 1,(n,2*n))`. |
| `duplicate_and_missing_workload` | Insert `[3,1,3]`, query `[3,2,1,3,7]`: `(3,(9,15))`; independent membership proves the result and actual paths determine the count. |
| `signed_workload` | Int insert `[-3,0,4,-3]`, query `[-3,-1,4,0,4]`: `(4,(15,29))`. |
| `measured_stored_default` | Actual writes `(2,5),(2,0)` distinguish `some 0` from `none`; `getD 0` agrees and both source hit tests fail. |
| `measured_type_payload` | Repeated Int-key writes of arbitrary `first,last : Type v` return `some last`, without payload equality, order or a default. |
| `measured_malformed_miss` | Root `(0,0)` with invalid left child `(1,7)` yields lookup 1 `(none,(1,2))` although the binding is enumerated. |
| `source_schedule_work` | Both actual descending source-index lists mapped by `n-j` have combined result `(n,(n*n,2*(n*n)))`, including zero. |
| `measured_boolean_observations` | Arbitrary comparator/raw-tree optional, caller-default and presence observations erase to `DK.lookup?`, `DK.lookup` and `DK.bound`, with no ordering premises. |
| `measured_boolean_history` | Arbitrary Boolean chronological execution erases to `bindAll (DK.ops ltb)` and its actual lookups; it does not assert independent membership correctness. |
| `measured_boolean_decoded_history` | Injective reflected decoding connects the actual Boolean history, arbitrary initial raw tree and suffix, and its full work pair to the mapped Int execution. |
| `measured_boolean_type_payload` | Only Boolean irreflexivity is needed for same-key raw insertion/lookup of arbitrary `Type v` payload; no decoder or BST is assumed. |
| `measured_boolean_signed_workload` | The actual supplied `SC.intLtb` executes the negative/duplicate/missing workload with the same `(4,(15,29))` result, using the independent count theorem. |
| `unlawful_boolean_counterexample` | Always-true Int comparison on insert/query `[1]` gives `(0,(1,1))`, while independent original-key expected hits are 1. |
| `four_bit_full_prefix` | At `w=4,n=8`, build work `(28,56)`, query `(8,(36,72))`, combined `(8,(64,128))`, and last key 7 lookup `(some 1,(8,16))` all hold at the non-strict prefix endpoint. |
| `four_bit_represented_missing` | At `w=4,n=4`, represented upper key 4 misses with `(none,(4,8))` under the strict guard. |
| `four_bit_wrapped_missing` | Encoding 8 at width 4 decodes to -8 and misses the full eight-key tree with `(none,(1,1))`; removing the strict missing-query guard would give a false path count. |
| `zero_width_repeated_workload` | Three width-zero writes and three queries give `(3,(5,10))`; replacement writes and queries are counted, independently of positive-width theorems. |
| `zero_width_type_payload` | For any width-zero key/query and raw tree, lookup after actual insertion of a `Type v` payload yields `(some value,(1,2))`; the displayed pair counts lookup only. |
| `word63_finite_family` | Every `n≤2^62` retains actual decoded build shape, both construction/query formulas and combined counts for the signed 63-bit provider. |
| `int64_finite_family` | Every `n≤2^63` retains the analogous complete result for the distinct Int64 provider and its guarded conversion. |
| `word63_signed_endpoints` | The low/high values decode to `-2^62` and `2^62-1`; actual signed build/query of both returns `(2,(4,8))`. |
| `int64_signed_endpoints` | The low/high Int64 values decode to `-2^63` and `2^63-1`; actual signed build/query of both returns `(2,(4,8))`. |
| `word_source_schedule_work` | Every positive width and `n≤2^(w-1)` connects both actual encoded source-index lists to the exact combined formula. |
| `unary_equal_work` | Every explicit unary non-strict comparison on `n,n` returns true with `n+1` calls. |
| `unary_difference_obstruction` | Every proposed difference-only bound fails universally; an equal-input witness exceeds its value at zero. |

### Exact correction to the numeric-comparison prose

Extract lines 63–69 claim unary non-strict comparison work is proportional to
the difference between inputs. The accepted explicit lockstep model instead
has the whole-result theorem
`Resources.UnaryComparison.unaryLERun_spec n m`:
`unaryLERun n m = (decide (n ≤ m), min n m + 1)`.
Equal inputs have zero difference and n+1 charged calls.
`no_difference_only_bound` rejects **every** proposed Nat→Nat bound of
`(n-m)+(m-n)` over all inputs; `EW.unary_difference_obstruction` also supplies
an equal-input witness exceeding its value at zero. `EW.unary_equal_work`
retains both the true returned comparison and that exact work.

The accepted strict adapter is `unaryLERun (n+1) m`, with exact charge
`min (n+1) m + 1`; its formula must not silently be replaced by the non-strict
one. These are stated abstract recurrences, distinct from Lean's native Nat,
from a bit-cost model for arbitrary-precision integers, and from host clock
observations. Signed reflection alone proves no constant-time or
constant-allocation property.

### Frozen current owners

| Current source | Public declarations | SHA-256 |
| --- | ---: | --- |
| `Applications/Resources/SearchTreeWorkload.lean` | 62 | `4d494f1414d31e1bcc5668ccb7f2f0fc1a9e7111313c986b2fe603aa4ab724ab` |
| `Applications/Resources/DecodedSearchTreeWorkload.lean` | 75 | `cd3c52fab1313ec35b2aa8b26cba1b533f31bd1dadf1fd7018842280e87bb35c` |
| `Examples/ExtractedProgramWork.lean` | 35 | `e4a6cb78f9be4e7f636a53bbd28b5923a33b285033fbbc565fa63c859aea1f65` |

The external development evidence preserves the complete 172-signature output
and the individual owner/client assessments. Its source and output identities
are recorded separately from the eventual exact-candidate validator and
publication receipt. No source body, generated compiler output or historical
ML timing transcript is bundled into this coverage document.

### Historical preservation and execution still open

All five checkpoint036 draft Lean files and their README remain byte-identical
historical artifacts with their original uncompiled status. The current
`Applications/Resources/SearchTreeWorkload.lean` is the fifth separately
promoted counterpart, with fresh elaboration and statement evidence. Earlier
promoted Basic/DecodedKeys/Models/pure-Workload counterparts retain their own
independent evidence. New representation adapters and connected resource
clients are current source additions, not a relabelling of the old draft.

All thirteen source-command execution adaptations at lines 40, 47, 58, 59, 60,
86, 114, 127, 131, 245, 349, 350 and 358 remain open. No standalone direct run,
compiled workload execution, seeded/random-generation regression, timer
measurement or historical-size benchmark is claimed here. The source-shaped
build-before-timer and RNG-inside-query protocol, controlled identical-list
protocol, independent result checking, signed conversion guards, actual
execution of both modes and complete retained runtime evidence remain
required by the full canonical specification.

This is a resource increment within the still-open chapter. Exact-candidate
proof audit, independent Standards/Spec reviews, receiving whole-library
acceptance and durable checkpoint publication remain separate gates. Abstract
count identities cannot replace them or the remaining execution obligations.

## Extract: executable observations and final qualification (CTB-91)

CTB-91 supplies the remaining executable-observation work under CTB-13,
following CTB-90. The complete [canonical Extract requirements](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1011-Extract.md)
still govern all 34 source records, four exercises, fourteen optional
enumeration groups, corrected resource prose and companion-program obligations.
The preceding checkpoint038 account remains historical, including its 10/17
VFA count and open execution obligations. All 48 previously selected
mathematical Lean files and the 172-signature resource probe remain unchanged;
runtime functions are counted separately and add no mathematical declarations.

The new owners are [the executable driver](../../scripts/ExtractSearchTree.lean),
[the public Python harness and receipt observer](../../scripts/test-extract-searchtree.py),
the exact `lean_exe` entry in [lakefile.toml](../../lakefile.toml)
(`name = "extract-searchtree"`, `root = "ExtractSearchTree"`, `srcDir = "scripts"`),
and [the runtime correspondence and assessment](vfa-extract-runtime.md).
The driver stays outside `SquareApplications`. It reuses accepted sorting,
Boolean-comparison, chronological-write and traversal operations.

Development completed fourteen driver feature slices: eight example families
and six workload behaviors covering defaults, configurable consecutive inputs,
independent replay lists, fresh seeded random queries, source timing, and
warmups/repetitions. Additional public regressions cover the named source
random specialization and malformed commands, option conflicts, files and
finite-range boundaries. That historical harness had26 public tests. The
following CTB-91 development observations are preserved with exact record hashes
in [the runtime assessment](vfa-extract-runtime.md). Receipt names identify old
external records; their current availability is not inferred from those names.
The maintained behavior lives in the actual driver and independent Python tests.

| Historical development record | Recorded result |
| --- | --- |
| `22-standalone-target-green-01.json` and its stdout | Explicit standalone build exited 0 and completed **1,812 Lake jobs**. |
| `28-compiled-examples-smoke-01.json` and its `.calls/` records | The hash-bound native-exec route ran `examples` successfully; the public observer accepted the complete result. |
| `29-compiled-workloads-smoke-01.json` and its `.calls/` records | The same compiled route passed default controlled, repeated source-random, empty word63-random and independent Int-replay cases; the observer accepted all four. |
| `26-receipt-coherent-stream-regression-02.json` | The workload rejection suite passed, including a falsified fixed random stream whose map-derived fields were changed consistently. |
| `27-unbounded-int-regression-01.json` | Signed Int replay and its public observer accepted positive/negative keys with 4,401 decimal digits. |

These observations do not substitute for final stable-candidate two-mode
qualification. The full 26-test suites in both modes, final candidate-bound
receipts and final reviews remain gates; no such completed qualification is
asserted by this development account.

### All thirteen source-command adaptations

Line numbers refer to the authenticated VFA 2.1 `Extract.v` inventoried in the
canonical requirements. `EP` denotes [Examples.ExtractedPrograms](../../Examples/ExtractedPrograms.lean),
`ET` denotes [Examples.ExtractedTrees](../../Examples/ExtractedTrees.lean), and
the supplied signed providers belong to [Representations.SignedComparison](../../Applications/Representations/SignedComparison.lean).
Private client names below belong to the executable driver. Every row requires
the final direct/compiled observations and inspected executable dependency
path; shared examples can discharge several source directives.

| Source line and directive | Actual Lean connection and required observation |
| --- | --- |
| 40 — `Extraction sort` | `natSortCase` calls `EP.sort`: empty, singleton, reversed and duplicate Nat lists retain their actual sorted results. |
| 47 — `Recursive Extraction sort` | The same Nat client follows the existing `InsertionSorting.sort` and `List.insertionSort`/`orderedInsert` closure. |
| 58 — native `bool` | Ordinary Lean Bool carries actual signed less/equal/greater and minimum/maximum comparison results. |
| 59 — native `list` | Ordinary List carries original sort inputs, labelled ties, workload schedules, queries and traversal results. |
| 60 — recursive sort after datatype directives | The same Nat sort and ordinary Bool/List realization share the observations and executable closure above. |
| 86 — `Recursive Extraction sortZ` | `examples` calls `EP.sortZ`; signed duplicates `[-3,2,-3,0,1]` produce `[-3,-3,0,1,2]`, with separate empty and singleton cases. |
| 114 — inline carrier `int` | Explicit `Int`, signed `BitVec 63` and `Int64` realizations retain distinct carrier labels, guarded finite conversions and signed endpoints. |
| 127 — inline strict comparison | Actual `intLtb`, `wordLtb` or `int64Ltb` reaches tree branches and comparison cases; the four-bit signed/unsigned disagreement remains explicit. |
| 131 — inline nonstrict comparison | The supplied `leb` reaches `EP.decodedSort`; labelled equal keys preserve original payload order for all three carriers. |
| 245 — `Recursive Extraction sort_int` | `finiteSortCase` and `stableSortCase` call the existing Boolean-only sort; signed minimum/maximum, negative repeats and labelled ties retain full results. |
| 349 — native `prod` | Ordinary Prod carries original keys and unequal payloads through writes, trees and enumeration, including the exact arbitrary traversal suffix. |
| 350 — recursive empty/insert/lookup/elements | `tableCase` and workloads use ET/DecodedKeys and shared `bindAll`: empty lookup, latest repeated write, stored zero versus absence, caller defaults and complete canonical entries. |
| 358 — standalone `searchtree.ml` | Global `main` and the ordinary Lake target expose the same examples/workloads through direct Lean execution and the actual hashed standalone ELF, including successful observations and normal rejection exits. |

The tree path is [DecodedKeys](../../Applications/Search/OrderedMap/DecodedKeys.lean),
[its operation record](../../Applications/Search/OrderedMap/DecodedKeysModels.lean),
[shared chronological execution](../../Applications/Search/OrderedMap/Interface.lean),
[source schedules and writes](../../Applications/Search/OrderedMap/Workload.lean),
and [fast enumeration](../../Applications/Search/OrderedMap/Enumeration.lean).
Sorting uses [DecodedInsertion](../../Applications/Sorting/DecodedInsertion.lean).
These are Lean adaptations of the source directives; no Coq-to-OCaml compiler
correctness result is claimed.

### Representation, independent checking and timing

`Int` is unbounded. Signed `BitVec 63` admits `[-2^62,2^62)` and its comparator
performs the pinned BitVec signed interpretation; it is not the Int64 native
primitive. `Int64` admits `[-2^63,2^63)` and selects its signed native overrides.
Finite conversion checks original keys before encoding and verifies round
trips. Nat counters remain unbounded. Width-zero collapse, four-bit signed
versus unsigned comparison, safe addition and overflowing addition illustrate
separate representation boundaries. Erasure of `Prop` does not erase decoding
or checking used as executable data.

Controlled timing includes traversal of precomputed queries, actual lookup
and hit counting. Source timing includes descending-schedule creation and
traversal, fresh key generation, checked conversion, lookup and hit counting;
schedule allocation and per-key round-trip decoding are included. Construction
precedes both query intervals. Source query replay/list capture, independent
model checks, enumeration and serialization follow the end clock. The clock
is `IO.monoNanosNow`, reporting elapsed nanoseconds; the source companion's
`Sys.time` reports process CPU time. There is no build-time claim or timing
threshold. Generated C must confirm the actual ordering and selected provider
path.

Each sample resets the seed and rebuilds. Random queries continue the
post-build `StdGen` state; `buildDraws`/`queryDraws` count logical `randNat` key
requests, not internal generator steps. The generalized size-8/universe-13
smoke differs from source `test_random n`, which requires
`size = queries = universe = n`. Empty draws preserve state. Replay retains
independent insertion/query bytes, including duplicates and misses.
An independent Int-key `Std.HashMap` checks the driver's full observations;
the host harness uses literal, sorted-list and Python-dictionary expectations.
Neither a checksum nor agreement of two launch modes replaces those checks.
Abstract node/comparison counts remain distinct from native timing, bit costs,
allocation, stack use, balance or compiler correctness. Random1e6, random20k
and consecutive20k remain named opt-in recipes unless separately executed.

### Evidence and chapter-transition gate

Qualification requires the same clean candidate and tree in the focused and
runtime receipts. Bind the actual compiler, pinned dependencies, configuration,
all four new owners, stable dependency artifacts, actual ELF and inspected
generated C. Re-run the unchanged focused mathematical check and 172-signature
probe. Record an explicit standalone build and the same complete public suite
through `lake env lean --run scripts/ExtractSearchTree.lean` and the hashed
ELF through the established native-profile route; each parent command must
exit zero.

Retain actual argv, exits, stdout/stderr, replay input bytes and their hashes
outside the curated archive. Match all invocation identities across modes.
Successful driver JSON must be complete and strictly parsed; compare every
semantic field after removing only sample `elapsedNs` and replacing replay
filenames by verified input-byte identities. Driver errors must be ordinary
exits 1 or 2 with empty stdout and an error. The public receipt observer must
accept complete consistent observations and reject malformed, incomplete or
wrong ones; observer rejection is exit 1. Observer parity compares acceptance
and status while preserving each raw fixture. Crashes do not count as expected
rejections.

The original compact runtime envelope bound focused/runtime/assessment identities,
source hashes, the thirteen command adaptations and a candidate-specific review.
[CTB-91/CTB-13](../textbooks/CTB.json) retain the historical qualification;
[vfa-extract-runtime.md](vfa-extract-runtime.md) owns the observation contract and
meaningful result boundary. Current CTB-78 receiving checks require their own
actual source/executable/command identities. No old envelope, raw primary body,
execution log, cache or binary is made a permanent dependency of this ledger.
The source adaptations, exact observation semantics and their limitations remain
unchanged; a historical hash alone is not a new execution or proof of availability.

After those gates, secured checkpoint039 source-qualifies Extract and moves
VFA from the historical **10/17** to **11/17**, with six chapters remaining;
CTB-14 then follows the [canonical Redblack requirements](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1012-Redblack.md).
This transition makes no Redblack implementation claim. FDSA/PFDS progress and
their readiness assessments are unchanged. Whole-library, exhaustive and
receiving acceptance retain their separately delegated status, and the
standing goal remains every chapter of all three books.

## Redblack: source operations, models, color invariants and depth (CTB-92)

CTB-92 is the first bounded implementation child of CTB-14, after the secured
Extract execution increment CTB-91. It implements the complete pure Redblack
theory and connected clients. The chapter remains open: its instrumented
resource model and actual ordinary/red-black execution comparison are separate
required work. VFA stays at **11 of 17** source-qualified units. FDSA/PFDS and
their primary-source readiness retain their previous states; this increment
does not advance another chapter or end the all-three-books instruction.

The [complete Redblack correspondence](vfa-redblack.md) retains all 45 exact
lexical source records, all 13 exercises, the six commands, abandoned-proof
dispositions, and substantive prose from the
[canonical requirements](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1012-Redblack.md).
The actual VFA 2.1 source has 838 lines, 27,066 bytes, and SHA-256
`f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2`.
The earlier canonical planning status is retained historically; it does not
erase any requirement or prohibit this work after accepted Extract.

### Actual representation and proof owners

The existing carrier is Batteries `RBTree.RBNode (κ × ν)`, with independent
key and payload universes. Raw malformed inputs remain representable. No
payload ordering, equality decision or global inhabitance requirement is
introduced. Decoding to Int is used in proof statements; actual executable
branches use the supplied Boolean comparisons.

| New source owner | Implemented responsibility |
| --- | --- |
| [Basic](../../Applications/Search/RedBlack/Basic.lean) | Raw carrier and observations, exact source balance and insertion, constructor equations and nonemptiness. |
| [Observations](../../Applications/Search/RedBlack/Observations.lean) | Exact inorder and suffix laws, arbitrary all-node predicates, root-blackening observations, and complete raw color-erasure bridges. |
| [Ordering](../../Applications/Search/RedBlack/Ordering.lean) | Full-descendant BST, ordering preservation, weak balance/same-key lookup and distinct-original-key lookup. |
| [Models](../../Applications/Search/RedBlack/Models.lean) | Presence, complete relevant enumeration, original-key partial meanings, independent structural abstraction, canonical lists, and accepted validity-guarded interfaces. |
| [Shape](../../Applications/Search/RedBlack/Shape.lean) | Parent-color RB, nonempty NearlyRB, exact source repairs, simultaneous insertion conclusions and existential root-blackening height. |
| [Depth](../../Applications/Search/RedBlack/Depth.lean) | Maximum/minimum depth, black-height path inequalities, the exact advanced source theorem and the qualified size/logarithm bounds. |

`find?`, `All`, `foldr`, `toList`, `setBlack` and `fold` supply the matching
provider operations. The missing source-specific recurrences are the exact
ordered `balance` and recursive `ins`. Red bypass precedes black left-left,
left-right, right-left, right-right and fallback. Both recursive insertion
branches call the full matcher; equality replaces both key and value; public
insertion always blackens. The provider's side-specific insertion and
right-right-before-right-left balancer differ observably on raw inputs.
The source nil insertion is black, while the provider's is red. Constructor
equalities and root observations establish these distinctions; the provider's
inorder-based `BEq` is not a shape equality test.

Color erasure preserves original pairs, all-node predicates, optional/default
lookup, arbitrary-suffix enumeration, maximum height and internal-node count.
It does not commute with balanced and unbalanced insertion as tree equality.
Exact inorder preservation by balance is an all-raw equality, retaining
duplicates and original keys. Predicate preservation also works for arbitrary
Boolean comparators.

### Semantic hypotheses and shared contracts

Balance preserves BST from both valid children and both full-subtree strict
separators. Insertion preserves BST under strict-comparison reflection.
Neither theorem needs RB. Balance lookup and same-key lookup retain those weak
ordering premises without decoder injectivity; distinct-original-key lookup
adds injection and original-key inequality. Noninjective-decoder examples keep
that distinction observable rather than imposing an unnecessary order on the
original key type.

Presence remains independent of the caller default. The raw `bound_value`
statement is `∃ value, ∀ default`. Successful optional search gives an original
enumerated pair on raw trees with reflection and key identification; conversely,
enumerated membership gives presence and lookup for all defaults under BST,
without injection. The two absence converse laws retain those different
scopes. BST alone gives strict decoded enumeration, source non-strict sortedness
and nodup of projected original keys, with no payload order or RB premise.

Source insertion's enumeration follows accepted replacement-aware `kvsInsert`.
Head-winning list decoding, enumeration abstraction and the independent
collision-removing structural abstraction are reused through actual color
erasure. Their source update and coherence laws retain the stated validity and
identification hypotheses. Equal partial bindings determine canonical inorder
lists for BSTs; equal values for one fixed default do not.

The actual source operation record instantiates `EnumeratedTable.ModelLaws`
for both abstractions, the separate strong-elements contract, and
`TotalTable.Laws` with validity `BST`. The existing `Ops.restrict` adapter gives
the BST subtype its unconditional partial-map `OrderedMap.Laws`. No unrestricted
raw enumerated-table law is asserted for source rotations.

### Parent colors, path bounds and connected clients

The source predicate indexes a hypothetical parent, while the provider indexes
the root. The exact bridge is red parent to black provider root, and black
parent to an existential provider root color. Nil has black height zero.
NearlyRB is exactly nonempty plus the provider's `RedRed True`; its temporary
red-root case may have two red children. Both simultaneous `ins_rb`
conclusions hold for arbitrary Boolean comparisons at the same black height.
Logical parent weakening leaves the tree unchanged. Actual root blackening
may change black height, so its result and final insertion quantify the new
height existentially.

The minimum-depth proof establishes black height at most minimum depth and
maximum depth at most twice black height plus one. It proves the exact advanced
source result, for either parent color:

```text
height t ≤ 2 * mindepth t + 1.
```

The provider's separate size result gives `height t ≤ 2 * (t.size + 1).log2`;
nil and singleton endpoints retain the `+1`. The bound also transfers to the
actual erased BinaryTree height and internal-node count. These are shape
results, without BST or comparison hypotheses, and do not yet establish
operation work or physical running time.

[RedBlackTrees](../../Examples/RedBlackTrees.lean) retains isolated rotations,
overlap priority, cross-side repairs, arbitrary comparisons, suffixes, full
replacement and malformed-tree behavior. Its malformed key3/default999 case
enumerates the written payload303 while directed lookup remains absent.
[RedBlackMaps](../../Examples/RedBlackMaps.lean) consumes ordering and model
laws, including the distinction between presence and a stored default and
between ordering and RB. [RedBlackShapes](../../Examples/RedBlackShapes.lean)
uses actual constructor/repair rules, parent weakening, changing root black
height, asymmetric path lengths and logarithmic endpoints.

[RedBlackHistory](../../Examples/RedBlackHistory.lean) executes the existing
chronological `bindAll` client with both actual operation records. The writes
`[(3,303),(1,101),(3,333),(-2,202)]` retain three bindings. The ordinary tree has
height 3 and the colored tree height 2; both give optional queries
`[-2,1,2,3]` the results `[some 202,some 101,none,some 333]`. Their inorder lists
agree while their erased shapes differ. The general client instantiates both
accepted model contracts to prove equal partial meanings after arbitrary
shared histories, and derives signed optional-lookup agreement. Separate
history clients preserve BST under reflection and black-root shape for
arbitrary Boolean comparisons. Connected higher-universe payload cases check
the absence of payload-class restrictions.

### Validation, preservation and the remaining chapter work

Development evidence retains exact source/case bytes, commands, exits and
outputs. Import/setup and proof-script failures remain distinguished from
genuine missing-obligation cases. All actual public types and relevant private
helpers require review. The 53 anonymous raw-operation examples are checked
by elaboration but discarded from the exported environment. A separate
inspection captures their real temporary InfoTree types from unchanged source;
they are counted separately from named authored declarations and exhaustive
kernel-audit roots.

The frozen checkpoint gates are the guarded focused imported-owner build,
complete unchanged upstream audit body, every new public signature plus the
retained 172-signature Extract probe, complete statement/body assessment,
independent Standards/Spec review, exact candidate reconstruction, final live
identity checks and durable publication. Whole-library build, exhaustive
whole-library audit and receiving acceptance remain separately delegated.
No whole-library verification receipt is supplied by these focused checks.

All 79 predecessor payload paths, fifteen operational files, CTB79–91 records,
five historical 036 draft files plus their README, and the complete prior
coverage prefix remain retained. Current Extract runtime sources and its
correspondence are unchanged. The accepted039 execution object is preserved
whole inside a current-candidate retention envelope, with its original
candidate, tree and observations intact. Current verification reparses and
hashes the actual runtime project closure, checks focused coverage and live
dependency artifacts, and checks the retained executable and fourteen selected
generated-C files. It does not represent old executions as new040 runs or
claim that selected C covers every linked module. The producer's existing narrow
runtime category and all archive/path/hash/type/size guards remain unchanged.

The canonical work recurrences remain open: exact short-circuit comparison
counts, balance attempts 1/2/3/4/5/5, sequential datatype observations at most 17,
actual measured return values, syntactic construction bounds including final
blackening, exact enumeration calls/cons operations, explicit weighted bounds,
qualified logarithmic families and costs along actual valid histories. Shape
alone does not discharge these requirements.

The extraction command at line 799 and the ordinary/balanced runtime comparison
also remain open. They must use these proved operations through both actual
Lean launch modes, retain identical controlled input lists and the source's
fresh-query timing discipline, and independently check full results, distinct
size, height and hits. Historical timing ratios and unrun large recipes remain
historical or unrun. Redblack may be source-qualified only after those remaining
obligations and their own acceptance gates are complete; Trie follows then.

## Redblack: measured resources and shared execution (CTB-93)

This continuation supplies the mathematical resource and runtime components
left open by CTB92. It preserves the complete preceding coverage ledger and
the pure Redblack source correspondence. The verified checkpoint041 records
the final qualification gates; successful local implementation alone does not
advance the chapter. The canonical parent remains CTB14, and CTB15 Trie is
next after full Redblack qualification.

The complete inventory remains 45 source records, 13 exercise headings, five
Check commands and the extraction command. Every pure source row and exercise
retains the CTB92 proof mapping. The remaining source obligations now map as
follows; the expanded derivation is in
[vfa-redblack.md](vfa-redblack.md#checkpoint-041-measured-work-and-comparative-execution),
and actual execution correspondence is in
[vfa-redblack-runtime.md](vfa-redblack-runtime.md).

| Canonical obligation | Implemented source and evidence |
| --- | --- |
| Actual sequential source balance, including failed recognition and overlap priority | `Resources.RedBlack.balanceRun`, actual red-node decompositions, six guarded exact branch equations, all-raw value erasure and complete cost form; `RedBlackBalanceWork` isolated/overlap/fallback cases. |
| Independent primitive observations and no guessed instrumentation | Eleven-coordinate natural `Metric`/`Cost`; existing measured bind consumes the actual comparator, subtree and suffix results. |
| Search and insertion recurrences | Actual `lookupRun`, `insRun`, `makeBlackRun`, `insertRun` and their raw erasure; original-input L/Q/M/T descent equality and exact root overhead. |
| Concrete operation bounds | `L<=height`, `Q<=2L`, input-sensitive `M<=2*K*height`, `B<=L`, `P<=5B`, `D<=17B`, internal `A<=3B+1`, public `A<=3*height+2`, `R=1`, `T<=1`. |
| Enumeration work | Raw arbitrary-suffix erasure, exact generic accumulator projection, `E=2*size+1`, `C=size`, all other metrics zero and whole-cost suffix independence. |
| Declared prices and logarithmic work | `weightedHom`, explicit lookup/insertion affine coefficients including terminal and blackening costs, actual RB size-log bound, operation-specific uniform and varying-comparator families, exact weighted enumeration. |
| Actual histories and current sizes | Existing `run` and `bindAll`, actual `scanl` prefix theorem, separate BST/RB preservation, per-write cost and weighted logarithmic sums on the real preceding states. |
| Shared complete workload meaning | `buildRun_meaning`, ordinary/balanced complete-meaning and optional-lookup agreement, actual source count equal to `expectedHits`, sourceIndices schedule equality, weighted build/query split and actual query sums. |
| Connected cases | Literal primitive/weighted expectations, replacement with no growth, all-hit/missing/empty/signed/default-presence cases, higher payload universes, actual growing Int prefix families and the accepted four-write height3/height2 comparison. |
| Source line799 extraction and both launch modes | Shared public driver selects exact proved operation records; direct Lean and fresh standalone execution, retained source/generated-C/ELF identities, actual output and statement correspondence. |
| Ordinary/balanced controlled and source-shaped comparisons | Identical shared replay files, fresh query generation in the source interval, separate untimed complete-map/size/height/BST/color/black-height checks; independent iterative preorder observer. |
| Historical versus actual timing | Raw elapsed-nanosecond observations are recorded by mode; named million/20,000 recipes and published OCaml ratios remain expressly historical or unexecuted. |

The unit-comparator four-write history has actual prefix sizes
`[0,1,2,2,3]`, per-write A counts `[2,3,2,6]`, and total
`L4,Q5,M5,B3,P8,D15,A13,R4,T3,E0,C0`. The final models agree although the
ordinary and balanced shapes differ. The general history theorems preserve
that separation for arbitrary chronological writes. Primitive source counts
remain distinct from heap allocation, native instructions, physical sharing,
stack use and elapsed time.

The affine lookup slope is `wL+2*wQ+2*K*wM`, with intercept `wT`. Insertion
adds `wB+5*wP+17*wD+3*wA` to the slope and has intercept `2*wA+wT+wR`.
Actual Nat-indexed operation families use their actual size function and
shape certificates. A varying comparison-work bound remains a factor
`1+K(i)` in the majorant. No family silently equates write count with distinct
size or interprets a fixed signed carrier as having unbounded capacity.

The direct and compiled bounded controlled comparison on 128 consecutive
inserted keys has 131 queries, 129 hits and equal complete bindings; observed
heights are 128 and 8. These facts come from actual shared inputs and separate
output validation, not from assuming performance. The source-shaped 32-key
comparison keeps RNG/schedule/conversion/lookup/hit consumption in the stated
query interval, with construction and checks outside it. The independent
observer checks all-descendant ordering and distinct color invariants from
raw shape tokens and rejects coherent but invalid reported trees. All 26
historical runtime test names remain; ten new tests exercise this extension.

The whole-scope review base remains the original
`268324a30dfed30f85e38d490dae873f00796ac7`. Exact final source, compiler,
configuration, dependency outputs, focused imported-owner audit, every new
public signature, the unchanged previous 466-signature output, actual runtime
mode parity, archive reconstruction and independent Standards/Spec reviews
form the acceptance gates. No whole-library `.lake/verification.json` is
created. Full-library build, exhaustive audit and receiving acceptance remain
separate delegated obligations.

Historical checkpoint039/040/041 executions retain their original source and
executable attribution. Their meaningful modeled/empirical conclusions are in
[vfa-redblack-runtime.md](vfa-redblack-runtime.md) and the corresponding source
owners. [CTB-93 and CTB-78](../textbooks/CTB.json) distinguish the donor result
from current receiving acceptance. Predecessor payload counts and recursively
embedded runtime envelopes are not continuing mathematical requirements.

When the final resource/runtime/coverage gates and both independent review
axes pass, CTB14 is source-qualified and the VFA count becomes 12 of 17.
That leaves Trie, Priqueue, Binom, Decide and Color. FDSA and PFDS retain
their preceding qualified/open status. All three complete books remain the
standing task; this checkpoint is a recovery point before continuing Trie.

## Trie: arithmetic, tables and collision semantics (CTB-94)

This bounded increment continues canonical CTB-15 after Redblack. The complete
[Trie correspondence](vfa-trie.md) maps the pinned primary source's 55 records,
12 exercise headings, 11 pedagogical commands and substantive prose. It records
the exact source identity, maintained owners, assumptions, connected cases and
every remaining resource obligation. **Trie is not yet source-qualified.** VFA
remains 12 of 17; FDSA, PFDS, source readiness and receiving acceptance retain
their existing status.

The useful staged positive-key mathematics now has a maintained owner in
[PositiveKeys](../../Applications/Numerals/PositiveKeys.lean), with the staged
source retained unchanged. Numeric value and shifted table key remain distinct:
positive one has value 1 and key 0; the source ten has value 10 and key 9. Both
key round trips, PNat correspondence, injectivity and arbitrary observation
transport are proved. [PositiveArithmetic](../../Applications/Numerals/PositiveArithmetic.lean)
retains all eighteen source carry-addition cases, including nested successors,
and reuses the existing successor and correct comparator. It supplies all nine
comparison cases, numeric correctness, the source append printer, the reversed
bit-list adapter and positive bit-length/power/logarithm bounds. These are
value and size results, with no inferred conversion or execution costs.

[PositiveTrie.Basic](../../Applications/Search/PositiveTrie/Basic.lean) uses the
existing raw `BinaryTree` together with a stored default. Lookup is exactly
`getOrElse`; insertion follows all six source key/tree cases and creates
default-filled intermediate nodes. Same-key and different-key laws hold on
every raw tree and for arbitrary payload universes. The invariant is `True`.
The existing total-table interface is instantiated without payload equality,
ordering or inhabitation assumptions, including raw tables whose own default
differs from the chosen empty default.

[PositiveTrie.Models](../../Applications/Search/PositiveTrie/Models.lean)
relates that implementation to total natural functions through the shifted key
bijection. It proves the source abstraction exercises and consumes existing
table/history, function-update and Squares APIs. The source tree and query
examples check writes at positive ten and three, hence natural keys nine and
two. Equal total meanings need not imply equal raw trees, and optional filler
presence does not identify explicit writes. Low-bit-first word behavior uses
the existing WordCoalgebra interface; its finite-state claim concerns only
states reachable from one fixed tree. Absorbing-leaf word semantics is a value
correspondence and does not identify its steps with early-stopping lookup.

[Collisions.Basic](../../Applications/Search/Collisions/Basic.lean) runs the
actual query-before-write client over existing total-table operations. Its
independent specification is input length minus deduplicated length. The
finite seen-set conservation proof gives complete correctness and every
processed prefix's seen keys. Separate arbitrary-state and injective-key
transport theorems require no finite-support premise on initial functions.
[Collisions.Representations](../../Applications/Search/Collisions/Representations.lean)
connects the source Nat/function, signed-binary/function and positive-key/trie
programs, retaining `c + 1` versus `1 + c` and signed arbitrary initial counters.
The actual three source numeral lists each return one. Three repeated keys
give two collisions; this result is not a count of unordered equal pairs.

The [number](../../Examples/PositiveNumbers.lean),
[trie](../../Examples/PositiveTries.lean) and
[collision](../../Examples/CollisionCounting.lean) clients exercise those public
results with both carry directions, comparison override, size endpoints,
nontrivial defaults, type-valued payloads, overwrite histories, signed negative
keys and counters, and the distinction between shifted and unshifted labels.
Actual frozen-candidate statement inspection, guarded focused build/audit,
independent Standards/Spec review, exact reconstruction and durable publication
remain the checkpoint gates; the source map itself does not assert those gates.

Before qualifying Trie, continue measured successor/addition/comparison,
sequential binary-counter amortization, concrete unary and signed-binary
history costs, actual trie visits/constructions, the long-single-key separating
family, accepted Redblack collision specialization and the qualified asymptotic
progression. No new timing benchmark is requested for Trie. Checkpoint-041's
runtime executions remain historical with their own candidate and controls;
current identity checks do not make them new executions. Whole-library build,
exhaustive audit and receiving acceptance remain separately delegated. Once
this bounded increment is secured, continue these remaining Trie obligations
before Priqueue and all later chapters of all three books.

## Trie: complete measured resources and qualified growth (CTB-95)

This increment completes the seven resource groups retained by CTB-94 under
canonical CTB-15 and upstream owner #558. The [complete source ledger](vfa-trie.md)
still maps all 55 primary records, 12 exercise headings and 11 pedagogical
commands. [Trie work](vfa-trie-work.md) records the actual measured algorithms,
all tariffs, independent parameters, proof endpoints, examples and operational
qualifications. Source qualification is conditional on the exact frozen
validation and both existing independent review axes. Once those gates pass,
Trie brings VFA to 13 of 17 units including Preface, with Priqueue, Binom, Decide
and Color remaining. FDSA/PFDS readiness, later chapters and appendices, and
receiving acceptance remain open.

[Measured positive arithmetic](../../Applications/Resources/PositiveArithmetic.lean)
follows actual successor, all eighteen carry-addition cases and all nine
comparison cases. Erasure reaches the accepted programs. Constructor visits
and changed-digit writes are separate: terminal positive one costs one visit
and two writes. All nested terminal-side successor work is included in the
maximum-input-bit-length addition bound. The comparator has exact minimum
operand bit-length work, with equal-length worst cases and arbitrarily long
comparison-against-one separators.

[Positive counters](../../Applications/Resources/PositiveCounter.lean) connect
canonical Nat.bits observations to existing BinaryCounter execution through
full measured result-and-cost equalities. Exact potential holds on the same
Resources.run trajectory with arbitrary initial credit. From positive one,
N increments cost at most 2N writes; for N>0 the average is at most two.
Before states1 through N, finalN+1, and N-1 transitions for N observed states
remain distinct. Existing Num supplies the zero-capable nonnegative counter,
with its one first write, actual c+1/Nat/toZNum laws and local potential bridge.
No random expectation or general persistent-branch guarantee is inferred.

[CollisionWork](../../Applications/Resources/CollisionWork.lean) specializes
existing measured execution to one read-before-write client over independent
counter/table carriers. Its transport, invariants, additive cost sums and
counter potential are consumed by all four concrete realizations. The
[history realization](../../Applications/Resources/CollisionHistory.lean)
keeps ordinary newest-first update lists, a total-function decoder and an
exact prefix history-length/distinct-key theorem. It measures the displayed
Boolean unary equality at min(x,y)+1, the actual first-operand unary c+1
counter, and a concrete signed comparison using measured positive comparison.
Key tests, key work, lookup terminals, history cells, counter work, wrapper
calls, loop steps and loop terminal remain separate observations. Exact source
loop erasure and independent repetition-count correctness are preserved.

The complete history totals are bounded by
nD(M+1)+nD+n(n+1)+4n+1 for unary keys and
2nD(B+1)+nD+6n+1 for signed binary keys. Here n is occurrence count, D is
distinct-key count, M bounds magnitude, and B bounds the defined signed bit
length, with zero length one and sign work separate. Literal c+1 unary counter
work has an exact quadratic identity; the binary counter uses same-trajectory
potential and includes wrapper dispatch. Neither counter is omitted from the
whole-program bounds.

The [balanced-tree client](../../Applications/Resources/CollisionRedBlack.lean)
consumes the accepted Redblack implementation and actual lookup, insertion,
balance, shape and height contracts. BST/key-enumeration invariants connect
stored size to D. Its comparator is the concrete signed binary less-than run,
and its counter is the measured Num increment. The corrected total bound is
90(n+1)(B+1)(1+log2(D+1)), with a nonempty n-form and a more precise operation
tariff retained. No fourth tree implementation or unit-cost-comparison
shortcut is introduced.

[Measured positive tries](../../Applications/Resources/PositiveTrie.lean)
follow the actual raw look/ins recurrences. Look may stop at a leaf; insertion
has exactly one recursive call and one syntactic node-construction event per
key digit. The common collision client retains source1+c, costing two unary
calls under the chosen first-operand model. Trie calls are at most twice the
sum of input bit lengths, constructions at most that sum, and total work is
at most3S+3n+1, hence3n(B+1)+1. The iterated-bit0 singleton family has one
distinct inserted key but arbitrarily long insertion and lookup paths. Default
filler nodes are not separately inserted keys.

[CollisionGrowth](../../Applications/Resources/CollisionGrowth.lean) specializes
all four actual measured clients to length at most n and natural keys in the
half-open interval0≤k<2n. Shifted encoding has value k+1; that offset appears
in the bit bound. A positive logarithmic scale handles empty and small inputs.
The standard real asymptotic progression is O(n³), O(n²log n), O(n(log n)²)
and O(nlog n), with explicit finite operation bounds first. The distinct unary
interval n through2n-1 incurs at least(n+1)n(n-1)/2 equality work and has the
matching cubic upper bound; the tight-family result is not a lower bound for
every input. The other three stages remain upper bounds.

Connected clients cover actual source lists, empty/short inputs, repeated keys,
signed negatives and zero, nontrivial defaults, higher-universe payloads,
arbitrary initial histories/counters, exact observation vectors, long paths,
shifted endpoints and indexed workload families. All four representations
compute the same independent length-minus-deduplicated-length result after
the stated injective input observations. Cost equality is never inferred from
that value agreement.

The operational boundaries remain explicit. OfNatSucc conversion, numeric
casts, parsing and printing lie outside native-positive lookup work; a
bijection does not establish logarithmic conversion. Absorbing-leaf word
semantics does not establish equal lookup cost. Digit writes and syntactic
constructors do not certify heap allocation, sharing, GC or wall time. The
contextual imperative comparison assumes in-range keys and a declared RAM
array model; no universal pure-update impossibility theorem is asserted.
Trie requests no timing benchmark. The historical checkpoint-041 runtime
observations keep their original input identities and are not new executions.
[CTB-94/CTB-95](../textbooks/CTB.json) retain the bounded Trie qualifications.
Current CTB-78 requires receiving whole-library validation, exhaustive audit and
independent Standards/Spec review. Complete mathematical coverage and meaningful
case distinctions remain above and in the ordinary source owners; old payload
counts and recursive receipt copies are not continuing requirements. Later VFA
chapters are already locally qualified at the donor. New formalization follows
the current integration gate, with all remaining FDSA/PFDS scope preserved.

## Priqueue: exact maximum occurrences and measured list operations (CTB-96)

The complete [Priqueue correspondence](vfa-priqueue.md) continues CTB-16 after
secured checkpoint043. It maps all 43 lexical declaration records, both grouped
standard exercises, both module obligations and the substantive source prose.
There are no inventoried pedagogical commands. The commented premature module
End and the selector's inner admission receive explicit dispositions. The
primary member is9,029 bytes / 273 lines, SHA256
`e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d`.
The unchanged canonical plan is SHA256
`0028ed8013db98fb62e365eb31153ab5030d027bc9a3b9d06f7e8fbb43a42c7d`.
The frozen validation and independent CONTENT gates determine source
qualification; when they pass, Priqueue brings VFA to 14 of 17 units including
Preface, with Binom, Decide and Color remaining. All other books' outstanding
chapters, appendices and source-readiness boundaries remain open.

[MaximumQueue](../../Applications/Search/MaximumQueue.lean) keeps an ordinary
carrier, four Nat-key operations, separate validity and abstraction predicates,
and exactly the eleven source proof fields. Guarded witness existence and
uniqueness up to permutation give a well-defined occurrence observation.
Successful deletion has a valid residual and an actual witness, returns an
occurring original maximum, removes exactly one copy and reduces length by
one. Native merge adds both multiplicities and lengths; every actual result
witness is covered. No source signature axiom becomes a new project axiom.

[ListMaximumQueue](../../Applications/Search/ListMaximumQueue.lean) reuses the
accepted comparison-first selector under the reversed natural order. It
preserves both branches, candidate-retaining ties and exact source remainder
construction. Cons insertion, Some/None deletion and operand-order append
operate on ordinary lists. True validity and identity abstraction remain
distinct from permutation observation. All 11 individual laws and the complete
bundle are proved, including the source auxiliary Forall premise and the
literal successful-deletion Forall wrapper.

The Unit/OrderDual adapter retains source execution and requires an explicit
observation witness. General guarded implementations use the valid subtype;
all-valid lists retain their raw carrier. Native merge is observed separately
because the existing ExactQueue operations have no meld field. A constructive
Option-list implementation checks invalid-state boundaries. The common
[queue client](../../Examples/MaximumQueueClients.lean) builds and natively
merges two queues containing three copies of 7, proves two successful maximum
removals and retains one copy. Both source lists and the accepted leftist
queue discharge the same client. Their final observations agree by
permutation without equating carrier states or raw residual shape.

[ListPriorityQueue](../../Applications/Resources/ListPriorityQueue.lean)
measures the actual comparison-first execution. Calls, comparison invocations,
actual comparator work and source cons constructions are separate coordinates.
Erasure reaches each actual source operation; unit projection agrees with the
accepted measured selector and append copies. Tail length n gives n+1 calls,
n comparisons and n cons; full queue length N gives N+1 delete/selector calls and
N-1comparisons/cons, including empty and singleton. Merge with left length m
has m+1 calls, m cons and no comparisons, independently of the right length.
Pairs/Options are uncharged, and the source merge alias adds no second entry
charge. These are declared source observations, not native allocation counts.

Explicit nonnegative weights and a local per-comparison work bound give
proved linear envelopes and real IsBigO results for actual size-indexed
families. Empty-left merge refutes a lower bound in total size for every
operand split; growing left lists attain the copy count. Actual lockstep
unary comparison costs min(head,candidate)+1. Changing-candidate examples have
work 5 and 16, while equal large keys make comparison work unbounded at fixed
queue length 2. Thus the unit-comparison account and magnitude-bounded unary
account remain distinct. Value agreement never implies agreement of costs.

Connected examples cover exact remainders, both branches and ties, duplicate
merge, repeated deletion, count/length/max consequences, identity-versus-
permutation abstraction, generic unlawful comparators, asymmetric merge cost,
independent key/payload universes and actual measured compositions. No new
runtime benchmark is requested. The later Binom measurement exercise remains
open; inherited runtime executions keep their original exact identities.

Frozen focused checks, full actual type/body/case assessment, both original-
base independent review axes, exact recovery reconstruction, final live gates
and successful checkpoint publication remain separate requirements. Preserve
all 121 predecessor payload paths, 95 targets, 15 operations, six historical objects
and CTB79–95 history. Whole-library build, exhaustive audit and receiving
acceptance remain delegated. After Priqueue is accepted and secured, proceed
to CTB17 Binom and continue the remaining chapters and appendices of all
three tracked books.

## Binom: dense queues, full deletion and amortized work (CTB-97)

The complete [Binom correspondence](vfa-binom.md) continues CTB-17 after
secured checkpoint 044. It maps all 44 lexical records, all 21 exercise
headings including the optional measurement exercise, the complete source
module, the actual Eval command and substantive prose. The authenticated
primary is 13,042 bytes / 400 lines, SHA256
`f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed`.
The unchanged canonical plan is SHA256
`956eacc44542fc26fe5dee1b7a4cd119acb00f6f92ed82d46dc17ccdbdec77c7`.
Both required readings have complete text attribution and explicitly bounded
visual-inspection attribution. Once exact-candidate CONTENT acceptance derives
qualification, Binom brings VFA to 15 of 17 units including Preface, with Decide
and Color remaining. Outstanding chapters and appendices in the other two books
remain open.

`Search.BinomialQueue` uses the existing binary-tree carrier and a dense list
of rank slots, including holes. Its raw source recursions preserve all ties,
argument orders, malformed fallbacks and the arbitrary-continuation CPS unzip.
Inductive occurrence relations account for every duplicate and every supplied
permutation witness. Rank validity distinguishes a child's root bound from its
sibling's external bound. Full successful deletion follows the literal first
maximum under a total preorder, reconstructs the selected slot and correctly
based children, removes one occurrence, preserves validity and retains stored
length. None includes arbitrary all-nil padding. Eleven explicit Nat laws and
the accepted valid-subtype ExactQueue adapter expose the source operations;
native merge has its separate occurrence theorem.

The measured layer executes those exact recursions with 18 separate coordinates:
12 source entry counters, comparison count, actual comparator work, cons, nodes,
closures and continuation applications. Exact erasure covers raw malformed
states and arbitrary measured comparators. Linking, scans, CPS work, selected
prefixes and full deletion have explicit bounds and nonunit comparator premises.
The actual occupancy increment connects to the accepted binary counter.
Sequential insertion comparisons plus final potential equal initial potential
plus the number of insertions; nonempty builds from empty use strictly fewer
comparisons than insertions. Explicit weighted boundary credit gives linear total
fixed-tariff build work. A persistent-fork example prevents reusing one initial
credit twice.

The exact insertion/merge/deletion length laws support actual admissible mixed
histories with initial padding B and historical mass bound H. Every retained
merge operand must satisfy the same capacity premises. Building and draining
N inputs leaves exactly `N.size` nil slots. Logarithmic operation and n-log-n
history families therefore retain their explicit capacity, validity, fixed
tariff and comparator-work hypotheses; they do not assert logarithmic cost in
current mass for every valid padded forest.

`DecodedBinomialQueue` proves complete result transport to signed Int64 and
bounded Nat correspondence, including source-list selection. Shared abstract
clients build, natively merge and remove repeated maxima while retaining old
versions. The [runtime note](vfa-binom-runtime.md) describes actual source
binomial/list execution, checked ranges, seeded/replay/ordered/equal inputs,
drain/mixed/native-merge/padding schedules, independent complete occurrence and
raw-structure observation, and comparative sizes 32/128/512 with explicit
warmup, repetition and order policy. The final runtime gate covers the full
legacy harness and both direct/compiled modes; finite elapsed observations are
separate from mathematical resource theorems.

The complete source/exercise/resource maps above and ordinary Examples owners
preserve the mathematical Binom coverage. [CTB-97](../textbooks/CTB.json) retains
its original donor qualification; CTB-78 owns current whole-library/runtime
acceptance and independent review. Historical type/body assessments and execution
envelopes remain attributed to their actual inputs without requiring every older
payload or runtime object inside the next checkpoint. Source qualification,
actual measurement, exact reconstruction and durable publication are distinct.
Current remaining work follows the canonical catalog and receiving gate, while
every remaining FDSA/PFDS chapter and appendix stays in scope.
