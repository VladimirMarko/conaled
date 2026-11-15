# Verified Functional Algorithms: Lean reconstruction map

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
`Examples.ComparisonPermutations.compareSwap_checkedPrefix` belongs with the
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

`certified_prefix` uses `compareSwap_checkedPrefix`,
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
current library; the separate VFA Sort chapter still needs its own complete
source correspondence and acceptance.

## Remaining chapters

Sort through Color are pending. Their definitions, all exercises, source
algorithm identity, statement review and acceptance gates remain obligations.
Existing sorting, selection, tree, queue, graph and resource libraries alone
do not establish chapter coverage. In particular, alternating-split mergesort
is not generally stable on equal-key payloads; default-valued tables differ
from optional finite maps; maximum priority queues differ from minimum or
key-deduplicating queues; and extraction assumptions need proved realizations.
The preserved source inventory and current local chapter tickets retain these
boundaries and the complete chapter sequence.
