# Verified Functional Algorithms: Lean reconstruction map

This work reconstructs Andrew W. Appel's *Verified Functional Algorithms*,
Software Foundations volume 3, in the existing conaled library. The user has
explicitly requested whole-book coverage in chapter order, including optional
and advanced mathematical exercises. This is additional scope alongside the
method-oriented toolkit objective of upstream issue #174; it does not close
that broader workstream or select one canonical data structure.

The [preserved VFA records](../history/textbooks/checkpoint-012/books/vfa/README.md)
retain the original local tickets, review findings and validation evidence.
Historical VFA ticket references use `VFA-0`, `VFA-2`, and so on.
The [exact commit registry](../history/textbooks/issue-lineages.md) resolves old
unqualified messages; no GitHub number range is reserved for them.
Current coverage and follow-up are owned by
[issue #558](https://github.com/VladimirMarko/conaled/issues/558).
The map below describes mathematical coverage; source implementation alone is
not accepted chapter coverage. Acceptance requires the recorded candidate's
build, proof audit, both review axes and final verification.

## Source identity and scope

- Author: Andrew W. Appel; editor: Benjamin C. Pierce.
- Edition: **2.1 (2026-08-24 10:11), Coq 9.0.0 or later**.
- [Official contents](https://softwarefoundations.cis.upenn.edu/vfa-current/toc.html).
- [Official source archive](https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz).
- Archive SHA-256: `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
- `Perm.v` SHA-256: `0d3ad2421a6bee80b987423b702e8688e59fe802cafa1efa9b98df71d619fd9f`.
- [Source license notice](../licenses/vfa-MIT.txt).

The order is Preface, Perm, Sort, Multiset, BagPerm, Selection, Merge, Maps,
SearchTree, ADT, Extract, Redblack, Trie, Priqueue, Binom, Decide, Color.
The pinned source inventory in the recovery state includes every explicit
declaration and exercise marker. Aborted teaching attempts are distinguished
from their later successful results; grading stubs and proof-assistant commands
are distinguished from mathematical claims. The inventory is a lexical aid,
not a Rocq parser or a verification of the upstream proofs.

The Preface's adaptation is this source identity, full chapter scope, Lean
prerequisites in the repository README, and the acceptance policy above.
Lean replaces Gallina and its proof language; the existing conaled contracts
determine module placement and reusable interfaces. The source's optional
OCaml execution material will need an explicit Lean execution adaptation and
representation boundary in Extract. It is not covered by the Perm work.

## Perm: comparisons and permutations

Implementation: `Applications/Sorting/FirstPair.lean`.
Checked specializations: `Examples/ComparisonPermutations.lean`.

The reusable operation `Applications.Sorting.compareSwap` accepts an arbitrary
Boolean comparator. It always preserves occurrence-sensitive `List.Perm` and
the suffix after the first two entries. Comparator asymmetry suffices for
idempotence. A separate branch contract relates the comparator to an arbitrary
relation for the first-pair ordering theorem. No total order on payloads,
transitivity, heap model, or runtime performance assumption is introduced.

`compareSwap_map` transports the operation along a comparison-preserving map;
the checked record specialization maps strings to their lengths and needs no
injectivity or order on payloads. The composition theorem
`Examples.ComparisonPermutations.compareSwap_checkedPrefix` reuses the
existing `OrderCertificate.adjacent_correct` consumer on the first two entries.
This is representation transport within Lean types and a bounded library
composition, not a claim of transport across arbitrary mathematical settings.

In the following table, unqualified example targets are in
`Examples.ComparisonPermutations`; generic targets are in
`Applications.Sorting`.

| Source declaration or exercise | Lean target and adaptation |
|---|---|
| `geb`, `gtb` | `geb`, `gtb`; reversed natural-number comparisons computed by `decide` |
| `lia_example1` (aborted and final), `lia_example2`, `lia_example_3` | Corresponding arithmetic theorems; `omega` reasons about truncated natural subtraction and treats the arbitrary function/product term as an expression |
| `truncated_subtraction` | `truncated_subtraction`, with the counterexample `k = 0` |
| `maybe_swap` | `maybeSwap`, specializing `compareSwap gtb`; the two-entry recurrence is unchanged |
| `maybe_swap_123`, `maybe_swap_321` | `already_ordered`, `first_calculation` |
| `eqb_reflect`, `ltb_reflect`, `leb_reflect`, `gtb_reflect`, `geb_reflect` | Same-named Boolean/proposition equivalences; `decidable_of_bool` supplies Lean's existing proof-carrying decision adapter; `reflectedLt`, `reflected_true_branch`, and `reflected_false_branch` check its executable specialization |
| `reflect_example1`, `reflect_example1'`, `reflect_example2` | Corresponding checked branch examples; `false_branch_reflect` also checks the negative comparison branch |
| `maybe_swap_idempotent` (aborted and final) | `maybe_swap_idempotent` through `compareSwap_idempotent` and the proved `gtb_asymmetric` law |
| `Permutation_properties` | `permutation_length`, `permutation_symmetry`, `not_a_permutation`, `four_values_permuted`; the three requested additional properties are `permutation_reflexivity`, `permutation_transitivity`, and `permutation_membership`; `permutation_occurrences` additionally preserves each multiplicity |
| `manual_grade_for_Permutation_properties` | Administrative grading marker replaced by the preceding checked properties |
| `butterfly` | `butterfly`, via append commutation and permutation composition, retaining arbitrary repeated variables |
| `permut_example` | `permut_example`, with arbitrary list arguments and the source's exact rearrangement |
| `not_a_permutation` | `not_a_permutation`, a kernel-checked finite decision; no native evaluation shortcut |
| `maybe_swap_perm` | `maybe_swap_perm` through comparator-independent `compareSwap_perm` |
| `first_le_second` | `FirstPair (· ≤ ·)`; the definition is vacuously true for zero or one entry, exactly as in the source |
| `maybe_swap_correct` | `maybe_swap_correct` through `compareSwap_correct` and the proved `gtb_order_law` |
| `Forall_perm` | `forall_perm` transports universal membership predicates; `forall_perm_inductive` uses `List.forall_iff_forall_mem` to connect the source-style `List.Forall` contract |
| `bdestruct`, `inv`, browsing commands | Use `by_cases` and `simp` with `decide` equivalences; `omega` handles linear arithmetic. `cases`/`rcases`, `subst`, constructor disjointness and injectivity provide inversion. `#check`, `#print` and source search replace Coq inspection commands. No redundant custom tactic language is introduced. |

### Statement review and connected cases

The independent calculation is `[3, 2, 1]` mapping to `[2, 3, 1]`.
`first_calculation_spec` and `first_calculation_idempotent` exercise the general
correctness and idempotence results on that calculation. `empty_case`,
`singleton_case`, and `repeated_values` cover the short-list and equality
branches. `not_whole_list_sorted` refutes the stronger claim that this single
comparison sorts the whole list. `certified_prefix` supplies the existing
ordering checker with precisely the prefix justified by the new theorem.
`positive_after_swap` composes the source permutation theorem with universal
predicate preservation. `record_map` checks the representation-map law without
requiring ordered payloads or injective representation changes.

The statements quantify over arbitrary tails and comparators where permitted.
The branch laws are proved for the natural-number realization; they are not
assumed as the desired result. Ordering covers only the first pair; permutation
preserves duplicates; natural subtraction is truncated. The Boolean reflection
equivalences and the `List.Forall` bridge preserve the source's positive and
negative branches and element quantifiers. No correctness claim depends on an
admission or an application-specific axiom.

## Remaining chapters

Sort through Color are pending. Their definitions, exercises, source algorithm
identity, and acceptance gates remain obligations. Existing related sorting,
selection, tree, queue, graph, and resource libraries do not by themselves count
as coverage. In particular, alternating-split mergesort is not generally stable
on equal-key payloads; default-valued tables differ from optional finite maps;
maximum priority queues differ from minimum/key-deduplicating queues; and
extraction assumptions must be discharged by actual realizations rather than
introduced as axioms. The local source inventory records these boundaries.
