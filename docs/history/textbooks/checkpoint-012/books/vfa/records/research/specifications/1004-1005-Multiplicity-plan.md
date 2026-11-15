# Shared multiplicity planning for local #1004 and #1005

Status: source/reuse planning only, written while #1002 waits for its mandatory
integrated validation. This does not implement or accept Multiset or BagPerm.
Chapter implementation order remains Sort, Multiset, then BagPerm.

## Exact sources and existing preparation

The complete pinned VFA 2.1 chapters were read for this note:

| Chapter | Source SHA-256 | Inventory |
| --- | --- | --- |
| Multiset | `ecdc47863b68bbef0d0579f75f4b5537cfb9f99c00f9b2fcc154eadcfdc9ef95` | 22 declaration records, 14 exercises; see `../source/Multiset.inventory.json`. |
| BagPerm | `a11149100fcdf0a2c366267288dfbe6538ad0bbc5ba65e53e2c026e1ec8899a7` | 19 declaration records, 9 exercises; see `../source/BagPerm.inventory.json`. |

Their official versioned archive and recovery hashes are recorded in
`../source/SOURCE-RECOVERY.md`. Immutable inventory coverage fields describe
the source inventory, not completed Lean acceptance.

The already checked shared draft is
`../staging/sorting-specs/SortingSpecifications.lean`, SHA-256
`45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c`.
Its count/permutation/function-equality theorems and negative cases are usable
preparation, not automatic chapter coverage. See its README, VALIDATION, and
`../reviews/sorting-spec-draft.md`. Sort should integrate only the ordering
portion it needs; these chapters can then integrate the multiplicity portion.

## Keep the source representations distinct

Multiset defines the unrestricted function space `Nat → Nat`, including
functions with infinite support. Its empty value is the zero function,
singleton tests the **query against the stored value**, and union adds counts
pointwise. Its union laws quantify over all functions, not merely functions
arising from finite lists. Use ordinary pointwise operations and existing
addition laws; no new algebraic hierarchy is needed. Do not replace this whole
source space with Lean's finite `Multiset` or `Finsupp`.

BagPerm defines a bag as `List Nat`. Its recursive count tests the **stored
value against the query**, and its bag equivalence compares all occurrence
counts. Bag equivalence does not identify the raw list representation by Lean
equality. Reuse `List.Perm` through the proved count equivalence; no new quotient
representation is required to cover this chapter.

The checked draft already records both singleton equations, with their equality
orientations, and proves that the everywhere-one function cannot be finite-list
contents. Under `LawfulBEq`, `List.count` gives the intended equality-based
occurrence interpretation. This is a sufficient standard assumption, without
claiming that every conceivable permutation-characterizing test must satisfy it.

## Small common proof layer

The source's advanced inverse exercises have the same mathematical content in
both representations. Implement them once over lawful list counts and transport
them through the exact source recurrence bridges. Proposed statement shapes,
not compiled new declarations:

1. If every occurrence count of a list is zero, the list is empty.
2. If `n + 1 = xs.count x`, there are lists `prefix` and `suffix` such that
   `xs = prefix ++ x :: suffix` and `(prefix ++ suffix).count x = n`.
3. If `y ≠ x`, inserting `x` between two list segments leaves the count of `y`
   unchanged.

The second statement retains a decomposition witness and the exact remaining
count, which is stronger than merely asserting membership. It does not assert
that the selected occurrence is unique or that a particular prefix is returned.
The third statement must retain the inequality hypothesis and the query/value
orientation when translated to the source definitions.

Relevant declarations were located in the pinned Lean 4.35 source, rather than
inferred from names in another version:

| Reuse | Pinned source location | Role |
| --- | --- | --- |
| `List.count_pos_iff` | `Init/Data/List/Count.lean` | A positive count supplies membership. |
| `List.mem_iff_append` | `Init/Data/List/Lemmas.lean` | Membership supplies the prefix/selected-occurrence/suffix decomposition. |
| `List.count_append`, `List.count_cons`, `List.count_cons_self`, `List.count_cons_of_ne` | `Init/Data/List/Count.lean` | Compute the remaining multiplicity and preserve other counts. |
| `List.count_eq_zero` | `Init/Data/List/Count.lean` | Relate zero count to absence, without discarding multiplicity. |
| `List.perm_iff_count` | `Init/Data/List/Perm.lean` | Existing complete equivalence between lawful occurrence counts and permutation. |
| `List.count_erase_self`, `List.count_erase_of_ne` | `Init/Data/List/Count.lean` | Optional connected removal client; do not replace the source's explicit decomposition witness with an erase-only claim. |

The pinned source root is the Lean toolchain's `src/lean` directory. The compiler
and toolchain identities are recorded in `../environment.md`. These reuse
pointers are planning evidence; final exact imports, hypotheses, and proofs must
be compiler checked during integration.

## Multiset coverage obligations

| Source records/exercises | Required coverage |
| --- | --- |
| `value`, `multiset` | Explain the Nat alias and preserve the unrestricted function space. |
| `empty`, `singleton`, `union` | Exact pointwise equations and recurrence connection; no finite-support restriction. |
| `union_assoc`, `union_comm`, `union_swap` | Laws for arbitrary function bags, with the source's associativity orientation. Derive from pointwise Nat addition and function extensionality. |
| `contents` | Exact empty and singleton-plus-tail recurrence, bridged for every list to the common occurrence observation. |
| `sort_pi_same_contents` | Retain the source input `[3,1,4,1,5,9,2,6,5,3,5]`; a checked case must consume the source-sort contents theorem and preserve repeated entries. |
| `is_a_sorting_algorithm'` | Input/output contents equality together with the source sortedness adapter from the accepted Sort chapter. |
| `insert_contents`, `sort_contents`, `insertion_sort_correct` | Prove the actual source recurrence's content preservation and combine it with accepted sorting correctness. Do not silently substitute a different implementation. |
| `permutations_vs_multiset` and grading stub | Explain the two proof routes and their tradeoff; the manual preference checkbox is not an algorithm or a proposition needing an invented Lean axiom. |
| `perm_contents` | Permutation preserves the contents function. |
| `contents_nil_inv`, `contents_cons_inv`, `contents_insert_other` | Preserve all advanced inverse statements via the shared lemmas above; retain source hypothesis orientations. |
| `contents_perm`, `same_contents_iff_perm` | Both directions, not merely a count-preservation theorem. Reuse the checked bridge to `List.perm_iff_count`. |
| `sort_specifications_equivalent` | Quantify over an arbitrary proposed sorting function and preserve its ordering contract unchanged. |

For the direct content-preservation exercises, a short induction following the
accepted source insertion recurrence can use the union laws without first
assuming insertion permutation. Retain that proof route if it clarifies the
chapter's method; use the common count/permutation equivalence for the final
specification transport. No duplicate general proof of the standard permutation
characterization is required merely because the source develops it from scratch.

## BagPerm coverage obligations

| Source records/exercises | Required coverage |
| --- | --- |
| `bag`, `count`, `bag_eqv` | List representation, exact stored-value/query recursive count, and pointwise equality of counts. Prove the all-input bridge to the shared observation. |
| `bag_eqv_properties`: `bag_eqv_refl`, `bag_eqv_sym`, `bag_eqv_trans`, `bag_eqv_cons` | Equivalence and congruence under prepending; keep this observational equivalence distinct from raw list equality. |
| `is_a_sorting_algorithm'` | Input/output bag equivalence and the same sortedness contract. |
| `insert_bag`, `sort_bag`, `insertion_sort_correct` | Consume the accepted source insertion/sort adapter and the common contents result, with explicit permutation orientation where needed. |
| `permutations_vs_multiset` and grading stub | Preserve the explanatory proof comparison; no artificial executable grading artifact. |
| `perm_bag` | Forward occurrence-preservation implication. |
| `bag_nil_inv`, `bag_cons_inv`, `count_insert_other` | Reuse the common inverse lemmas with the exact source count bridge. All advanced exercises remain in scope. |
| `bag_perm`, `bag_eqv_iff_perm` | Reverse implication and full equivalence. |
| `sort_specifications_equivalent` | Arbitrary-function contract transport, without adding stability or an algorithm premise. |

## Connected cases and architectural integration

Reuse the existing checked duplicate/permutation, absent-count, unlawful-BEq,
infinite-support, and equal-key-instability cases where they directly consume
the final public declarations. Add only cases needed to exercise newly exposed
claims: a positive-count decomposition with a remaining duplicate; preservation
of a distinct query under insertion; empty-content inversion; raw lists that
differ but have equivalent bags; and the source's pi-prefix example.

The accepted Sort chapter supplies the actual algorithm and sortedness bridge.
The common count observation also composes with existing conaled queue laws
expressed using `List.Perm`, for example `LeftistQueue.entries` insertion and
deletion laws. Any universal cross-domain composition belongs in `Examples`
under ADR 0010; keep domain specification theory independent of queue imports.
This note proposes no new queue implementation or queue chapter acceptance.

Each chapter still needs its own exact coverage map, checked source adapters and
clients, integrated build/audit, both independent review axes, final candidate
verification, and immediate uploaded acceptance checkpoint before the next
chapter starts. This shared plan does not change those gates.
