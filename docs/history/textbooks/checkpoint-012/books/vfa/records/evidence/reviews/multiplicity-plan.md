# Source and statement review of the multiplicity plan

Date: 2026-11-02. Reviewer: `vfa_scope`.

**Disposition: no unresolved findings within this planning review.** The plan
accounts for both complete pinned chapters and preserves their mathematical
statements. This is a review of requirements and proposed reuse, not a proof
check, implementation review, mandatory chapter review axis, or chapter
acceptance. Sort, Multiset, and BagPerm implementation/acceptance remain pending
in the stated sequence.

## Exact reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `../specs/1004-1005-Multiplicity-plan.md` | `39eb5bf01936bc326298de880d83b87912902fe693d5b83fb187a4d05e5e6487` |
| Pinned VFA 2.1 `Multiset.v` | `ecdc47863b68bbef0d0579f75f4b5537cfb9f99c00f9b2fcc154eadcfdc9ef95` |
| Pinned VFA 2.1 `BagPerm.v` | `a11149100fcdf0a2c366267288dfbe6538ad0bbc5ba65e53e2c026e1ec8899a7` |
| `../staging/sorting-specs/SortingSpecifications.lean` | `45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c` |

The reviewer read both complete source chapters, the complete plan, the two
declaration/exercise inventories, the shared Lean draft, and its existing
independent review. Hashes were recomputed from the local bytes. The inventory
records were checked against the source and the plan's grouped obligation
tables; merely counting table rows would not establish coverage.

## Coverage assessment

| Chapter | Records covered by the plan | Exercises covered | Advanced exercises |
| --- | --- | --- | --- |
| Multiset | 22 of 22 | 14 of 14 | All four: `contents_nil_inv`, `contents_cons_inv`, `contents_insert_other`, `contents_perm`. |
| BagPerm | 19 of 19 | 9 of 9 | All four: `bag_nil_inv`, `bag_cons_inv`, `count_insert_other`, `bag_perm`. |

Neither chapter has an optional exercise marker. BagPerm's single
`bag_eqv_properties` exercise contains four separate declaration records;
the plan explicitly retains reflexivity, symmetry, transitivity, and cons
congruence. The prose exercise `permutations_vs_multiset` and its
`manual_grade_for_permutations_vs_multiset` record occur in both chapters and
are correctly assigned an explanatory adaptation rather than an invented
mathematical axiom. The eventual comparison should describe the proof routes
actually used.

The Multiset pi example is retained with its exact eleven-element input and
duplicate multiplicities. The final equivalence and arbitrary-function sorting
contract are present in both tables. BagPerm's already supplied source proofs
of `insertion_sort_correct`, `bag_eqv_iff_perm`, and
`sort_specifications_equivalent` are included even though they are not separate
exercise markers; their source `Qed` status does not discharge their admitted
dependencies or the future Lean obligations.

## Statement and representation assessment

| Concern | Assessment |
| --- | --- |
| Function bags | The plan preserves the entire `Nat → Nat` space, not only finite support or the image of `contents`. Its union laws quantify over arbitrary function bags. The everywhere-one counterexample in the shared draft establishes the intended boundary of finite-list observations. |
| List bags | BagPerm remains a raw list plus an observational equivalence. Equality of every count does not become raw list equality, and no quotient is required. |
| Count equations | Source Multiset tests the query against the stored singleton value; BagPerm tests the stored element against the query. The shared draft's `contents_cons_by_query` and `contents_cons` respectively preserve those orientations and the singleton-plus-tail addition order. The plan requires an all-input recurrence bridge for each source definition. |
| Equality assumptions | `LawfulBEq` is presented as a sufficient standard hypothesis for the shared count/permutation theorem. The plan correctly avoids the stronger false claim that every conceivable count-vector encoding of permutation must use lawful equality. Nat supplies the intended concrete instance. |
| Empty inversion | The all-zero observation implies an empty list. Reversing the source equality `0 = contents l x` when using a shared count lemma is an ordinary symmetry step, not a weaker hypothesis. |
| Selected-occurrence inverse | The proposed `n + 1 = xs.count x` premise is the source successor premise. The conclusion retains both `xs = prefix ++ x :: suffix` and the exact remaining count `n`. Membership alone, a length fact, or an erase-only statement would be insufficient; the plan explicitly excludes those substitutions. No occurrence uniqueness or prescribed prefix is claimed. |
| Other counts | The distinct-query hypothesis is retained. The statement concerns inserting the selected value between arbitrary segments and leaves the other count unchanged. |
| Permutation transport | Both implications and their equivalence remain obligations. Reusing the lawful `List.perm_iff_count` characterization is compatible with these statements; it does not eliminate the separate inverse exercises or the source recurrence adapters. |
| Sorting contract | The final equivalence quantifies an arbitrary candidate function, retaining the same sortedness predicate on each side. It proves equivalence of contracts, not correctness of every function. Stability remains a separate existing observation. |

The plan preserves the source orientation of union associativity and calls for
the accepted Sort implementation rather than substituting another sorting
algorithm. These chapters suggest inductive proof routes but do not impose the
explicit alternate-proof prohibition found in Sort. Reusing existing general
count/permutation results therefore does not violate a source proof constraint.
The plan still leaves room for the short direct contents proof that explains
the chapter's alternative method.

## Scope and remaining work

The proposed examples exercise the missing inverse observations and actual
source-sort connection. The shared draft already supplies meaningful duplicate,
function-space, unlawful-equality, and stability boundary cases, so the plan
does not require redundant generic frameworks. Queue composition is confined
to a prospective example using an existing permutation contract; it adds no
queue implementation or dependency to sorting specification theory.

No new Lean statement in the plan has been compiler checked by this review.
Library identifier references are reuse candidates, and exact imports,
hypotheses, proofs, final public names, source coverage mappings, and meaningful
clients remain integration work. The plan says this explicitly and preserves
the separate integrated build/audit, two review axes, candidate verification,
and chapter checkpoint gates. There is no wording that marks either chapter
complete or starts its implementation early.

Only this review file was written. No plan, ticket, main source, staged Lean
source, compiler output, dependency, or cache was changed, and no compiler or
build was launched.
