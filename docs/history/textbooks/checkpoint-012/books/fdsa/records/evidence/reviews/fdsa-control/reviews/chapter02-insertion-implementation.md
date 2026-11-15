# Chapter 2 ordered-insertion implementation handoff

Recorded 3 November 2026. This continues the active Chapter 2 implementation
and its existing full-spec loop; it is not a new shared-unit acceptance.
**Committed source draft; not compiled or accepted.** Both source files and
this handoff are stopped for root's checkpoint and later validation.

## Exact source and authority

- Base: `07e480f6ec9958d4975bb90151005b84f2907614`, the accepted Chapter 1 tip.
- Candidate: `95cfce304b9b63057286acc7d5b20b53d95d8eaa`.
- Branch: `work/fdsa-ch02-insertion-observations`.
- Worktree: `conaled-ch02-insertion`, initially and finally clean at the
  respective commits, with no pre-existing task or unrelated edits.
- Source release: root's explicit message after saved checkpoint 0078, under
  `reviews/chapter02-active-scope.md`. Only the two agreed new Lean paths changed.
- Parent is exactly the accepted base. No root imports, reconstruction map,
  requirements, tickets, dependencies, build artifacts or other source was edited.

| New source | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| `Applications/Sorting/InsertionObservations.lean` | 3,325 / 69 | `e537e85fa7d06db4e3030fbac3ad2123dfa295158ee87480ece9c47a56ee5add` |
| `Examples/InsertionObservations.lean` | 10,998 / 224 | `29ba454b380ab837133863318611b059bc0af385008667d60c410ddedb7ba0f1` |

The three complete stopped preparation reports, the root preflight assessment,
the current Sort/Stable/StableSorting implementations, and applicable AGENTS,
implementation/example-driven/architecture/domain/ADR guidance were read.
The recovered pinned PDF's actual ordinary and keyed insertion passages were
also read from the local research extract. Pinned Mathlib and Lean source reads
confirmed the exact public sublist/filter/permutation/length APIs. No copy of
book prose or imported theory source was added. The source attributes the
chapter to Tobias Nipkow and Christian Sternagel; the proofs are original
applications of existing Lean/Mathlib operations and laws.

## Intended claims and statement review

| New library law | Reviewed mathematical meaning and assumptions | Proof route |
| --- | --- | --- |
| `pairwise_of_orderedInsert` | Inserting cannot remove an old pairwise violation. The observed relation `s` is independent of the decidable insertion relation `r`; `s` needs no decision or order laws. | Actual old-list sublist, then pairwise inheritance. |
| `pairwise_orderedInsert_iff` | Source C02-009: output is pairwise `r` iff input is. Totality/transitivity suffice for constructing sorted output; the reverse implication retains the law-free preceding theorem. No antisymmetry. | The converse above plus canonical `List.Pairwise.orderedInsert`. |
| `orderedInsert_eq_cons_of_forall` | Source C02-095/(2.36): all old members follow the new value, so result is exactly new value cons old list. No input sorting, payload equality or global relation laws. This is a sufficient premise, not a necessary characterization. | Nil/cons analysis and the existing immediate-head branch equation. |
| `filter_orderedInsert_of_neg` | C02-096/(2.37): a rejected new value leaves the complete old filtered subsequence unchanged, including order and duplicates, on arbitrary raw input. | Filtered input-sublist and filtered insertion permutation have equal lengths. |
| `filter_orderedInsert_of_pos` | C02-097/(2.38): a retained new value commutes with filtering when the original input is pairwise under the same transitive insertion relation. No totality/reflexivity/antisymmetry or predicate monotonicity is required. | Apply existing insertion-sublist preservation to the filtered input, prove the lower insertion is unchanged by filtering, and compare exact lengths. |

All library laws quantify over `Type u`, actual supplied elements and finite
lists. No default payload or semantic payload instance is introduced. The
filter premise is explicitly `p a = false` or `p a = true`, matching the Bool
list API. Neither equality compares resource observations. The positive proof's
length equality follows from filtered permutation and insertion length; it does
not assume the intended commutation. Its sortedness premise is the original
input's `Pairwise r`, not sortedness of a different executor's output.

The example module exposes exact canonical source nil/cons equations, the
full-record multiset plus support/length observations, and mapped-key sortedness
iff. Local key-relation law instances are built only where needed. The combined
whole-sort observation uses the actual `insertionOn_spec`: its key equality
decision supports equal-key filtering, with no equality or order on payloads.
No new sorting contract, operation wrapper or cost executor was introduced.

## Cases and public connections

The independently calculated expectations in the stopped case preparation are
retained through public results rather than by testing only isolated arithmetic.
These are currently written proof scripts awaiting root's compiler run:

- `raw_insertion_cannot_repair` consumes the law-free converse for any decidable
  insertion relation, observing the old Nat inversion `[2,0]` with `<=`.
- `all_members_without_sorted_input` connects (2.36) to insertion of 0 into
  `[2,0]`; `tied_head_ignores_inversion` shows immediate insertion of 2 despite
  failure of the stronger all-members premise. Arbitrary payloads with key 2
  connect the same public all-members theorem to the source tie direction.
- Whole sorts over `List Empty` and `List (Nat × Empty)` retain their genuine
  empty-domain cases. There is no attempted inserted value of type Empty.
  Nil counterexamples keep both predicate premises explicit.
- Negative filtering connects the new law to the unsorted flagged input
  `[(1,true),(3,false),(0,true)]`, producing `[(1,true),(0,true)]`. Universal
  always-true and always-false insertion relations exercise the absence of
  any order-law requirement.
- Positive filtering connects the new generic law through the mapped-key
  specialization to `[(0,false),(1,true),(3,true),(4,false)]`, retaining
  `[(0,false),(2,false),(4,false)]`. Both a traversed element and the actual
  stopping head are discarded.
- The lawful-order unsorted input `[3,0]` yields `[2,0]` versus `[0,2]` after
  the two positive routes. A finite existing carrier `Fin 3`, with equality
  plus the directed 0→1→2→0 cycle, provides totality, nontransitivity,
  sorted input, failed output sorting and the differing positive-filter
  results `[0,2]` and `[2,0]`. No new carrier or public instance is added.
- Strict tied keys reverse the two signed-record payloads and fail strict
  pairwise order. The already accepted `StableSorting.sorted_permutation_not_stable`
  supplies the independent nondecreasing/permutation versus equal-key order
  distinction; it is not reproved under a renamed wrapper.
- `signed_tail_fixed` uses the existing insertion-sort fixed-point theorem.
  Both signed stability-proof steps use that actual recursively sorted tail;
  the negative step consumes the new negative law, while the positive step
  composes the new positive and all-members laws. Full stable-sort observation
  comes from the existing contract. The actual signed complete sort also
  disproves preservation of arbitrary filtered subsequences.

The source and examples contain no admissions, additional axioms, native
execution shortcuts or new algorithms. The explicit closed counterexamples
use ordinary `decide` proof terms, subject to later kernel compilation/audit.
No elaboration success is inferred from this source inspection.

## Measured boundary and remaining work

This R-based unit intentionally has no import of the unaccepted X002 prefix.
The prepared positive flagged example has existing X002 insertion subcounts
three before filtering and two after filtering; that expected cost separation
remains in the frozen preparation and is **not** newly compiled here. After
X002 acceptance, root may connect its `insertRun_value` and exact branch costs
to the same example as a measured client. These value helpers neither equate
those counts nor charge the filter, keys, allocation or machine runtime.

`git diff --cached --check` passed before the commit. There was no Lean/Lake
invocation, proof audit, validator-fixture run, source-policy pass, full
candidate record or independent review in this assignment. Root owns public
imports, the source coverage map and exact Chapter 2 integration, followed by
focused compilation, corrections, full immutable-candidate verification,
independent Standards/Spec review and immediate final verification.

No C02-009 or C02-094–098 acceptance is asserted yet. All 112 current Chapter 2
obligations and the other algorithms, cost/probability claims and exercises
remain mandatory. The first foundation prefix is unchanged and retains its
separate required gates. Future proof-only corrections should retain these
statements, premises and independently justified expected cases.
