# RandomQuickSortRank: first compiler repair

The triggering central attempt is CLOSED, exit1, at immutable clean candidate
`c0440a99c2a503b7816a44367f7e4168378dbbf1`. Recorded elapsed time is
1086.281581494 seconds. The complete 47237-byte log has SHA-256
`d367cd2e1054973cac7d1e1c6fa7d9a278eea9cccfa038b2436c377367b6160e`.
Its recorder and native evidence are preserved under
`chapter02-tail-numerical-rank-operations-focused-20261104-attempt5/`.

I read every one of the 279 lines in `rank-diagnostics.txt`, including all
expanded type-mismatch contexts and the terminal aggregate failure. The rank
resource target failed; its example target's dependent `Ran` entry is not a
successful example compilation. Tail, numerical and natural example failures
are owned by their separate repairs; this change does not rewrite their status.

The repair starts from exact clean author HEAD
`08a1e78d6becc713256d245206ef163f9eb55a0a`. Only
`Applications/Resources/RandomQuickSortRank.lean` changes. The complete 393-line
original core and the full corrective diff were read. The resulting core has
392 lines. The example file, both growth files, both mean files and all checked
pins remain byte-identical to the author start.

## Actual findings and bounded corrections

| Reported source sites | Finding | Correction and preserved meaning |
| --- | --- | --- |
| 37,43,56,73,99,112,131,165,216,323 | The parser rejects an explicit-proof getElem expression when its brackets follow an unparenthesized function application. Later local child terms also generate List/Array-size inference errors. | Parenthesize the intended indexed list value before passing it to `key`, the predicate, or the comparator. The valid occurrence, explicit bound proof, actual erased list and filter predicate remain the same. This includes the occurrenceRank definition body, seven headers and local proof terms. |
| 187 and216 | The equal-length mean theorem is left unfinished after the earlier parser failure, with spurious inferred Array operations on a List. | Repair the reported actual-child term syntax. No induction hypothesis, local distinctness assumption or child-size equality is replaced. Whether all downstream proof goals now elaborate remains for the next compiler result. |
| 305,308 | Dot resolution selects `Equiv.Perm.sum_comp`, whose next argument is a Finset and whose support premise is unsuitable for the requested all-Fintype equation. Associated `i.val` errors follow from that argument mismatch. | Use the fully qualified `Equiv.sum_comp` at both existing reindexing sites. Its pinned theorem sums over all elements of the finite type; the same Fin.revPerm and occurrence-rank permutation are retained. |
| 374 | `simpa only [ht]` normalizes scalar lengths but does not rewrite the dependent Fin index type of the finite sum. | Obtain the actual cons-size equation, rewrite both finite sums with `Fin.sum_univ_eq_sum_range`, then simplify by the existing length equality. The exact actual successor recurrence and all coefficients are unchanged. |
| 385 | The unused-tactic linter rejects a `change` that does nothing. | Remove only that no-op tactic. The successor-to-positive-size derivation and all enabled linters remain. |

The module-system import notices are preserved historical tool output. No
module conversion, linter suppression, compiler flag, dependency or environment
change is made to hide them or any error.

## Pinned APIs inspected

At Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` exposes both relevant
overloads. The additive theorem generated from `Equiv.Perm.prod_comp` takes a
finite set, summand and support-containment premise. The additive theorem
generated from `Equiv.prod_comp` has exactly the desired full-Fintype reindexing
equation. Explicit qualification selects that existing API without a new lemma
or stronger assumption.

`Mathlib/Data/Fintype/BigOperators.lean` supplies
`Fin.sum_univ_eq_sum_range`, generated from its named product theorem. It takes
a Nat-indexed summand and size and rewrites a Fin-index sum to the corresponding
range sum. This removes the dependent-domain simplification issue before the
already established equality `tail.length = m` is used. The pinned Lean
`Init/Data/Nat/Lemmas.lean` also confirms `Nat.add_left_inj` is the existing
right-summand cancellation used in the unchanged same-length proof.

## Header and mathematical statement assessment

The root explicitly authorized minimal parentheses in the definition and
headers after reading the parser diagnostics. It would be inaccurate to report
all headers byte-identical or to claim equality of previously elaborated types:
the original declarations at these sites failed to parse.

Exactly seven source headers change, only by explicit parentheses around the
same intended indexed value:

- Public `occurrenceRank_lt_iff`, `left_length_eq_rank`,
  `right_length_eq_rank`, `child_keys_nodup`, and `left_length_law`.
- Private `filter_length_eq_card_indices` and `strict_filter_length_eq_rank`.

Every before/after header is recorded in `header-assessment.json`. Their binder
types, independent universes, mapped-key Nodup hypotheses, selected Fin index,
key relation, actual erased/filter children, Nat lengths and actual PMF laws are
unchanged by source assessment. The other 12 core headers are byte-identical.
The occurrenceRank definition still takes the inverse of the same sorted key
tuple; only its key argument's syntax changes.

All 19 core declaration names (12 public, seven private) and all 18 example
declarations remain. Thus all 37 authored claims, including all 30 public
claims, retain the approved intended contracts and every case. Both source
growth files remain frozen at their exact G identities. No actual run,
sampler, cost projection, recurrence, numeric expectation or asymptotic premise
is weakened or replaced.

The successor remains uncompiled. The correction is a bounded source response
to the closed diagnostic evidence, not a claim that every remaining elaboration
goal has passed. Root must run the next exclusive focused compiler cycle and
complete explicit statement inspection. Full immutable-candidate check/audit,
both independent acceptance axes and immediate verification remain mandatory.
No acceptance or coverage closure is claimed.

Public documentation preparation is paused coherently in the new
`chapter02-public-documentation-draft-20261104/progress.json`. Its complete
537-line reconciliation and 112-row scope were read, but no final public
documentation/map/import draft is claimed completed. No existing control or
handoff record was overwritten.
