# Independent review of sorting stability planning

Reviewer: `reuse_survey`. Date: 2026-11-02.
**Disposition: no discrepancies found.** This is an independent read-only
planning review, not chapter acceptance or a mandatory candidate review gate.

Reviewed note: `../source/SORTING-STABILITY-BOUNDARIES.md`, SHA-256
`dba97ea118b343c779d9d11feed6ca4e65c2ebc665454c1642970db4aca83b81`.
The three recorded VFA source hashes were independently verified. Inspection
covered the exact `Sort.v:30–39`, `Selection.v:41–50,77–84,102–103`, and
`Merge.v:47–54,209–217,358–364` recursions, the four named conaled sorting
modules, and pinned Mathlib's `List.Perm.eq_of_pairwise'` statement.

## Independent hand calculations

For Selection, let A=(2,"a"), B=(2,"b"), C=(1,"c"), with comparisons only
on keys. `select A [B,C]` takes the equal-key true branch at B. Its recursive
`select A [C]` takes the false branch and returns `(C,[A])`; reconstructing
the outer remainder prepends B, giving `(C,[B,A])`. With fuel three, the next
call selects B from `[B,A]`, leaving A, so the output is `[C,B,A]`. The key-2
filtered lists are `[A,B]` before and `[B,A]` afterward. The note's trace is
correct and does not exhaust fuel early. This input was not already sorted,
so the trace does not refute a separate sorted-input fixed-point theorem.

For alternating Merge, give distinct records A, B, C the same key. Splitting
`[A,B,C]` produces `([A,C],[B])`; sorting the two-element left list preserves
its order, and the true equality branch of merge takes A then C before B.
Thus f(`[A,B,C]`) = `[A,C,B]`. On that result, split produces `([A,B],[C])`,
and the same calculation gives f(`[A,C,B]`) = `[A,B,C]`.

Both lists satisfy KeySorted. Because B and C are distinct, the first result
differs from its input, disproving fixation of every KeySorted input. Also
f(f(`[A,B,C]`)) differs from f(`[A,B,C]`), directly disproving idempotence.
This conclusion uses the second trace, not merely the first instability case.

The note explicitly calls these hand calculations for a proposed record/key
generalization preserving source branches and reconstruction order. It does
not assign identities to indistinguishable Nat duplicates. Erasing Selection's
tags gives the valid sorted output `[1,2,2]`; erasing Merge's tags gives the
same three equal numbers at every step. Future checked Lean cases are still
listed as obligations.

## Library boundaries and assumptions

- `Applications/Sorting/Stable.lean:13–25` distinguishes Pairwise key order,
  exact-record permutation, and equality of each equal-key filtered record
  list. The counterexamples violate the last field while retaining the first
  two observations. `StableSort.unique` also requires both stability proofs.
- `Applications/Sorting/Merge.lean:71–125` proves filter preservation and
  stability relative to `xs ++ ys`, with both input blocks KeySorted.
  For this alternating split, that concatenation is `[A,C,B]`; it is not
  `[A,B,C]`. The plan does not invent the missing original-input premise.
- `Applications/Sorting/SourceMerge.lean:12–35` contains only the merge
  primitive recurrence and its equality to standard merge, including the
  explicit key-pullback adapter `mergeBy_source`. It does not bridge source
  alternating mergesort to the standard contiguous-split algorithm.
- Pinned `Mathlib/Data/List/Sort.lean:298–305` requires `[Std.Antisymm r]`
  on the element relation for `List.Perm.eq_of_pairwise'`. For distinct records
  with an equal key, both pulled-back inequalities hold without record
  equality. Antisymmetry on keys therefore cannot supply that instance.
  Applying uniqueness to Nat lists, or to mapped key lists after proving their
  sortedness/permutation under an antisymmetric key order, is a valid weaker
  route; it does not recover tagged-output equality or costs.
- `Applications/Sorting/Sort.lean:89–115` supports the stated insertion reuse:
  the source's tail-first recursion and insertion before equals match the
  right-fold behavior after a recurrence bridge. A left fold of the same
  insertion reverses a two-record all-equal input. Existing `insertionOn_spec`
  and `sortOn_eq_insertionOn` retain their explicit key-order hypotheses.
  `sortOn_sorted_fixed` concerns the existing standard sorter; it cannot
  establish the false fixed-point claim for a different source recurrence.

No algorithm was implemented or simulated in code, no compiler or build was
run, and no source/candidate file was edited. The planning note is suitable
to preserve with its stated future proof obligations and chapter-order scope.
