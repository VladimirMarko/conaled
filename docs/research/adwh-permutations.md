# Ordered permutation generation and finite search

The Chapter 1 permutation material uses existing standard list operations and
adds the positional-selection and first-occurrence-erasure algorithms in
`Applications/Sequences/Permutations.lean`. Checked source derivations and
boundaries are in `Examples/Permutations.lean`; the actual search composition
is in `Examples/PermutationSearch.lean`. Both examples belong to the public
`SquareApplications` import closure.

The ordered positional-choice primitive and its membership/projection laws have
one shared owner, `Sequences.Occurrences`, in
`Applications/Sequences/Occurrences.lean`. The existing `Sequences.Permutations`
names forward directly to that owner. Nested Kruskal and Prim use the same
operation through the retained `ForestKruskalSource.Occurrences` interfaces;
they do not depend on the permutation-generation module. This keeps the exact
choice order and repeated occurrences shared across these applications.

## Three algorithms and their observations

| Generator | Required element equality | Checked contract |
| --- | --- | --- |
| `List.permutations'` | None | Exact textbook insertion order, `List.Perm` membership, factorial output count and original input first. |
| `Sequences.Permutations.bySelection` | None | Each input position is chosen in order; exact source equation, independent `List.Perm` membership, mapping and first-result laws. Its entire output list is a permutation of the insertion output list. |
| `Sequences.Permutations.byErasure` | `DecidableEq` | Each input occurrence is chosen, then `List.erase` removes the first equal value. The actual source order, membership and first-result contracts are retained. |

The insertion recursion already exists as Mathlib's `List.permutations'` and
`List.permutations'Aux`. Their definitions match the source recursion exactly.
The implementation uses them directly, together with `Nat.factorial`,
`List.Perm`, the standard map/flatMap laws and standard lawful erasure.

For `[1,2,3]`, insertion produces
`[123,213,231,132,312,321]`, while positional selection produces
`[123,132,213,231,312,321]`, writing each output word compactly here.
`insertion_perm_selection` relates the full lists by outer `List.Perm`.
Consequently it preserves the count of every output and every Boolean
predicate, including repeated values. It has no input-distinctness assumption.
Its proof tags positions with standard `List.zipIdx`, proves the distinct
tagged case, then maps away the tags through the two exact mapping laws.

This is stronger than membership equivalence. For example, `[1,1,2]` produces
six occurrences, and `[1,2,1]` appears twice. There are three distinct value
lists. The first-occurrence-erasure generator retains the source's membership
comparison; this reconstruction does not assert an additional general outer
multiplicity comparison for that algorithm.

## Independent specifications and recursion

`mem_picks_iff` specifies a choice by decomposing the original input into a
front, selected element, and back. The remainder is the front followed by the
back. This description distinguishes positions without requiring element
equality. `picks_remainder_length` proves that every actual choice removes one
position, and the attached membership evidence in `bySelection` justifies
termination. `bySelection_eqn` removes that proof packaging and exposes the
literal ordered source recurrence.

Both new generators are connected to the independent standard relation
`List.Perm`. No generator's result is used as its own specification. Standard
`List.erase_eq_iff` provides the absent-value/first-occurrence decomposition
for erasure, and `List.length_erase_add_one` justifies its recursive decrease.
The empty input yields the singleton result `[[]]`. The separately retained
`byErasureWithoutBase` counterexample yields `[]` for every input, establishing
the consequence of omitting the source's empty base clause.

## Actual finite-search composition

`Examples.PermutationSearch.next` uses the new positional choices as actual
successors of a state containing a reversed chosen prefix and remaining
input. The shared `FiniteSearch.enumerate` executor runs for the remaining
input's length. Its full ordered leaf list is proved equal to the selection
generator's outputs transformed to final states:

```lean
enumerate next remaining.length (chosen, remaining) =
  (bySelection remaining).map
    (fun result => (result.reverse ++ chosen, []))
```

The readout theorem restores chronological order and places any prior chosen
prefix before the new choices. With an empty prior prefix, readout is exactly
`bySelection remaining`; membership therefore satisfies independent
`List.Perm` semantics. `FiniteSearch.count_eq_length` then supplies the actual
counter's factorial result. Equal successor states remain separate list
occurrences. The proof neither deduplicates them nor assumes an injective
representation.

The checked cases retain six paths for `[1,1,2]`, all six readouts in order,
the frontier partition into three residual counts of two, the arbitrary
stored prefix `[9,8]` read back as `[8,9]`, and exhaustion after every input
position has been selected. A zero-depth empty input has one occurrence;
positive depth after complete selection has none.

## Fold derivations and function values

`insertion_fold` gives the standard right-fold presentation. The composition
spelling is checked separately, and the mapped presentations of selection and
erasure are checked as equations of the same canonical executors. Standard
map, flatten and singleton-fold operations replace the source's bespoke list
wrappers, so no parallel basic-list library or duplicate spelling executors
are introduced.

`insertsWith` is the actual result-function accumulator. Its theorem quantifies
over every function `List α → β`, including arbitrary appended list tails.
The identity specialization recovers standard insertion. The head/tail
`insertStep` fold is proved correct on all reached insertion states; its
explicit empty fallback on malformed states is retained and checked. These
are finite value results, without an implicit lazy or partial-language claim.

Insertion and positional selection work for arbitrary function values because
they do not compare elements. First-occurrence erasure uses the existing
constructive `Fintype.decidablePiFintype` instance for functions on a finite
domain. Only pointwise decidable equality is required of the codomain; it
need not be finite. The checked Boolean-domain client uses natural-number
outputs and verifies first-occurrence behavior and the two output orders.

The resource observation here is output cardinality. A factorial output count
is not a bound on runtime, allocation or arithmetic bit complexity. The
result-function accumulator is proved extensionally correct, with no new
speed claim. Chapter 1's structural/fusion costs and partial/infinite/numeric
material remain separate work.

## Supplied source and declaration reconciliation

The selected sources are from the user-supplied checkpoint 335 reference.

| Source member | SHA-256 | Named declarations in this slice |
| --- | --- | ---: |
| `ADWH/Chapter01/Permutations.lean` | `1a95de12dbf6de945bb5fe0785a593bade9da61fb34d8562d784a46d1a50d64b` | 54 |
| `ADWH/Chapter01/ErasePermutations.lean` | `70f69ae60968a0118f7cbe70ddd0e9256252a5dab86658791d52538c2b08210a` | 28 |
| `ADWH/Chapter01/Interfaces.lean` | `17b51cd1806d370ea3561a3cf7418158a33c81604259e62f9739a61656f89d0a` | Final 5 function-related declarations |

[`adwh-permutations-provenance.tsv`](adwh-permutations-provenance.tsv) accounts
for all 87 selected declarations exactly once. It distinguishes direct
standard replacements, adapted algorithms/theorems, checked applications of
standard results, and canonicalized spelling variants. Each row records the
actual observation and hypotheses; a private positional-tag lemma is marked
as a proof detail. Anonymous source examples are retained among the checked
insertion, duplicate-count, first-erasure, repeated-erasure and missing-base
cases. The other 31 `Interfaces` declarations belong to the separate finite
list reconciliation, so this slice does not close that source module.

Standard definitions and theorem names were inspected in the pinned Lean 4.35
and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. In particular, the exact insertion
definitions are in `Mathlib/Data/List/Defs.lean`, their established semantics
are in `Mathlib/Data/List/Permutation.lean`, and constructive finite-function
equality is in `Mathlib/Data/Fintype/Defs.lean`. The source files are provenance
and reconstruction inputs; no ADWH package is added as a build dependency.
