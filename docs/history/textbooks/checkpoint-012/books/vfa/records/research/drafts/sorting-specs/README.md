# Shared sorting specification bridges — staged preparation

**Status: compiler-checked draft; not integrated or accepted as any chapter.**
This is the cross-cutting specification preparation explicitly assigned while
Perm acceptance work continues. No Sort, Multiset, or BagPerm algorithm was
implemented, and no later chapter is marked complete.

`SortingSpecifications.lean` contains three definitions and twenty-nine
theorems, including twelve connected examples or specification clients. The
draft is outside the main repository source graph and is intended to be
preserved with local tickets and checkpoint state.

Source references are the pinned VFA 2.1 `Sort.v`, `Multiset.v`, and `BagPerm.v`;
their exact hashes and declaration/exercise boundaries are preserved in
`../../source/Sort.inventory.json`, `../../source/Multiset.inventory.json`, and
`../../source/BagPerm.inventory.json`. Existing conaled semantics were read from
`Applications/Sorting/Stable.lean` before choosing the bridges.

## Proposed placement

The reusable declarations use namespace
`Applications.Sorting.Specification`. Proposed eventual module:
`Applications/Sorting/Specification.lean`. The checked cases are currently
in `Examples.SortingSpecificationDraft` in the same staging file; separate
them into an appropriate Examples module when integrating in chapter order.
These names are proposals, not an independent namespace decision for root.

The draft imports only the pinned Batteries list libraries. An attempted
Mathlib.Data.List.Sort import found a missing transitive cached artifact;
no build, download, dependency edit, or cache repair was performed. The needed
standard lemmas already exist below Mathlib in Lean/Batteries. This keeps the
draft reusable by Mathlib and conaled without duplicating their basic proofs.

## What the bridges establish

### Ordering observations

`Indexed R xs` states that any two successful optional list lookups at indices
`i < j` return values related by `R`. This is VFA Sort's `sorted'` generalized
from naturals to an arbitrary type and relation.

`BoundedIndexed R d xs` states the same ordering using a default-valued lookup,
with `i < j` and `j < xs.length`. It is the generalized `sorted''` contract.
`boundedIndexed_iff_getD` connects the optional-lookup presentation to ordinary
`List.getD`, the analogue of the source's `nth`.

The following equivalences require **no order laws**, not even reflexivity:

- `pairwise_iff_indexed`.
- `pairwise_iff_boundedIndexed`.
- `indexed_iff_boundedIndexed`.
- `boundedIndexed_default_irrelevant`.

The ordering relation is evaluated only on earlier/later valid positions.
The default is irrelevant because neither lookup can be out of bounds.
The proof composes existing `List.pairwise_iff_getElem` and optional-lookup
lemmas; it does not invent a new sorting predicate on values.

`adjacent_iff_indexed` and `adjacent_iff_boundedIndexed` add exactly a
`Trans R R R` assumption to reuse `List.isChain_iff_pairwise`. Neither totality,
decidability of the relation, antisymmetry, nor reflexivity is needed. Conversely,
pairwise ordering entails adjacent ordering without those laws; the additional
transitivity is needed for the other direction of the equivalence.

VFA's inductive `sorted` has the same empty/singleton/adjacent-step shape as
`List.IsChain`. A chapter adapter can use `List.IsChain (· ≤ ·)` directly.
If a new literal source inductive is chosen instead, explicitly prove its
equivalence to IsChain; this staged file does not assert equality between two
unintroduced inductive types.

### Existing KeySorted seam

`Applications.Sorting.KeySorted key xs` is defined in
`Applications/Sorting/Stable.lean` as
`xs.Pairwise (fun a b => key a ≤ key b)`.
The staged `keySorted_shape_iff_indexed` has precisely that left-hand shape
and needs only `[LE κ]`. When integrated, it can be stated directly with
`KeySorted key xs` by unfolding the abbreviation. It puts no ordering
requirement on payloads. The draft deliberately does not shadow or redefine
KeySorted because existing project outputs were not built for this preparation.

### Occurrence observations

`contents xs : α → Nat` is the function assigning each value its occurrence
count in a finite list. Its type is the **unrestricted function space**;
no Finset, Finsupp, or Mathlib Multiset support condition is imposed on that
space. The definition needs only `[BEq α]`.

`contents_nil`, `contents_cons`, and `contents_append` show the expected empty,
singleton-plus-tail, and pointwise-addition equations. The source's two counting
presentations use opposite Boolean equality orientations: BagPerm's recursion
tests the list value against the query, while Multiset's singleton tests the
query against the stored value. `contents_cons_by_query` proves that alternate
equation under `[LawfulBEq α]`; the distinction is not silently ignored.

`contents_eq_iff_count` connects function equality with equality of every
occurrence count, using function extensionality. It needs only `[BEq α]`.
`contents_eq_iff_perm` additionally assumes `[LawfulBEq α]` and reuses
`List.perm_iff_count`. It retains both directions, so equal counts really
recover occurrence-sensitive permutation. This is a sufficient law for the
standard occurrence interpretation, not a proof that every alternative Boolean
test with a permutation-characterizing count vector must satisfy LawfulBEq.

The source Multiset function space can contain infinite-support observations.
`finite_contents_has_zero` proves that each finite list of naturals omits a
value, and `constant_one_not_contents` proves that the everywhere-one function
is not the contents of any finite list. Thus the whole source function space
must not be identified with the finite list observation image or with a
finite-multiset representation.

### Changing the specification of an arbitrary proposed algorithm

`sorting_specifications_equivalent` converts between two contracts for any
supplied function `f : List α → List α`: pairwise ordering plus permutation,
or the same ordering plus contents-function equality. There is no assumption
that f is a particular algorithm and no theorem that f is correct without
one of those contracts. No ordering laws are needed for the change of contents
observation itself.

`recover_pairwise_spec` demonstrates composition: given an arbitrary function's
contents and optional-index contract, it derives the permutation and Pairwise
contract through both bridges. It is a specification transport client, not a
new sorting algorithm.

These contracts remain weaker than conaled's StableSort: stability is its
separate equal-key-sublist observation. Sortedness plus exact multiplicities
does not determine the order of equal-key payloads.

## Checked cases and statement review

The expected conclusions were chosen independently from the generic proofs.
The positive examples consume the public staged bridges, and the negative
examples expose real assumption/observation boundaries.

| Case | Independent expectation and connected result |
|---|---|
| `signed_indexed` | `[-3,-1,2]` orders all increasing indices; derived from its decidable Pairwise specification through `pairwise_iff_indexed`. |
| `adjacent_to_indexed` | `[1,2,2]` is ordered even with repeated values; `adjacent_iff_indexed` turns adjacent order into the index contract. |
| `signed_defaults` | Defaults -999 and 999 do not affect valid lookups; uses both index-equivalence and default-independence theorems. |
| `nontransitive_boundary` | Successor adjacency holds on `[0,1,2]`, but 0 and 2 do not satisfy the successor relation; demonstrates why transitivity cannot be omitted. |
| `index_bound_matters` | A singleton `[1]` is sorted, while an unbounded comparison with default 0 fails at indices 0 and 1. |
| `multiplicities_matter` | `[1,1]` and `[1]` have the same membership set but unequal contents. The function-equality bridge would force a false equal-length permutation. |
| `reordered_contents` | `[2,1,1]` and `[1,2,1]` preserve both occurrences of 1; uses an explicit Perm.swap through the function bridge. |
| `concatenated_occurrences` | Appending `[1]` to `[1,2]` gives count 2 for 1; uses `contents_append`. |
| `recover_pairwise_spec` | A client can recover the existing mathematical sorting contract from independent index and contents observations. |
| `records_indexed` | Nat keys with String payloads require an order only on keys; consumes the KeySorted-shape bridge. |
| `sorted_contents_do_not_imply_stability` | Reversing two distinct equal-key payloads preserves sortedness and counts but changes the key-filter observation. |
| `lawful_equality_matters` | An always-false Boolean equality test makes `[1]` and `[]` have identical counts while they cannot be permutations; LawfulBEq is consequential. |

Quantifier review: index variables are explicitly Nat; optional values have
the list's element type; `i < j` is directed; the bound on j implies the bound
on i; no out-of-bounds default comparison is included. Function equality
quantifies all values, retaining absent values as count zero and duplicates
as larger counts. The permutation orientation matches the source contract.
Generic relation and equality hypotheses are satisfiable in the checked Nat,
Int and record examples. The counterexamples demonstrate that the stated
boundaries cannot simply be removed.

## Remaining integration work

Root should choose final names, incorporate the direct KeySorted statement,
separate examples as useful, and add public imports at the appropriate chapter.
The actual source definitions, insertion-sort algorithms, their correctness
proofs, and every remaining exercise obligation stay owned by the sequential
chapter tickets. This draft does not claim source coverage for algorithms.

The final staging compile passed with warningAsError enabled. This is not the
integrated project build, exhaustive proof audit, Standards review, or Spec
review. `VALIDATION.md` records the exact commands and outcomes. No independent
review loop was launched for this assigned preparation.
