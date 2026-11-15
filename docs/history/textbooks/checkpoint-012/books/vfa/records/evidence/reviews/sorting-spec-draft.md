# Independent review of the staged sorting specification bridges

Date: 2026-11-02. Reviewer: `reuse_survey`.

**Disposition: no unresolved findings after the SS-1 wording correction.** This
is a bounded independent review of cross-cutting preparation. It is not a Sort,
Multiset, BagPerm, or Perm chapter acceptance review, an integrated build, or
either mandatory chapter review axis. No sorting algorithm or later chapter is
accepted by this record.

## Reviewed inputs and validation boundary

The initial reviewed `../staging/sorting-specs/SortingSpecifications.lean` had
SHA-256 `2582dde9bc3c8621e4ddf8b6bbef6bafcebc0d4cc76820af70e870065aecc1a4`.
After SS-1, the independently inspected file has SHA-256
`45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c`.
Replacing only the corrected comment with its original wording reconstructs
the original hash exactly. Definitions, theorem statements, proofs, imports,
and examples are therefore unchanged by that correction.

The review covered the complete Lean draft, its `README.md` and `VALIDATION.md`,
the exact reference definitions in `reference/vfa/vfa/Sort.v`, `Multiset.v`, and
`BagPerm.v`, and the existing `conaled/Applications/Sorting/Stable.lean` contract.
The draft contains three definitions and twenty-nine theorems, including twelve
examples or specification clients, as its README reports.

The owner recorded an exact-byte focused Lean check of the corrected file,
exit 0 with no diagnostics, under the pinned Nix/Lean environment with
`LEAN_NUM_THREADS=1`. The associated `review-correction.log` is empty. The
reviewer reused that recorded check and did not rerun the compiler, build
dependencies, write caches, modify the draft, or integrate main source. A
read-only source scan found no admissions, new axioms, unsafe declarations, or
native-evaluation proof shortcuts. This scan and the focused check do not
replace the eventual exhaustive project axiom audit or candidate checks.

The validation record accurately distinguishes earlier missing cached imports,
unsuccessful speculative identifier queries, and the first draft's missing
explicit Nat binders from the final successful checks. It does not claim that
the original import probe or every intermediate revision compiled.

## Statement and source-semantics review

| Area | Independent assessment |
|---|---|
| Optional indices | `Indexed` preserves the source `sorted'` quantifier and implication shape: Nat indices, directed `i < j`, and two successful lookups before comparing their returned values. No out-of-bounds values participate. Generalizing Nat elements and `≤` to an arbitrary type and relation is explicit. |
| Default-valued indices | `BoundedIndexed` matches `sorted''`: the source conjunction `i < j < length al` becomes two premises. The bound on `j`, together with `i < j`, proves the bound on `i`. The optional-getD presentation is explicitly related to `List.getD`, so the chosen default is never consulted. |
| Pairwise observations | Equivalence between Pairwise and either indexed shape requires no relation laws. The proofs reuse the existing indexed Pairwise characterization and lookup lemmas. Default independence follows from these actual bounds rather than assuming a distinguished harmless default. |
| Adjacent observations | The adjacent-to-Pairwise conversion uses exactly `[Trans R R R]`; it adds no totality, reflexivity, antisymmetry, or decidability requirement. The source inductive `sorted` has the stated empty/singleton/adjacent-step shape. The draft does not pretend that an unintroduced literal source inductive is definitionally `List.IsChain`; README correctly leaves a literal-inductive adapter to integration if that representation is chosen. |
| Existing key sorting | The left side of `keySorted_shape_iff_indexed` is precisely the body of existing `Applications.Sorting.KeySorted`, and `[LE κ]` suffices for that shape bridge. Record payloads need no order. Direct integration with the existing name remains explicitly pending. |
| Counting equations | `contents_nil`, `contents_cons`, and `contents_append` need only the given Boolean test. The cons equation preserves singleton-plus-tail addition. BagPerm compares the stored list element with the query; Multiset's singleton compares the query with the stored element. `contents_cons_by_query` explicitly reconciles the opposite orientations under lawful equality. |
| Count equality and permutation | Function equality is equivalent to equality at every argument. Under `[LawfulBEq α]`, `contents_eq_iff_perm` reuses `List.perm_iff_count` in both directions, preserving actual occurrences and multiplicities. Full lawful equality is sufficient for this standard interpretation; the resolved SS-1 below concerns only an overstatement of its logical necessity. |
| Unrestricted function space | Source Multiset defines `Nat → Nat`, without finite support. The draft preserves the unrestricted codomain. Its lawful Nat instantiation proves that every finite list omits a value and hence cannot produce the everywhere-one function. This correctly distinguishes the full source space, the image of finite lists, and a finite-multiset representation. It does not assert finite support for arbitrary unlawful Boolean tests. |
| Contract transport | `sorting_specifications_equivalent` quantifies an arbitrary proposed function and proves equivalence of two correctness contracts. It does not assert that an arbitrary function sorts. `recover_pairwise_spec` consumes a supplied observable contract and composes the two bridges; that is a meaningful specification-transport client, not an implementation-correctness theorem. |
| Permutation and stability | The draft's input-to-output permutation direction matches VFA. Existing `StableSort.perm` is output-to-input; symmetry will reconcile this during integration. Neither direction implies stability. Existing `Stable` compares complete equal-key filtered record lists, and the draft correctly retains that as an additional obligation. |

There is no formal statement, proof-structure, assumption, or source-shape
defect identified in the reviewed draft. It introduces a small observation and
transport layer justified by the concrete source contracts, without a new
container hierarchy or duplicated sorting algorithm.

## Examples, counterexamples, and nonvacuity

The examples exercise actual public bridges rather than merely unfolding their
definitions. Nat, Int, and key/payload records give satisfiable concrete
instantiations. Signed values demonstrate that the indexed shapes are not tied
to Nat order, and repeated values demonstrate non-strict ordering. The defaults
-999 and 999 are varied while retaining the same valid-index contract.

The negative examples expose distinct genuine boundaries:

- Successor adjacency on `[0, 1, 2]` holds while the endpoints fail that relation,
  so transitivity cannot be dropped from a general adjacent-to-indexed theorem.
- `[1]` is Pairwise ordered but its unbounded lookups with default 0 fail at
  indices 0 and 1, showing why the bounds matter.
- `[1, 1]` and `[1]` have identical membership but different counts; deriving
  permutation from an assumed count equality yields the independently false
  equal-length conclusion.
- Swapping two distinct String payloads with the same key preserves exact
  contents and sortedness but changes the equal-key filtered list. This is a
  concrete failure of the existing `Stable` observation, not merely a claim
  that stability was not proved.
- An always-false Boolean test equates the count functions of `[1]` and `[]`,
  despite their different lengths. Thus unrestricted arbitrary `BEq` cannot
  uniformly support the permutation characterization.

The reordered duplicate example and append example preserve multiplicities
through the public count bridges. No counterexample depends on an impossible
invariant or an uninhabited hypothesis. The function-transport example is
appropriately conditional and does not misrepresent that condition as a
proved algorithm.

## Finding history

### SS-1 — overstatement of logical necessity — resolved

The initial comment above `contents_eq_iff_perm` said that lawful equality was
“necessary” for counts to characterize permutation. The theorem proves
sufficiency, and the always-false example shows that an unrestricted Boolean
test is inadequate in general. Those facts do not prove that every Boolean
test whose complete count vector characterizes permutation is lawful. For
example, on Bool, comparing each stored value to the negation of the query
swaps the two count coordinates; their equality still determines both
multiplicities although the test is not lawful equality.

Root changed the comment to: “Under lawful equality, counts characterize
occurrence permutation.” README now says the theorem “assumes” LawfulBEq and
explicitly distinguishes this sufficient law from a necessary characterization
of every alternative Boolean test. The reviewer inspected both corrections
independently and verified the comment-only Lean-source change by reconstructing
the original hash. The correction resolves SS-1; no additional finding remains.

## Handoff

The reviewed draft is suitable to retain as checked, independently reviewed
staging preparation. Integration still belongs to the sequential chapter
tickets: choose final public names, connect the existing `KeySorted` name,
place examples appropriately, and discharge the actual source algorithms,
exercises, invariant obligations, and chapter gates. This review grants none
of those pending acceptance claims.
