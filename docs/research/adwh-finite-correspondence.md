# Finite iteration, scan and collapse source correspondences

The [declaration ledger](adwh-finite-correspondence-provenance.tsv) maps 24 source
rows to standard operations, shared laws and connected cases. It retains source
hashes, assumptions and the reason for each adaptation. These correspondences
cover the selected iteration, scan and collapse results, not the whole chapter.

## Source identity and evidence limits

The supplied compact recovery archive has SHA-256
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
The selected members are under `project/adwh-lean/ADWH/Chapter01/`:

| Member | SHA-256 | Selected authored rows |
| --- | --- | ---: |
| `Iteration.lean` | `869286b90db05b9ba8ca82e1b407bada42ce85de7e0c83b405776a8cf35c1c7d` | 9 |
| `ScanFusion.lean` | `143eb5e6f216c89508bf161600ee56b3ca2512997a592cc40626d31a6b09d4a7` | 12 |
| `Accumulation.lean` | `986fb1477c58aae55d010a7e5c3a7376e73156a569f8003636a624494d7c3ac3` | 3 |

The retained companion `project/sources/adwh/code/part0/chap1.hs` has SHA-256
`51bc05fb7aa76ae5fdbb8cdb4e8d8f99d134e1d21dd7a0fff137776268f82711`.
Its original `LINE 839` and `LINE 1077` anchors retain the fixed-count signature
and two equations; `LINE 871` retains the replacement test; `LINE 561` retains
the three exact collapse cases. These are companion-source anchors, not newly
verified book-page citations. The missing textbook PDF and other unfinished
Chapter 1 contracts remain recorded by the historical audit. The entire
queens-16 proof remains excluded by the user.

## Existing owners and small missing equalities

No iterator, prefix/suffix operation, scan algorithm, collapse executor or
numeric wrapper is reimplemented. The shared additions belong to the existing
`SquareKit/Iteration.lean` and `SquareKit/ListFusion.lean` owners. Application
examples remain in the existing iteration, scan-fusion and accumulation example
modules, already imported by `SquareApplications.lean`.

| Source family | Candidate destination and reason |
| --- | --- |
| `apply`, `applyTail`, their correspondence and laws; 9 rows | Use core `Nat.repeat` and Mathlib `Nat.iterate` directly. `Iteration.repeat_eq_iterate` is the missing value-equality bridge. Standard successor, addition and predicate-preservation laws supply the other contracts. |
| Ordered prefix/suffix formulas and fixtures; 4 rows | `inits_eq_range_take` and `tails_eq_range_drop` combine standard length and indexed-element observations into exact ordered list equalities. |
| Literal prefix Scan Lemma; 1 row | `foldl_inits_eq_scanl` connects standard `List.inits.map (List.foldl f e)` to the existing `scanl_prefix_values` theorem. |
| Parity helper family and signed fixture; 7 rows | Native `List.foldr doubleStep 0` replaces the `evenSum` wrapper. The exact `2 * xs.sum` meaning, its parity consequence and the divisibility-test bridge extend `Examples.ScanFusion`. Conditional branch helpers are absorbed by the actual definition and core conditional laws. |
| Original collapse fixtures; 3 rows | Each conjunction states ordinary, cached and difference-list outputs plus the independent `CollapseSpec`. Optimized outputs and specification consume existing public refinement/correctness results. |

The dependency source search found no bridge between core `Nat.repeat` and
Mathlib `Nat.iterate`, nor the exact prefix/suffix range or literal prefix-fold
equalities. It did find their smaller standard building blocks. Core's
`Nat.repeat_eq_repeatTR` concerns a runtime replacement and does not supply the
required Mathlib correspondence.

The pinned dependencies are Lean `leanprover/lean4:v4.35.0`, Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Batteries commit
`66e469188fe07963e5cf666c7d4433f45b8131c5`. Relevant standard owners are core
`Init/Data/Nat/Basic.lean`, `Mathlib/Logic/Function/Iterate.lean`,
`Mathlib/Data/Set/Function.lean`, `Batteries/Data/List/Basic.lean`,
`Mathlib/Data/List/Infix.lean`, and core integer and conditional laws. Exact
source-file hashes and inspected declarations are retained in the local input
manifest; no dependency caches or active validation outputs are part of this
preparation.

### Fixed-count repetition

The bridge quantifies over `α : Type u`, any `f : α → α`, natural count and seed.
Core repetition applies `f` after recursion; standard iteration moves `f` into
the seed. `Function.iterate_succ_apply'` supplies the former orientation and
`Function.iterate_succ_apply` the latter. `Function.iterate_add_apply` preserves
the order `f^[m] (f^[n] x)` for count `m + n`.

Anonymous generic clients in `Examples.RankedIteration` specialize these laws
back to core repetition. Another specializes `Set.MapsTo.iterate` to
`{y | P y}` with arbitrary predicate `P`, its actual preservation premise and a
valid initial seed. It does not export another invariant API. The source
`apply_spec` wrapper identification becomes reflexive after choosing core
repetition itself; the source `applyTail_eq` is the symmetry of the new bridge.
Existing first-hit, ranked, while, divergent and Dijkstra clients are retained.
There is no stopping predicate, rank assumption, commutativity assumption,
runtime, stack, overflow or cost-equivalence claim in the finite bridge.

### Ordered prefixes and arbitrary accumulator states

The standard `List.inits` and `List.tails` definitions retain their empty
observations. Their lengths and `getElem` laws give the exact `range` / `take`
and `range` / `drop` formulas by list extensionality. The literal prefix Scan
Lemma then composes the prefix equality with the existing indexed scan law.
Input elements and accumulator states have independent universes, and both
the seed and transition are arbitrary. No associativity or identity hypothesis
is introduced. The existing literal right-scan theorem
`foldr_tails_eq_scanr` is unchanged.

### Mathematical integer parity

`doubleStep_foldr` states the independent meaning
`xs.foldr doubleStep 0 = 2 * xs.sum` for every finite list of mathematical
integers, including negative elements and the empty list. Its parity consequence
now discharges the reached-context premise in the existing
`restricted_foldr_via_context` proof; the public statement is unchanged.
`replaceOdd_dvd` translates the actual remainder test using
`Int.dvd_iff_emod_eq_zero`.

The source true/false branch helpers are direct specializations of `if_pos` and
`if_neg` after unfolding the existing `replaceOdd`. Their original hypotheses
are preserved in the provenance record. No extra wrapper is needed. The
unreachable odd-state and odd-seed counterexamples are unchanged, and the
restricted commuting condition is not strengthened to a false global law.

## Connected development cases

The mathematical expectations were recorded before editing. Finite reduction
already establishes several small values; the missing work is their connection
to shared contracts. No artificial failing compiler attempt is claimed.

| Candidate client | Independent expectation and public connection |
| --- | --- |
| `iterate_source_fixture`, `repeat_source_fixture` | Five increments of two from three give thirteen. The core fixture uses the bridge and the standard-iterator fixture. |
| `source_inits`, `source_tails` | The exact `[1,2,3]` prefix and suffix lists, including empty observations, follow through the new range equalities. |
| `prefix_decimal_seed` | Seed five and digits `[2,7]` give `[5,52,527]`; literal prefix folds use the generic Scan Lemma. |
| `prefix_ordered_accumulator` | Natural inputs and list-valued seed `[9]` give `[[9],[9,2],[9,2,7]]`. This exercises different element/accumulator types and ordered append. |
| `signed_doubleStep`, `signed_replacement` | `[-3,4,2]` sums to three, so the doubled fold gives six. Replacement uses actual restricted fusion followed by that result. |
| `source_first_positive` | `[[1],[-3],[2,4]]` returns `[1]`; the first block is already positive. |
| `source_exhaustion` | `[[-2,1],[-3],[2,4]]` consumes every block and returns `[-2,1,-3,2,4]`. Earlier boundary sums are zero, minus one and minus four; the final sum is two. |
| `source_later_positive` | `[[-2,1],[3],[2,4]]` returns `[-2,1,3]`; the second block creates the first positive boundary. |

Each collapse client calculates the ordinary result once, derives both optimized
outputs via `cachedResult_refines` and `differenceResult_refines`, and derives
the independent specification via `collapse_spec_iff`. Existing empty-block,
negative-exhaustion, arbitrary-tail, positive-seed and incorrect-cache examples
remain unchanged.
