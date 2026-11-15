# FDSA-X002 insertion-sort costs: independent preflight

Date: 2026-11-02. Status: mathematical/architecture preflight only; **not** a
Standards or Spec acceptance review. No Lean source, repository state or chapter
acceptance status was changed, and no build or audit was run for this note.

## Evidence and scope

Inspected the separate worktree
`/workspace/scratch/845aa1048b05/conaled-insertion-costs`, based on
`1aabd512284fe86254278ac631eda061d311050b`, and the active local ticket
`FDSA-X002`. The two uncommitted files inspected had these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `Applications/Resources/InsertionSort.lean` | `d114ef463ef7b5564d18e29ed198678f7d576e1e3883bb20c315936a6bf52111` |
| `Examples/InsertionCosts.lean` | `75609084d2807e533dd00c3a2844771c8c250924f031dad35b9df3836c56c910` |

Source comparison used FDSA, July 27, 2026, section 2.2, printed pp. 14–15,
and Exercise 2.1 on p. 28, from the pinned PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`
(<https://fdsa-book.net/functional_data_structures_algorithms.pdf>).
Related source obligations are C02-004–016 and C02-099–100. Chapter 3's
existing inventory was consulted only for the intended downstream small-input
selection use, especially C03-027 and C03-032–038.

The local comparisons covered `Resources.Measured`, `Resources.CallCount`,
`Applications.Sorting.{Stable,Sort}`, `Applications.Selection.Rank`, and
Mathlib `Data/List/Sort.lean` at the project's pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`. AGENTS, architectural-quality,
domain/glossary, ADR 0001 and ADR 0010, and `fdsa-control/DECISIONS.md` supplied
the architecture and status boundaries. `SquareApplications.lean` imports
`Examples.InsertionCosts`, which in turn imports the new resource module.

## Assessment

**No mathematical contradiction or architectural blocker was found in the
inspected definitions or claims.** The source recurrences, erasure route and
uniform/exact bounds agree. There is one narrow interface gap against the ticket:
the immediate-insertion theorem currently asks for relations to every list
element even though the branch depends only on its head. A connected selection
example would also substantiate the stated shared-client motivation. Neither
finding calls for a new sorting specification or a general resource framework.

### Exact counting convention

Write `I(x,xs)` for the insertion count and `S(xs)` for the sort count.

| Inspected equation | Source match and consequence |
|---|---|
| `I(x,[]) = 1` | Includes the empty insertion call; this is not zero comparisons. |
| `I(x,y::ys) = 1` if `r x y`, else `I(x,ys)+1` | Exactly the source's conditional recursive call plus entry charge. Equal ordered keys take the first branch. |
| `S([]) = 1` | Includes the empty sort call. |
| `S(x::xs) = S(xs) + I(x,(sortRun r xs).1) + 1` | `bind` uses the actual sorted tail value; `CallCount.tick` charges the outer sort entry once. |

The measured functions are connected to the existing values by
`insertRun_value` and `sortRun_value`. Mathlib's `orderedInsert` has the same
comparison direction and its `insertionSort` is the corresponding right fold.
The project's `insertionOn key` specializes precisely that relation. This is
stronger evidence than equality to an unrelated sorter, and avoids assigning a
source cost to a different algorithm merely because it returns the same list.

Comparisons, key computations and constructors are uncharged by this abstract
model. The module does not claim elapsed Lean execution time. For example,
inserting 4 into `[1,2,3]` has four insertion calls but three comparisons. Future
comparison-cost or expensive-key interpretations should retain this distinction.

### Bounds and equality cases

| Claim in the candidate | Mathematical assessment |
|---|---|
| `1 <= I(x,xs) <= length xs+1` | Correct for every decidable relation, even on unsorted inputs. |
| All `r x y` imply insertion count 1 | Correct, including the empty list; stronger input condition than the local head branch requires. |
| All `not r x y` imply count `length xs+1` | Correct; every list cell and the final empty call are visited. |
| `2n+1 <= S(xs)` | Correct: `n+1` sort entries and at least one insertion entry for each of `n` elements. |
| `2*S(xs) <= (n+1)*(n+2)` and its division form | Correct: insertion into a sorted tail of length `m` costs at most `m+1`; summing gives `1 + n*(n+3)/2`. The division-free form avoids an unnecessary parity dependency. |
| `S(xs) <= (n+1)^2` | Correct weaker source bound, including `n=0`. |
| `Pairwise r xs` implies `S(xs)=2n+1` | Correct without global order laws: the pairwise fixed-point theorem makes every recursive insertion immediate. For `r=(<=)`, duplicates remain allowed. |
| `Pairwise (fun x y => not r x y) xs` implies the triangular equality | Correct: permutation of the recursively sorted tail preserves the universal failure condition for the earlier element. No transitivity or totality is needed. |
| `reverse(range n)` attains the triangular bound for natural `<=` | Correct; its length is `n`, and its values are `n-1,...,0` when nonempty. This preserves the exercise's indexing rather than confusing it with the preceding prose list `[n,...,0]`. |

The two extrema coincide at empty and singleton inputs: the counts are 1 and 3.
For length two they are 5 and 6. Reversed lists with repeated values need not
attain the upper bound for `<=`: `[1,1]` costs 5 because the tie stops immediately.
The candidate correctly uses strict comparison failure, not a merely
nonincreasing list, for its general worst-case hypothesis.

Do not strengthen the best-case theorem into an arbitrary-relation equivalence
with `Pairwise r`: without transitivity, immediate insertions need not establish
every pairwise comparison. The current sufficient statement is sound and covers
the book's sorted-input contract.

### Requirements and reuse boundaries

Operations, value erasure, length and uniform cost bounds assume only
`DecidableRel r`. They require neither an inhabited payload nor decidable payload
equality, reflexivity, antisymmetry, totality or transitivity. This separation is
appropriate. The exact best/worst lemmas expose their list-specific hypotheses
rather than installing global order instances.

`sortRun_stable` uses the existing `StableSort` contract and its existing
`insertionOn_spec` theorem. Its key-side `Std.IsLinearPreorder` and
`DecidableEq` requirements match that API: decidable key equality is used in the
independent equal-key filter observation. No order on payloads is added, and
antisymmetry is not needed just to establish this contract. Antisymmetry belongs
to uniqueness/agreement with another sorter when that later theorem is invoked.

The measured module should remain independent of the Selection library. A
cross-domain selection result belongs in `Examples`, consuming the exported
sorting contract and resource bound. Generic `erasureSquare` can package the
existing erasure theorem if a square-composition client actually needs it; there
is no reason to duplicate that framework merely to wrap this function.

## Focused improvements before final review

1. **Expose the actual head-only insertion premise.** Add a lemma with premise
   `h : r x y` and conclusion `(insertRun r x (y::ys)).2 = 1`, or the stronger
   measured-pair equation `insertRun r x (y::ys) = (x::y::ys,1)`. No relation to
   `ys` or sortedness is required. The existing `insertRun_cost_of_all` remains
   useful for its quantified sorted-list client and can be derived through this
   lemma. A meaningful example is inserting 2 into `[2,0]`: the head tie yields
   cost 1 although `2<=0` fails. The present `[2,3]` example cannot distinguish
   these assumptions.
2. **Connect the same measured run to occurrence rank.** For ordered payloads,
   obtain `hs := sortRun_stable id xs`. If its result has `some a` at zero-based
   index `k`, `Selection.pairwise_ranked hs.sorted hs.perm` gives
   `RankedAt xs k a`. Combine that result with `sortRun_cost_le` for the same
   input. This directly connects the two intended clients without defining a
   new selector or changing the public one-based `selectWith` convention.
   This statement accounts for sorting work only; indexing work must not be
   silently folded into that count.
3. **Make the absence of payload assumptions observable in an example.** The
   generic resource theorem already has the right signature. Strengthening
   `key_contract` to `List (Nat × payload)` for arbitrary `payload : Type u`
   with no instances would make this architectural property checked by a
   client too. Keep the concrete String example for distinct equal-key tags;
   a concrete String payload alone would not expose an accidental future order
   requirement because String has standard order instances.

Other small examples can be selected according to the remaining review risk,
rather than added as a broad test suite. Useful options are singleton count 3,
an arbitrary false relation attaining the triangular bound even with repeated
payloads, or the existing tagged-tie run with its exact count 8 alongside the
stable-filter observation. Existing empty, duplicate-sorted, descending,
insertion-short-circuit and full-traversal examples already cover their stated
cases. `best_is_global`, `worst_is_global` and `source_quadratic` are direct
specializations, so they do not replace the connected selection example.

## Downstream and acceptance handoff

For Chapter 3, the present upper bound supplies the sorting part of the
size-five and size-twenty base cases (at most 21 and 231 sort/insertion calls,
respectively). Its actual `slow_select` and `slow_median` source models also
charge indexing and length traversal, as recorded in C03-032/033. Preserve those
charges and their valid-index/nonempty hypotheses when composing the later
client. Do not describe the numbers 21 or 231 as complete selection costs.

FDSA-X002 intentionally supplies shared resource results, not every Chapter 2
insertion obligation. For example, the ordinary multiset/set adapters and the
one-insertion sortedness iff correspondence still need their Chapter 2 coverage
witnesses; `StableSort` output correctness alone does not close all those rows.
Chapter 1's frozen candidate and the sequential chapter tracker remain unchanged.
Final statement review, stable-candidate verification/audit and both independent
review axes remain required before integration or acceptance.
