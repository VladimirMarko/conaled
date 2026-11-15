# FDSA-002 — exact chapter requirements

Recorded 2026-11-02 during read-only preparation, before activation of Chapter2.
Chapter1 remains unaccepted. This document does not authorize a change to the
chapter sequence or confer acceptance on any shared draft.

## Governing request, source and frozen inventory

The complete user request is `../REQUEST.md`. Formalize the entire pinned book
in Lean, harmonized with conaled and its AGENTS/workflow requirements. Track
tickets locally, make no GitHub writes, and preserve/expose/upload recoverable
checkpoints as they are created. Independent Standards and Spec review,
example-driven development, statement review, the applicable full guarded
build and exhaustive axiom audit remain required.

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July27,2026 edition, Chapter2 printed pp.13–29. PDF SHA-256:
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The exact Isabelle, AFP and pinned Lean/Mathlib sources are recorded in the
following inventories and provenance files. These are proof references, not
assumed axioms or evidence of an Isabelle rebuild.

All 107 obligations C02-001 through C02-107 are part of this specification:

| Preparation record | SHA-256 when requirements were recorded |
| --- | --- |
| `research/chapter02-obligations.md` | `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d` |
| `research/chapter02-reuse-plan.md` | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `research/mergesort-proof-plan.md` | `fa19bd92a19f06087da321bc7b4a18f337883bf3be63fe96b0e2da9b43cb2010` |
| `research/quicksort-average-proof-plan.md` | `ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46` |

Paths in the table are relative to `fdsa-control`. The first two records fix
the detailed source scope and reuse mapping, including the corrected C02-024
classification. The latter two give proof routes rather than a requirement
to reproduce a particular proof script. Any later source correction must be
recorded explicitly with its mathematical reason; an implementation difficulty
must not silently remove or weaken an obligation.

The inspected integrated source anchor is
`1aabd512284fe86254278ac631eda061d311050b`. The actual implementation/review base
must be the accepted Chapter1 candidate, with any independently accepted shared
prerequisites identified by commit. Record each immutable candidate and exact
base separately in review/validation evidence. The shared insertion, list-call
and notation drafts do not become accepted dependencies merely by being present.

## Required mathematical and algorithmic content

1. **Specifications and insertion, C02-001–016.** Reuse the existing ordinary
   `List.Pairwise` plus `List.Perm` contracts and standard multiset/set
   observations. Match the source insertion/sort equations, including their
   tie branch and right-fold orientation. Retain all support, length,
   sortedness-iff and cost results. Reuse the measured insertion unit after
   its gates rather than creating another instrumented sorter.
2. **Two-way quicksort, C02-017–024.** Formalize the source first-pivot
   less-than/greater-or-equal recursion, termination, permutation/multiset/set
   preservation and sortedness. Retain the explicit pairwise-append and
   complementary-filter facts. The quadratic worst-case assertion and the two
   probabilistic assertions are separate obligations; the latter are detailed
   below and are not covered by Exercise2.4's deterministic bound.
3. **Top-down merge sort, C02-025–039.** Reuse the actual left-tie source merge.
   Prove its missing converse/support observations. Implement the book's
   floor-left split, its termination and ordinary/keyed correctness. Instrument
   its comparisons on the actual sorted halves and prove the stated merge and
   power-of-two bounds, including the real-log correspondence. Lean's logical
   library sorter uses a different odd-length split; value equality does not
   identify comparison counts.
4. **Bottom-up merge sort, C02-040–057.** Implement adjacent-pair passes and
   repeated passes, with the exact empty/singleton/odd-leftover behavior.
   Preserve flattened permutation, run count, total length and sorted-run
   invariants. Instrument the actual comparisons and prove both the stated
   uniform-length/power-of-two results and the hypotheses needed for them.
   In particular, evenness is required for uniform output-length doubling;
   it is not required for the basic total-length comparison bound.
5. **Natural runs, C02-058–088.** Implement the actual mutually recursive
   scanner and both workers. Ascending runs include ties; descending runs are
   strictly decreasing. Reuse `Batteries.DList` with an explicit bridge for
   every raw source builder satisfying its D law. Retain arbitrary-accumulator
   worker statements, termination, multiset, sortedness, length, run-count and
   comparison results. Compose with the same bottom-up merger. Prove the
   general total-length times ceiling-log run-count bound and the natural-sort
   bound, as well as sorted-input scan/merge behavior.
6. **Uniqueness, keys and stability, C02-089–098.** Reuse existing standard
   uniqueness and stable-sorting interfaces, preserving full payload
   permutation and the order of equal-key payloads. Prove the displayed
   helper claims with their actual hypotheses. Antisymmetry, totality and
   transitivity have distinct roles; a generic helper must not acquire an
   unnecessary global order or payload equality decision.
7. **All exercises, C02-099–107.** Retain exact attained insertion best/worst
   bounds; append-free accumulator quicksort with its arbitrary-suffix law;
   three-way quicksort with duplicates; the supplied quicksort tariff and its
   exact worst case; the actual alternating accumulator splitter and its
   sorter; append-free tail versions of the merge pass and repeated merging,
   with arbitrary accumulator invariants and requested comparison bounds;
   and a concrete non-insertion stable keyed sorter. Ordinary correctness of
   a reordered merge pass is not a stable-sort proof.

The choice of module boundaries must follow reusable domain concepts, not
chapter numbering. Existing Selection partition values may be shared through
a small independent partition interface while preserving existing public
names. Do not make ordinary sorting depend on the complete selection algorithm.

## Exact resource models and probability claims

| Construction | Required observation |
| --- | --- |
| Insertion | Function-entry calls, including the terminal branch, at the actual sorted tail |
| Merge, top-down, bottom-up and natural sort | Head/adjacent-key comparisons; no unstated function-entry, split traversal or DList materialization tariff |
| Quicksort Exercise2.4 | The explicitly supplied call tariff, including predicate cost1 and excluding append traversal |
| Literal append-using quicksort | A separately specified measured execution with both source append occurrences accounted for and a proved bound linking it to the supplied tariff |
| Random-pivot quicksort | The same specified comparison/scan observation plus any separately claimed pivot selection/removal costs |

`Resources.Measured`, `bind`, call-count/list interfaces and existing growth
interfaces supply the shared infrastructure. Value erasure and independent
resource equations are separate obligations. No theorem about mathematical
counts may be presented as a machine runtime, allocation or sharing theorem.

For C02-024, retain these precise mathematical targets, together with their
actual execution and observation correspondence:

- For first-pivot quicksort on a uniform permutation of fixed distinct totally
  ordered keys, the average work is `O(n log n)` in the stated model.
- For fixed distinct-key input and a uniform input-occurrence pivot chosen
  conditionally at every recursive call, expected work is `O(n log n)`.
- The uniform quadratic upper bound has an attained quadratic family for the
  source algorithm and the relevant metric. Show explicitly why arbitrary
  duplicate inputs do not satisfy the preceding distinct-key average claim:
  all-equal two-way partitions retain a subproblem of length n−1 every time.

Use a finite distribution over input occurrences/permutations; do not assume
the payload type is finite or impose an arbitrary distribution on all values.
The average-input and randomized-execution distributions must each be linked
to their actual source executions. If proving only expectations, independence
of the two recursive partition permutations need not be assumed when correct
conditional marginal laws suffice. A full distribution identity, if used,
requires its stronger joint-law proof.

The proposed harmonic identity for the exercise tariff is
`A_n = 8*(n+1)*H_n - 12*n + 1`, arising from a proposed pointwise bridge to
the standard comparison count. It is an independently calculated proof target,
not an axiom. Recovering the asserted asymptotic claims through another fully
proved route is allowed. The source's empty and singleton values, the actual
filter convention, the distinct-key condition, and any append-cost bridge
remain required regardless of the chosen derivation. The pinned AFP
Quick_Sort_Cost source is a reference, not a Lean theorem dependency.

## Connected cases and statement review

Retain the existing stable sorting and measured insertion clients, then add
checked applications that expose consequential distinctions:

- Empty/singleton inputs, duplicate keys and payloads with no order assumption.
- Source floor-left versus library ceil-left comparison counts: `[0,1,2]`
  gives2versus3 and `[2,1,0]` gives3versus2 under the independently specified
  merge-comparison recurrence.
- Odd run counts and unequal run lengths, with counterexamples when a printed
  uniformity hypothesis would be omitted; empty inner runs remain supported.
- Natural scanning across ascending/descending boundaries and ties, arbitrary
  lawful difference-list builders, and a nonempty sorted input yielding one
  run and no merge comparisons.
- Accumulator quicksort with a nonempty suffix, the actual alternating split
  order, and the reversed run order of a tail merge pass without an unsupported
  stability claim.
- Stable equal-key payload filtering through the chosen source sorter and its
  composition with an existing client such as rank/selection observation.
- Small exact probability calculations, zero/singleton boundaries, the
  all-equal quadratic counterexample, and universal distribution/cost laws
  supporting the asymptotic results. Finite numerical checks alone do not
  discharge those laws.

Every new or changed formal claim requires statement review: quantifiers,
domains, satisfiable premises, multiplicities, order/tie choices, actual
executed recursion, observation meaning and resource boundaries. Correct false
printed claims by retaining a checked counterexample and a faithful corrected
statement, with source provenance and an explicit explanation.

## Completion and chapter transition

Do not activate this chapter until Chapter1 is accepted. During implementation,
use the existing conaled implementation/review loop and preserve independent
reviewer roles. For each candidate, retain exact requirements outside its diff,
focused validation evidence, full candidate check/audit evidence and both
independent review outcomes. Preserve all source obligations through corrections.

Close FDSA-002 only after every required obligation has a checked destination or
an explicitly justified explanatory/correction disposition, all applicable
gates pass on the same immutable candidate, and `--verify-candidate` succeeds
immediately before acceptance. Save and upload its acceptance checkpoint before
moving on to Chapter3. A durable draft checkpoint is useful recovery evidence;
it is not a substitute for any of these completion conditions.
