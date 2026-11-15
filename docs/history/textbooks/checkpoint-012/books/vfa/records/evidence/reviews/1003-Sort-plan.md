# Independent prerequisite review: local #1003 Sort plan

Reviewer: `reuse_survey`. Date: 2026-11-02.
**Disposition: no concrete omissions or incorrect claims found within this
bounded planning review.** Implementation remains blocked on accepted Perm.
This is neither chapter acceptance nor a mandatory current-candidate gate.

## Exact reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `../specs/1003-Sort.md` | `fcc06acf05245de79637600479006e3d4a98f8bdf85c2537f5e7451cf3042955` |
| Pinned `reference/vfa/vfa/Sort.v` | `aeaf646d3b7e4dd88cb5d6dba9d35ae5714e5451c154d90de499bb09a32a7d33` |
| `../source/Sort.inventory.json` | `3d86cab6546eb6efe0d08deefec63181bdb01d7f27a963c972120c2c73126f2c` |
| `../staging/sorting-specs/SortingSpecifications.lean` | `45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c` |
| That draft's `README.md` | `aae009b8094aeec68a610f77e7bf448beb9e04d205e8cdecdf700e87f2d22ba6` |
| `../source/SORTING-STABILITY-BOUNDARIES.md` | `dba97ea118b343c779d9d11feed6ca4e65c2ebc665454c1642970db4aca83b81` |
| `../source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |

The chapter file is exactly 308 lines and 10,864 bytes as recorded. The five
existing code identities in plan §11 independently match: conaled's
`Applications/Sorting/{Sort,Stable,SourceMerge}.lean`,
`Examples/StableSorting.lean`, and pinned Mathlib's `Data/List/Sort.lean`.
The additionally consulted `Applications/Sorting/Merge.lean` has SHA-256
`79b35252d0f551b381ef63974497311336ea92a5d118691647825cade12a1338`.
The earlier reviewed shared specification issues were not reopened.

## Coverage and proof-method check

The obligation table covers the source definitions, both checked examples/
calculations, ordinary correctness results, both advanced equivalence
directions, optional lookup-origin and indexed-insertion claims, and the final
indexed sort theorem. The source's `sorted''` presentation and default
irrelevance are also explicitly accounted for rather than lost because they
lack separate named theorem exercises.

The optional proof restriction is preserved substantively: the planned
`insert_sorted'` derivation cannot hide a detour through Pairwise insertion
correctness and equivalence bridges. Its positional induction plan is sound.
The zero/positive-index case needs the inserted-or-old-value distinction and
an actual successful old-index witness; the plan requires both. The final
indexed sort theorem then uses the independently established insertion result.
The existing source `Qed` depending on an admitted helper is correctly treated
as an obligation to complete, not as independently established evidence.

## Recurrence, assumptions, and existing APIs

Pinned Mathlib `orderedInsert` has the stated nil/cons and left-tie equations;
`insertionSort` is the stated right fold. All-input recurrence bridges require
only the decidable relation. Preservation of sortedness adds totality and
transitivity, while Pairwise/indexed equivalence does not. The IsChain source
adapter, Nat index types, lookup bounds, and reversal of the source versus
conaled permutation orientation are all explicit and appropriate.

The plan uses stable-record correctness only for this insertion recurrence.
Tail-first sorting and insertion before equals support the existing
`insertionOn_spec`; the plan still requires their exact bridge. Its fixed-point
and idempotence goals are valid for insertion sort and do not import the false
tagged fixed-point claim for alternating mergesort. Uniqueness/agreement keeps
antisymmetry on keys, with no unjustified order or equality decision on record
payloads. The named record, payload-map, and negative stability clients exist.

## Resource and representation check

The comparison model is explicit and consistent: no comparison at nil, one
per visited cons, and stopping at the first successful test. Inserting 7 into
the displayed prefix takes four comparisons regardless of the tail after 8.
Summing the length bounds over actual recursively sorted tails yields the
triangular upper bound. Descending distinct `(List.range n).reverse` makes
each insertion traverse its whole shorter tail, so it is a correct proposed
arbitrary-size equality witness; empty/singleton cases are included.

Three reconstructed prefix cons requests plus the two in the literal stopping
branch give five. Four fresh cells belongs to the separately named realization
that reuses the matched node. The plan does not confuse these counts, the
unchanged suffix value, length increase, retained heap size, or GC eligibility.
It correctly requires additional realization evidence if physical sharing is
claimed, and comparator-cost assumptions if primitive counts become weighted
time. Conditional empirical qualification does not assert a local benchmark.

## Scope and handoff

No plan/ticket changes are requested by this review. Its pending baseline
capture, public integration, proof audit, chapter reviews, and durability
checkpoint remain requirements, not completed results. Proposed modules,
signatures, resource recurrences, and examples still need normal elaboration
and proof during #1003. No Sort algorithm, code simulation, compiler/build,
candidate edit, main-source mutation, or repeated broad inventory was performed.
