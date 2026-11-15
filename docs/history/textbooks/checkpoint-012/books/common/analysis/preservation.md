# Textbook integration preservation preflight

Date: 2026-11-13. Scope: read-only source/evidence audit for the enclosing
implementation workflow. No source edits, compilation, mathematical acceptance,
environment troubleshooting, or GitHub mutation occurred in this audit.

Pinned target master: `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
Original shared source base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
The user requires local checkpoint-persisted issue/spec tracking. Historical
process holds and statuses in imported records are evidence, not current orders.

## Decisive finding

Merging only the three candidate refs would omit substantial recovered work.
FDSA has **65 distinct Lean paths (67 file versions) absent from its candidate**
across its preserved task-branch tips; none exists at the same path in the pinned
master. It also has 36 existing paths with 81 earlier/alternate versions that
need preservation accounting, not indiscriminate replacement. VFA has five
substantive standalone drafts outside Git. PFDS's additional branch tips contain
no absent Lean path after normalizing the historical `conaled/` directory wrapper.

These are source-identity observations. A missing path does not prove a missing
capability under another name, or establish that the draft compiles or should be
adopted unchanged. Keep all 131 original refs and immutable records while deciding
each mathematical disposition against the pinned library's actual interfaces.

## Three candidate boundaries

| Book | Candidate | Change from original base | Acceptance boundary retained |
|---|---|---|---|
| VFA | `eae9e110adc7ba1cc28386448a6deef23e406c13` | 26 paths, 22 Lean | No accepted chapter. Preface/Perm remains blocked; focused116-module success is not a completed full build/audit. |
| FDSA | `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe` | 184 paths, 169 Lean | Historical local Chapters1–3 and shared-unit acceptance; no acceptance for the new integration. Chapter4 remains unaccepted. |
| PFDS | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | 170 paths, 159 Lean | Chapter1 is introductory source accounting; Chapter2 remains unaccepted. Latest full observation is nonterminal, despite focused signed-potential success. |

Source roles and exact original names are owned by checkpoint `source/refs.json`.
PFDS's original main is `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`, not its
latest candidate. All branch names below are under original `refs/heads/work/`
for FDSA; their durable names prepend `refs/checkpoint/fdsa/heads/work/`.

## FDSA work beyond the main candidate

The table groups capabilities rather than generating another file inventory.
Short object IDs are unambiguous in the restored bundle; full identities are in
`source/refs.json`. Chains retain distinct source/review bases and corrections.

| Draft family / original branch | Preserved tip(s) | Material needing a disposition |
|---|---|---|
| `fdsa-tree-fold`, `fdsa-tree-accumulator`, `fdsa-tree-traversal-work` | `b0fce71f` → `b035f115` → `317aae79` | XT03–XT05: measured whole-tree folds; suffix invocation and construction/application separation; shape-sensitive traversal and exact append/cache costs. |
| `fdsa-tree-rotations`, `fdsa-tree-order` | `28ba79d8` → `66eae348` | XT06–XT07: ordinary/cached root rotations, qualified ordered summaries, relation invariant and transport. |
| `fdsa-ordered-search`, `fdsa-tree-leftmost` | `863aedb9`, `7b8ab2bb` | Separate search-path and leftmost-extraction branches over the rotation/order work; preserve failure domains and actual measured programs. |
| `fdsa-braun-shape` | `156ba817` | XT09: Braun predicate on the existing BinaryTree, shape facts and its qualified relation to almost completeness. |
| `fdsa-ch04-structural` | `af03b76c` | Basic observations and weighted paths, with connected examples. |
| `fdsa-ch04-balancing` | `a8f57dbf` | Sequential balance construction and actual call-count observations. |
| `fdsa-ch04-exercises` | `d0241973` | Levels, rose trees, enumeration and reconstruction; includes the same BasicObservations bytes as the structural stream. |
| `fdsa-adt-refinement` | `20a5b553` | XA01: `Applications/Collections/{Set,Map,AList,Modify}`, `SquareKit/ValidGraphs`, and four client modules. |
| `fdsa-potential-development` | `12cb14fc` | XP01: generalized mapped/invariant-aware ordered potential accounting and `Examples/MappedPotentialAccounting`. |
| `fdsa-logarithm-bounds` | `a601ad71` | XL01: common logarithm inequalities and source boundary examples. |
| `fdsa-priority-observations` | `c088beeb` | XH01: exact-occurrence priority observations and merge laws, not a selected concrete heap. |
| `fdsa-accumulated-work` | `7c6bc92c` | XW01: integrated geometric drift, accumulated/remaining work and prefix-qualified tail bounds. |
| `fdsa-permutation-expectation`, `fdsa-permutation-joint`, `fdsa-permutation-placement` | `11923e9f` → `a5341221` → `49d6d470` | XU04–XU06: preceding-count/position means, joint relative orders and fixed-placement independence under one global permutation. |

Most listed records expressly say uncompiled/unaccepted. XP01 has later focused
and actual-type evidence but still lacks full acceptance gates. Read current
book STATE and original requirements before interpreting dated ticket paragraphs.

**Review bases that must survive incorporation:** whole Chapter4 starts at
`298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`; XT03's original base is
`64c6b777d828ecfe83234fc2aed94600a1f24297`. Chapter4 retains all 76 obligations
and 11 exercises. Merging a shared prerequisite does not close the chapter.

Original tickets are resolved at
`books/fdsa/records/research/coverage/fdsa-control/tickets/`; the corresponding
frozen requirements and source assessments are under
`books/fdsa/records/evidence/reviews/fdsa-control/reviews/`. `RETENTION.json`
resolves deduplicated original paths and byte-range aliases. Keep these existing
owners rather than copying ticket histories into a new sprawling ledger.

## VFA standalone mathematical drafts

All VFA branch-tip Lean files are represented in the latest candidate. The three
older file variants inspected differ only by imports subsequently added to
StructuredCosts, FiniteMH and Temporal.Monitor. The following independently
useful source files are outside that candidate and need explicit integration or
owned preservation dispositions:

| Checkpoint path below `books/vfa/records/math/drafts/` | Contract/counterexample that must survive |
|---|---|
| `sorting-specs/SortingSpecifications.lean` | Optional-index/default-bounded/Pairwise ordering bridges; multiplicity-function equality iff permutation; arbitrary algorithm specification transport. Preserve transitivity boundary, invalid-index counterexample, infinite-support observation boundary and equal-key stability distinction. |
| `table-specs/TableObservations.lean` | Separate operations/laws/invariant, function and first-binding association-list models, partial versus default-valued observation, explicit presence and enumeration distinctions. |
| `positive-keys/VFAStaging/PositiveKeys.lean` | Existing PosNum/PNat/Nat correspondence with shifted key0↔positive1, inverse laws, comparator observations and arbitrary observation-family transport. Unshifted `PosNum.ofNat` is not injective on Nat. |
| `unary-costs/UnaryComparisonCosts.lean` | Actual unary≤ recursion, exact `min n m + 1` call count, no bound depending only on operand difference, measured erasure and sequencing clients. This is not a theorem about Lean native Nat execution or strict comparison. |
| `queue-costs/QueuePeekCost.lean` | Reachable empty-front queues with arbitrarily long backs; source-style peek returns a value without normalizing the queue. Repeated full reversals refute the unqualified amortized claim; preserve the structural-recursion tariff and actual execution connection. |

Each has a companion under `records/research/drafts/<family>/`, including historical
focused validation and statement review. Those checks do not establish acceptance
at the new master. Also retain `records/research/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md`
and `records/research/Perm-coverage-draft.md`: source corrections and future semantic obligations
are useful mathematics, even where no integrated theorem exists yet.

## PFDS variants and paper scope

The apparent1046 missing paths in two output-migration refs are the historical
`conaled/` wrapper, not1046 additional mathematical modules. After normalizing it,
there are zero absent paths and five variant paths (11 file versions). Inspection
found additions/generalizations in current SharedTree.Observation, OrderedTree
examples and Suspensions.Recursive; proof elaboration fixes in PersistentObservation;
and changing public imports. Do not resurrect the old wrapped tree or duplicate it.

The substantive candidate includes immutable sharing/lookup, ordered sets/maps,
suspension evaluators and correspondence, pure recursive forcing/cache reuse,
finite cache/body-event counts, persistent histories/debits, and signed potentials.
Use the existing common scope matrix for its nine scopes:
`books/pfds/records/evidence/reviews/common-integration-scope-matrix-045.md`.
Keep its finding history and `records/math/paper/`, `research/coverage/coverage.json`
and `research/source/thesis-obligations.json`. Sixteen forward cost contracts and
source-text coverage limits cannot be inferred closed by bringing these modules
into one import graph.

## Concrete integration seams and merge risks

1. **Potential accounting has an extra hidden donor.** PFDS's candidate generalizes
   `Applications/Resources/Potential.lean` to generic same-carrier additive
   telescoping, `budget_congr_state`, explicit final nonnegativity, plus
   `SignedPotential` savings/debt. FDSA XP01 independently supplies separate raw
   and accounting carriers, mapped/invariant-aware bounds, ordered exact laws,
   and `budget_amortized`; its `budget_map` uses weaker AddZero assumptions.
   The FDSA main candidate does not contain XP01, so a three-tip merge will miss
   this seam. Reconcile both public capabilities and their positive/boundary
   clients through the pinned library; choosing either file wholesale loses scope.
2. **Sorting specifications and algorithms meet at semantic contracts.** Connect
   VFA's staged ordering/count bridges with FDSA's sorting and uniqueness results
   and the pinned StableSort owner. Preserve duplicate occurrences, arbitrary
   payloads and equal-key stability; sortedness plus multiplicities alone is weaker.
3. **Collections have three representation presentations.** Compare VFA tables,
   FDSA XA01 Set/Map refinement and PFDS OrderedMap/AbstractSet. An interchangeable
   client needs checked invariant/lookup/update/presence correspondence, not a
   shared English name or extensional equality that erases absent versus present.
4. **Trees and resource observations cross books.** FDSA uses Mathlib BinaryTree
   fold/cache/shape/rotation laws; PFDS adds ordinary ordered and explicitly shared
   representations. Preserve representation invariants, path/failure domains,
   occurrence order and actual executor costs when connecting them. The shared
   carrier or final value does not by itself prove sharing or cost equivalence.
5. **Overlapping edits are few but global.** VFA/PFDS both change FRP Spec,
   Equivalence and Progress.Evaluation differently; FRP.Demand and
   Examples.IndefiniteService are byte-identical at those tips. All three change
   SquareApplications and docs/SOURCES. New master also changes Growth (FDSA),
   Progress.Evaluation/IndefiniteService (VFA/PFDS), and README (VFA). Preserve new
   master instructions, union intended public coverage, and retain needed import
   repairs without treating a clean textual merge as semantic validation.

## Required preservation disposition

Keep the original source and evidence immutable. For each useful candidate/draft
family, the local integration issue should identify one of: integrated unchanged;
generalized with a checked specialization; replaced with proved correspondence;
corrected with explicit reason and retained counterexample; or preserved pending
work with an owner and exact source pointer. Pending is a legitimate checkpoint
status but not completion of the user's full integration request. Preserve the
full integration baseline throughout review corrections.

This audit used exact Git tree/blob identity, merge-base/ancestry inspection,
bounded diffs and the named checkpoint status/requirement records. It did not
reprove declarations or certify exhaustive semantic equivalence. In particular,
FDSA's existing-path variants require capability-level reconciliation beyond
the65 absent-path check. Root owns including this report in the next verified,
durably uploaded checkpoint before another extended phase.
