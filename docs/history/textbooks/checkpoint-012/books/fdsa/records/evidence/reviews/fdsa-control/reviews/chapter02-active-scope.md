# Active Chapter 2 implementation scope

Chapter 1 accepted at 07e480f6ec9958d4975bb90151005b84f2907614; its checkpoint
0077 is saved. Chapter 2 is now active. Its full-spec integration review retains
that accepted Chapter 1 starting base and all 112 current sorting obligations.
The frozen chapter02-requirements.md and explicit scope reconciliation remain
unchanged. Shared prerequisites retain their own recorded acceptance workflow.

The exact first foundation prefix is being corrected/validated separately as
recorded in shared-foundations-round1.md. Its unaccepted status is explicit.

## First parallel chapter implementation

After checkpoint 0078, release the already prepared ordered-insertion work
from accepted C1 base 07e480f. Root assessed all three stopped preparation reports
in ordered-insertion-preflight-assessment.md; their exact hashes remain frozen.
The implementation has exclusive ownership of two new paths in its own worktree:
Applications/Sorting/InsertionObservations.lean and
Examples/InsertionObservations.lean. Root owns public imports, reconstruction
mapping, trackers, compilation and full acceptance. No new shared unit is added.

Required thin laws use canonical List.orderedInsert: law-free sortedness
converse for an independent observation relation; total/transitive source iff;
all-members immediate-cons value equation; negative filtering without order
laws; positive filter/insertion commutation with transitivity and source
sorted-input premise. Retain full-occurrence and keyed mapping/stability
connections, all prepared edge/counterexample cases and minimal assumptions.
Reuse existing algorithms/contracts and exact source observations; no new
executor, carrier, cost model, payload order/equality instance or default value.

A committed draft and statement-reviewed connected cases are development only.
Root will validate before any promotion and preserve all outstanding Chapter 2
obligations, including the separate average/randomized and cost-model claims.
No compiler shares writable project outputs across checkouts. The worker may
read the pinned dependency source but does not run builds until coordinated.

## Floor-left top-down value implementation

Root also works in separate conaled-ch02-top-down, branch work/fdsa-ch02-top-down,
starting at the same exact accepted R=07e480f. It implements the source floor-left
value recurrence and stable-sort observations already specified by
research/mergesort-proof-plan.md and C02-026/027/030/032/036/107. Ownership is
Applications/Sorting/TopDown.lean and Examples/TopDownSorting.lean. Existing
List.merge and conaled StableSort are reused; comparator-generic permutation
and input-local sortedness retain weaker assumptions than the keyed contract.
No measured cost is inferred from value agreement with the standard sorter.
The required comparison model, logarithmic bounds and source/reference split
counterexamples remain subsequent obligations, using XM01 after its own gates.
Root's current full foundation validation checkout is unchanged by this work.

## First-pivot quicksort and arbitrary-suffix implementation

After the insertion author returned its complete stopped draft, root released
its next independent active-C2 subset at the same accepted R: C02-017–023 and
Exercise2.2/C02-101. Worktree conaled-ch02-quicksort, branch
work/fdsa-ch02-quicksort, owns only Applications/Sorting/QuickSort.lean and
Examples/QuickSort.lean. Existing operations/observation contracts, exact
first-pivot strict-less/complementary partition and full occurrences remain.
The append-free variant must satisfy its source recurrence and arbitrary-suffix
law, with no sorted-suffix premise for value equality. Root owns public root,
coverage, compilation and all acceptance; no compiler is released to the worker.
The author handoff is chapter02-quicksort-implementation.md. C02-024's separate
probability and runtime correspondence, the exercise tariff, both source append
charges, three-way variant and every other chapter requirement remain pending.
No new shared unit or enclosing review workflow is introduced.

## Further independent Chapter 2 value components

- Bottom-up worker: conaled-ch02-bottom-up / work/fdsa-ch02-bottom-up at accepted
  R; exclusive Applications/Sorting/BottomUp.lean and Examples/BottomUpSorting.lean.
  Public mergePairsBy / mergeAllBy / sortBottomUpBy use actual canonical merge,
  with flattened permutation/length, ceil-half run count and input-local sorted
  run preservation. The permitted tail-pass choice has exact arbitrary-accumulator
  law mergePairsRevBy cmp acc xss = (mergePairsBy cmp xss).reverse ++ acc.
  Exercise2.6 permits a different pass value; no stability transfer is inferred.
  Comparison bounds remain required after the measured merge dependency passes.
- Natural-run worker: conaled-ch02-natural-runs / work/fdsa-ch02-natural-runs at
  accepted R; exclusive Applications/Sorting/NaturalRuns.lean and
  Examples/NaturalRuns.lean. Preserve actual mutual scanner/workers, source D-law
  raw-builder bridge through Batteries.DList, strict descent and ties in ascent,
  arbitrary worker accumulators and occurrence/length/run-count/order invariants.
  runsBy lt tests lt b a for current a / next b; keyed specialization supplies
  fun x y => decide (key x < key y). Composition with BottomUp is subsequent
  source reconciliation, not an import of an unavailable draft. C02-108–112
  builder construction/invocation observations remain separate and mandatory.

At checkpoint0082, all three algorithm workers are write-held after source
authoring. Quicksort has clean uncompiled draft edbfeb7d810befefd6a3698bd226face6f3de926.
Bottom-up and natural-run worktrees now exist at R and contain their two owned
untracked Lean drafts. Their explicit implementation handoffs preserve static
statement assessments, independently expected cases and all outstanding gates.
Natural-run connected examples and one-run laws are still unfinished. No new
compiler result, component acceptance or reduced chapter scope follows.

The new host's exact primary native environment is now qualified. Root will
record the new immutable full foundation gate and coordinate private focused
builds for these drafts. Never share writable outputs across concurrent builders.

## Alternating accumulator splitter and sorter (Exercise 2.5)

The idle conaled-ch02-insertion worktree is now repurposed on
work/fdsa-ch02-alternating at accepted R. Its original checked insertion ref
95cfce3 and combined value ref b167717 remain intact. The assigned author owns
only Applications/Sorting/Alternating.lean and Examples/AlternatingSorting.lean,
plus chapter02-alternating-implementation.md. Preserve the actual one-pass
alternating accumulator operation, its arbitrary-accumulator occurrence and
length laws, balanced decreasing recursive arguments, sorter correctness and
the source nonempty-accumulator example. No stability or extra numerical
resource formula is inferred. This is active Chapter2 scope, not a new shared
unit. Root owns compilation release, public imports, coverage and acceptance.

The alternating development branch now explicitly retains the unchanged checked
insertion prefix 95cfce3, after those original files reappeared untracked when
the idle worktree changed branches. Their bytes match the preserved commit.
The accepted chapter/review base remains R, and the new alternating operation
uses only accepted sorting interfaces. No new dependency is declared accepted.
See provenance/chapter02-alternating-retained-prefix-20261104/.

## Top-down comparison execution and bounds

Root owns the isolated top-down-costs development branch, retaining checked
values b167717 and focused ordinary merge72a0951 without claiming either final
acceptance. New TopDownSorting resource/TopDownCosts example files and a thin
existing Growth bridge extension remain uncompiled. Source provenance, exact
requirements, actual measured child/merge sequencing, all-length ceiling-log
bound, printed power-of-two premise and real-log consequences are preserved
in chapter02-top-down-costs-implementation.md. The exact foundation acceptance
candidate remains isolated and unchanged. No separate shared unit is created.

## Checkpoint0085 continuation: measured and remaining sorting work

The central development checkout is now cumulative work/fdsa-ch02-development
in conaled-ch02-top-down, with private outputs. Bottom-up/alternating values
passed all four focused targets at98696d and126 public declaration inspections.
The six-target measured candidate841413dc retains exact previously checked
components and bounded name/binder/simp corrections after actual failed
attempt1. The isolated foundation candidate f17cc6b remains unchanged.

The natural-run author holds its two bounded correction files atdd01c1cb. The
bottom-up author implements the prepared two-file comparison execution/bounds
on98696d, without compiling. The random-pivot author is released after saved/
exposed0085 to the two-file actual PMF slice specified in its complete handoff,
retaining all mandatory expectation/asymptotic continuation.

The stopped quicksort author is assigned C02-102's two new three-way sorter
files in genuinely new source-only conaled-ch02-three-way, branch
work/fdsa-ch02-three-way at exact XQ01 de5410286bbefd841dff50bef55c2e52d2ebbd2a.
That shared prerequisite remains uncompiled/unaccepted and the first acceptance
remains f17cc6b. The existing frozen source/API/case preparation and full chapter
requirements control the source recurrence, all-occurrence correctness and
consequential cases. No Selection-algorithm dependency, new cost/stability
claim or reduced mathematical scope is authorized. Root owns compilation,
public exposure, coverage and all independent full acceptance gates.
