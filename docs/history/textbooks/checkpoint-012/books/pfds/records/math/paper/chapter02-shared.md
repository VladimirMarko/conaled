# Shared general trees, Chapter2 implementation record

Base82501d108f33c62d21b5e0d0f7d2376b902d8d49, branchpfds/ch02-shared.
Assigned files Applications/Search/SharedTree and Examples/SharedTree. No
entrypoint/tracker or unrelated source edits. Full requirements chapter02.md.

## First intended case and exposed obligation

One cell contains7 and no children. A second contains9 and points twice at
that original cell. The independent expected unfolded value has three nodes,
but the graph allocates two cells. Both old and new roots must remain valid.
Before this work the shared-list observation could not express two child
roots; Mathlib BinaryTree supplied the value type but no graph relation.
This was a missing representation/connection obligation, not an unprovable
arithmetic proposition. The new Represents relation and allocation theorem
connect Examples.SharedTree.fork_observes, fork_shares_child and leaf_survives
to the public API. No build or acceptance has yet been established.

## Architecture choice

The existing SharedList.Store is a fresh immutable cell allocator whose cell
shape is payload × Root; it imposes no list validity on stored cells. Choosing
payload α × Root reuses that allocator exactly. Tree validity is a separate
inductive relation requiring both children below the parent and observing a
Mathlib BinaryTree. No strict BST order is required or asserted. This permits
the repeated-value and shared-child cases demanded by Exercise2.5.

## Recovery checkpoint state

Basic.lean and Examples.SharedTree have a running focused build; dependencies
compiled but the first source result has not yet returned. A vanished prior
lock-wait session produced no result. Complete.lean and Balanced.lean are written
but not yet submitted to compilation. They contain no admissions; their Lean
proof scripts remain unverified work in progress until compilation succeeds.
Complete uses one recursive result twice and states exact d fresh cells/d+1
visits. Paired construction uses two fresh parents per halving step and one
base leaf, aiming at exact 2*log2(n+1)+1 fresh cells and log2(n+1)+1 visits.
Its separate Fits predicate requires exact unfolded size, all repeated values,
and child-size balance at every node. No formal or chapter acceptance is claimed.
Root owns Path.lean and Ordered.lean; this worker will not edit those files.

## Focused compilation and statement review, next iteration

- Core and original fork/retention examples compiled successfully: 659 jobs,
  active-validation/chapter02-shared-basic.log. This is focused progress only.
- Constructor round1 reached Complete and found one unused simp argument
  (pow_succ). Removed that redundant argument; no statement change. Balanced
  had not yet compiled in that run.
- Round2 targets Examples.SharedTree through Complete, Balanced and Costs.
  It is queued/running and has no acceptance result yet.

### Intended mathematics and checks

Complete depth0 is nil. Depthd has heightd and unfolded nodes2^d-1. The graph
executes one recursive call at each level and stores the same returned root
twice. Allocation count is d, independent of the prior store frontier; visits
include the base, hence d+1. Explicit stored-root equality establishes sharing.

Paired construction returns requested unfolded sizesn,n+1. The independent Fits
predicate requires exact size, all nodes equal to the supplied payload, and
every child-subtree size differing by at most1. This is stronger than height
balance and requires no BST order. The graph reuses one recursive root pair
and allocates two parents per nonbase call, with one base leaf. The intended
exact formulas are 2*log2(n+1)+1 fresh cells and log2(n+1)+1 visits. Natural
sizes/depths are the intended domain; negative source integers have no tree-size
meaning. For size0 the pair still constructs its size1 companion; this constant
is retained, not silently removed from the cost formula.

Work means recursive visits plus modeled fresh cells. Separate asymptotic
statements use existing Resources.isBigO_of_nat_bound: linear in depth, and
logarithmic in the requested unfolded node count, with floor binary logarithm
and threshold2. Tests, integer arithmetic, field operations and each modeled
allocation have bounded unit overhead; these are not Lean allocator or bignum
runtime claims. Old valid trees at arbitrary retained roots survive every
construction by heap extension. The relation allows arbitrary unrelated heap
cells and shared children, with backward edges guaranteeing finite observation.

Connected cases include the initial 3-occurrence/2-cell fork, complete depth3
(7 unfolded nodes/3 cells), size6 (5 cells and unequal child sizes), size0
(companion allocation), exact stored child references and retention of the
old fork across a separately constructed size6 tree. Each uses the public
correctness, shape, sharing or retention theorem rather than a separate proof
of an unrelated numeral fact. No formal approval or chapter completion follows
from this statement review or focused compilation.

## Final focused candidate

Current candidate `b6b93fec6cc636fe6cb3794d79280c363de619d6` on `pfds/ch02-shared`, following WIP3224ae1.
All six assigned modules/examples compiled successfully together through
`lake build Examples.SharedTree` in the pinned Nix environment: exit0,1587jobs.
The final source files are unchanged from that successful build and the
worktree is clean. `validation/chapter02-shared-focused.json` pins their
SHA256 fingerprints and the candidate. Frozen logs for all iterations are
under `session/validation/chapter02-shared-*.log`.

Round2 corrected explicit well-founded base-equation rewrites and removed one
redundant tactic. All recursive shape, store, reference-sharing and logarithm
proofs then compiled without weakening their statements. Round3 compiled the
observation adapter, standard asymptotic adapter and all connected cases.
Map worker supplied a separate read-only recurrence/design check confirming
parity, sizes, balance and log2 counts; this is not either formal review axis.

### Source-to-declaration handoff

| Scope | Public declarations |
| --- | --- |
| Shared general-tree observation | `Represents`, `.mono`, `.unique`, `.below_next`, `.height_le_next` |
| Fresh parents and old versions | `allocate_represents`, `allocate_retains`, `allocate_extends`, `read_allocate` |
| Ex2.5(a), sourcep15 | `completeValue_height`, `completeValue_nodes`, `completeValue_fits`, `completeRun_correct`, `completeRun_children`, `completeRun_retains` |
| Ex2.5(b), sourcep15 | `Fits`, `create2Value_fits`, `create2Run_correct`, `create2Run_children`, `create2Run_retains`, `balancedRun_correct` |
| Exact and standard asymptotic work | `Resources.SharedTree.completeWork_exact`, `.pairedWork_exact`, `.completeWork_linear`, `.pairedWork_logarithmic` |
| conaled observations/composition | `representation`, `optionalRepresentation`, `pairInput`, `allocateSquare`, `rootValueSquare`, `allocatedValueSquare`, `allocatedValue_correct` |

The resource module lives at `Applications/Resources/SharedTree.lean`, matching
existing resource-domain placement; `Search/SharedTree/Costs.lean` was an
untracked draft and is absent. Root explicitly assigned Observation and the
resource module in the later handoff. `Path.lean` and `Ordered.lean` remain
root-owned and untouched. Root must import all these modules in the integrated
entrypoint. No ordering, set/map correctness, exact minimal reachable-space,
Lean runtime, or garbage-collection guarantee is claimed by these constructors.
Whole-Chapter2 integrated build/audit/finalverify and both review axes remain
pending; focused success does not accept the chapter or prerequisite10013.
