# Local10021: debit laws and connected graph cases

Implementation handoff, 2026-11-03, by `/root/persistent_trace_scope`.
This is part of root's existing local10021 loop; no new review loop was opened.

## Inputs, ownership and validation status

Requirements: `requirements/persistent-debit-foundation.md`, version1,
SHA256 `2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
Checkout: `persistent-accounting`, branch `pfds/persistent-accounting`,
starting base `3dd930c3e3989f3e5530463f3ac937a629551335`.
The two assigned Lean files did not exist at assignment. Other authors own
History, Realization, Observation, their clients and public integration.
No other author file, source, Git ref/index, compiler output or tracker was edited.

Current assigned sources are frozen for root's next combined focused compilation:

| File | Size | Lines | SHA256 |
| --- | --- | --- | --- |
|`Applications/Resources/Persistent/Debits.lean`|16168bytes|325|`528f2dfa589b82ed46c0e21684d8a2e77be60acf37df8ea36e799b7884f55254`|
|`Examples/PersistentDebits.lean`|13299bytes|363|`ea391f67f3082ea44ec91bff213f5b1b59d30b18467bc13b12637b2cdec8f090`|

**No Lean compiler/build command was run by this author.** Root's second
focused run compiled the core successfully and failed on client errors recorded
below. The corrected client is source-inspected and awaits its next check.
Root owns the existing full/focused process queue and will run the frozen
targets. No separate elaborated-type inspection, complete focused success,
full audit or acceptance is claimed. All actual errors and corrective iterations
must be retained by that loop.

### First focused result and assigned correction

Root's `persistent-debits-r1` check ended with exit1 on2026-11-03. Its recorded
inputs remained unchanged. The original core hash was
`970c73dcf7333a5169d6eaf283f52e9cf38cec8e44854e7b20df2c79c9d05f98`;
the client hash was
`9df8db51432449c90657329925cb5e80a4d1458e6da05e8e3eee91e38f0807be`.
Root preserved the exact
record and raw diagnostics in `validation/persistent-debits-r1.json` and
`validation/persistent-debits-r1.log`. The core failed after52s and the client
did not build. This was an elaboration/lint failure, not a mathematical
counterexample to any independently stated case.

The compiler reported eight unused automatic Quiver assumptions and two
mapped-membership type mismatches. The second draft removes the global Quiver
section assumption and explicitly binds a Quiver only on declarations using
history or history-dependent laws. Consequently graph-free helpers also shed
the unnecessary assumption propagated by calls to earlier helpers. In
particular finite support inclusion/cardinality, finite allocation counting,
set disjointness, freshness uniqueness and graph-free renaming observations
do not require a graph. No linter setting was suppressed.

The forward and reverse proofs of `supportUnion_map` and `allocationUnion_map`
now distinguish mapped membership, original membership and the image equality
by name. They pass the original membership into the original union and retain
the image equality explicitly instead of reusing a shadowed `hd` after a
substitution pattern. Their statements and the embedding requirement are
unchanged.

Statement review of this correction retained every source law, scope premise,
boundary witness and example expectation. The Quiver changes remove an
accidental restriction from graph-free claims; they do not remove graph
assumptions from actual history claims. Existing Parallel renaming and
allocation cases and the Fork global-coverage case remain connected to these
helpers. All public Fork and Cycle definitions/theorems were unchanged, and
the client file was byte-for-byte unchanged during that correction. The
second draft was handed to root uncompiled for the next check.

### Second focused result and assigned client correction

Root's `persistent-debits-r2` check ended with exit1, with recorded inputs
unchanged. The core hash in the current table compiled successfully in10s.
The unchanged first client draft failed after26s. The exact record and raw
diagnostics are retained in `validation/persistent-debits-r2.json` and
`validation/persistent-debits-r2.log`.

The client errors were deprecated `if_neg`, unnecessary uses of `simpa`, and
dotted node constructors whose expected type could not be inferred at generic
helper applications. The correction uses the current `ite_eq_right` lemma and
simplifies contradictory hypotheses directly. It explicitly names
`Node.source`, `Node.origin` and `Node.first` at the reported `fresh_at` calls,
and `Node.origin` at the reported `history_refl` call. No graph, labels,
statement, expected number, premise or public name changed. The original
worked expectations and their public theorem connections remain intact.

The successfully compiled core remains byte-for-byte frozen because root is
using it in the Observation core check. Only the assigned client and this
handoff changed in the second correction. No linter suppression or toolchain
change was introduced. The corrected client has not yet been compiled; root
owns the next combined focused run.

AGENTS, the example-driven-development skill and its worked example, the
implementation skill's assignment rule, domain/glossary and relevant ADRs were
read. Primary-source statement evidence is the frozen
`research/persistent-trace-source-scope.md`: thesis printed19-24 and book57-63,
with the graph definitions and exact I-III formulas visually inspected.

## Public core and statement review

The namespace is `Resources.Persistent`. The definitions use the existing
raw `Quiver`, `history` and `HistoryClosed` interface; no new graph structure
or evaluation engine is introduced.

### Separate source laws and provenance

- `Fresh s` quantifies over every pair of distinct operation vertices and
  requires disjoint allocation sets. It is not restricted to a selected scope.
- `Allocated s a` requires an actual history/allocation witness for every debit
  occurring in a discharge multiset.
- `Paid a r` requires an actual history/discharge witness for every debit
  occurring in a realization multiset. Duplicate membership does not demand
  duplicate witnesses; this is the source's support interpretation.
- `Discipline s a r` is a small optional proposition bundle of those three
  independent laws. Allocation sets may be infinite; these signatures add no
  decidable debit equality or finite-vertex assumption.

`realized_origin` composes the two history witnesses using `history_trans`.
`allocation_origin_unique` uses freshness to identify two allocation origins;
`realized_origin_unique` combines existence with that uniqueness. Only the
latter two conclusions require freshness. No operation-order or termination
claim follows from the history relation, which remains reflexive and may cycle.

### Scope and aggregate cost

The requested stable API is present:

- `supportUnion scope labels` is `scope.biUnion (fun v => (labels v).toFinset)`.
- `dischargeCost scope labels` is the finite sum of multiset cardinalities.
- `realized_card_le closed paid` bounds realized-support cardinality by
  discharge cost, taking `HistoryClosed scope` and the source-local `Paid` law.

`PaidWithin` names the intermediate witness-in-scope property.
`paidWithin_of_closed` derives it from the original history witness and scope
closure; `realized_support_subset` then derives global inclusion. The source
law is not replaced by assuming the desired support inclusion.
`supportUnion_card_le` uses Mathlib's finite-union bound, support-cardinality
bound, and monotonicity of finite sums. These numerical conclusions do not
unnecessarily require I or II, disjoint realizations, or disjoint discharges.

`PaidWithBoundary scope boundary a r` retains an actual supporting discharge
`u` in the realizing node's history. It additionally requires either `u` in
the accounted scope or the debit in the boundary. Thus a boundary-only claim
does not admit a discharge in an unrelated logical future. The public
`realized_card_le_boundary` adds `boundary.card` explicitly. The boundary is
an accounting allowance backed by a discharge witness; it is not an initial
cache/seen set. Root approved this witness-preserving formulation.

### Finite allocation and partition

`allocationUnion` specializes set allocations to finite labels.
`allocationUnion_card` needs only Fresh and uses pairwise-disjoint finite union.
`realized_support_subset_allocation` needs II, III and scope closure, but no
freshness. `unrealizedDebits` is the allocated union minus realized support;
it is not the complement in all possible debit identities.

The public partition results give disjointness, the exact union, and a
subtraction-free cardinality equation. `shared_partition` additionally uses
freshness to identify the allocated union's cardinality with the sum of fresh
allocation cardinalities. These dependencies retain each source law's role.

### Debit renaming

`fresh_map` uses an ordinary embedding and set images. `allocated_map` and
`paid_map` need only a function: their support witnesses survive even a
noninjective image. `Discipline.map` requires an embedding to retain all three
laws together. `paidWithBoundary_map` preserves the actual history witness and
maps the boundary finite set.

`supportUnion_map`, `allocationUnion_map`, `unrealizedDebits_map` and their
cardinality results use ordinary finite-set maps under embeddings. Multiset
cardinality is preserved by `dischargeCost_map` even without injectivity.
These statements do not grant freshness or support-cardinality preservation to
noninjective identification of separately allocated work.

## Connected cases and independent expectations

The cases were worked out mathematically before their proof connections were
written. All finite equalities use ordinary kernel-reduced `decide`; no native
proof shortcut, admission, new axiom, proof-limit change or linter suppression
is present. The corrected client's compilation remains pending as stated above.

### Parallel uses

`Examples.PersistentDebits.Parallel` has a source and joined operation with
two distinct arrows between them. The source allocates7 and8. The joined node
discharges7 twice and realizes7 twice. Expected observations are realization
support `{7}`, discharge cost2, total fresh allocation2, and unrealized set `{8}`.

The client establishes all three laws and calls `realized_card_le`; its
`unique_origin` uses `realized_origin_unique`. Its finite partition case calls
`shared_partition` with the finite allocation labels related to the general
set allocation law. The `renamed` theorem transports the source discipline
and checks support, discharge and unrealized cardinalities for an arbitrary
injective embedding into any debit type with decidable equality. This does
not collapse equal-valued independently allocated work.

Two negative cases preserve distinct roles of the source laws. The same paid
labels with empty allocations satisfy III but fail II (`invented_debit`).
Giving the same debit7 to both allocation vertices fails I
(`duplicate_allocation`), using the generic allocation-origin uniqueness
theorem to expose the contradiction.

### Fork and incomparable payments

`Examples.PersistentDebits.Fork` exposes public reusable data for root's
measured-run composition:

- `Node.origin`, `Node.left`, `Node.right`, and `Arrow.toLeft`/`Arrow.toRight`;
- the ordinary Quiver instance;
- `allocations`, `discharges`, `realizations`, `scope`;
- `operations = [origin,left,right]`, `operations_nodup`,
  `operations_toFinset`;
- `closed`, `law : Discipline allocations discharges realizations` and `bound`.

Debit7 is allocated and discharged at the origin, then realized once on each
branch. Both futures' logical histories include that prior payment. The
source-valid generic bound has realized-support cost1 and discharge cost1,
while realization multiplicities sum to2. `repeated_realization_exceeds`
preserves the call-by-name boundary; counting repeated work cannot use the
memoized support bound.

A second labelling pays7 on the left,8 on the right, and realizes both on the
left. It has fresh origins, valid allocation provenance, global support
coverage and a numerical global bound, but fails III. The proof uses the
History author's public `history_eq_of_no_outgoing` to establish that the
right branch is not in the left branch's history. Thus the numerical result
does not silently acquire the stronger local source legality.

### Cycle and an open scope

`Examples.PersistentDebits.Cycle` has both directed edges between first and
second. Allocation is at first, discharge at second, and realization at
first. The full scope is closed and satisfies I-III; the client calls
`realized_card_le` and independently expects realized1/discharged1.

The singleton scope containing first is not history-closed. It has realized1
and discharged0 using the same source-valid global labels. `open_scope_exceeds`
retains this counterexample. `paid_with_boundary` supplies the actual discharge
witness at second and boundary `{7}`; `boundary_bound` then calls the public
boundary theorem to account for the missing charge. No chronological
operational interpretation of the cycle is asserted.

## Integration handoff and retained limits

The exact root-facing names above are available in the written drafts. Root
can build `Applications.Resources.Persistent.Debits` and
`Examples.PersistentDebits` once the shared History input is frozen and the
focused slot is available. Root owns all compilation, public-entrypoint edits,
candidate capture, Git commits, independent review and final acceptance gates.
This author will make only assigned corrections in the same loop.

The mathematical claims are abstract debit accounting. Root's Realization/
Observation layers own the positive connection to the unchanged measured
executor and reuse the Fork case. Existing actual-source exception/retry
behavior and the complete source/machine work bridge remain explicit in the
requirements and root-owned client; this file does not import a second
evaluator or assert a body-attempt bound. Local10017, later chapters and all
forward cost obligations remain open.

## Root completion evidence after the author handoff

The unchanged corrected client compiled99s in combined persistent-accounting-r1;
the complete nine-module combined r3 finished exit0 at eb61c35 with67 inputs
unchanged. The current candidate577be121e074ddb5de6727a7481c115cb61b3b27 changes
only public documentation after that success. Core and client hashes in the
author handoff remain identical; exact input equality and full scope are in
validation/persistent-accounting-candidate-r3.json. This supersedes the earlier
client-compilation-pending note without erasing its raw failed rounds. Own full
gate and both independent reviews remain pending; no acceptance is implied.
