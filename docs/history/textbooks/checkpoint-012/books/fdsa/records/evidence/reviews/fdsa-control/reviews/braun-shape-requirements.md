# Frozen requirements — shared Braun structural facts

Ticket: **FDSA-XT09**. Version1, frozen2026-11-03 before source edits.

## Authority, source and original base

The governing user request covers the entire pinned FDSA book chapter by
chapter, permitting genuine cross-cutting concerns. Chapter11 arrays and
Chapter16 heaps use the same Braun shape invariant and height input. This
bounded shared unit does not activate either chapter or remove any obligation.
Tickets, branches and commits stay local. Every new durability checkpoint is
immediately exposed and uploaded under the user's existing permission.

Original review base and initial source head:
`974a97321a8ec174b56104c7e6efaaca881b6639`, the saved unaccepted XT02 tip.
Its XT01 ancestor is`64c6b777d828ecfe83234fc2aed94600a1f24297`.
Branch: `work/fdsa-braun-shape`.
Source worktree: `/workspace/scratch/845aa1048b05/conaled-braun-shape`.
The separate `reviews/braun-shape-start.json` records its actual initial state
and baseline identities before author release. This is a source worktree;
only pinned dependency source packages may be linked. No project build output
or compiler cache is copied, moved or shared into it.

Accepted repaired FDSA-001, XT01 and XT02 are prerequisites for integrating or
accepting this unit. Preserve this original base, requirements, all findings
and candidate history when an accepted integration base is later incorporated.
The exact first C2 prefix remains`c80eec92f5458eccfd1c34c8314d666c2a1e3847`.
No second compiler, checker or project hash helper may run while C1's gate is
active. This applies to every author and to scratch elaboration experiments.

Source edition: July27,2026 PDF, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Primary structural sources are Braun_Tree.thy, Tree.thy and Tree_Real.thy at
Isabelle mirror`f86f290225eebcc52c1ae7dba2e098f405f51c21`, with actual
Chapter11/16 consumers and the dated AFP Braun-PQ source as recorded in the
preflights. These companion pins postdate the manuscript; do not call them
its generating revision. Preserve applicable attribution and the full retained
Isabelle BSD notice for adapted structural proof material. AFP consumer/proof
references retain their own provenance; no PQ algorithm is ported here.

All three complete stopped reports were root-read and assessed:

| Report under research/ | SHA-256 |
| --- | --- |
| braun-shape-source-preflight.md | `5a11f1e66cf45870d7b0e0651445459457bdca5cf4c8ddd599c7c5ddb40d5931` |
| braun-shape-api-preflight.md | `cc445c1eef96e836dee9fb77a73932d221307f31b11fa58c5d0974efce4772e3` |
| braun-shape-case-preflight.md | `9561054896a97e49cf55ba0d1b19eb7f7e3da51b16b4771b04b58c2963313d52` |

Root's disposition is`reviews/braun-shape-preflight-assessment.md`.
All applicable AGENTS, architecture/domain, implement, example-driven and
existing review-loop instructions remain in force. Root owns the task;
disjoint author assignments are within this existing workflow, not new loops.

## Exact seven-path source boundary

- Add `Applications/Trees/Braun.lean`.
- Add declarations to `Applications/Trees/Shape.lean`.
- Add declarations to `Applications/Trees/ShapeLog.lean`.
- Add `Examples/BraunShape.lean`.
- Add `docs/research/fdsa-braun-shape.md`.
- Append the new unit to `docs/research/fdsa-reconstruction-map.md`.
- Append the public import `Examples.BraunShape` to `SquareApplications.lean`.

Preserve every existing declaration, statement and proof in Shape and ShapeLog;
insert new declarations before the final namespace end. Existing imports and
options remain. Preserve the complete prior map/root bytes as a prefix before
the additive entry/import. Do not change policies, pins, checkers, dependency
files, previous examples or any other source path. A concrete obstruction to
this boundary must be reported before changing it; a speculative convenience
is not a reason to expand scope.

Use the existing `BinaryTree`, `Trees` namespace, XT01 ordinary count/map/erasure
facts and XT02 minimum-height/AlmostComplete/log APIs. The natural core imports
no Real analysis. The existing ShapeLog layer holds the actual analytic
correspondence. Reuse facts directly; do not create a second carrier, shape
quotient, balance hierarchy, canonical generator, checker, or cost framework.

## XT09-01 — Exact Braun invariant and arbitrary labels

Define one ordinary recursive Prop predicate on `BinaryTree alpha`:

```text
Braun nil = True
Braun (node a l r) iff
  (l.numNodes = r.numNodes or l.numNodes = r.numNodes + 1)
  and Braun l and Braun r.
```

Expose its nil/node equations and the equivalent node inequalities
`r.numNodes <= l.numNodes` and`l.numNodes <= r.numNodes+1`, retaining both
recursive child predicates. Node labels are never inspected. Prove for every
supplied `f : alpha -> beta`, with independent universes,
`Braun (t.map f) iff Braun t`. No injectivity, payload order/equality,
inhabitation or finiteness assumption is allowed for these shape facts.

The predicate is a logical source invariant, not a claimed efficient runtime
checker. No timing declaration or cached-size implementation is introduced.
Child-shape consequences may be derived where a real case needs them; do not
add a redundant generic pattern/decomposition framework.

## XT09-02 — Equal-size uniqueness of erased shape

For `s : BinaryTree alpha` and`t : BinaryTree beta` in independent universes,
prove that `Braun s`, `Braun t` and`s.numNodes = t.numNodes` imply

```text
s.map (fun _ => ()) = t.map (fun _ => ()).
```

The equality is in existing `BinaryTree Unit`. Retain the source Unit-labelled
tree equality as a checked specialization; a private Unit proof may support
the generic result. Both Braun premises are substantive. This is at-most-one
erased shape for a size, not existence of a tree at every size over arbitrary
payloads, equality of labelled trees, equality of inorder values, or an array
representation theorem. No tree enumeration or new shape relation is needed.

## XT09-03 — Local constructor arithmetic and source identities

Add the generic local theorem: for an arbitrary root label, two AlmostComplete
children with`l.numNodes <= r.numNodes+1` and`r.numNodes <= l.numNodes+1`
form an AlmostComplete parent. Both child premises and both inequalities stay
explicit. Handle equal counts and both one-larger orientations; no Braun
premise is imposed on the children of this general theorem.

Also expose the actual one-larger intermediate identities. Given those two
AlmostComplete children and`l.numNodes = r.numNodes+1`, let`k = r.numLeaves`:

```text
(node a l r).height = Nat.clog 2 (k+1) + 1
Trees.minHeight (node a l r) = Nat.log 2 k + 1.
```

Here`k >= 1` follows from the actual external-leaf count. The proof must retain
the source's adjacent power interval: from`2^i <= k < 2^(i+1)` infer
`2^i < k+1 <= 2^(i+1)`. Reuse pinned power/log/clog laws; an internal arithmetic
lemma is permissible, but a new public logarithm framework is not needed.
The empty right child is included (`k=1`). Do not add a nonempty-tree premise.

In ShapeLog, prove the corresponding actual source natural-rounding formulas
under the same child/size hypotheses:

```text
(node a l r).height = ceil_nat(Real.logb 2 (k+1)) + 1
Trees.minHeight (node a l r) = floor_nat(Real.logb 2 k) + 1.
```

Casts to Real must describe those same natural arguments. Use the existing
`Real.natCeil_logb_natCast`/`natFloor_logb_natCast` bridges; prose or floating-point
estimates are insufficient. Preserve natural/real separation and all old
Shape/ShapeLog declarations. This is the selected C11-014/015 constructor
support, not full recursive symmetric balance C11-018.

## XT09-04 — Braun-to-almost-complete and existing consequences

Prove `Braun t -> Trees.AlmostComplete t` by the actual recursive invariant
and local constructor result. Retain both equal/one-larger size cases, the
empty base and arbitrary payload types. Existing general XT02 theorems then
give exact Nat/Real rounded heights and height optimality. Consume those
theorems directly in connected applications instead of renaming every result
as a new Braun-specific library wrapper.

For the source connection retain `numLeaves = numNodes+1`, so nil uses log1,
not log0. The optimum compares a Braun tree against any independently typed
tree with at least its node count; the competitor need not be Braun or AC.
This supplies the C11-016/017 facts and a height input for later C16 cost
proofs. It is not an operation cost or optimal-algorithm claim.

## XT09-05 — Connected cases and statement review

Develop actual public-law connections alongside the theory, using the
independent stopped case report and existing fixtures. Do not mirror every
helper with a new case or manufacture failed goals when the existing API
already suffices. No compiler is released during C1; draft source and statement
review remain explicitly uncompiled until the matching validation phase.

1. Nil and singleton, with the arbitrary`BinaryTree Empty` case through the
   existing empty-tree result. Preserve count0/leaf1/height0 and both log1
   boundaries, without a payload default or positive-size existence claim.
2. Reuse`chain 2`, `rightTwo`, `balancedThree`/`perfectThree`, and`leftThree`.
   Exercise Braun's orientation and recursion, the smallest one-larger
   constructor (right nil), and the symmetric constructor's mirrored case.
   A parent over two`leftThree` values has equal root counts but fails AC;
   establish why the child AC premises cannot be dropped. No public or private
   generic recursive symmetric-balance predicate is required in this unit.
3. Use the independently calculated five-node pair, with arbitrary or explicit
   labels: B5 has two left-only two-node children (counts2/2); A5 has a complete
   three-node left child and singleton right child (counts3/1). Both have
   nodes5/leaves6/height3/minHeight2. Prove B5 Braun and connect its AC/log/real
   rounding/optimum through the actual public results. Prove A5 AC but its
   local size-balance condition and Braun predicate false, and their erased
   shapes unequal. This makes the uniqueness and converse boundaries explicit.
4. Connect arbitrary-map iff across independent payload universes, a concrete
   noninjective map, and Unit-erased uniqueness. Different Bool singletons
   preserve shape but have different payload/inorder observations. A constant
   relabelling of the existing non-Braun sample must remain non-Braun.
5. Compose the map law with actual`Cached.erase` and`erase_annotate`, including
   generic fold algebras. Connect an actual size annotation of a Braun value
   with`annotate_valid`, `read_annotate`/`read_eq_fold`, and`fold_numNodes`.
   Reuse sizeSample (valid cache, non-Braun shape) and corrupt.left (Braun
   singleton, invalid stored size2) to separate both assumptions. Structural
   transport does not require cache validity; a reader-to-value claim retains
   its real validity premise. Add no cache representation or tariff.

Use meaningful generic applications and concrete substitutions, not just
unrelated numeral reductions. The report's indexing/BFS, heap order and
ordinary-versus-swapping-extraction calculations are documented boundaries;
do not implement those operations or import XT08 to reproduce them here.
Keep all independent expected values unchanged unless a mathematical error is
identified and recorded. Statement review covers all new claims' domains,
quantifier order, universes, recursive premises, observation equality,
nonvacuous cases, node/leaf counts, min/max conventions and rounding casts.

## Documentation, coverage and retained obligations

The original reconstruction note records actual declarations and public-law
connections, source provenance/full applicable notice, both empty/generic
domains and the case boundaries. Explain that Braun bias is not conventional
breadth-first left packing. State that full array observations/cache validity,
heap order and actual algorithm/cost correspondence are separate.

Append this unit to the existing map without changing prior text. Cover only
the selected common statements C11-008,014–017,019 and shape-only contributions
to C16-001/042; no whole chapter or unit is accepted by this mapping. C11-018's
recursive symmetric predicate/global result stays mandatory later work.
C11-122/Exercise11.1 retains the independent direct proof without AC; its
primary PQ proof route is already documented and is not selected here.
All other exercises, index positivity/cardinality/contiguity including its
converse, array contracts/order/constructors/converters/operations, heap
algorithms/domains, source tariffs and all135 C11/48 C16 rows remain required.
The original XT02 scope/failure/validation records remain untouched.

## Source release, validation and acceptance

Before any source edit, root captures the clean selected base, obtains author
readiness on these full requirements, and creates/exposes/uploads the pre-code
checkpoint. A separate root message releases disjoint source ownership. Authors
do not mutate refs/index or run compiler/checker/hash-helper/cache experiments.
Root reads final sources, reconciles statements/coverage, commits the stable
draft and immediately saves the next complete source/control checkpoint.

Later matching validation covers Shape, ShapeLog, Braun and the connected
example module (including reused imported cases), then the entire unchanged
guarded candidate route with compiler/dependency identity, source coverage,
both integrity phases, every local module and exhaustive transitive axiom
audit. Both independent Standards and Spec axes review the full immutable
scope against the preserved original requirements/base and any recorded
integration-base transition. Immediate matching`--verify-candidate HEAD`
is required before acceptance. Preserve every failure and unresolved finding.

No `sorry`, `admit`, new axiom, unsafe/partial definition, `native_decide` or
skipped kernel checking is permitted. Source readback, draft/commit, focused
passes and saved checkpoints are not acceptance. No GitHub mutation is allowed.
