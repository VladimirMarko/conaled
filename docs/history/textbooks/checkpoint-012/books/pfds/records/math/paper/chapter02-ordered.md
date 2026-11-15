# Chapter 2 ordered trees — implementation status

Assigned worker: /root/chapter02_ordered; branch pfds/ch02-ordered;
worktree chapter02-ordered; fixed task base82501d108f33c62d21b5e0d0f7d2376b902d8d49.

The first Basic.lean layer reuses Mathlib BinaryTree and declares independent
Contains/entries/All observations, keyed OrderedBy and identity-key Ordered,
actual baseline comparison-counted member, pure path-copy insert, content/order
preservation and a two-times-height comparison bound. Constructor equality does
not claim physical sharing. Generic payload labels need no order; algorithms
use a LinearOrder on set elements. The finite-map worker reuses OrderedBy.

Initial intended cases: a three-node set with root2/left1/right3; successful
member2; absent4; insertion4 preserves1 and adds4; an invalid descendant beneath
a locally plausible child must violate all-descendant order. The baseline
absent4 comparison count is4 at height2, whereas candidate-carrying search
should need3. A root match need not use fewer comparisons in the candidate
variant; only the worst-case bound is promised. These are independently fixed
expectations to connect to the public theorems, not completed case evidence yet.

First compile session25533 vanished during the disk-full/interruption incident;
no output or success artifact was observed. Offline focused build session93736
is pending under the shared focused-build lock. The initial source commit is a
recovery snapshot only; no compilation or formal acceptance is asserted.
Candidate membership, baseline abort insertion, combined candidate-abort
insertion, connected examples and full chapter integration are still pending.
No SquareApplications or shared tracker edits are owned by this worker.

Second recovery snapshot adds Candidate.lean: a LowerBound invariant, actual
candidate member traversal and height+1 bound, baseline abort insertion and
single outer handler, combined candidate/abort traversal, semantic refinement
and a joint order/content/comparison theorem. All remain uncompiled while the
first dependency build in another worker owns the focused-build lock. Deprecated
if_pos/if_neg uses in the first layer were replaced by Lean4.35 ite_eq_left/
ite_eq_right. These are intended proofs, not checked/accepted claims yet.
Physical zero allocation/off-path root sharing remains with root's graph
realization. Connected examples and set-interface laws still need completing.

## Focused compilation succeeded

The offline pinned-Nix command `env LEAN_NUM_THREADS=1 lake build Examples.OrderedTree`
completed successfully (594 jobs), session85155. It compiled AbstractSet,
OrderedTree.Basic, OrderedTree.Candidate, OrderedTree.Interface and the retained
Examples.OrderedTree. The earlier Basic attempt failed only unused simp
arguments and the insertion equality branch's simplification; those were fixed
without changing statements. No warnings-as-errors, admissions or extra axioms
were introduced. Dependency module-system advisories remain preexisting.

The concrete retained examples now connect the expected cases to public
member/insert/candidate/abort results and generic Laws.member_from_empty. The
invalid-descendant example establishes why immediate-child comparisons are
insufficient. The four-versus-three absent-query counts are checks of the
actual recurrences; the bound instances and combined correctness use public
universal theorems. Physical-sharing/allocation claims remain excluded.

This is focused compilation, not full candidate acceptance: public-entrypoint
integration, exhaustive proof audit, exact candidate verification and both
independent review axes remain with the parent Chapter2 loop. Additional
finite-content/no-duplicates and sharp worst-case family proofs are in progress.

## Statement review and source mapping

Primary book printedpp12–16 were inspected from the exact attached PDF; printed
p15's rendered image was separately viewed to check Exercises2.2–2.4's final
candidate equality and single-handler wording. The map exercise is owned by
another worker; shared-tree allocation and Exercise2.5 are outside this branch.

- B2-ORDER: `All` quantifies every label; `OrderedBy` separates keys from labels
  and requires strict bounds over both entire subtrees. It needs only `LT` for
  its definition. Search/insertion correctness requires the source's coherent
  total order, instantiated by Mathlib `LinearOrder` on set elements.
- B2-SET: `Search.AbstractSet.Ops` contains only empty/insert/member. `Laws`
  separately states validity and membership contracts. Insertion squares reuse
  Relational.RelSquare; word clients reuse ListFusion.foldl_reachable. Actual
  tree instances and nonempty/duplicate clients establish satisfiability.
- B2-MEMBER: `Contains` is independent whole-tree membership, equivalent to the
  inorder list. `memberRun` charges each actual executed `<` test, with zero
  element comparisons at nil. The bound is2*node-height, not logarithmic size
  and not total node visits or machine time.
- B2-INSERT: value correctness and invariant preservation include all keys and
  both duplicate/absent cases. The baseline returns the matched subtree, but
  its recursively reconstructed ancestors are only value-equal here. Actual
  copying and shared-root conclusions remain the graph worker's responsibility.
- E2.2: `LowerBound candidate t` is a strict bound on every remaining label.
  The helper's semantic union includes a matching candidate; its public wrapper
  starts with none. Only a present final candidate incurs an equality test.
  The universal comparison bound is height+1, including empty trees.
- E2.3: optional duplicate abort is propagated by constructor maps and handled
  only by the outer getD. Its value equals baseline insertion, with exactly
  baseline membership comparisons. This does not assert Lean allocation or
  cost equivalence of language-level exception machinery.
- E2.4: a single combined traversal has abort correctness, baseline insertion
  refinement on ordered inputs, exactly candidate-search comparisons and the
  joint content/order/height+1 theorem. Zero actual cell allocations on duplicate
  abort is an outstanding graph-refinement obligation, not inferred from Eq.

The Contents layer's first focused compile passed. It proves pairwise increasing
inorder entries and no duplicates, with an explicit finite enumeration whose
length is numNodes. Comparison's first check needed only `change start < x`
before omega to unfold the identity-key invariant; no statement was weakened.
It supplies ordered right spines with height/numNodes=n and witnesses exact
baseline2n and candidate/combinedn+1 comparisons. Empty, finite, absent-key and
five-deep applications were added to the retained examples. Final focused
run41962 is waiting for the shared lock; no final success is asserted yet.

## Final pure-set focused result

Commitdf1b362a9ed9023089da64d0ad37fa6a154d41ed passed the final focused
build (598jobs, exit0). Exact output and source SHA256 identities are retained
in validation/chapter02-ordered-focused-r3.log and.json. All pure-set assigned
layers and connected examples now compile. No full audit/review acceptance is
claimed. Root has additionally assigned SharedTree/Optimized.lean and
Examples/SharedTreeOptimized.lean to this worker for physical abort/combined
insertion; that new graph implementation is not yet written or validated.

## Graph-optimization recovery snapshot

The worker now also owns Applications/Search/SharedTree/Optimized.lean and the
future Examples/SharedTreeOptimized.lean, by root's follow-up assignment.
Baseline SharedTree.Ordered remains root-owned. Shared core3224ae1/b6b93fe and
Path3cd2686/17de2f7 were imported as dependency commits (local cherry-pick SHAs
d97a87b/151d8a4/ad59eac/b0c5b2d). Optimized imports Path directly and uses
`searchPathBy id`; it does not depend on root's in-progress Ordered module.

The graph draft distinguishes outer invalid/fuel failure from inner duplicate
abort; uses Option.Rel for correspondence with pure optional insertions; calls
allocate only after recursive success; and handles duplicates only at the public
boundary. The intended proofs cover exact comparison/visit/cell profiles,
frontier deltas, retained old roots, matching original store/root on duplicate,
zero duplicate allocations, and actual off-path addresses. Initial focused run
63663 is queued/running and logs outside session to
active-validation/chapter02-optimized-focused-r1.log. No graph compilation or
acceptance is asserted. The earlier pure-set build success remains unchanged.
Graph examples and further corrections are pending; this is a WIP recovery
snapshot, not a completed source claim or chapter acceptance.

## Graph refinement statement review and focused corrections

The raw nested Option makes invalid roots/fuel distinguishable from duplicate
abort. A representation proof and height-bounded fuel exclude the invalid
case; Store.next supplies sufficient fuel from backwards references. The
Option.Rel conclusion matches the actual optional pure result, and the
allocator is called only after a successful recursive return. Exact profile
equality is proved against the instrumented heap traversal, not assigned as
an unrelated formula. Allocation increases the fresh frontier once per call.

The duplicate equations return exactly the original store/root pair with
fresh-cell count0. On absence, Inserted records heap extension, output value,
frontier delta and Rebuilds at the actual search path. The combined retention
contract quantifies arbitrary old roots and every diverging probe; it preserves
addresses in the final heap, independently of extensional tree equality.
Comparison, visit and allocation coordinates remain different. In the fixed
1/2/3 fixture, duplicate1 should give baseline(3,2,0) and combined(3,3,0);
absent4 should give combined(3,3,3), frontier6 and old left-child address0.

The operational value theorem deliberately needs no Ordered hypothesis: it
refines the pure operational variant on every represented tree. The set
interpretation and agreement with baseline insert use Ordered separately.
The generic optional root observer preserves outer failure versus a present
empty root as Option(Option α). New insertion squares and composed examples
are being checked in OptimizedObservation and SharedTreeOptimized.

First graph compile found only nil-equation simplification, fresh-root
normalization and tuple projection issues. Second check reduced these to
unused projection simp arguments plus one unused order section variable.
Corrections use explicit scalar change and omit the unused order hypothesis;
no bound, domain or semantic conclusion was weakened. Failed logs are retained
in validation/chapter02-optimized-focused-r1.log and-r2.log. Run20669 now
checks the corrected complete graph scope and examples; it remains pending.

## Final optimized-graph focused result

Commit `26975a435a38ea89512c68a9d87f9efd7c971113` on `pfds/ch02-ordered` passed the complete
focused `lake build Examples.SharedTreeOptimized` command (672 jobs, exit 0).
The worktree is clean. Exact pinned-shell command, committed source hashes,
dependency identities, successful output and prior failed attempts are in
`validation/chapter02-optimized-focused-r3.json` and the corresponding logs.
The source was frozen throughout that successful compilation; the subsequent
commit did not alter the checked files.

The successful scope includes `Optimized`, `OptimizedObservation`, and
`Examples.SharedTreeOptimized`. Both raw traversals refine their pure optional
algorithms, exclude fuel/input failure on represented inputs, and count actual
modeled comparisons, visits and allocation calls. Duplicate insertion returns
the exact initial store/root with zero fresh cells. Absent insertion preserves
baseline insertion semantics, arbitrary retained old trees and actual off-path
addresses. The combined execution carries the height+1 comparison bound.
Its public squares compose with the independent optional root-value observer.

Connected checked examples cover an invalid root; exact duplicate profiles
(3,2,0) for abort and (3,3,0) for combined insertion; absent insertion of 4 into
{1,2,3} with profile (3,3,3), frontier 6, retained old tree and original left
address 0; the comparison bound; insertion into an empty store and duplicate
root-value observations through composed squares. The abstract and physical
contracts distinguish value equality, address identity and cost coordinates.

Assigned pure ordered-set and optimized physical scopes are now implemented
and focused-compiled. Root owns full Chapter 2 integration, entrypoint/audit
coverage, isolated exact-candidate verification and independent statement/
architecture reviews. Those remaining acceptance gates are not claimed here.
The published-book/thesis union beyond this chapter remains on the coordinator's
chapter frontier; this focused result does not declare a chapter or book done.
