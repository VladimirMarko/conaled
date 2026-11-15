# Chapter 2 finite maps — implementation evidence

Assigned implementation at clean base82501d108f33c62d21b5e0d0f7d2376b902d8d49,
branch pfds/ch02-map. No previous task changes or unrelated user edits.
Read primary book printedpp15–16 (physicalPDF27–28), including Exercise2.6
and Figure2.10. The signature requires empty/bind/lookup, polymorphic values,
and an observable missing-key failure. We interpret the common NOTFOUND
failure as Option.none; values of type Option α remain distinct via some none.

Initial cases: binding key2 to a payload, rebinding key2 to another payload,
then binding key1 must preserve the new key2 result; an unbound key remains
none. A value of type Option Nat bound as none must look up as some none.
These can be evaluated independently from a finite function update model,
but connection to a generic ordered-tree law is initially absent. No syntax
or import failure is counted as a mathematical failing test.

Architecture: reuse Mathlib BinaryTree and the parallel OrderedTree generic
All/OrderedBy definitions with key Prod.fst; values require no ordering or
equality. Observation examines the complete tree independently of ordered
search. The minimal operation interface, its observation laws and concrete
ordered realization remain separate. Existing Squares supplies composable
bind/refinement squares; no new preservation framework is introduced.

Pure and shared finite-map implementations have passed focused compilation.
The modeled heap/root/count claims are described below; no Lean-runtime
allocation guarantee, complete chapter, exact candidate build/audit or review
acceptance is asserted by this record.

## First durable layer

Applications/Search/OrderedMap/Interface.lean now defines the minimal Ops,
function-valued Meaning, write, separate Laws, bind/lookup Squares, and the
left-to-right bindAll client with generic correctness. Payloads require no
instances; failed lookup remains Option.none. This is committed as a coherent
source layer; its first focused build is queued behind the shared compiler
lock, so no successful compilation is yet claimed. The ordered-tree realization
and connected concrete cases remain in progress.

## Initial focused compiler result

Pinned Nix offline build of Applications.Search.OrderedMap.Interface passed,
exit0, 3 jobs (Squares10s, Interface4.2s). Record:
validation/ch02-map-interface.log. Interface source is unchanged since95fc538.
The focused Nix invocation saw unrelated map realization work in progress;
this is not an isolated candidate acceptance check. Full Chapter2 validation,
public imports, exhaustive audit and independent review remain parent-owned.

The committed realization draft at117746c includes key-only invariant
preservation, search/whole-tree observation correspondence, all-query bind
update law, explicit finite-domain witness and subtype-backed operations/laws.
Connected examples cover overwrite, stored optional-none versus absence,
function payloads, composed bind squares, two retained value observations and
finite domain. It has not yet been compiled; OrderedTree.Basic dependency
corrections are pending before the next focused build. The source signature
in Figure2.10 was also independently viewed in the primary scanned page16.

## Pure realization result and statement review

Clean commit3dd96173695d1b01162fd509e99c1e9bd11da5e8 on pfds/ch02-map.
Owned commits95fc538,0f0cf2e,117746c,3dd9617. The other three branch commits
are unchanged cherry-picks of the ordered-tree worker's original29b04b2,
a0075f5,3894128; integrate that common source only once.

Focused `lake build Examples.OrderedMap` passed592jobs in pinned Nix,
exit0. Interface passed separately; Basic passed round2; all examples passed
round3. Round1 corrected only unused simp arguments; round2's two example
obligations were the remaining definitional reductions after generic laws.
No expected outcome, theorem statement or mathematical definition changed to
obtain green. Logs and exact source blobs are in validation/ch02-map-focused*.
The build ran in the development checkout, not an isolated full candidate;
Nix's dirty-tree warning reflects source work before its final commit.

Public claims:
- `lookup_correct`: ordered directed search equals independent whole-tree
  observation. The invariant concerns every descendant key, not child roots.
- `all_bind` and `ordered_bind`: actual recursive binding retains arbitrary
  label predicates when the new pair satisfies them, and preserves key order.
- `lookup_bind`: arbitrary raw trees satisfy selected-key overwrite and all
  other directed lookups stay equal. This stronger law requires no orderedness;
  `observe_bind` separately supplies whole-tree refinement under OrderedBy.
- `lookup_some_contains` and `lookup_finite_domain`: every returned key/value
  pair occurs in the tree's independent contents; an explicit node-key list
  contains every successful lookup key.
- `trees_laws`: the invariant subtype realizes minimal Ops with finite-domain
  evidence separate from the observation laws. Payloads need no typeclass.
- Generic bindAll correctness and bind/lookup Squares allow clients to reuse
  these laws and compose operations through the existing Squares API.

Connected checked examples retain their independently specified expectations:
key2 overwritten7→9, stored optional-none at key1, absentkey3, function payload
f(7)=10 without value ordering, composition order producing11 rather than7,
old/new value observations9/12, and explicit finite-domain witness. They use
public Laws, Squares and finite-domain results; no physical allocation claim
is inferred from these pure values.

Statement review found the intended domains/hypotheses/conclusions aligned:
keys have LinearOrder, values are arbitrary Type; failure is Option.none and
stored None is Some None; orderedness is independent, satisfiable via empty
and preserved bind; there are no additional axioms or admissions. The complete
chapter's shared-root/resource contracts and full build/audit/reviews remain
necessary. Root retains entrypoint/tracker/integration ownership.

## Follow-on assignment

Root assigned actual shared-tree finite-map traversal/refinement after this
pure layer: Applications/Search/SharedTree/Map.lean and
Examples/SharedTreeMap.lean. Reuse Store (κ×ν), pure bind/lookup, stable Path
Rebuilds/off-path contracts, actual root traversal, copied path including the
replacement node, retained old roots and off-path identities. This assignment
is complete at the focused implementation scope recorded below; integration
and formal acceptance remain pending.

## Shared finite-map implementation — current candidate

The physical-map draft is committed fdb02214c56c03b16ca694af1bf83883fd8b8f54;
corrections and composed observation are committed
ed2740c34b7e7e56fcf87c89760ef5067456245c. Dependency source is unchanged from
shared-tree worker3224ae1/b6b93fe and root Path3cd2686/17de2f7, cherry-picked
into this worktree. Initial shared-focused checks compiled those dependencies
and found only elaboration/redundancy corrections in the new file. Round2 left
two allocation-count tuple projection goals; direct Nat.add_assoc now closes
those intended arithmetic steps. Round3 is running; no successful shared-map
compile is asserted until its terminal result is recorded.

`Map.lookupRunFuel`/`lookupRun` read actual heap cells and compare only keys.
Valid representation and its height/frontier bound make the public fuel
sufficient. Missing lookup is None; stored optional-none is Some None.
`Map.bindRunFuel`/`bindRun` allocate the new/replaced endpoint and every
ancestor. The predicted profile is (key comparisons, visits, cells): comparison
count is the existing member execution on the mapped key tree, and visits and
cells are both searchPathBy.length+1. The execution theorem relates the actual
counters and frontier growth to this independent profile and pure bind.

`WrittenAt` supplements `Rebuilds`: it records concrete old/new focus roots,
the original or empty endpoint, and the new label with exactly the same two
child addresses. This is necessary because Diverges only covers branches
selected before reaching the path's endpoint. `WrittenAt.nil_children` exposes
that sharing for root replacement. Allocation/freshness is not assumed by the
path predicates; it is supplied by the actual allocator recursion and counts.
All old represented roots survive heap extension; Rebuilds.off_path supplies
identical addresses for the unselected ancestor branches.

The all-query `bind_lookup` theorem connects shared execution to the minimal
map update law. `bindSquare`, `lookupSquare`, `optionalLookupSquare`, and
`bindThenLookupSquare` reuse conaled's RelSquare composition. Optional lifting
leaves the lookup API unchanged and distinguishes the outer bind failure from
a successful missing lookup; valid represented inputs rule out bind failure.
This physical composition was added following the shared worker's read-only
design check, not an independent acceptance review.

Connected cases construct actual cells at addresses0,1,2 and establish their
representation and key-order predicates. Root replacement copies1cell and
retains both nonempty child addresses, while a left-child replacement copies
2cells and retains the exact right-root address. Old/new observations are
retained. A full physical bind→lookup client covers stored optional-none versus
missing lookup. Expected outcomes follow the independently specified map
updates and explicit allocation sequence, rather than being altered to match
compiler output. Mathematical cell counts do not claim Lean allocator or
runtime preservation.

## Final focused result and integration handoff

Both pure and shared map targets passed. Current clean branch tip is
fcf086ddc271d4b20d4714e36238e47a325316bd. SharedTree.Map compiled in round3;
Examples.SharedTreeMap compiled in round4 (65s), final result592/666 jobs for
the respective pure/shared target closures, both exit0. Frozen final shared
log is validation/ch02-shared-map-focused-r4.log; exact owned commits, source
blobs, reused dependency blobs, command/environment and scope limits are in
validation/ch02-shared-map-focused.json. The Nix process reported a dirty Git
tree warning; the recorded Git worktree is clean. These focused runs are not
used as isolated candidate acceptance evidence.

First shared correction addressed explicit fuel case reduction, allocated-root
rewriting, an unused section parameter and redundant tactics. The second
addressed only tuple-projection exposure for Nat addition. The final example
correction unfolded the explicit ordering predicate rather than asking for an
unprovided Decidable instance. No expected value, count, sharing relation or
ordering premise was weakened or changed to obtain green.

Statement review of the physical layer confirms: actual heap traversal is the
implementation, pure ordered-tree bind/lookup is its specification, fuel is
proved sufficient from representation height, and counters distinguish actual
comparison calls from visits and fresh allocations. Valid bind allocates
path-length+1 cells, including the replaced endpoint. All old represented roots
are retained by whole-heap extension. Rebuilds proves exact off-path addresses;
WrittenAt proves exact child addresses at the endpoint. Both must be retained
in the scope description. The raw procedures are not validators of arbitrary
malformed roots. An ordered valid tree supplies the independent whole-map
observation contract; payloads require no ordering/equality. Physical adapters
use the existing relational representation and optional-result representation.

The concrete cases establish an actual three-cell map and its ordering, then
exercise replacement at the root and below the root, exact counts and child
addresses, old/new value observations, missing versus optional-none payloads,
the all-key update law, lookup refinement, and a composed physical bind→lookup
client. These are public-theorem applications. No admissions, added axioms,
unchecked native proof shortcuts or disabled linters were introduced.

Root should cherry-pick only these owned commits, in order, after the unchanged
dependencies have landed:95fc538,0f0cf2e,117746c,3dd9617,fdb0221,ed2740c,fcf086d.
Do not re-integrate the unchanged dependency cherry-picks from this branch.
Root owns SquareApplications import coverage, full Chapter2 candidate capture,
full build/exhaustive audit/final verification and both independent review axes.
No further compiler process is running for this worker, and no Chapter3
implementation has been started.
