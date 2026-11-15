# Frozen requirements — FDSA-XS01 ordered-tree search paths

Frozen before source authoring on 2026-11-02. This is one bounded shared
component under the user's cross-cutting exception, with actual repeated query
clients in Chapters5,6,8,9 and10. Chapter1 remains active. No chapter, appendix
or shared unit is accepted. The full request, all original chapter inventories,
scope corrections and unresolved findings remain mandatory.

## 1. Original base, evidence and chosen boundary

Original review base and intended immediate parent:
`66eae34815a177c6b4bf5120e05202ebb8876c91`.
Clean isolated checkout: `conaled-ordered-search`; branch:
`work/fdsa-ordered-search`. The start and clean-start JSON records capture the
actual clean HEAD, preserved main/review checkouts,21 baseline file identities,
absent new paths and package symlink. There is no project build directory.

This base is the retained XT07 ordered-tree draft, with parent
`28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2` and XT01 ancestor
`64c6b777d828ecfe83234fc2aed94600a1f24297`. Those tree components remain
uncompiled and unaccepted. Their ancestry does not replace future validation
or permit loss of the repaired C1 changes when this draft is integrated.
The required Measured/CallCount interfaces have identical bytes at this base
and repaired C1 candidate07e480f. No other draft branch is a new dependency.

Root read all complete stopped source/API/case reports and reconciled the
bounded documentation findings. Final identities:

| Report under `research/` | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| ordered-search-source-preflight.md | 29001 /410 | `71fe9b69807db736c0d6319995a61bf72b1b5ff508c085d128de96c07b589c21` |
| ordered-search-api-preflight.md | 35342 /342 | `ccb85b57a2900d0bf2aadfd8135d314438738e73aa6d2a925f110453c9d42209` |
| ordered-search-case-preflight.md | 30396 /536 | `dec26d65e156f7ca381a4e49a653729fd4cc011e3fca56331c8468d6f6f7a754` |

XS01-PRE-DOC01 corrects only interruption attribution. XS01-PRE-DOC02 corrects
only two existing fixture namespace references to OrderedTreeExamples. Both
complete originals and root's assessments remain preserved. Neither changes
mathematics, source obligations, validation history or acceptance status.

Primary source is the July27,2026 FDSA PDF, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Pinned companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`,
with exact Cmp, Tree_Set, Tree_Map, Isin2, Lookup2 and later-client identities
in the source preflight. The companion revision postdates the manuscript and
is not claimed to be its generation revision.

Reuse pinned Lean4.35.0/Mathlib APIs, including compareOfLessAndEq,
cmp_eq_compareOfLessAndEq, Ordering.Compares, BinaryTree, List.find? and
List.lookup. No new comparator wrapper/law record, tree hierarchy, search
machine, pure duplicate recursion or source translator is part of this scope.

## 2. Exactly five source paths and ownership

| Path | Responsibility / owner |
| --- | --- |
| `Applications/Resources/TreeSearch.lean` | One actual measured path executor, projections/derived visits, semantic/transport/count/height/tightness laws; architecture author. |
| `Examples/TreeSearch.lean` | Connected general and concrete applications with the independent expectations below; rotation_cases author. |
| `SquareApplications.lean` | Add exactly one public import of Examples.TreeSearch, preserving all existing imports; root. |
| `docs/research/fdsa-tree-search.md` | Source/license, statement/model assessment, public correspondence and honest remaining scope; book_inventory author. |
| `docs/research/fdsa-reconstruction-map.md` | Append this limited source/public-claim map and downstream limits without changing earlier content; book_inventory author. |

Keep all existing tree/resource definitions, theorem statements, proofs and
fixtures unchanged. Keep every toolchain, manifest, guard, audit, root policy,
environment setting and other source path unchanged. Do not import another
unaccepted branch to obtain ADT, probability, logarithm or traversal machinery.
Proof-local helpers within these files are permitted when they serve the
required statements; no declaration quota or new framework is required.

The resource core imports the existing CallCount, Trees.Ordered and ordinary
comparison interfaces. Existing ordered fixtures and the optional-dependency
path interface belong in examples. Use independent universes for labels,
keys, mapped labels and semantic payloads. No payload order, equality decision,
inhabitance, finite enumeration or default value may leak into the raw API.

## 3. One actual execution and its exact observations

Use namespace Resources.TreeSearch and the fixed public operation names
run, find?, entries and visits. Required operation:

`run (route : α → Ordering) : BinaryTree α → Measured (Option α) Nat`.

This is one structural recursion over the actual input tree. At nil use
CallCount.tick (Resources.pure none). At a node, inspect route on its stored
entry once in the model: EQ ticks pure(some entry), LT ticks the actual left
recursive computation, and GT ticks the actual right recursive computation.
Only the selected child contributes. Do not compute inorder, map the whole
tree, visit both children, run indexOf followed by get, or attach an independent
counter to a separately evaluated result as the implementation.

find? and entries are the Option/Nat projections. Define visits from the one
measured result as E minus its terminal-miss indicator in Nat. A let binding
can expose that result; this is not a memoization or Lean sharing theorem.
E counts search invocations including a reached empty call. V counts reached
nonempty nodes/three-way route evaluations. Comparator internals, key
projections, Option constructors and nonrecursive observations are uncharged
under this explicitly declared source-style model.

Prove the complete pair equations and useful projection/derived equations:

| Reached case | Option result | E | V |
| --- | --- | ---: | ---: |
| nil | none | 1 | 0 |
| node/EQ | some stored entry | 1 | 1 |
| node/LT | actual left result | E(left)+1 | V(left)+1 |
| node/GT | actual right result | E(right)+1 | V(right)+1 |

Prove1≤E before using truncated subtraction. Prove the unconditional identity

`E = V + (if (find? route t).isNone then 1 else 0)`,

and its hit E=V and miss E=V+1 consequences. Prove the direct V equations from
the same selected computation; defining subtraction alone does not establish
its visit interpretation. Every raw tree/route, including invalid ordering
and dishonest routes, is in the domain of these equations.

Do not identify V with an additive reweighting of E alone. A root hit and an
empty query both have E1 but different V. In a composition of multiple queries,
the difference is the sum of their actual miss indicators, not one final
indicator. This scope does not add a redundant product run or second V
executor. Nonrecursive membership/payload clients consume the actual measured
result through ordinary bind/pure and CallCount.primitive_rule.

## 4. Raw and calibrated semantic laws

### Raw success and minimum premises

For arbitrary route and tree, prove that find? route t = some a implies both
`a ∈ Trees.inorder t` and `route a = .eq`. No order or invariant is needed.
With key : α→κ, query q and local comparison calibration on stored entries,
a successful entry has key a=q. This soundness implication needs only the
comparison predicate's LT structure; it must not require orderedness merely
to obtain key equality at an honest EQ hit.

### Strict keyed correctness

Under `[Preorder κ]`, require exactly the substantive semantic premises:

- `Trees.Ordered (fun a b => key a < key b) t`;
- `∀ a ∈ Trees.inorder t, (route a).Compares q (key a)`.

Prove the full-entry statement

`find? route t = some a ↔ a ∈ Trees.inorder t ∧ key a = q`,

and the absence statement

`find? route t = none ↔ ∀ a ∈ Trees.inorder t, key a ≠ q`.

Derive presence/membership from the same result. Calibration is input-local;
it is a theorem premise, not an executed inorder check. Strict subtree bounds
justify pruning; they are not weakened to child-root comparisons, full-record
lexicographic order, weak key sorting or merely distinct full entries. Use
within-tree key uniqueness when necessary; no global key injectivity is added.

For the source specialization use the existing compareOfLessAndEq q (key a)
with LinearOrder keys. Its calibration is obtained using the already proved
cmp_eq_compareOfLessAndEq and cmp_compares. Consume those existing facts in
the connected examples; do not duplicate their definitions or proofs.

### First-inorder and semantic map observations

Under the same strict-key/local-calibration premises, prove equality with
the existing List.find? on inorder using the Boolean predicate
`fun a => decide (route a = Ordering.eq)`. This observer needs no decision
of key or payload equality. If a key-equality observer is used additionally,
its extra decision assumption belongs to that observer alone.

For labels κ×β, prove

`(find? route t).map Prod.snd = (Trees.inorder t).lookup q`,

with strict first-key ordering, calibrated route, and only the actual lawful
key BEq interface needed by List.lookup. The semantic β has no additional
structure. Retain first-binding behavior of the existing list observation;
do not introduce another list lookup or use an arbitrary later duplicate.
Bool presence and semantic payload are distinct observations: some false
means a present entry and is different from none.

## 5. Exact label transport, raw bounds and tightness

### Transport the actual run

For f : α→β in independent universes and local route agreement
`∀ a ∈ Trees.inorder t, route' (f a) = route a`, prove the full pair equation

`run route' (t.map f) = ((run route t).1.map f, (run route t).2)`.

Derive the returned-option, E and V observations from this equation. Include
the unconditional pullback specialization where useful. No order, cache
validity, injectivity or global route agreement is required. The proof follows
identical selected branches; inorder/height equality alone is insufficient.
An actual client that constructs t.map f performs additional work; this
transport theorem does not declare that construction free.

### Bounds on raw paths

For every tree/route, prove V≤height and E≤height+1, together with the above
E positivity. For a successful result prove1≤V and E≤height. These statements
require no search correctness, strict order, cache or balance premise.
Empty has height0/E1/V0. The existing height_le_numNodes may supply a direct
linear bound without a new growth framework; no logarithmic bound is claimed.

### General nonempty deepest-present-key witness

This requirement is selected now, not deferred behind an upper bound.
With `[Preorder κ]`, key : α→κ, route : κ→α→Ordering, t≠nil and the strict
keyed invariant, assume calibration only for pairs of stored entries:

`∀ a ∈ inorder t, ∀ b ∈ inorder t,
  (route (key a) b).Compares (key a) (key b)`.

Prove that some a∈inorder t satisfies

`run (route (key a)) t = (some a, t.height)`.

Connect the hit relation to V=height as well. A structural maximum-child
argument supplies the actual witness: choose the root when both children are
empty, otherwise a nonempty child attaining maximum height, and use the whole
subtree bound/calibration to force the parent route into that child. No depth
datatype, global Inhabited instance, absent-key assumption, probability model
or supremum over an empty domain is required. Include the source LinearOrder
specialization using its existing literal comparator.

This proves present-key height tightness; an absent query can take height+1.
It does not say every query costs height or every strict BST has logarithmic
height. All later balance/height/cardinality premises remain mandatory.

## 6. Connected independent applications

Use actual public operations/laws and the existing fixtures. Do not replace
them by expected constants or prove only a separately defined reference
program. No additional example per helper declaration is required.

### Source comparator and existing path interface

Instantiate the raw/semantic/count laws with compareOfLessAndEq and use the
existing comparison equality to relate the complete query run to the cmp
route. This equality concerns the declared query observation, not comparator
primitive tests or real runtime. Retain arbitrary label/key universes.

Include the general value-only bridge for the homogeneous existing path API:

`find? (fun a => cmpUsing lt q a) t =
  (BinaryTree.indexOf lt q t).bind (fun n => BinaryTree.get n t)`.

It needs the actual decidable relation, not order laws. Import Tree.Get in the
examples, and prove the matching structural branches. No cost correspondence
for this two-pass expression or for a whole-tree key map is asserted.

### Existing printed tree and a valid rotation

Reuse OrderedTreeExamples.printedTree, its actual inorder/height/ordered laws
and source comparator. Required exact executions are:

| Query | Result | V | E |
| ---: | --- | ---: | ---: |
| 6 | some6 | 1 | 1 |
| 3 | some3 | 2 | 2 |
| 9 | some9 | 2 | 2 |
| 8 | some8 | 3 | 3 |
| 4 | none | 3 | 4 |

Connect successful entries and absence to the public correctness theorem and
printed_inorder. Query8 and query4 attain the respective height and
height-plus-one bounds. Instantiate the general deepest-key theorem.
Use the existing legal left rotation and ordered/inorder facts to show lookup
value preservation, while actual query6 changes E=V from1 to2. Do not claim
path-cost preservation from inorder preservation.

### Semantic payload and noninjective transport

Reuse taggedTree = three (0,false) (1,true) (2,false), treating Bool as semantic
payload. Query0 returns some(0,false), E=V=2; payload projection gives
some false and presence true. Query3 returns none, V2/E3. Connect both actual
measured observations through CallCount.primitive_rule, and connect the
payload result to first-inorder List.lookup.

Use discardTag (k,b)=(k,()) and its existing noninjectivity/key-preservation
facts with the raw run-map theorem. Query0 gives some(0,()) with E=V2;
query3 remains none with V2/E3. This changes semantic Bool to Unit and does
not preserve the old Bool value. Separately instantiate general outer-tag
erasure `((κ×β)×γ)→κ×β`: ignore only γ, preserve arbitrary β and its Option
payload, and preserve E/V without cache/color/height validity. This is a
cross-universe public transport use, not executable full-tree preprocessing.

### Empty and three missing-premise boundaries

Prove empty result/counts for arbitrary labels. Use a nonvacuous key query on
BinaryTree(Nat×Empty) to show every such tree is empty and every available key
query returns no semantic value with E1/V0. Do not assume a default payload.

Use the independent malformed tree with root(2,"root"), left singleton
(5,"left") and empty right. Query5 returns none with V1/E2 despite the
stored key and inorder lookup some "left". Its keys are distinct; ordering
is missing. Raw success/height laws remain applicable.

Reuse sameKeyRecords and its actual left rotation. Both have inorder
[(1,10),(1,20)], distinct full records and weakly sorted keys. Query1 returns
payload10 before and20 after, each E=V1; first-binding list lookup is10.
This refutes unconditional stored-entry/payload lookup invariance, not Bool
membership in this particular example. Strict semantic-key order is absent.

On the valid three-key tree with root2 and leaves1/3, query9 with an always-EQ
route returns some2, E=V1. The returned entry is stored but the key is wrong;
orderedness cannot discharge comparison calibration.

### Actual finite present-key average

For uniform queries among the three present keys[3,6,9], execute the balanced
three 3 6 9 and literal increasing right chain3→6→9. Their actual successful
query cost lists are respectively E=V=[2,1,2] and E=V=[1,2,3]. Prove sums5/6
and rational arithmetic means5/3 and2 from those actual runs. This is the
preserved C05-094 finite interpretation. No distribution on infinite keys,
absent queries, arbitrary nonuniform weights or probabilistic framework is
introduced. Use only existing arithmetic/list interfaces; no other draft
expectation branch is imported.

## 7. Source documentation and unchanged downstream scope

The note must retain exact source/version/hash references and the complete
applicable Isabelle BSD-3-Clause copyright/conditions/disclaimer. Reuse the
existing Lean/Mathlib operations under their pinned provenance; do not copy
the manuscript or claim the later companion revision generated it.

Distinguish source query equations, reconstructed E invocations, derived V
visits/three-way calls, and excluded comparator primitive/internal work. The
source report found no generated T_isin/T_lookup in the inspected theories.
Literal LT takes one primitive test and EQ/GT two, but this unit adds no
primitive-test counter and claims no primitive-cost equality from cmp value
agreement. No compiler, allocation, sharing, wall-clock or target-runtime
result follows. V is not an additive reweighting of E across arbitrary binds.

Map public statements and actual examples to only the relevant source claims:
C05-003/004, query portions of C05-014/028, C05-066 and C05-094; C06-045 and
query portions of C06-064/065; C08-020/021/075/076 and query portions of
C08-071/072; C09-008/009 and query portions of C09-039/040; inherited C10-003
query semantics. Record the p59 nonempty tightness witness explicitly. No
partial row is marked wholly complete just because its query clause is covered.

All concrete mutations, both deletions, split_min/nonemptiness, direct-proof
exercise obligations beyond query, joins, unions, rotations' reconstruction
costs, interval/sweep algorithms, full Set/Map realizations, color/black-height
or height/cache invariants and logarithmic proofs remain mandatory. Chapter7
Node3 has a conditional second comparison and requires its own carrier/count.
Chapter10 split returns rebuilt trees and its Boolean; query correctness alone
does not prove those trees, joins or total cost. The retained conditional
treap-work gap C10-117 and all whole-book obligations are unchanged.

The note and appended map must state source-only/uncompiled status honestly
until matching acceptance evidence exists. A preflight or draft checkpoint
does not complete a chapter or validate inherited tree drafts.

## 8. Release, validation, integration and recovery

Before source release, capture this complete scope, all stopped reports and
findings, clean/original starting-state identities, author readiness and local
tracking in checkpoint0055. Expose and successfully save that checkpoint
before root releases any author. Authors write only their assigned paths and
coordinate public signatures without weakening the frozen statements.
No Lean/compiler/checker/project hash helper or project build-cache mutation
is authorized for XS01 while C1 attempt3 is the sole validation run.

Root must read all complete source files, review every formal statement and
its actual public connections, preserve findings/corrections, and stop all
writers before capture. Commit all non-main edits locally, then create,
expose and save the full draft checkpoint. No GitHub mutation or push occurs.

Accepted repaired C1 and the applicable ordered-tree prerequisites precede
XS01 integration/acceptance. The original initial C2 prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; XS01 is not included in it.
The unchanged shared-integration plan permits successive immutable candidates
in the same idle normal-cache checkout. Preserve this original66eae348 base,
full scope and all predecessor changes when reconciling future integration.

Required eventual gates remain applicable focused checks, clean immutable
full `./check.sh --candidate HEAD`, source/coverage/pinned identity checks,
both integrity passes, all integrated modules and exhaustive transitive axiom
audit, both independent Standards and Spec axes against the full original
XS01 scope, and immediate `./check.sh --verify-candidate HEAD`. C1's retained
review loop and original14-path scope remain separate and unchanged. Fresh
mode requires the existing concrete README/runbook triggers. No focused pass,
branch ancestry, source read, cache observation or bookkeeping field replaces
acceptance. Preserve every failed, superseded and unknown prior outcome.
