# Chapter 2 preparatory obligation audit

Recorded 2026-11-02 16:33 UTC by the shared-tree worker. This is a read-only
source/statement investigation within ticket 10002, not either final Standards
or Spec review and not a verification result. No compiler, full build, audit,
checkpoint change, or source modification was performed for this investigation.
The report was first saved after checkpoint 008's capture window was released.

## Inputs and snapshot limits

Requirements: `session/requirements/chapter02.md`, the original request and
`REQUEST-union-v2.md`. Source accounting:
`session/research/book-full-inventory.md` and `book-thesis-union.md`.
The primary book's complete printed pp. 7–16 were reread, including Figures
2.1–2.10 and Exercises 2.1–2.6, from the supplied PDF with SHA256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
Physical PDF pages are printed pages plus 12 (one-based).

The final ref observation for this report was:

| Worktree | Ref | Additional observed draft inputs |
| --- | --- | --- |
| `conaled` | `570577621870121f28cffb1a591c3c767b83f751` | Clean at the observation; includes pure ordered sets/maps, baseline physical insertion and its observation adapters |
| `chapter02-ordered` | `c0e93a44243ead88e77aceb520766f91076a9c1b` | `Examples/SharedTreeOptimized.lean` was untracked; observation adapters were explicitly planned after the snapshot |
| `chapter02-map` | `6aec9496168129b79e9516c5667a386e3df3e86a` | `SharedTree/Map.lean` and `Examples/SharedTreeMap.lean` had live proof corrections; optional lookup composition was explicitly planned |

Main and worker branches changed during this investigation. Conclusions about
draft declarations concern the bodies read here, not an immutable accepted
candidate. In particular, present statements and plausible proofs are not
substitutes for successful compilation. Root subsequently reported successful
focused compilation of baseline `Ordered` at `8eaa9c2`; this report did not
rerun that check.

## Concrete gap checklist

### CH02-PRE-001 — matched endpoint identity in baseline insertion

**Open, required statement correction; assigned to shared-tree worker by root.**
Source: pp. 13–15, baseline insertion's equal-key branch and the contrast in
Exercise 2.3. The equal-key branch returns the original matched subtree, while
strict ancestors are copied.

`SharedTree.insertRun_correct` and `insertRun_retention` already establish the
pure inserted value, exact allocation profile, extension of the old heap, and
`Rebuilds` along `searchPath`. However:

- `Rebuilds.here` permits any old and new roots at the empty path.
- `Diverges [] probe` is false for every probe.
- Consequently `Rebuilds.off_path` covers an unselected branch at a strict
  ancestor, but by itself says nothing about the matched endpoint root or a
  path continuing below that endpoint.

This is a missing explicit contract, not an observed execution bug:
`insertRunFuel`'s equality branch does return the original `(store, root)`.
An appropriate completion is a valid-input duplicate theorem saying that
following the search path from the output root reaches exactly the original
endpoint root. State both observations in the retained final heap, or use heap
extension to transport the original one. Derive equality for every further
descendant path. Exercise the theorem on a duplicate below a copied ancestor
whose matched node itself has a nonempty child; a leaf-only example would miss
the descendant issue.

Root assigned separate `PathEndpoint`, `OrderedTerminal` and
`Examples/SharedTreeTerminal` files after this audit. Do not weaken the generic
`Rebuilds` relation merely to make its existing theorem appear sufficient.

### CH02-PRE-002 — finish checking and integrating actual aborting traversals

**Open implementation/validation work already owned by ordered worker; no
additional algorithmic defect found in the statements read.**
Sources: Exercises 2.3 and 2.4, p. 15.

The committed `SharedTree/Optimized.lean` draft contains the necessary stronger
shape of contract:

- Raw `Option (Option (Store × Root))` distinguishes malformed/fuel failure,
  duplicate abort, and success. `insertAbortRunFuel_refines` and
  `insertCandidateRunFuel_refines` rule out the outer failure on represented
  inputs with sufficient fuel.
- Allocations occur only after recursive success. `handleAbort` occurs at the
  public boundary and returns the exact original store/root on duplicate.
- `insertAbortRun_duplicate` and `insertCandidateRun_duplicate` state identical
  original store/root and a zero fresh-cell measure, not only equal unfolded
  values or equality of final allocation frontiers.
- `Inserted`, the absent-input theorems and `insertCandidateRun_retention`
  connect actual allocations, retained old observations and concrete off-path
  roots. `candidateProfile_bounds` and the retention theorem bound the very
  same combined execution by height plus one comparisons.

Acceptance still needs successful checking of these declarations and the graph
examples, integration into the main import closure, and the required final
verification/reviews. Preserve the separation between equality/less-than
comparison count, terminal-inclusive visits and cell allocation count. The
combined route continues to an empty node, unlike the baseline's equal-key
termination, so do not reuse baseline `searchPath` for that route.

### CH02-PRE-003 — finite-map physical layer and its endpoint children

**Open implementation/validation work already owned by map worker. The subtle
endpoint statement is present in the draft, not an additional missing theorem.**
Source: Exercise 2.6 and Figure 2.10, pp. 15–16, interpreted with the chapter's
path-copy persistence contract.

`Map.bindRun_correct` supplies exact counts, old-heap extension, the independently
defined `OrderedMap.bind` value, ancestor `Rebuilds`, and `WrittenAt`.
`WrittenAt` is significant: overwriting a key changes the endpoint binding but
retains both of that endpoint's child addresses. An overwrite at the root has
an empty ancestor path, so `Rebuilds.off_path` alone would be vacuous. The draft
avoids that defect; `WrittenAt.nil_children` and
`replacement_keeps_children` use two nonempty old children.

`lookupRun_observes` connects directed physical lookup to whole-tree meaning
under key ordering. `bind_lookup` proves the all-query update law for actual
execution. Keep its weaker raw-tree directed-lookup law distinct from the
independent `observe` interpretation, which needs `OrderedBy Prod.fst`.
Finish checking and integrating the physical module and examples. No payload
equality/order should be added: the existing pure function-payload case and
physical optional-payload cases test that distinction.

### CH02-PRE-004 — compose the new physical observation adapters

**Open small integration work, explicitly confirmed by both workers.**
Basis: Chapter 2 architecture requirements and ADR 0010; independent value
algorithms and root implementations should connect through the existing square
interfaces with checked composed clients.

Baseline already has `OrderedObservation.insertSquare`,
`optionalRootValueSquare`, `insertRootValueSquare`, and a composed example.
General allocation already has `Observation.allocateSquare` and a composed
root-value observation. Shared-list append/update have their ordinary square
clients. Thus these are not gaps.

At the read snapshot, physical optimized insertion had no corresponding
observation adapters. The ordered worker confirmed it will add adapters to the
pure `insertAbort`/`insertCandidate` wrappers and a composed observer example.
The raw refinement supports wrapper equivalence even on unordered tree values;
ordered set correctness remains a separate premise rather than contaminating
the general tree representation.

Physical map already has `bindSquare` and `lookupSquare`, but their boundary
representations do not compose directly because bind returns an optional
state. The map worker confirmed an optional lookup adapter and a checked
bind-to-lookup composition will be added. Use the existing
`optionalRepresentation`, with the chosen flattening/nesting stated in its
specification. Do not invent a new mandatory error taxonomy: the existing
SharedList optional-head client is a suitable precedent. A stored optional
`none` must still be distinguishable from absence at the relevant value layer.

### CH02-PRE-005 — reconcile every final input with exact-candidate validation

**Open mandatory integration gate; root owns it.**

`SquareApplications` now imports the integrated Chapter 2 examples, including
pure maps, constructor cases and baseline insertion. The optimized/map physical
worker outputs and the new terminal-retention correction were not yet all in
that integrated candidate. Their new modules must enter its local import
closure, not remain checked only by a worker's focused command.

Freeze the final combined candidate before the applicable complete build and
exhaustive axiom/source audit, matching verification record, final candidate
verification and both independent review axes. The currently running full
check of import-only candidate `226ebae` is not a Chapter 2 acceptance check.
SharedList ticket 10013's earlier focused results and reviews must retain their
own pending dispositions; adding Chapter 2 consumers does not retroactively
accept the prerequisite. Update the statement/source coverage record against
the final declarations after the above corrections, and checkpoint that work.

## Obligation map: substantive coverage already present

“Present” below means a declaration or explicit source disposition was found.
It does not override the open validation gate.

| Requirement/source item | Present evidence | Qualification |
| --- | --- | --- |
| B2-STACK, LIST, CUSTOM; Figs. 2.1–2.3 | `AbstractStack.Ops`, separate `Laws`, `lists_laws`, custom inductive `Stack` and `custom_laws` | Empty head/tail failures remain observable; custom representation is actually distinct |
| B2-APPEND-ABSTRACT/LIST; p. 9 | `appendRun_correct`, `appendDirect_eq`, `lists_appendRun`, `custom_appendRun`, `appendSquare` and composed head client | Generic algorithm uses abstract operations. Length-at-most-fuel is proved sufficient; a redundant fuel-free API is not required by the agreed spec |
| B2-PERSIST/APPEND-SHARING; pp. 7, 9–10 | `SharedList.appendRun_correct`, heap extension and `Represents.mono` | Exact left-length allocations, terminal-inclusive visits and original right-root identity are stronger than an unsupported O(n) slogan |
| B2-UPDATE; pp. 10–11 | Natural `updateRun_success`/`failure`; `IntegerUpdate` exact nonnegative refinement, negative traversal cost and `updateIntegerSquare` | Signed negative inputs traverse to empty. Do not replace that with a fast negative rejection or infer signed behavior from Nat alone |
| E2.1; p. 11 | Suffix execution/chain/value correctness, closure, reachable-cell/distinct-root counts and `Resources.SharedList` | Outer root-list cells and reachable input cells are both charged; value equality alone does not prove shared space |
| B2-ORDER/SET; pp. 11–14 | `OrderedTree.OrderedBy`, all-descendant `All`, independent `Contains`/`entries`, `OrderedTree.finite_contents` from `Contents.lean`, baseline/candidate abstract set laws | Strict descendant ordering, finite contents and uniqueness are proved. `LinearOrder` supplies coherent equality and comparison laws; no arbitrary inconsistent comparator claim is made |
| B2-MEMBER; p. 12/Fig. 2.9 | `member_correct`, `memberRun_bound`, right-spine sharpness results | Bound is in node-height. The ordered skew family has height equal to size, so no logarithmic-in-size claim follows |
| B2-INSERT; pp. 13–14 | Physical `insertRun_correct`, `insertProfile_bounds`, `insertRun_retention`, `insertRun_ordered` and root-value composition | Terminal identity is CH02-PRE-001; baseline duplicate ancestor copying is already explicitly exhibited |
| E2.2; pp. 14–15 | `memberCandidateRun_correct`, `memberCandidate_correct`, bound by height+1, exact sharpness family | One less-than comparison per visited node, and at most one equality at empty; empty/no-candidate case uses zero comparisons |
| E2.3/E2.4; p. 15 | Pure candidate/abort correctness plus actual `Optimized` contracts described above | Must finish physical integration/checks; separate pure algorithms alone are not the discharge |
| E2.5a; p. 15 | `completeValue` height/node-count facts, `completeRun_correct`, stored equal child roots and retention, `completeWork_exact`/`linear` | Natural depth, empty depth zero; exact d cells versus 2^d−1 unfolded nodes. No strict-BST premise |
| E2.5b; p. 15 | Recursive `SizeBalanced`/`Fits`, `create2Value_fits`, `create2Run_correct`, actual `create2Run_children`, `balancedRun_correct`, logarithmic work theorem | Every node has child unfolded sizes differing by at most one. Actual pair has n,n+1 sizes. Size zero still allocates the one-node companion; that cost is counted |
| E2.6; pp. 15–16 | `OrderedMap.Ops`/`Laws`, independent `observe`, directed `lookup_correct`, `ordered_bind`, `observe_bind`, finite-domain theorem, subtype realization and generic `bindAll` clients | Missing key differs from stored optional-none; values are unconstrained. Physical layer/adapters are CH02-PRE-003/004 |
| B2-NOTES and other context | Complete primary inventory's contextual classifications | Imperative ownership diagram, garbage collection and historical nonfunctional persistence methods are not extra verified runtime algorithms |

## Assumptions and scope that must remain visible

1. The counts describe modeled operations. A primitive key comparison, heap
   access/allocation and integer arithmetic have the explicitly chosen bounded
   unit overhead. They are not measurements or complexity theorems about Lean's
   functional heap representation, arbitrary-precision arithmetic, allocator,
   or exception runtime.
2. `Represents` supplies valid backward references and a sufficient frontier
   fuel bound. Raw traversals are not validators of arbitrary heaps, and their
   invalid-input behavior must not be confused with source exceptions under
   valid-input contracts.
3. Equal unfolded values do not imply shared addresses. Distinct old versions
   are retained by heap extension; unchanged branches by root identities; the
   number of newly allocated cells differs from unfolded size and live-space
   reclamation. No minimal live-space or garbage-collector theorem is claimed.
4. The exercise constructors use natural sizes/depths; the inventory and shared
   worker report explicitly give that mathematical domain. The logarithmic
   formula uses `log2(n+1)` with a separately stated eventual O(log n) theorem;
   n=0 is not silently excluded from functional correctness.
5. Thesis chapter numbering is not book chapter numbering. The union inventory
   assigns thesis Chapter 2's lazy streams to book Chapter 4, and its trace/debit
   persistence analysis to book Chapters 5–6. The book's introductory
   persistence exercises are book-only. No extra thesis Chapter 2 algorithm was
   discovered for this book Chapter 2 closure. The current acyclic reference
   graph does not discharge the later trace model, whose allowed graph features
   differ. Keep those existing later owners and obligations.

No additional missing Chapter 2 algorithm was identified beyond the explicit
endpoint statement and already assigned physical integration work. This is a
bounded preparatory finding, not a claim that either final review will find no
further issues.

## Implementation followup after the audit

After checkpoint 009's capture window was released, CH02-PRE-001 was implemented
in the assigned shared-tree worktree. Final source candidate:
`4b0f0c0bc7c139480fb72407b93a2d9eb6874289`, comprising implementation commits
`dfd9411`, `d3f1e87`, and `4b0f0c0`. Dependency-copy commit `3385a48` imports the
unchanged stable main versions of Path, Ordered and OrderedTree.Basic; it is
not an additional implementation change for main.

`Search.SharedTree.follow_append` in `PathEndpoint.lean` expresses path
concatenation through optional endpoint observation. `follow_descendants`
transports equality of endpoints
to every suffix path in the same heap. Neither lemma assumes a valid heap,
since failed traversals compose in the same way.

`Search.SharedTree.insertRunFuel_duplicate_endpoint` in `OrderedTerminal.lean`
connects actual baseline execution to the identical old nonempty endpoint address under sufficient
fuel and directed membership. Its public wrapper
`insertRun_duplicate_subtree` derives directed membership from the independent
ordered-tree content predicate, obtains the actual output, counts exactly the
strict ancestors as fresh cells, retains the old represented version, and
preserves every path continuing below the matched endpoint. The assumptions
are representation validity and the existing strict ordering invariant; root
identity is a conclusion, not an input relation.

The worked tree has root 4, left child 2 with nonempty child 1, and right child
5. Inserting duplicate 2 performs three comparisons, two visits and one cell
allocation. `duplicate_retains_terminal_and_child` obtains the exact old roots
of nodes 2 and 1 through the public theorem, while retaining the old tree.
`duplicate_retains_deep_observation` additionally transports a path which runs
beyond the retained leaf and fails. These cases cover the endpoint/descendant
gap rather than merely a divergent branch at an ancestor.

The generic and execution theorems compiled on their first Lean pass. The
example corrections only made the concrete search route and list append
normalization explicit; they did not change any expected statement. The final
focused `lake build Examples.SharedTreeTerminal` passed with 665 jobs and exit
0. Exact source hashes and all attempt logs are recorded in
`session/validation/chapter02-shared-terminal-focused.json` and its listed
frozen logs. The initial default-sandbox Nix startup failure occurred before
Lean ran and is identified separately.

This supplies the missing implementation statement and its checked uses.
Integration into the final Chapter 2 candidate, the complete verification gate,
and independent review remain root-owned. Root also reported the optimized and
map physical families and their composed observation cases compiled and
integrated before this final terminal correction; that progress does not
replace CH02-PRE-005.
