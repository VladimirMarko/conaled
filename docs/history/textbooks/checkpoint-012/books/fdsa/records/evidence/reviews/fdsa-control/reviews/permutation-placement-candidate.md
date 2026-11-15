# FDSA-XU06 committed source-draft handoff

Status: **committed, uncompiled source draft; all final gates pending**.
No chapter, appendix or shared unit is accepted. Old Chapter 1 gate 80227
continues unchanged; its source/cache/configuration is untouched.

## Candidate and fixed requirements

- Candidate: 49d6d4700b41f2837ae4cc5e74d23fc1eff8afbe.
- Parent and fixed source review base: a5341221bd3e28d76e3b8ad2bc1683a74621ad5e.
- Branch: work/fdsa-permutation-placement.
- Checkout: /workspace/scratch/845aa1048b05/conaled-permutation-placement.
- Commit: feat(probability): separate fixed placement from internal order (#174).
- Eight paths; 1,513 insertions; no deletions. Git status was empty after commit.
- Requirements: permutation-placement-requirements.md, 15,590 bytes / 282 lines,
  SHA-256 1769c0550a448d9a5de06b4e926006318723887397f65d4dfabf687bdbef6902.
- Starting state/ownership: permutation-placement-start.md and matching JSON.
- Exact final source identities: permutation-placement-source-identities.json.
- Complete stopped-source assessments, findings and rechecks:
  permutation-placement-source-preflight.md.
- Pre-code checkpoint 0037 is saved and receipted in ../checkpoints.json.

Only unchanged pinned dependency packages are linked. Project outputs are
separate; no compiler/checker/project hash helper ran in this checkout.
No toolchain, dependency, checker, integrity-policy or configuration changed.

## Actual source additions

### One invariant-event law and deterministic count transport

The existing Order module has a private sliced-fiber lemma and the public
uniformOn_inter_restrictedOrder_eq. The actual right-relabeling bijection
preserves E and transports the supported order. The finite partition under
μ0.restrict E normalizes by A.card!, never by μ0 E. Null events, empty A,
empty I and unsupported lists retain the exact frozen semantics.

PermutationExpectation.beforeCount_relabel reindexes the defining counted set
as the inverse image under σ.symm and applies the ordinary Set.ncard bijection
law. It needs only LT P, preserves the infinite-set convention, and does not
claim that a named outsider's event is preserved.

Both predecessor formal bodies remain byte-identical before the appended
sections, independently checked against the saved joint checkout. New direct
imports/header paragraphs are the only earlier-file textual changes.

### Ordinary independence and weighted moments on the actual environment

PermutationPlacement first derives canonical independence by summing the
invariant actual count-event slices over supported lists in a target event.
Its public indepFun_beforeCount_restrictedOrder transports the joint event
and both marginals through a full-global-permutation HasLaw. It imposes no
finite Ω or stronger Measurable Π premise and no list-singleton requirement.

The two scalar weighted theorems combine the new independence with the old
count mean. The ENNReal version permits infinite weights. The real version
uses a private conjunction proving integrability of count, actual order weight
and product on the finite target, transporting all three through hΠ before
extracting the moment identity. Signed real weights are permitted. Scalar
statements expose no measurable space on lists; the proof's discrete choice
is local. Nat subtraction precedes the casts.

There are exactly the five frozen new public core results and no new operation,
probability carrier, product-law alias or conditional wrapper.

### Connected actual cases

The main client uses the original Fin3 selected/rank3/law3 observation:
its actual count is an indicator with mass 1/3; complement mass is 2/3.
The four new event-law cells have masses 1/3,1/3,1/6,1/6. New independence is
specialized through HasLaw.id. The fixed weights 2/5 have mean 7/2, product
mean 7/6 through both weighted APIs, and actual finite-image ordinal product
mean 14/3 through the old first_position_bridge. Negative weights and a
nonnegative coefficient increase are separate connected uses.

Complete own-order conditioning retains the count probabilities; count-one
conditioning retains the two order probabilities and gives actual count mean
1 under that changed measure. Both changed measures are explicitly unequal
to the original law. Empty, impossible and unsupported events retain zero
mass and zero conditional measure. The actual placement-dependent weight
count has product mean 1/3 versus marginal product 1/9.

The boundary client consumes new independence for empty/full/singleton/tied
and Empty-index observations. A locally always-true LT Unit has full Fin2
count 2 while still satisfying the weak independence theorem. A lawful full
subset with infinite ENNReal weight retains a zero product and an infinite
weight integral. An arbitrary-Ω case explicitly transports product integrability.

The two-atom measure is literally half-dirac at identity and half at swap0 2.
Actual observations (count,order) are (0,[0,1]) and (1,[1,0]). The map theorem
establishes the old uniform nonconstant order marginal, but a joint cell 1/2
differs from product 1/4. This establishes nonindependence and then refutes
the full-global HasLaw premise. Earlier global-head/adaptive mean boundaries
are reused accurately; a Fin4 outsider swap exercises aggregate relabeling.

All cases are source-written and uncompiled. No numerical arithmetic, source
read or prior unrelated focused result is substituted for kernel checking.

## Source assessments and retained findings

Root read the complete new Order section/header, all root-owned source, both
complete clients and documentation. Independent bounded readings of the root
count/placement cores and main client found no concrete issue. The full
documentation read and later matching to actual clients found no discrepancy.

The boundary reading retained:

- XU06-BC01: a direct rw used a distinct ordinary rank3 alias. The typed hzero
  application is implemented and same-reader source-rechecked. This was a
  predicted elaboration issue, not an observed compiler failure.
- XU06-BC02: the direct Dirac umbrella import was explicitly deprecated in the
  pinned Mathlib source. The current Dirac.Def import is implemented and
  same-reader source-rechecked.

Both retain compiler/final-review confirmation as pending. The complete
original boundary source is saved under permutation-placement-preflight-snapshots,
with both finding identities. The reader verified exactly those two changes,
with no statement, assumption, definition, case or prose change.

Full staged and unstaged Git whitespace checks passed. A bounded forbidden-marker
inspection of the six changed Lean paths found no matches; it is not the
production source guard. Seven of eight stopped preflight source identities
remained identical, and the eighth matched exactly the recorded two fixes.

## Pending acceptance and integration

Required future focused targets include Applications.Probability.PermutationPlacement,
Examples.PermutationPlacement and Examples.PermutationPlacementBoundary,
with their inherited probability prerequisites. Focused builds cannot run
concurrently with old gate 80227 and do not replace the full candidate check.

After repaired Chapter 1 and the inherited shared chain have their required
acceptance, reconcile this saved history with the exact accepted predecessor,
retaining all accepted corrections and the complete frozen scope. See the
separate permutation-placement-integration-addendum.md. Do not reset/rebase
saved refs, cherry-pick around a preceding-base requirement, or overwrite an
accepted Order/Expectation file with this old prefix.

The immutable reconciled candidate still needs the full guarded build,
exhaustive audit, matching success record, both final independent Standards
and Spec reviews, and immediate --verify-candidate before acceptance.
The old C1 outcome and any source preflight cannot close these gates.

The smaller Chapter 2 mean path does not depend on XU06. The actual treap
history, frontier/weighted charging, join2 and C10-117 obligations stay open.
The whole book, all original inventories and every earlier finding remain
in scope. Checkpoint 0038 will preserve this draft and complete control history.
