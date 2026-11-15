# FDSA-XU03: immutable conditional-tail source draft

Recorded 2026-11-02. **Uncompiled and unaccepted.** No chapter is accepted
and Chapter 1 remains active. This is a draft handoff within the existing
book implementation loop, not either final review axis.

## Identity and scope

- Base: `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`.
- Candidate: `a0597381f02eddd074ee96cabaa974f2062285f8`.
- Worktree: `conaled-permutation-tail`.
- Branch: `work/fdsa-permutation-tail`.
- Commit: `feat(probability): formalize conditional remaining orders (#174)`.
- Six tracked files, 1,134 inserted lines; clean index and working tree after
  the commit. Only the unchanged dependency packages are shared with other
  worktrees; no compiler or project output writer was started here.
- Frozen requirements: `permutation-tail-requirements.md`, SHA-256
  `80323e579fe63419a10d7b26eb55f7ac540fea98a8a7c9c4efe36dce5f088b9c`.
- Starting state and coordinated API: `permutation-tail-start.md`.
  Checkpoint 0019 preserves the requirements, evidence and clean pre-code
  branch. Its receipt is in `../checkpoints.json`.

The predecessor chain includes the unvalidated Chapter 1 repair, minimum
law and whole-order law. No accepted dependency or successful inherited gate
is claimed. Changes needed when validating those drafts must be reconciled
explicitly before accepting this unit.

| Candidate file | Bytes | SHA-256 |
|---|---:|---|
| Applications/Probability/PermutationTail.lean | 23,402 | `1093b94886936b4cb859a371a863bfcf0b388db90a3bc063018329a399fe6f33` |
| Examples/PermutationTail.lean | 8,775 | `7470b1889baf878488eca8dad1240e1ca419a925b6f18f853a82eccd1178abfe` |
| Examples/PermutationTailBoundary.lean | 10,173 | `1bf7dd1e54ca551712b93a45b3c1db96bb6d95ad81a2297b34e29f288769fd73` |
| SquareApplications.lean | 8,392 | `7aedfca880167dc6a66e1b49b7ce1c5210c5f97ad090817061c5961c0b1aa321` |
| docs/research/fdsa-permutation-tail.md | 10,367 | `34162854a3bfabbec1e87bea6111b4939495cc27eb9ee811758dceaeb62dc96f` |
| docs/research/fdsa-reconstruction-map.md | 18,893 | `f519e995709de1e147439ebfc5a903a9e753883b49fd82f02d5bd484619acb9f` |

## Claims and proof connections

The core adds one ordinary optional-head event, defined before equality or
measurable assumptions. Its head/tail joint-event identity is unconditional.
The deterministic cons-support helper retains Nodup and the two needed
memberships without adding completeness. The actual projection's tail/erase
and filtered-tail bridges remain on the revealed-head event and need no
completeness. Actual outsider events are empty; conditioning any measure on
them gives zero.

The actual global head law sums XU02 whole-list fibers over the finite image
of cons a. Cons injectivity, the old supported-order cardinality and factorial
successor normalize that sum. The universal conditional tail formula uses
the exact joint-event equality, ordinary `cond_apply`, the old fiber law and
explicit finite/nonzero ENNReal cancellation. The singleton remainder is
covered by 0!=1, and unsupported lists retain mass zero. A singleton-extensional
map proof supplies the actual conditional tail distribution. The original
uniform conditional-environment identity follows from finite counting-measure
conditioning and also holds on null events.

A private `hasLaw_cond` helper unfolds ordinary conditioning and uses existing
AEMeasurable restriction/map/scalar compatibility and absolute continuity.
It does not require global measurability of the observation or a finite or
uniform environment. The canonical conditional tail law is obtained from
the actual global experiment; standard HasLaw composition transports it to
an arbitrary observed-law premise. A private canonical filter law uses XU02
map composition with the original complete positions. The public fixed-T
HasLaw and actual same-sample projection-map corollaries retain containment
T⊆S.erase a. No new probability carrier, executor, kernel or law record appears.

The main example assembles the initial HasLaw from XU02's actual map law.
For Fin 4, S={0,2,3}, it derives first-key-0 mass 1/3, supported tails [2,3]
and [3,2] of conditional mass 1/2 through different public connections, and
repeated-tail mass 0 through the off-support formula. It instantiates the conditional-uniform
identity and map law. Filtering the actual tail to {3} uses the generic
HasLaw, an on-event pointwise bridge and the actual projection-map theorem.

The second reveal uses the tail's HasLaw under the already changed
`afterFirst` measure. It obtains next-head-2 probability 1/2 and sole further
tail [3] with mass 1 under the actual nested conditional measure. Separately,
the first-key-0 event has mass 1 under afterFirst versus 1/3 originally, proving the full
environment measures differ. No partial tail is passed as a complete
enumeration, and no complete history theorem is claimed.

The boundary module checks the actual swap witness separating selected and
global first keys; a singleton through `cond_tail_eq`; empty/outsider zero
conditioning through both new helpers; and the empty-index none observation.
Its Fin 3 containment counterexample uses the same original T projection
under the conditioned sample. The new head theorem supplies event mass 1/2;
old whole-output fibers and finite supported-list identities give joint
masses 1/6 and 1/3; ordinary conditioning gives 1/3 and 2/3. It proves that T
excludes 0 but is not contained in S.erase 0.

## Source statement assessment

Root read the complete stable core and both example modules, the new source
document and map addition, and the bounded preflights. The core author also
checked its agreed public signatures against both clients. No mathematical,
scope, quantifier, orientation or new-interface mismatch was identified at
source level. In particular:

- Scalar global event statements expose only sample-space measurability;
  generic HasLaw/map statements separately expose List measurable singletons.
- Full support under a generic HasLaw is only a.e.; literal empty-event and
  on-event pointwise facts belong to the actual projection.
- Positive member conditioning is not extended to empty or outsider events.
- The selected head can differ from the global head. Fixed remaining-subset
  containment is preserved and has a concrete counterexample if weakened.
- The generic result assumes an unconditioned whole observed-order law,
  rather than the desired conditional conclusion or uniformity of the full
  environment. The second-step example exercises this distinction.
- Original complete positions are reused. List I is countable, not generally
  finite, and no output/index default element or index order is introduced.

Separate contributor report:
`../research/permutation-tail-draft-preflight.md`, 10,846 bytes, SHA-256
`8f5baa6f9403a579803a2efa6bb416ef31409535212bccba5e301b904580f368`.
It found no XU03-SP issue in the root-owned main/docs/map addition/import at
the matching hashes. It explicitly excludes the then-moving core/boundary
proofs; root's later reading and their authors' assessments cover those at
source level. It is not final independent Standards or Spec approval.

The source/API reports and saved exact finite calculation remain pinned in
the requirements. No expected value or source obligation was weakened to
make the draft fit. The chapter source limits in the requirements and docs
remain unchanged: actual quicksort/selection histories, program updates,
occurrence/value distinctions, fresh-choice coupling, costs, drift, tails,
joint independence, adaptive subsets and treap charging are not supplied.

## Validation boundary and next step

Nix-shell `git diff --cached --check` passed before the commit, and the staged
scope was exactly the six files listed above. A marker search in the three
new Lean files found no admission, axiom, unsafe/partial definition or listed
proof-checking bypass marker. That source search is not an axiom audit.

No Lean elaboration, focused build, full candidate gate, exhaustive audit,
final independent approval or immediate candidate verification has run for
this candidate. The normal compiler risks remain: finite-fiber rewrites,
Boolean membership simplification, map-composition and conditional transport,
implicit measurable instances and ENNReal arithmetic. Source inspection does
not resolve those risks. The old Chapter 1 gate remains unchanged and active;
no additional compiler may run concurrently under the current plan.

After the old gate completes, validate and accept repaired Chapter 1 first.
Reconcile this branch and its predecessors with their accepted bases, keeping
all scope and findings. Then run focused elaboration, applicable immutable
full guarded verification and exhaustive audit, both retained independent
review axes, and immediate `--verify-candidate` before acceptance. Preserve
new correction candidates and matching results rather than reusing a pass
from a different source tree. No acceptance box is closed by this handoff.


## Recovered first compiler findings — 4 November 2026

The original a0597381 six-path source scope and frozen requirements remain.
Minimal proof/API preparation6f76a4d entered its first actual compiler run at
centralc0440a99c2a503b7816a44367f7e4168378dbbf1. Two concrete core proof sites
failed: erased-set simplification expanded the target before hfilter applied,
and rw could not form a type-correct motive for support equivalence inside a
dependent ite. The exact partial log is retained separately from any later
terminal result in chapter02-focused-attempt5-partial-diagnostics-20261104/.
At observation, the aggregate command is still live; no terminal exit is inferred.

XU03-ELAB-001 and002 are recorded in
chapter02-xu03-elaboration-correction1-20261104/. Successor fa86bfb800c1e70cdf61fefd75b8cb2f428daea6 preserves
every declaration/expected case/domain/mass. It removes the actual head filter
with the pinned filter_cons_of_neg, then uses hfilter.symm; the support rewrite
uses simp only with the exact existing cons_mem_orders equivalence. Root read
both complete changed proofs and the full actual goals; no mathematical
statement changed and no linter was suppressed. The successor is uncompiled.
All focused/type, whole-scope independent, full-candidate/audit and immediate
verification gates remain, after the established predecessor acceptances.
