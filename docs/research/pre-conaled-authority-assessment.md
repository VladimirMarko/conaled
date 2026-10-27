# Assessment of the pre-Conaled authority spike

Assessed on 2026-10-27 for [#194](https://github.com/VladimirMarko/conaled/issues/194)
and [#196](https://github.com/VladimirMarko/conaled/issues/196). Source:
`VladimirMarko/t3swarmforge`, branch `spike/issue-16-proof-carrying-authority`,
clean local revision `1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9`. Links below pin
that revision. This assessment reads the source and its evidence records; it
does not rerun the old toolchain or establish fresh runtime test results.

The spike contains useful verified mechanisms and well-chosen negative cases.
It is stronger than a collection of certificates whose fields merely restate
desired outcomes. Its limits are also architectural: it certifies a particular
executable authority and selected transitions, not a reusable theory of recovery
or a refinement of every external execution. Preserve its lessons and examples;
do not import its domain records or storage choices as Conaled foundations.

## What the Lean development establishes

[`Authority.lean`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/Authority.lean#L351)
packages an accepted transition as `CertifiedTx`. Its fields connect the
abstract event, next domain state, exact encoded next blob, receipt, ledger and
new intents. `receiptMeaning` binds the complete receipt to the accepted event;
`intentsInitial` requires new intents to be pending, unattempted and without
premature evidence. `newExternalObligations` at line 169 derives obligations
from the domain-state difference, separately from the planner's proposed list.
Omitting both an event annotation and an inserted intent therefore does not
automatically remove the obligation being checked.

Some headline theorems, such as `claim_preservation` and `intent_completeness`,
project certificate fields. That is appropriate elimination of a certified
interface, but their names alone are not evidence that certificates can be
constructed. The executable `planCommand` at line 381 supplies that connection:
it computes a next state, checks decidable preservation, lineage and obligation
guards, and constructs the proof-bearing result on acceptance. This establishes
acceptance soundness relative to those definitions. It does not establish that
every legal abstract transition passes the guards.

[`Acquisition.lean`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/Acquisition.lean#L369)
goes further. `fresh_acquisition_accepted` proves that the actual planner returns
an accepted certificate for a valid state satisfying `FreshAcquisition`.
The hypotheses concern inputs: role eligibility, fresh identities, version
headroom and key reservations. They do not assume a valid next state or a
successful planner result. Preservation and obligation lemmas discharge those
guards. `fresh_acquisition_meaning` then connects the accepted result to ordered
membership, receipt meaning and initial merge intents. This is substantive
conditional admission completeness, with a narrower scope than the whole
authority.

The [acquisition fixtures](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/AcquisitionFixtures.lean#L35)
include kernel-checked witnesses for both receive modes. They also exhibit
invariant-valid imports where the abstract operation succeeds but a Claim
identity collision causes `invalidNext`, and an intent namespace collision
excluded by `FreshAcquisition`. Larger ordered-batch and escaped-key examples
are execution checks, explicitly distinguished from proof terms. This is a
good pattern for Conaled: prove usable premises and preserve counterexamples
to a tempting stronger completeness claim.

[`Recovery.lean`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/Recovery.lean#L65)
certifies enabled lease/observation transitions, preserving domain state and
obligation identities while updating the selected intent. At line 126,
`certified_ambiguous_never_settles` uses the certificate's actual next-state
relation; it does not stop at proving the helper assigns an `ambiguous` label.
The [certificate mutation runner](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/test/certificate-fixtures.mjs)
checks that receipt and initial-intent forgeries fail at the intended proof
field while other obligations continue to typecheck. These are useful
statement-review tests, alongside the positive constructors.

## What remains outside those proofs

The [design](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/design.md)
connects a certified plan to a fixed-operation SQLite host. The inspected
[`host.c`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/native/host.c)
uses a transaction, checks expected version and full base bytes, writes the
specified next blob, rebuilds projections and commits before acknowledgement.
The pure `exact_encoded_commit` theorem concerns `applyPlan`; it is not a
verification of that C implementation, SQLite, durable flushes or the native
compiler. Process-stop fixtures test selected boundaries. They are not sudden
power-loss or hostile-storage proofs. The spike's
[report](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/report.md)
states those limits rather than claiming their elimination.

Likewise, `noUnrecordedEffect` requires the plan's `authorizedAttempts` list to
be empty. It does not constrain arbitrary external callers to perform effects
only after a lease is committed. [`effects.ts`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/client/effects.ts)
requires that ordering from the driver. The internal driver interface trusts
supplied observations. Git ancestry checks and T3 reconciliation provide
concrete evidence mechanisms, but a string matching an obligation subject is
not itself a theorem that the external operation happened.

Two distinctions matter for our next experiment:

- `observe .absent` permits retry. An observation of absence needs a contract
  strong enough for the intended retry: absence now need not exclude an older
  delayed attempt taking effect later. Complete synchronized T3 snapshots
  address some observation gaps; they do not by themselves establish fencing
  of every in-flight old command.
- Matching a lease attempt rejects stale local observations. Preventing the old
  worker's external effect requires the destination or an exclusive gateway
  to enforce the generation, or a justified weaker idempotence/reconciliation
  contract. A local counter cannot supply that enforcement alone.

These are limitations of the stated guarantees, not newly demonstrated bugs in
the supported single-driver experiment. Its own earlier
[recovery-abstractions assessment](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/docs/research/lean-recovery-abstractions-source-assessment.md)
already identifies whole-history refinement, absence contracts, downstream
fencing and separate progress obligations. That agenda should be reused rather
than presented as a new discovery.

[`Audit.lean`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/Audit.lean)
lists 41 declarations whose axiom dependencies are checked against the three
documented Lean foundations. The check script also invokes `leanchecker` on
four modules. This is meaningful evidence for those roots and artifacts; the
selected-root policy is not Conaled's exhaustive local-declaration audit.
Any port must enter Conaled's existing audit unchanged. No fresh execution of
these old checks is claimed here.

## Architecture: keep the semantics, revisit the coupling

The spike's `abstractStep` is an executable domain reducer over concrete lists,
strings and bounded protocol conventions. Its representation-independent
boundary is therefore narrower than Conaled's intended mathematical
specification boundary. For example, `FreshAcquisition.headroom` reflects the
numeric storage/protocol bound, and its namespace conditions mention serialized
JSON keys because general codec injectivity is not proved. These are honest
implementation obligations. They should not become restrictions on the
mathematical meaning of acquiring work or recording an obligation.

The proof-authoring cost is visible in `acquisition_preserves`: it decomposes
the Boolean invariant and reconstructs its conjunction after list updates.
Supporting lemmas prove concrete list properties. This is not evidence that
Lean is unsuitable; it shows the cost of proving directly against this
representation. Conaled should compare an interface that derives such
representation obligations once with this existing approach, retaining the
same admission and counterexample cases. Replacing lists with abstract records
while asking every caller for the same proofs would not improve that cost.

The filesystem spool is a separate architectural question. The source
[ADR 0001](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/docs/adr/0001-preserve-swarmforge-actor-mailbox-architecture.md)
preserves persistent role actors and mailboxes; the spike does not authorize
replacing that runtime. [ADR 0002](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/docs/adr/0002-retry-partial-delivery-from-outbox.md)
keeps an incompletely delivered handoff retryable, preserves existing recipient
copies, and projects the board after all copies exist. [ADR 0004](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/docs/adr/0004-bound-native-lifecycle-compatibility.md)
explicitly retains the difference between that partial fan-out and the native
authority's atomic recipient insertion. Agreement after recovery does not
establish agreement at intermediate observations.

For #194, the useful shared question is which observations may hide that
difference. Neither filesystem layout nor SQL atomicity should be mandated for
every model. An interpretation may preserve acceptance and eventual completed
delivery while exposing different partial-progress diagnostics. It must state
that contract rather than silently equate the histories.

A durable mailbox plus a lossy wake separates work availability from notification
and can support recovery after missed notifications. The filesystem design is
not invalid merely because several files represent one lifecycle. It does need
explicit intermediate states and recovery rules for copies, Claims and board
projections. A local transaction reduces those atomicity obligations; it does
not remove the external Git/T3 effect-and-observation gap.

## Use in the next Conaled experiment

Add one durable-obligation scenario to the existing interface comparison,
without rebuilding the authority:

1. Specify acceptance, obligation identity, lease, external attempt,
   observation and recorded outcome as distinct events. Keep target-specific
   codecs, version bounds and persistence operations in interpretations.
2. Require a history interpretation to preserve accepted obligations and
   receipt meaning through interruption. Compare direct relations and an
   event/handler interface against those same requirements.
3. Retain the spike's receipt, initial-intent and lost-acknowledgement cases.
   Add a delayed old attempt after retry and an observation that hides partial
   fan-out as explicit counterexamples; these are proposed checks, not claims
   that the spike already implements those fixtures. Include an allowed
   successful history.
4. Separate admission soundness from conditional completeness, just as the
   acquisition slice does. Record which assumptions an interpreter proves,
   checks or trusts, and what the ordinary caller must still supply.

This complements our [checked observation contracts](external-interaction-contracts.md#checked-observation-contracts):
they currently show ambiguity and conditional safety in small models, while
the spike supplies a concrete acceptance/obligation/lease protocol and richer
regression cases. Neither alone supplies an end-to-end external-state theorem.
The combined examples can constrain a reusable interface before production
code or a universal effect framework is selected.
