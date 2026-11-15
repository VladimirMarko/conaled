# Local 10021 implementation and review record

## Current scope and state

This is the retained implementation/review loop for the persistent logical
history and finite debit accounting foundation. The complete user request is
the published-book/thesis union, chapter by chapter, with necessary shared
foundations permitted. Requirements are `requirements/persistent-debit-foundation.md`
version 1, SHA256
`2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
The bounded and original integration bases are both
`3dd930c3e3989f3e5530463f3ac937a629551335`. No exclusions or pre-existing task
changes. Baseline identity is in `validation/persistent-accounting-baseline.json`.

The first recovery WIP commit is
`dc16a3b457b0393bb94188269fa3749deef39657`, preserved in uploaded checkpoint029.
It is not an acceptance candidate. Corrections and the complete measured
boundary connection are being developed in `persistent-accounting`, branch
`pfds/persistent-accounting`. Root owns all Git, compiler, capture and acceptance
actions. Authors work in assigned files with active input closures frozen.

No independent acceptance review has begun. Standards and Spec outcomes are
pending; the eventual coordinator must retain an independent pair and review
the entire fixed-base task scope, including all corrections. The required own
full build, exhaustive audit, matching candidate record and immediate final
verification are also pending. Focused evidence is development evidence only.

## Source scope and intended connections

The inspected source scope is thesis §§3.2.1, 3.3.2 and 3.4.1, printed pages
19–24, and book §§6.1–6.3.1, printed pages 57–63. Exact identities and inspected
source statements are retained in `research/union-source-identities.json`,
`research/persistent-trace-source-scope.md` and `research/persistent-trace-reuse.md`.
Do not copy manuscript text into the library or reports.

Logical histories reuse ordinary Mathlib quivers and finite paths, including
empty paths, cycles and parallel edges. Finite history closure is a separate
premise. Set-valued allocations and multiset discharge/realization labels have
separate freshness, allocation-origin and paid-realization predicates. Source
law III plus closure derives global support inclusion and the numerical bound;
the desired global inequality is not an assumption replacing that law.

Finite allocation unions and realized/unrealized partitions use only their
necessary premises. Injective debit renaming reuses ordinary embeddings, set
images and finite/multiset maps. Graph assumptions must not leak into purely
finite-set or multiset accounting helpers.

The measured adapter reuses `Resources.run` without changing Measured,
Workload or Potential. Its state is already realized support; each operation
charges unshared cost and newly encountered debit identities. The exact balance
retains initial and final support. The finite-node budget requires a Nodup exact
enumeration of the operation list, including its unshared charges.

Boundary payment credit has a separate witness and cardinality term. It is
not initially realized support. The complete source evaluator/work incidence
bridge remains task 10017 with its original Chapter 4/5 dependencies. Neither
this foundation, abstract accounting, one cache write per address, nor any
focused result closes a chapter or an algorithmic complexity contract.

## Author roles and retained expectations

The History author owns `Persistent/History.lean`, its connected client and
`research/persistent-history-implementation.md`. The Debits author owns
`Persistent/Debits.lean`, its connected client and
`research/persistent-debit-implementation.md`. Root owns Realization,
Observation, their clients, the actual source-boundary client, public imports,
documentation and `research/persistent-realization-implementation.md`.

The preserved cases cover unrestricted graph histories, parallel arguments,
one payment supporting two fork realizations, global coverage without local
legality, a source-valid cycle whose open scope omits payment, invented debits,
duplicate allocation and injective renaming. Measured examples retain shared
cost 3, pre-realized cost 2, fork cost 4, duplicate-list cost 5 with unchanged
finite scope, and open-cycle cost 1 with internal payment 0 and boundary 1.
Already realized cycle support gives cost 0; mere payment credit does not.
Actual source examples reuse the public repeated-force and handled-retry
observations, retaining two body attempts with zero cache writes in the latter.

## Development corrections before candidate freeze

History r1 compiled the core but failed client lint/normalization. The same
statements passed r2 with unchanged inputs; raw evidence and handoff retain
both rounds. Realization r1 needed the correct finite-set-map direction; the
core and source-boundary client passed in r2. Worked-client corrections retain
explicit public executor composition, natural-number cancellation and an
explicit singleton-map calculation. All failed rounds remain preserved.

Debits r1 exposed automatically included unused Quiver assumptions and shadowed
membership witnesses in map proofs. The correction scopes the graph instance
only to declarations that actually use history and distinguishes original and
mapped membership proofs. Core r2 compiled; its client is still being checked
at the time of this entry. No client expectation was weakened.

Bounded author assistance found that Observation's closed-scope bridge was
sound in scope but did not yet connect the existing boundary support theorem
to measured execution. Root added that connection and the open-cycle cases
before the first Observation compile, preserving the closed result. The
duplicate-list case also explicitly retains its original finite scope.
The operation-list documentation avoids claiming chronological correspondence
that is not in the formal hypotheses. This author assistance is not an
independent acceptance review.

No proof budgets, linter policy, axioms, admissions or acceptance gates were
relaxed. Exact final candidate identity, focused-input matching and both review
reports will be appended once the implementation is ready.

## Combined focused correction

First combined check at c6f96cf ended1 with67inputs unchanged. All four cores
and four clients passed; only PersistentObservation had alias/constructor
elaboration errors. Raw persistent-accounting-r1 JSON/log and the root report
retain the actual evidence. The same statements and independent expectations
are now explicit at eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8, and combined r2
is running. No independent review or formal acceptance is implied.

## Complete focused success and documentation-only candidate correction

The combined persistent-accounting-r2 ended1 at eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8,
with all67 recorded inputs unchanged. Explicit constructor names elaborated,
but simpa lists still did not unfold two private functions occurring as bare
higher-order arguments. Root added explicit `unfold realized` and
`unfold cycleRealized` before those two public-bound applications. The same
statements, law hypotheses, exact costs, finite scopes and independent expected
observations remained unchanged. Commit eb61c35f911ad0fac36758c878559eaf5f795cfa
contains this correction. The raw r2 JSON/log retain the actual failure.

The complete combined persistent-accounting-r3 then finished exit0 at eb61,
with875 Lake jobs and all67 queued/start/final formal and configuration inputs
identical. All four core modules and all five connected clients passed. The
Observation client compiled176s; the other completed modules were reused by
stock Lake. Its terminal record/log are validation/persistent-accounting-r3.*.
This includes the corrected Debits and Realization clients, whose earlier
successful combined-r1 compilations were99s and153s respectively.

Author statement review then found a documentation precision issue: the words
“prior payment” could suggest chronology not supplied by unrestricted graph
histories. The boundary law retains a real supporting discharge in logical
history, possibly outside the scope. The public document now states that
meaning and leaves temporal order to concrete evaluator correspondence10017.
This documentation-only correction is commit577be121e074ddb5de6727a7481c115cb61b3b27.
No formal or configuration input changed; all67 hashes match the clean isolated
candidate. Its complete base-to-tip scope is11files and5commits, with no
exclusions and fixed bounded/original base3dd930c3e3989f3e5530463f3ac937a629551335.

The immutable candidate is validation-persistent-accounting on
pfds/persistent-accounting-review-r3. Earlier r1/r2 refs and manifests remain.
The completed ordinary-output warm copied125 groups/875 files/89351399 bytes
to its earlier eb61 materialization, with stock output hashing and no approval
record. The doc-only switch preserves identical formal/configuration inputs;
this does not replace the candidate's own full guard/build/audit. Unrun future
helpers now name577be12 and still require successful exact3dd as predecessor.

Both independent review axes have yet to run. Full acceptance, exhaustive
audit, matching verification and immediate final verification remain pending.
The whole Chapter2 frontier and all parent10017 work remain unchanged.

## Independent review round1 opened

Opened 2026-11-03T02:12:38.744057+00:00 by coordinator
`/root/persistent_accounting_review`, within this retained10021 loop. Independent
axes are `/root/persistent_accounting_review/standards` and
`/root/persistent_accounting_review/spec`; neither is an implementation author.
Both received the entire577be12 dispatch, full requirements v1, all11files and
all5commits, relevant standards, author statement-review records, actual focused
evidence and explicit validation restrictions. Neither reads the other axis's
report before submitting its own.

Coordinator read-only checks confirmed clean isolated candidate
`577be121e074ddb5de6727a7481c115cb61b3b27`, nonempty11-file/5-commit scope and
merge base equal to the fixed bounded/original base
`3dd930c3e3989f3e5530463f3ac937a629551335`. No exclusions. Requirements file
SHA256 matches `2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
The candidate manifest records all67 focused formal/configuration inputs as
matching current577 after its doc-only correction. The underlying combined-r3
record ends0 at eb61 and declares development evidence only. The candidate's
`.lake/verification.json` is absent. No new compiler, check or cache operation
is authorized to the review team.

Standards: pending complete report, required-validation blocker retained.
Spec: pending complete report, required-validation blocker retained.
Report paths are `reviews/persistent-accounting-standards-r1.md` and
`reviews/persistent-accounting-spec-r1.md`. The coordinator will reconcile the
two reports without adding a third axis. No task or chapter acceptance advances.

## Independent review round1 reconciled

Reconciled 2026-11-03T02:16:48.245827+00:00 by `/root/persistent_accounting_review` after
receiving and reading both independent complete reports. Coordinator did not
perform a third Standards/Spec review. Candidate remains clean at
`577be121e074ddb5de6727a7481c115cb61b3b27`; fixed bounded/original base remains
`3dd930c3e3989f3e5530463f3ac937a629551335`; full11files/5commits/no exclusions.
Requirements version1 and SHA remain unchanged.

### Standards findings and outcome

Report `reviews/persistent-accounting-standards-r1.md`, SHA256
`6a64a766f3b763d8a5b8e418d323861910692380fc2e67d28b70b1566c0b0aa4`. Outcome **Blocked**;0 static code/architecture findings,
1 unresolved validation finding. **PERSIST-ACC-STD-VAL-001 — High — unresolved:**
missing own exact full build, exhaustive audit, matching verification and
immediate final verification, with applicable predecessor gates pending.
No source correction requested. Preserve the complete report and stable ID.

### Spec findings and outcome

Report `reviews/persistent-accounting-spec-r1.md`, SHA256
`bcb34d737f08eb987e9286b9d09bfa47a1ceb9a8d896a4de34fe0d8b465277b6`. Outcome **Blocked**;0 static mathematical/coverage findings,
1 unresolved validation finding. **PERSIST-ACC-SPEC-VAL-001 — Blocking — unresolved:**
missing the same required exact candidate/predecessor evidence under the saved
completion requirements. No source correction requested. Preserve the complete
report and stable ID separately from the Standards finding.

### Reconciliation and continuation

Both reviewers independently matched11 manifest files and67 focused-input
hashes, read all changed code/clients/docs and relevant unchanged dependencies,
and retained the doc-only difference after focused success at eb61. Spec also
read the complete bounded book/thesis extracted passages. The reports agree
on the need for validation while retaining their separate axes/severities.
Neither focused success, no static findings nor ordinary output transfer closes
either blocker. No10021,10017 or chapter acceptance advances.

Complete coordination report `reviews/persistent-accounting-coordinator-r1.md`,
SHA256 `77aa8e655a20eb29f9227bae5a9557c0553e59315eb6dca900d0bba485b519fd`. Root should supply successful own exact577 full
build/audit/record evidence after predecessor gates, then reuse this coordinator
and pair for evidence continuation. Any changed candidate requires both
full-scope continuations from the fixed base with these findings retained.
Root owns final immediate verification and acceptance of identical bytes.

## Common-candidate continuation 045 — pending

Root explicitly retargets scope10021 to `{'commit': '3cf3de4fbc24c1a144353ae64b13b72f5ead54a5', 'tree': 'd3dcf94916de5ccaf3df357e06192e69c4e0cf33', 'preserved_branch': 'pfds/signed-potential', 'planned_isolated_checkout': 'validation-pfds-integration', 'restored_main': '76d77a107deb37c30e0b061c30b03a3f8c6aa12c'}` from historical `577be121e074ddb5de6727a7481c115cb61b3b27`. Original full base `3dd930c3e3989f3e5530463f3ac937a629551335` remains fixed; the complete delivered range has 26 files/14 commits. Existing requirements, source ownership, findings and prior outcomes remain above. Full matrix and independent dispatch: `common-integration-scope-matrix-045.md`, `common-integration-dispatch-r1-045.md`. Both current independent axes, actual fresh full/audit, applicable regressions and immediate verification are pending. No acceptance or old-SHA approval is inferred.
