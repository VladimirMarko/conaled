# Suspension foundation — independent review dispatch

This is preparation for the existing10014 loop in reviews/suspension-foundation.md.
No reviewer pair has yet been dispatched on this scope. A coordinator must use
the repository code-review workflow and its independent Standards/Spec axes,
retaining one record through corrections. Root remains the implementer and owns
all full compilation/candidate changes. No GitHub writes.

## Immutable candidate and complete scope

- Candidate: a3feaff319ad5fad912fb8bdc113f33fea4e2a60.
- Checkout: validation-suspensions-r3; branch pfds/suspensions-review-r3.
- Incorporated Chapter2/ticket-review base: 99a29dcd02eb529fbefbb675e244a8c47b78cdef.
- Original full integration base: 69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4.
- Both bases are ancestors. The newer-integration base rule is recorded in the
  coordinator; original requirements/findings/evidence remain preserved.
- Ticket diff: git diff 99a29dcd02eb529fbefbb675e244a8c47b78cdef...a3feaff319ad5fad912fb8bdc113f33fea4e2a60.
- Complete integration diff: git diff 69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4...a3feaff319ad5fad912fb8bdc113f33fea4e2a60.
- Task38files/8commits; integration42files/10commits; no exclusions.
- Exact file/commit/hash manifest: validation/suspension-candidate-r3.json.
- All formal development bytes equal original completedc8ea1f8; the only added
  differences are four direct FRP imports. The snapshot contains no10019 pure
  extension files. Neither predecessor approvals nor focus passes approve it.

## Requirements and primary sources

Read the complete saved requirements (not this dispatch as a substitute):
- REQUEST.md: b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499
- REQUEST-union-v2.md: 3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c
- suspension-foundation.md: 56828fa549b0f96b76db9c2451b82106ea12cf4c6e15bd7cd0fc5ecdf3a98f3e

The accepted user scope is the complete book/thesis union, chapter ordered with
explicit cross-cutting prerequisites.10014 supplies the suspension mechanism;
stream algorithms/exercises remain owned by Chapter4 and later algorithms.
Original thesis AppendixA pp131–135 extends the1990 Standard ML Definition;
the book cites1997. The inherited core fragment must remain explicit. Do not
silently upgrade the source rules or claim a complete SML elaborator/compiler.

Source identities/locators and inspected obligations are in
research/union-source-identities.json, suspension-foundation-inventory.md,
sml90-source-identity.json and suspension-base-core.md. Actual supplied book,
public thesis and official1990 Definition are available under research-pfds for
read-only source inspection; manuscripts are excluded from deliverables under
ADR0001. If primary material is absent after recovery, obtain the recorded exact
sources rather than infer source wording from reports.

## Implementation/source map and statement evidence

Read candidate docs/research/pfds-suspensions.md and every changed source/client,
plus relevant unchanged Progress, Resources, Durability, source primitives and
public entrypoint. Follow AGENTS.md and architecture/domain/language/ADR pointers.
Both reviewers use example-driven-development statement review. In particular,
verify quantifiers, state/result classes, initial invariants, named freshness and
capture premises, all count meanings, nonvacuity and actual connected applications.
Do not infer missing formal guarantees from prose.

The required families include grammar/static extension/hygienic lazy sugar;
finite mutable cells and names; actual source-specific control machine and
independent rule relation; normal/raised/mismatch/fault/unknown distinction;
write-before-match and retained effects; ordered reference patterns and four
source clause cases; Rec/SRec creation/footprint/closing; forcing/strict-lazy
observations; private-allocation/renaming/relocation transport; measured search
and relational observations through existing project interfaces.

Retained development reports: research/suspension-{store,rules,machine,static,
renaming,force-observation}.md, suspension-base-core.md,
suspension-progress-import.json, and the candidate's source map. Latest green
records include Static r8, Correspondence r3, Derived r8/r10, Invariant r3,
Recursive r3, Renaming r3, Relocation r6 core and ForceObservation r1/r2 for its
client and full chain. Preserve their exact input hashes: Recursive has only
documentation clarification after its focused pass; full candidate validation
must cover current comments/entrypoint. Earlier failed/interrupted runs remain
historical evidence, never substituted for a terminal pass.

## Explicit boundaries to assess

The original effectful model must still allow reentry, two successful cache
writes, an outer exception after an inner write, repeated uncached body exceptions,
and alias-versus-new-allocation distinctions. Extends is for fresh immutable
allocation, not thunk replacement or SRec. Do not add rollback, blackholing,
backward-DAG restrictions or unconditional at-most-once claims.

SUSP-STAT-001 is the same-expression static/runtime counterexample: under the
explicit1990+AppendixA core rules the cachedReference expression has Boolean
typing yet finitely returns integer0. Verify both sides on that identical public
term and their delimited assumptions; neither full SML unsoundness nor a universal
type-preservation theorem is claimed. Source rules must not be silently repaired.

Private-allocation finite observation comparison is delimited to its proved
normal/raised/domain contracts, with address/capture/freshness premises retained.
It does not claim arbitrary faults, unknown budgets, divergence, whole-memory
identity, equal event traces, or host timing equivalence. Independent returned
counts are actual model transitions. Pure self-forcing/nontermination and its
cache consequences are separately owned by10019; its focused-complete code is
outside this candidate and still requires its own acceptance. That separation
must not be mistaken for acceptance of wholeAppendixA/Chapter4.

Applications/Progress/Evaluation narrows Mathlib.Tactic to Mathlib.Tactic.Common;
all non-import bytes are unchanged. Review that exact helper record and affected
consumer validation. This is separate from10018's four FRP consumer repairs;
no statement/proof change or guard/budget relaxation is permitted by implication.

## Validation and outputs

This candidate's full exact gate, audit and verification record have not started.
Root will provide its own unchanged ./check.sh --candidate HEAD result and matching
.lake/verification.json, then immediate final verify before acceptance. Shared
ordinary outputs may be reused only through the stock integrity mechanism;
no candidate approval record is copied. Upstream prerequisite/Chapter2 acceptance
is separately required. Reviewers may perform read-only assessment while blocked,
but no Passed outcome without all exact mandatory evidence.

Expected first axis reports: suspension-foundation-standards-r1.md and
suspension-foundation-spec-r1.md. Report all findings with stable IDs, severity,
evidence and requirement/standard, with separate validation limitations. Retain
SUSP-STAT-001's counterexample status and all unresolved source-contract concerns;
resolve findings by evidence, not by moving the base or weakening the specification.
This dispatch and candidate preparation are not independent review or acceptance.
