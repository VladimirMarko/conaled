# Pending-address implementation and statement review

Local10020, root-owned. Bounded base361f5f3; original full integration baseea8.
Pending.lean and Examples/SuspensionPending.lean passed focused r3, terminal0,
all recorded source/config inputs unchanged. Core125s, connected client97s.
Raw evidence: validation/suspension-pending-r3.{json,log}. Earlier r1 and r2
failures remain unchanged in their own records; no acceptance is inferred.

Frame.memoizeAddress and pendingAddresses select actual memoize occurrences
without deduplicating them. pendingAddresses_mem_iff supplies a concrete frame
from address membership, with its environment and inner pattern. It needs no
decidable equality on primitive values or source purity.

pending_transition covers every control/frame branch of the unchanged actual
transition. A finished answer satisfies True because there is no residual
configuration. An unfinished next stack is either a sublist of the earlier
pending list, or prepends the address of the actual body event. Exceptional
unwinding is allowed to remove a frame without a successful write. This is
one-step provenance, not a claim that raw pending addresses are unique.

step_pending_nodup requires distinct initial pending occurrences and freshness
of the actual possible body-event address. Sublist preservation handles other
steps; a fresh cons handles body entry. The later finite source specialization
must derive the freshness premise from actual pure nonreentry, not assume it.

The connected firstForce client uses the actual body transition and public
conditional theorem to obtain a single pending occurrence. The reentry client
has an older same-address frame with a different caller pattern; its actual
next stack contains [0,0]. It consumes pending_transition while independently
checking the duplicate list and failed Nodup proposition. Thus the examples
preserve the unrestricted behavior rather than silently strengthening the raw
model to a pure-source invariant.

r1 exposed branch-equality/filterMap proof handling, not a statement defect.
r2 discharged the mathematical goals but failed six unused tactic/simp
linters. r3 removed those unused branches, added the public membership lemma,
and checked both module and client. No new axiom, admission, proof-limit
increase, linter suppression or machine transition change occurred. Full
candidate build/audit/review/final verification remain pending for10020.
