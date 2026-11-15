# Overlapping request games (#440)

## Frozen independent contract

This contract was selected at repository revision
`3c064b11a5812e38c317601473e6897f65ce2a32`, before constructing the strategy
representation. It extends the completed #390 evidence without changing that
issue's original serial scope.

The client issues two Boolean requests, identified by left and right slots,
before waiting for either reply. A finite environment schedule may answer either
outstanding request first, answer only one, or answer neither. An answer must
refer to an outstanding request; an unmatched or duplicate answer is illegal.
Issuing a second request in an already pending slot is illegal. Distinct slots
may be pending simultaneously. Slots may be reused after a completed exchange
in the reusable interface, while the selected two-request client issues each
slot only once.

Observations retain the exact issued/request/reply sequence and the pending or
answered state of each slot. The client returns the conjunction of both Boolean
answers only once both are present; otherwise its result is pending. Equal
returned values do not identify different interaction sequences. Contexts are
finite prefixes, including an unanswered final request. No fairness or eventual
reply is assumed. There is no global alternation or global stack bracketing:
matching is local to each slot. A slot is correlation data, not a higher-order
justification pointer.

The independent native account will use request/response transitions and a
finite reply schedule. It must be committed and checked before the strategy
representation. The expected examples are:

| Schedule after issuing left and right | Result | Pending slots |
|---|---|---|
| No replies | pending | left and right |
| Right replies `true` | pending | left |
| Right `true`, then left `false` | `false` | none |
| Left `false`, then right `true` | `false` | none |
| Right replies twice | rejected | not a legal execution |

The two complete schedules have equal results but different observed order.
The old `FiniteStrategies.Phase` admits only one requested/waiting/answered
exchange globally: the second ask is rejected before the first round ends.
An encoding that serializes the requests changes the frozen observation.

## Primary-source boundary

Abramsky, Jagadeesan and Malacaria's
[*Full Abstraction for PCF*, arXiv:1311.6125v2, §2.4](https://arxiv.org/html/1311.6125v2#S2.SS4)
defines composition using matched component projections and hiding the shared
interface, with copycat as identity. These operations guide the bounded
construction. Its PCF, history-free and alternating-game theorems are not
imported into a nonalternating protocol.

Melliès and Mimram's
[*Asynchronous games: innocence without alternation*, arXiv:0706.1118v1](https://arxiv.org/pdf/0706.1118v1)
explicitly studies the additional issues arising without alternation. This
motivates stating our synchronization and strategy conditions separately. The
construction below is not claimed to instantiate their asynchronous tiles,
innocence conditions or category of general concurrent games. Every claimed
local composition law must be proved in Lean for the selected fragment.

## Implementation and acceptance

The independent contract above is frozen. Implementation and focused checks
are described below; integrated acceptance is recorded separately.

### Implemented fragment

The independent native definition is
`Applications/Interaction/OverlappingQueries.lean`. It was checked before the
strategy implementation was drafted. Its separate commit was made after that
draft; the earlier contract's intended pre-implementation commit ordering was
not followed literally. The frozen contract commit itself precedes both.

`OverlappingStrategies.lean` provides a finite-slot Boolean arena and an
endomorphism strategy family. A strategy selects a Boolean reply policy per
slot. Its positions are all global interleavings whose slot projections obey
the serial relay discipline. The full ordered list is retained: permutations
of independent events are not identified. There is no claim that these are
all strategies on a general game, or morphisms between arbitrary arena shapes.

`OverlappingArenaLaws.lean` supplies the independent arena boundary legality:
a question opens a slot, and an answer closes that slot. Both client and
service projections of every strategy play satisfy this law. Relative to the
forwarding strategy, client questions and service answers are Opponent moves;
service questions and client answers are Player moves. A slot alternates and
has one outstanding exchange. Different slots may progress independently;
global determinism, alternation, stack bracketing, and innocence are not
asserted. `Strategy.local_deterministic` proves the response within one slot
is determined. Prefix closure and the empty position are proved.

Interaction consists of globally ordered, slot-tagged A/B/C events with one
shared B event, not independently guessed component transcripts. Each slot
obeys the selected three-channel synchronization discipline. Component
projection and middle hiding preserve legality. Conversely, `hide_insert`
constructs a shared interaction for every composite external play and recovers
the original global list exactly. Thus `compose_exact` includes arbitrary
pending prefixes and arbitrary interleavings, not only completed examples.
Identity and associativity compare hidden external play languages; no equality
of differently parenthesized internal histories is asserted. The one-slot
`serial_recovery` theorem recovers #390's relay language.

`OverlappingCaller.lean` is a reusable two-request client for any policy in this
family. It issues both requests before consuming replies. `network_legal`
connects every accepted independent native schedule to an actual three-channel
interaction, and `network_hides` recovers its caller play. `service_recovery`
and `client_recovery` identify both exposed boundaries. `client_native`
compares the actual copycat client projection with the independent native
observation for **every** finite schedule, including malformed schedules.
`native_comparison` compares the service boundary for any policies. These are
distinct statements: a nonidentity policy can change the client's answer.
The checked negation example exhibits that difference.

`Examples/OverlappingStrategies.lean` is an ordinary importing caller. It
obtains network legality, a completed client result, and a pending result;
constructs consecutive questions on distinct slots; and rejects unmatched,
wrong-slot, duplicate, and illegally ordered strategy events. Erasing the slot
from the consecutive questions produces a position rejected by the old serial
model. The native examples separately distinguish equal results from unequal
interaction histories and reject a request reissued while pending.

### Statement review

| Claim group | Intended meaning and checked boundary |
|---|---|
| Native execution and examples | A rejected schedule is `none`; a valid but unanswered client is `some` with pending status/result. These cases are not conflated. |
| Projection/translation lemmas | Exact lists, preserving global order where hiding is reversed; no multiset or per-slot-only observational equality. |
| Strategy and arena legality | Per-slot finite prefix laws are derived from transition paths. No response liveness premise or conclusion. |
| Interaction components/hiding | Actual shared internal events give legal component and external projections. Interaction is the explicitly selected synchronized subfamily. |
| `compose_exact` | Both directions for every finite play of the selected policy family, with an explicit insertion witness. It does not assert a characterization of all general concurrent game strategies. |
| Identity/associativity | Equality of observable languages via logical equivalence, not strict equality of internal synchronization paths. |
| Serial recovery | One-slot tagged plays recover existing serial legality. Existing #390 modules are unchanged. |
| Caller/native comparison | Quantifies all finite schedules. Client result/history is proved from the client projection for copycat, service observation separately for arbitrary policies. |
| Negative controls | Native and strategy levels reject malformed correlation and order. Two simultaneous outstanding requests remain legal. |

### Adoption and remaining scope

Adopt this family for bounded independently outstanding Boolean requests when
exact reply order and pending status matter. Its setup cost is selecting slots,
per-slot response policies, and a boundary observation. Ordinary callers reuse
the checked interaction and observation lemmas. Recurring proof cost appears
when introducing a new move discipline or policy family: component projection,
hiding, its converse, and native comparison must be re-established. Merely
adding more slots does not require new composition proofs.

This does not replace the simpler serial model for serial clients. Higher-order
callbacks, arbitrary arena morphisms, dynamic allocation of correlation names,
unbounded concurrency, asynchronous innocence, fairness, and full abstraction
remain outside this bounded issue. They need their own independently selected
contracts; the enclosing orchestration owns any follow-up routing.

Focused builds of all new modules and the ordinary caller pass with the pinned
toolchain and default proof limits. Candidate-wide build/audit and independent
Standards/Spec reviews remain acceptance obligations owned by the enclosing
orchestration; this report does not claim them before execution.

All interface data here live in `Type` (universe zero). A finite arena has a
natural-number slot count; the selected client has two slots. Plays and
interaction witnesses are finite lists. Composition completeness constructs
its witness by a list translation, rather than extracting it from an opaque
existence axiom. Native execution and selected observations are computable;
no new axiom, choice-based executable recovery, or larger proof limit is used.
Published sources supply the organizing constructions; the transition and
list proofs listed above are new Lean results, reusing the checked #390 serial
path lemmas. No author-effort or productivity measurement was performed.
