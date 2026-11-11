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

Pending. The independent contract above is frozen. The enclosing orchestration
owns independent Standards/Spec review and integrated build and proof audit.
