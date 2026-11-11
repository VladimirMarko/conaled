# FRP runtime: retain the contracts, test state boundaries earlier

Assessment date: 2026-11-11. This is a design investigation of source
`1ecdea2376786920a043009a35712a5dec93723a` and the preserved
[neutral candidate](packet.txt). It recommends experiments and scope revisions;
it does not implement them or change issue acceptance criteria.

Retain the compositional runtime ambition, existing denotations, compiler targets,
local simulation proofs and explicit resource/IO contracts. Revise the proposed
starting sequence: test an active-session state transfer and the boundary between
phase queries and committed execution early. Use the existing synchronous
machines as reference semantics and a small executable baseline. Decide the role
of a general demand scheduler through a matched client, rather than making it the
common foundation in advance. Startup selection remains a useful independent
client, but its success would not establish that boundary.

Here synchronous means a defined logical transition and commit order. It does not
mean periodic polling, discarding event occurrences, or requiring all future
runtime execution to be globally serialized. Independent demand progress may
justify early asynchronous execution. The experiment must preserve that
requirement rather than remove it to simplify a comparison.

## Independent assessments and reconciliation

All three perspectives completed:

| Perspective | Initial assessment | Main emphasis |
|---|---|---|
| Contracts and foundations | [Contracts](contracts.md) | Phase queries, delivered ticks and numerical endpoints have different observations; existing continuation transport already removes much generic proof work. |
| Implementation and use | [Implementation](implementation.md) | Test state transfer and effect ownership early; retention, callback retirement and measurement placement determine executable costs. |
| Alternatives and generality | [Alternatives](alternatives.md) | Compare a synchronous execution baseline and direct residual composition with demand scheduling; readiness should depend on the requested observation. |

The initial reports were saved independently before synthesis, with no peer
reports supplied. Their agreement is not a vote or a substitute for evidence.
All judges received the same selected brief and archive, so shared framing is a
possible source of agreement. They had fresh contexts, no supplied prior
involvement, no original checkout/history or live project discussions, and no
reported exposure to the withheld preference. Exact model builds and sampling
settings were unavailable; no model diversity is claimed.

The coordinator checked the decisive local declarations cited below and the
three primary papers used by the alternatives judge. A targeted numerical
clarification corrected ambiguous wording in IU-4; the
[separate supplement](implementation-supplement.md) preserves that correction
without rewriting the initial report. A second targeted question challenged the
alternatives judge's proposed sequencing; its
[supplement](alternatives-supplement.md) distinguishes a reference transition
order from global runtime serialization. Neither follow-up supplied peer reports
or the prior preference.

## What the evidence supports

**Continuation proofs are already available; executable migration is not.**
`Progress.Feedback.run_related` accepts arbitrary related starting states and
preserves ordered outputs and final-state relatedness. It does not require a new
session's original seeds. The existing `redundant` client represents a delayed
Boolean as the Boolean and its complement, with a local step relation and a
transported retained-state bound. This is a concrete first conversion pair.
An executable transfer, reachable-state validity, preparation failure and single
ownership at commit still need construction. Repeated transfers must compose
those obligations. See [Reactive.lean](../../../../../Applications/Progress/Reactive.lean)
and [IndefiniteService.lean](../../../../../Examples/IndefiniteService.lean).

B's function and circuit targets both realize state as `Val B s` through
[`ReactiveCompiler.realize`](../../../../../SquareKit/ReactiveCompiler.lean).
That experiment tests target interpretation and choice, but not heterogeneous
state conversion. CF-3, IU-1 and ALT-4 therefore support moving the first G
experiment forward. They do not show that startup selection is useless, that
conversion will be fast, or that a universal migration interface is needed.
Keep explicit migration usable without policy ranking.

**A phase query is not an accepted consumer tick.** `Event.switcher` selects a
behavior from changes strictly before a timestamp and evaluates it at that
global time. `Pipeline.responseMealy` instead advances once for every emitted
batch, including an empty batch, while silence leaves state unchanged. A pure
value can be shared between two requests at the same timestamp, but that does
not authorize coalescing two accepted consumer ticks. Likewise, evaluating a
dependency twice must not accidentally advance a delayed consumer twice.
Existing [pipeline examples](../../../../../Examples/ReactivePipeline.lean)
prove the empty-delivery/silence distinction; the RNF-to-execution bridge is the
new obligation identified by CF-1 and IU-2/IU-4.

Before choosing a common phase API, specify which actions query a value, attempt
a numerical step, commit an accepted transition and publish an output. These are
semantic distinctions to test, not a demand for four new generic interfaces.
A consumer with delayed state also needs a defined commit order: delivering each
request exactly once does not make arbitrary completion order equivalent.

**Phase retention needs an explicit query invariant.**
[`Frontier.windowValid`](../../../../../Applications/FRP/Frontier.lean) permits
packet timestamps in any list order within the certified window, while
[`Event.past`](../../../../../Applications/FRP/Spec.lean) orders timestamps
chronologically and preserves within-timestamp occurrences. A phase evaluator
cannot simply fold incoming packet order as chronological order. Nor can the
latest known phase answer every query admitted above an older lower bound.
The [retained lifecycle](../../../../../Applications/FRP/RetainedLifecycle.lean)
keeps cropped source history and advances its lower bound only by an explicit
command; its theorem does not justify replacing that history by a phase pointer.

CF-2 and IU-2 refine a choice the candidate already leaves open. Compare a cursor
with pending future changes against retained bounded activation history. Even
monotone queries can lag an advanced source frontier, so monotonicity alone does
not eliminate pending-change storage. Check an unsorted packet, a query exactly
at a known switch, equal-time changes and pruning at the retention boundary.
These are proposed separating cases, not newly checked Lean counterexamples.

**Numerical attempts and observations must not silently commit twice.**
[`Numerical.run_append`](../../../../../Applications/Orbifold/NumericalExecution.lean)
already proves chunked execution equals execution of the same concatenated tick
list. Its endpoint/error results do not supply arbitrary interior-time queries.
The [driver](../../../../../Applications/Orbifold/Driver/Execution.lean) retries
from an incoming packet and commits accepted intervals while preserving the
pending event suffix. Reusing that client exposes rejected attempts and carried
error that exact affine examples could avoid.

The numerical experiment should compare committed advancement with an
uninterrupted execution of the identical accepted tick list. Repeated reads and
failed trials must leave committed packet/time unchanged under a read-only query
contract; their diagnostic and resource records may change. If different
partitions are selected, use each result's approximation and clock contract,
not equality of numerical packets or error budgets. IU-4's initial phrase
“one unsplit command execution” is superseded by its supplement on this point.
CF-4 and ALT-2 independently distinguish endpoint correctness from a general
phase-query guarantee. A thin numerical bridge should therefore be exercised
before freezing the phase interface, even if affine phases are implemented first.

## Concerns that agreement must not hide

IU-3 identifies a boundedness issue that the other reports do not develop in the
same detail. A finite generation token can repeat while a cancelled worker's old
callback remains possible. Token equality alone then cannot identify the current
owner. One candidate mechanism is to quarantine the slot until callback retirement
is established. Count quarantined work and undelivered output in admission, and
state the environment assumption needed to retire them. This applies to adapters
with delayed callbacks; a pure synchronous transition has no such callback merely
because its state is stored in a finite slot. This is a paper adversarial schedule,
not a defect found in an implemented new scheduler.

ALT-3 identifies a separate progress question. The two-source merge correctly
waits for both frontiers because it observes both sources. An unrelated output
that depends only on the left source need not wait for the right. Generalizing
that merge into a graph-wide barrier could preserve soundness while losing the
independent progress that motivates asynchronous demand. Readiness should be
specified per requested observation and its dependencies. The candidate does not
currently require a global barrier; this is a design constraint for D, not a
finding that its code is wrong.

The alternatives supplement adds a necessary qualification: independent
publication requires separate output channels or a protocol permitting a ready
request's identified response to overtake an unresolved request. If the client
requires a single response stream in admission order, that order itself can
force publication to wait. Preserve occurrence order within each request, and
choose cross-request observation order explicitly before promising independent
progress. The synchronous baseline must not quietly weaken an admitted
multi-request workload to exclusive admission.

CF-5 and IU-5 support retaining the candidate's pending-publication and peer
contracts. The existing interaction-prefix results show that internal stages can
forget delivered history, and hidden histories can forget internal progress. See
[the inspected observer](../../../interaction-prefix-observation.md). This is
evidence against treating current machine state or last output as a sufficient
migration checkpoint. It does not require retaining all history forever: a bounded
summary needs its own sufficiency argument. Local flush, abstract commit and peer
acknowledgment remain different events. Between-ticks migration must keep the
pending-work successor explicit; it cannot close that scope by itself.

## Alternatives worth comparing

The alternatives report supplies three external comparisons. None is an adopted
implementation or a proof that it satisfies this project's contracts.

| Primary source | Useful comparison and limit |
|---|---|
| [Zélus, HSCC 2013, §§3.1–3.2](https://www.di.ens.fr/~pouzet/bib/hscc13.pdf) | Separate repeatable continuous evaluation from discrete state changes. Its clock/causality discipline is evidence for testing that boundary, not a numerical error certificate or a match to strict RNF switching. |
| [Naiad, SOSP 2013, §2.3](https://www.microsoft.com/en-us/research/wp-content/uploads/2013/11/naiad_sosp2013.pdf) | Track readiness using timestamped locations and possible predecessors. Compare dependency-specific progress; importing distributed progress machinery is not justified for a finite DAG without a demanding client. |
| [Elliott, Push-Pull FRP, 2009, §§7–12](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf) | Compare compositional residual sampling with an explicit demand graph. Its compatible-choice and cleanup conditions do not provide Lean ownership, bounded queues or certified integration automatically. |

A synchronous baseline, a direct compositional evaluator and a demand executor
can coexist. Which deserves a shared public interface remains open until the
same client exposes benefits and costs. The proposed D scope is discrete and
finite; no inspected declaration makes rational affine phase evaluation a
mathematical prerequisite. A-before-D can remain a chosen learning sequence, but
should not be recorded as a proved dependency.

## Proposed next steps and acceptance evidence

These are recommendations for the next scope decisions. They do not modify the
existing A–G specifications or authorize new implementation here.

1. **Freeze observations and commit boundaries for one composed client.** Specify
   pure phase queries, accepted delivery ticks, numerical trials and publication.
   Compare repeated same-time queries, empty deliveries, silence, reversed worker
   completion and a blocked sink. Preserve the existing pipeline's ordered
   outputs and final state. This contract should precede a common runtime API.
2. **Run two early, largely independent construction experiments.** First, an
   explicit between-ticks transfer using the delay/redundant pair after a nonempty
   prefix, with failure before commit and transfers in both directions. Reuse
   `run_related` for the universal suffix result. Second, rational phase evaluation
   with a selected query/retention invariant, checked against RNF at strict switch
   boundaries and under unsorted packets. Neither needs a general graph or native
   emitter; the migration trial need not wait for the new phase grammar.
3. **Exercise a numerical client before stabilizing the phase interface.** Use a
   nonzero incoming error, a rejected trial, repeated endpoint observation, a
   control switch and continued execution. Compare the accepted tick-list
   reference, approximation and clock results as specified above. Restrict
   observations to supported endpoints or construct the required interior-query
   result; an exact affine example alone cannot close this question.
4. **Compare demand execution on a discriminating workload.** Use a diamond with
   shared work, two owners, cancellation and a blocked sink, plus independent
   outputs with unequal source progress. Compare direct composition and bounded
   scheduling under the same observations, progress assumptions, live-storage
   accounting and caller tasks. If independent progress is already an essential
   client requirement, run this comparison early alongside the other experiments.
   Include callback quarantine only for adapters that actually permit late work.
5. **Extend the effect contract, not just the state converter.** First model one
   pending output and explicit sink acceptance for migration pause/deferral. Then
   select the pending-work/publication and recovery contract, including a lost
   acknowledgment. Check ownership across the transfer cut, stale callbacks,
   retries and resource retirement. Whole-umbrella closure is not a prerequisite;
   an unselected peer protocol blocks only guarantees that depend on it.

Startup choice and emitted artifacts can proceed as independent bounded clients.
Keep policy evidence validation off the tick path when selection is session-wide;
measure initialization, conversion, selection and observation overhead against a
fixed/direct caller. Do not require tuning for explicit migration or a performance
win for acceptance. A native artifact still needs its own execution/trust boundary.

No report establishes a performance winner, general scheduler necessity, automatic
migration or a finished hybrid runtime. All initial evidence is source inspection,
primary-paper reading and labeled paper cases; no judge ran a Lean build, proof
audit, executable experiment or benchmark. The coordinator likewise checked
statements rather than executing the proposed runtime tests. Independent
publication review verifies this record, not the correctness of a future runtime.
