# Sequence client implementation handoff

## Scope and starting state

This is assigned implementation inside the existing integration/review loop.
The whole-task baseline remains `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`;
the preserved baseline receipt explicitly scopes `Examples/TextbookSequences.lean`.
The observed checkout before this edit was clean at
`f5441b0e52cceea6efe825f823925319731f4c69`.
Only `Examples/TextbookSequences.lean` is owned source; this handoff is outside
the source diff. No entrypoint, index, commit, dependency or setup was changed.

## Intended claim and existing public connections

The universal `append_materialize_correct` theorem connects any lawful PFDS
`AbstractStack` realization to the existing FDSA difference-list materializer.
Given both complete list observations and sufficient explicit left-length fuel,
the stack execution succeeds and its result is related to the entire materialized
list. Order, duplicate occurrences and the suffix are retained. The proof uses
`AbstractStack.appendRun_correct` and
`Examples.DifferenceListCosts.materialize_eq`; the latter already connects the
actual measured creation/application executor to `build_rep`, `build_cost` and
`build_appCost`.

The concrete custom-stack summary client uses that full relation first, then
`OrderedSummary.summary_append`. It quantifies over an arbitrary monoid and
measure: multiplication order matters and no commutativity or injective summary
is assumed. `append_head_materialize` reuses the existing relationally composed
`AbstractStack.appendHead_correct`, preserving its optional head observation.

No new general container interface or decoder is introduced. The generic theorem
retains the original relation and invariants. Only the already existing custom
stack decoder is used for the concrete executable summary observer. SharedList's
relation/heap/persistence APIs were inspected; this bounded client deliberately
uses AbstractStack rather than adding another adapter.

## Example-driven statement review

Before the edit, the missing item was a checked connection between existing
public results, not an unproved new append algorithm. No artificial failed proof
or changed expectation was manufactured.

The independently selected positive case is the full output
`[(3,true),(3,true),(5,false)]`: it distinguishes repeated occurrences and
left-before-right ordering. The connected diagnostic has length three and word
`[true,true,false]`. The new universal bridge supplies the full representation
proof and exact execution facts before the summary case is derived.

The public charges remain separate: `4*n+1` stack primitive invocations and
`4*n+2` difference-list creation/application events. Their unit definitions
differ; the statements assert no machine-time comparison, sharing, allocation,
or performance dominance.

The empty case uses payload type `Empty`, demonstrating no hidden inhabitance
assumption: zero fuel succeeds with `some 1`. The consequential boundary is a
nonempty custom stack with zero fuel: its optional summary is `none`, while the
difference-list materializer still returns `[true]`. This exposes why the fuel
premise cannot simply be dropped. Full-sequence preservation precedes possibly
lossy summary observation; no converse from equal summaries is claimed.

## Validation status

Focused sequence compilation passed on 2026-11-14 through the coordinator's
approved native wrapper: `lake build Examples.TextbookSequences`, exit zero,
5.478 seconds, 859 jobs. Exact commands, terminal native receipts and preserved
log hashes are in `intake/sequences/validation.json`; output is retained in
`intake/sequences/focused-build-02.log`.

The first combined sequence/sorting check is retained as a failure in
`focused-build-01.log`. It found two concrete sequence proof elaboration issues:
list-append normalization and unfolding the diagnostic abbreviation during the
public-theorem connection. Both were corrected without changing statements or
expected examples. The independent sorting error was reported to its author;
this agent changed no sorting source. Existing module-system migration warnings
were replayed from dependencies; the new sequence module compiled successfully.

Frozen sequence source identity: 6,486 bytes, SHA256
`10c90bcf2470823fff6485ecbf25602e503f0f7ec5a791e6f58569bd1ee8f71a`.
The compiler slot has been released and no compiler process remains active.

No exhaustive axiom audit, independent acceptance or whole-integration completion
is claimed. The coordinator owns public-entrypoint inclusion, stable candidate
capture, full validation and the existing independent review loop. This handoff
and the bounded logs belong in the next durable checkpoint.
