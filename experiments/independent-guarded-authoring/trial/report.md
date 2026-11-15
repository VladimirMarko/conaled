# Independent guarded authoring attempt for #108

The independent author constructed the selected upstream `inv-inv` theorem in
the frozen guarded source theory, with a retained generated certificate and
the required ordinary-groupoid, C4 and reindexing applications. The finalized
caller passed its targeted Lean check, the full fresh build and exhaustive
proof audit, and exact-candidate receipt verification. The author outcome is
successful construction and validation within 27/40 cycles. Independent
evaluation and Standards/Spec review remain separate, after this archive.

The candidate was independently selected after the freeze, then locked before
proof construction. See [selection.md](selection.md), the original
[phase-1 manifest](phase1/MANIFEST.sha256), the retained solution-free
[scope check](inputs/scope-review.md), and the [prospective log](prospective-log.md).
The scope check qualified the corpus search: the selected upstream text is
present in retained public archives, but no prior guarded translation or
theorem-specific preparation was found. That public upstream proof was a
declared input. The fresh agent had no prior implementation/review involvement
in the framework, repair, or earlier trial. Exact model/configuration metadata
were unavailable and remain marked unknown in the launch record.

## Result and source correspondence

[work/Attempt.lean](work/Attempt.lean) contains the complete caller. It adapts
`foundation-core.identity-types.inv-inv` from agda-unimath revision
`75518656f287c203b41cb7f71df46e02b987a084`; the original source and MIT notice
are under `inputs/upstream/`. `involutionTyped` gives one generated term of
`Id (Id A x y) (reverse (reverse p)) p` for arbitrary typed context, family,
endpoints and path. A derived generated inverse supplies the two occurrences
of upstream `inv`. The construction adds no guarded rule or assumption and
changes no frozen framework file.

The generic semantic application accepts arbitrary groupoid families, including
nonconstant families. `certificate_evaluates` uses the frozen soundness
interface to identify the value of that same generated term; the ordinary
arrow equation is extracted from its selected section. C4 applications retain
all labels in faithful and ineffective models, check the nonzero sequence
1 to 3 to 1, and distinguish observed labels 1 and 0 in the ineffective case.
`involutionReindexed` retains the substituted original source certificate and
normalizes its endpoints, without claiming equality with a newly generated
higher witness. The [statement review](statement-review.md) records quantifiers,
assumptions, semantic correspondences and the connection of every claim group
to the checked applications.

## Effort and failures

The log records each substantive cycle under the immutable #106 definition.
Cycles 1–3 selected and froze the candidate; Phase 2 began at cycle 4. Checkpoints
at cycles 10 and 20 were retained and sent without requesting solution help.
Each runner check has a command, cwd where available, full output and a
pre-check snapshot. Completed checks retain exit status and timing; the
interrupted full run retains its incomplete metadata and a separate incident
record, without an invented exit code or termination time. Failed callers were
preserved, including
Lean's recovery-sorry diagnostics. No recovery placeholder is present in the
finalized caller.

The main friction was semantic elaboration: early endpoint-reduction attempts
hit the default heartbeat limit. Rewriting the selected J section before
reducing its reindexing resolved this within the existing limit. Other failures
were missing explicit context/model binders, a namespace collision for the C4
object, and normalization between categorical inverse and negative C4 labels.
All corrections were local to the caller. No framework repair, theorem switch,
coaching, budget extension or assisted proof retry occurred.

This attempt's theorem is smaller than the original associativity trial and
uses no nonempty dependent argument tail. Its result cannot demonstrate that
all earlier tail-authoring friction has disappeared or establish a causal
productivity improvement. It records one independent outcome at this frozen
boundary. No direct-Lean baseline comparison has been performed by the author;
the coordinator will arrange independent evaluation only after archival.

## Validation scope

Authoring used the frozen commit
`2f89f8651843797822efbb7da038311ab3d9f04d`, with all pre-existing tracked files
unchanged. The archive commit adds only this new experiment directory. All
author artifacts remain under it.
The isolated validation candidate is
`ec027e79f612ef1bf21c9968c91639dcfae0f554`, directly parented by that freeze.
It adds the byte-identical caller as `Examples/IndependentGuardedInvolution.lean`,
the source license notice, and one import to `SquareApplications.lean` so the
existing full fresh build and exhaustive audit cover the caller. This overlay
is validation infrastructure, not final production integration. The exact
mapping, hashes and public-import delta are in
[validation-record/overlay.json](validation-record/overlay.json) and
[validation-record/overlay.diff](validation-record/overlay.diff).

The finalized caller's SHA-256 is
`4dc308b0b8cf2e69b322796c264092e1025bfb2f9fdf21ddc6a33a7b3e66133a`.
Cycle 24's targeted command exited 0 at the normal resource limits. Cycle 25
materialized the pinned dependencies/cache for the overlay and exited 0.
Cycle 27's full fresh invocation exited 0: all 2257 modules checked and the
exhaustive audit passed. The transitive axiom union was exactly `propext`,
`Classical.choice`, and `Quot.sound`, with zero excluded kernel-unsafe runtime
declarations. The check took 5266.132 seconds by the runner interval. Its
separate exact-candidate verification exited 0 and performed no compilation.
The copied [receipt](validation-record/verification.json) fixes the candidate,
Lean 4.35.0 compiler and all manifest-pinned dependency revisions. Full output,
commands, timestamps and the unchanged source snapshots are retained under
[cycle 27](cycles/27/).

Final accounting is 27/40 cycles, with 13 unused. Both full fresh invocations
were consumed: the first interrupted, the second passed. The category totals
are dependency investigation 6, proof translation 1, helper writing 2,
debugging 10, application 3, and validation 5. The runner retained 26 checks:
15 passed, 10 failed and 1 interrupted. These counts include investigation and
infrastructure commands; they are not counts of mathematical obligations.
[effort.json](effort.json) maps every cycle to its category and every runner
check to its evidence. First-phase reads and administrative checks are
separately described in the prospective log.

The coordinator serialized heavy builds and owned the final unchanged
validation process. It supplied no proof advice and did not inspect unarchived
proof output. Hibernation, scheduling, process monitoring and report/manifest
preparation are distinguished from substantive author effort. This operational
change did not reset the cap or allow a third invocation.

The archive retains the caller, all failed source versions and diagnostics,
selected public inputs, locked protocol, statement review, accounting and
validation receipts. Its manifest fixes these bytes before external proof
feedback, repair, direct-Lean comparison or evaluation. Independent
Standards/Spec reviews belong to the enclosing workflow and have not yet
reviewed this caller.

## Full validation interruption

Cycle 26 launched full fresh invocation 1/2 on the exact overlay candidate.
The process disappeared after completed compilation step 202/2256. Its tool
session was unavailable and the original runner metadata has no exit/end
fields. No verification receipt existed at that interruption. The retained output establishes neither
a completed validation nor a source failure. The termination cause is unknown.
The original log/metadata/source remain intact; `cycles/26/interruption.json`
records the observations and hashes. This invocation was consumed, leaving the
trial at 26/40 cycles
and 1/2 full fresh invocations used at that point. The second invocation was
subsequently run under root-owned process control, passed, and was exact-verified
as recorded above. There was no third invocation or budget extension.

Raw compiler traces retain their original whitespace. The whole-archive
whitespace check reports those bytes; the authored-file check passes. The
exception and exact diagnostics are in `validation-record/archive-checks.json`.
