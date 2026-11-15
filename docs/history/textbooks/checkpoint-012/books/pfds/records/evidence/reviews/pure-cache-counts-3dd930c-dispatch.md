# Finite pure cache-write counts — initial complete review dispatch

This begins independent review inside the existing local10020 implementation
loop. The complete development is captured, with all new formal modules and
connected examples focused-green. This is a static review while its exact own
full acceptance gate is pending. Both axes must remain Blocked until that gate,
exhaustive audit, matching record and immediate final verification are supplied.
No Chapter2 or later chapter frontier advances through this task.

## Immutable complete scope

Candidate `3dd930c3e3989f3e5530463f3ac937a629551335` is clean and frozen in
`/workspace/scratch/ca9a61d0bf30/validation-cache-counts`, branch
`pfds/cache-counts-review-r1`. Development checkout `cache-counts` is also clean
at the same commit. Bounded ticket base is
`361f5f3f6bb3de1974510ce355883dac2bf25333`; original full integration base is
`ea8afa12706d30cdc69ece1a172d5f21a3ea1809`. Each supplied base is its own merge
base with the candidate. The incorporated newer pure tip changes documentation
only; the recorded base adjustment follows the shared review-loop procedure.
No task findings were dropped and there are no exclusions.

Task diff:
`git diff 361f5f3f6bb3de1974510ce355883dac2bf25333...3dd930c3e3989f3e5530463f3ac937a629551335`
Full integration diff:
`git diff ea8afa12706d30cdc69ece1a172d5f21a3ea1809...3dd930c3e3989f3e5530463f3ac937a629551335`

The task has13files/3commits; the full integration has14files/4commits.
`validation/pure-cache-counts-candidate-r1.json` retains both complete file
sets, exact SHA256 values, commit lists, requirement hash and matching focused
input evidence. Review the complete scope, including documentation and inherited
integration differences, while inspecting unchanged dependencies as needed.

## Requirements and methodology

Read the full saved user requirements `requirements/REQUEST.md` and
`requirements/REQUEST-union-v2.md`, then `requirements/pure-cache-counts.md` v1.
The latter's SHA256 is
`fa5b5c01205aea18cc19aa53047cc7e0d57c0bb225534f0152bc04d7c87e569e`.
Follow candidate AGENTS, README build/audit/environment, architectural-quality,
domain/glossary, language-direction, applicable ADRs0001/0006/0010,
example-driven-development, code-review and its heuristics/shared review loop.
No external tracker writes: the user explicitly replaces GitHub tracking with
local tickets and authorizes recoverable checkpoint uploads.

Source locators are the book printed pp31–33 memoization discussion and thesis
AppendixA p135 reentrant overwrite remark. Exact identities and source inspection
are in `research/union-source-identities.json` and
`research/suspension-foundation-inventory.md`. Source PDFs and page images are
research assets in `research-pfds`; do not copy manuscript content into reports.
The scope is a cross-cutting semantic/resource consequence for later algorithms,
not chapter completion, a totality theorem or a host runtime complexity theorem.

Both axes use the required formal statement review: inspect quantifiers,
actual predicates, assumptions, conclusion, vacuity and connected cases.
Standards assesses methodology, public integration, reuse and architecture;
Spec assesses the intended mathematics and complete requirement coverage.
Review the actual theorem/client derivations, not only these summaries.

## Intended public claims and connected evidence

- Pending extracts actual memoize-frame addresses. Membership recovers a
  concrete frame; an unfinished raw transition retains a sublist or pushes the
  address of its actual body event. No raw uniqueness/purity is assumed.
- CacheWrite characterizes actual value/memoize writes. Settled means an existing
  value cell plus no same-address pending frame. Boundedness preserves settled
  status; an actual write from distinct pending addresses establishes it, and
  all later prefixes have no further writes there. Payload constancy is absent.
- CacheAccounting defines an additive charge equal to actual ordered trace
  event counting and to resource reweighting. FreshEntries is an actual
  observed-prefix provenance premise. Boundedness plus initially distinct
  pending addresses plus freshness implies at most one successful write per
  address for every observation budget. It also provides settled zero counts,
  monotonicity, finished suffix absorption and completed-zero propagation.
- Pure/CacheCounts derives FreshEntries from10019's actual finite nonreentry
  theorem. The source start discharges boundedness and initial distinctness;
  represented captures/world/state, pure code, compatible primitives,
  hereditary output preservation and a real finite Evaluates witness remain
  explicit. The universal count covers every address and budget, not arbitrary
  nonterminating runs. The list-count corollary is the same observation.
- TraceObservation proves the two existing instruments agree on the full answer
  and exact appended event list of an actual finite evaluation. It retains an
  arbitrary prior log, introduces no evaluator/count assumption, and has an
  empty-prior specialization.

Connected clients exercise the actual raw push/reentry, first successful force,
older-frame overwrite, mutable payload, outer exception retaining inner cache,
five-event trace, post-write hit and nonempty prior log. Source clients discharge
the general pure theorem's premises for repeated literal forcing, the existing
cached recursive returned closure, two fresh addresses with identical code,
a handled fixed exception retried, and an unforced delay. They retain exact
21/34/50-step source evaluations, public53-step closure execution, arbitrary-
budget zero writes where appropriate, and the unchanged unrestricted
observe300=2 counterexample. Its final proof reuses the original checked trace,
the new exact bridge, actual Prefix completion76, evaluation uniqueness and
absorption; it does not increase reduction limits or weaken the expectation.

Implementation statement reports, including independent expected calculations:
`research/suspension-pending.md`, `suspension-cache-write.md`,
`pure-cache-accounting.md`, `pure-cache-counts-source.md`, and
`suspension-trace-observation.md`. These are author/development evidence, not
independent acceptance outcomes. The separate10019 PREP-10019-02 boundary is
not retroactively removed from its frozen candidate or review.

## Exact validation evidence and limits

The candidate manifest verifies every recorded final input hash against the
captured candidate for successful focuses: Pendingr3, CacheWriter2,
CacheAccountingr3, TraceObservationr1 and PureCacheCountsr3. Their terminal JSON
and raw logs are in session/validation. All earlier failures are preserved:
Pendingr1/r2, CacheWriter1, CacheAccountingr1/r2 and PureCacheCountsr1/r2.
The latter two reached the default reduction-depth limit only in the negative
example; the final statement is unchanged. No axiom, admission, native shortcut,
proof-budget increase, linter suppression or source/build/audit weakening occurs.

Root alone owns full validation. The new candidate has no successful own
`./check.sh --candidate HEAD`, exhaustive audit, matching `.lake/verification.json`
or final verification yet. Its own full check follows the successful exact
pure361 dependency through prepared guarded ordinary-output reuse and a stock
candidate command. Copying ordinary artifacts copies no approval record and
cannot approve the target. Full901 is currently the only full check running.
Do not launch any compiler, gate, cache mutation or optional validation.

## Reports and continuation

Use the existing record `reviews/pure-cache-counts.md`. No prior independent
10020 findings exist. Give stable IDs prefixed COUNT-STD and COUNT-SPEC, with
separate required-validation findings and any code/spec findings. Write new
`reviews/pure-cache-counts-standards-r1.md` and
`reviews/pure-cache-counts-spec-r1.md`; preserve these through later corrections.
Each reviewer assesses its own axis independently, without consuming the other
axis's report. The coordinator reconciles reports and does not add a third
Standards/Spec review. Return complete findings, exact candidate/base, explicit
outcome and report hash, then remain available for this same loop's gate or
correction continuation. Root owns all fixes, Git/ref/index changes and final
acceptance. Only assigned review reports/record may be written.

## Exact full-integration file set

- Applications/Suspensions/CacheAccounting.lean
- Applications/Suspensions/CacheWrite.lean
- Applications/Suspensions/Pending.lean
- Applications/Suspensions/Pure/CacheCounts.lean
- Applications/Suspensions/TraceObservation.lean
- Examples/SuspensionCacheAccounting.lean
- Examples/SuspensionCacheWrite.lean
- Examples/SuspensionPending.lean
- Examples/SuspensionPureCacheCounts.lean
- Examples/SuspensionTraceObservation.lean
- SquareApplications.lean
- docs/research/pfds-cache-counts.md
- docs/research/pfds-pure-suspensions.md
- docs/research/pfds-suspensions.md

## Exact full-integration commit list

- 361f5f3f6bb3de1974510ce355883dac2bf25333
- 78ed1a1501a955a5579a7a098910a5d4bc1361be
- 0ebbf185d084b2cfe0b11501e8c7d4998932c16a
- 3dd930c3e3989f3e5530463f3ac937a629551335
