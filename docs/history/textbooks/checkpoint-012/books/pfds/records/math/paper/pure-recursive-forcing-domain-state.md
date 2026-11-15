# Pure runtime hereditary-domain preservation

Assigned slice within the existing #10019 implementation loop. Owner:
`chapter02_shared`; parent owns integration, commits, acceptance and checkpoints.

## Intended statement and connected expectations

The actual pure machine preserves the existing `Domain` code/value predicates
in every control and retained caller frame. `ControlAllowed`, `FrameAllowed`,
`ConfigAllowed`, `ResultAllowed` and `OutcomeAllowed` inspect the stored finite
data; they do not execute bodies or expand recursive group members. The
selected primitive parameter must independently satisfy the existing
`Domain.ParametersPreserve`. Compatibility with a heap primitive alone does
not discharge that condition.

Every diagnostic result is admitted. The claim is hereditary code preservation,
not source typing, success, absence of faults or termination. Empty matches,
unbound names and ill-typed applications remain in the domain. No new
address-identity, nonempty-match or type premise is introduced. Recursive
groups use the already specified permitted-shape and distinct-binder source
conditions, inherited through `Domain.CodeAllowed` and `Domain.GroupAllowed`.

Public step preservation follows the actual `Machine.step`; finite-result
preservation uses `Progress.Evaluates`; unfinished-prefix preservation uses
the already existing `Recurrence.Reaches`. No new execution relation or runner
is introduced. Per-control private proofs retain symbolic frame-list tails
without unfolding their recursive predicate.

The connected expectations are independently fixed by earlier checked runs:

- The recursive returned-closure program takes 51 pure transitions, enters the
  same suspension meaning twice, and returns integer 7. The new application
  derives result admissibility and admissibility of its actual 50-transition
  unfinished delivery prefix from the general preservation laws.
- Closure formation in the prior cyclic capture takes two transitions and
  returns the exact closure whose capture still looks up the recursive
  suspension. Its hereditary output is derived from the actual run and an
  independently established initial environment/code domain.
- Applying integer 3 as a function to integer 4 still produces the expected
  function fault after five transitions. The preservation theorem retains
  that diagnostic result rather than asserting type safety.
- Scalar successor 41 returns 42, and is-zero 0 returns true, each in six
  pure transitions. Both use the public scalar parameter preservation law.

## Statement review before first check

All stored expressions and patterns in control/frames are inspected, including
record continuations, both branch arms, remaining clauses, force-inner patterns
and row patterns. All stored values/captures are inspected, including original
handler packets, layered originals, record accumulation, row bindings and
primitive function tokens. Recursive descriptors enter through the existing
proved `GroupAllowed.members`/`bodyEnvironment_allowed` connection.

`ResultAllowed` constrains returned/raised values and matched environments;
mismatch and every fault are true. Primitive output preservation likewise
permits faults. Therefore the preservation statement is deliberately weaker
than a guarantee that forbidden-effect faults can never appear through a
parameter; this slice does not claim such a guarantee.

The finite evaluation is a hypothesis of `evaluates_preserves`, not a hidden
field in the domain. The connected cases establish that the hypotheses have
concrete inhabitants. The output-domain conclusions are obtained through the
new public preservation theorems, not through separate constructor proofs.

## Validation status

First focused run `suspension-pure-domain-state-r1` ended exit 1 with all 33
source/configuration hashes unchanged (21:17:06–21:18:04 UTC). The first
feedback was two reserved tactic-case labels and redundant case selection
after a successful `trivial` proof, corrected without changing statements or
expected examples. The eval/pattern proofs need their first elaboration after
those parser fixes; other control proofs and the public lifts produced no
reported errors in this pass. Exact log/record are in `session/validation`.
No acceptance claim; full #10019 remains parent-owned.

## Preparatory peer statement pass

The ordered worker read the predicate equations and connected cases without
editing them or claiming acceptance. It confirmed coverage of saved code,
captures, original handler/layered values, record accumulators, row fields and
force caller environments. It identified one concrete expectation error in
the new scalar clients: successful primitive application takes six steps,
because dispatch uses `proceed` to a value control and a separate step then
finishes. The five-step expectedFunction failure finishes at dispatch. The
scalar counts were corrected to six and the extra explicit transition added;
values 42/true and all prior 51/50/2/5 observations are unchanged. This
correction follows the source transition equations, not compiler convenience.

Second focused run `suspension-pure-domain-state-r2` ended exit 1 with the
same 33-file closure unchanged (21:19:00–21:19:39 UTC). All eval cases and
public lifts elaborated. Remaining feedback was deprecated simplifier names
(`if_true`/`if_false`) and one explicit list case split needed by the existing
record-pattern decision tree. The correction uses `ite_true`/`ite_false` and
splits only that concrete record field list; no statements or expectations
change. Core is not yet reported green; the connected client is still pending.

Third focused run `suspension-pure-domain-state-r3` established a green
`Applications.Suspensions.Pure.DomainState` core (30 s). All public statements
are unchanged and the core is now frozen for downstream WorldDomain/Ordinary
checks. The batch ended exit 1 solely in the captured-closure client: its
source-list membership needed an explicit binder name and direct singleton
membership. This example-only correction retains the same initial-code
justification and conclusion. All 33 inputs stayed unchanged through the run
(21:19:58–21:21:22 UTC). Other connected examples produced no reported errors.

## Final focused handoff

`suspension-pure-domain-state-r4` passed: exit 0, 758 Lake jobs, all 33
source/configuration hashes unchanged. It ran from 21:22:38.343287 to
21:23:55.117294 UTC on 2026-11-02, under the pinned offline Nix environment,
`LEAN_NUM_THREADS=1` and the shared focused lock. The connected example module
compiled in 64 seconds; the unchanged library core was replayed from its
successful r3 compilation. Exact r1–r4 logs and JSON records are retained in
`session/validation/suspension-pure-domain-state-r*.{log,json}`. The owned
source whitespace check also passed.

The public API is in `Suspensions.Pure.DomainState`:

- Structural predicates: `ControlAllowed`, `FrameAllowed`, `ConfigAllowed`,
  `ResultAllowed`, `OutcomeAllowed`.
- Initial configurations: `start_allowed`, `startPattern_allowed`.
- Actual execution: `step_preserves`, `evaluates_preserves`, `reaches_preserves`.

All original public statement shapes remained unchanged through proof fixes.
The connected returned-closure execution keeps its exact two body meanings,
51-step run and actual 50-step live prefix. The captured closure retains its
2-step formation and recursive-suspension lookup. The invalid function still
faults after 5 steps. The two successful primitive applications use the
source-verified 6-step count, as documented above. Each new output-domain
conclusion uses the general theorem with an independently established initial
domain and the actual finite run. The cached-closure client deliberately
discards the older direct output-admissibility proof and derives it from
`evaluates_preserves`.

The ordered worker subsequently reported a green downstream WorldDomain
check using the unchanged `start_allowed`/`evaluates_preserves` API to derive
admissibility of the exact cached pure witness's result. That is a connected
consumer of this slice, not an acceptance claim for all of #10019.

No type-safety, termination, absence-of-fault, no-reentry, cache-count or
whole-machine simulation theorem is claimed here. No proof budgets, source
semantics, entrypoints, dependency configuration or existing modules were
changed. Parent owns commits, complete-candidate gates, independent acceptance
reviews, checkpoint integration and the remaining #10019 bridge. Both owned
sources are frozen; no focused job remains active for this slice.

Final source SHA-256:

- `Applications/Suspensions/Pure/DomainState.lean`: `5e6d5294dd41029867b5f6590a98a08dce5a9801572cf81c46c19c9e160bb058`
- `Examples/SuspensionPureDomainState.lean`: `512aa48d4f42854a9e996206417847e1406d41fe8b2c248b3c1b0482aceb2ebd`
