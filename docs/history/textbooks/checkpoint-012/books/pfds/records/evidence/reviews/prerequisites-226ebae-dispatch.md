# Frozen prerequisite review handoff — candidate 226ebae

Coordinator: `/root/prerequisite_review`. This handoff continues the existing
local #10013 loop as round 3 and links the new import-only #10018 round 1.
The two independent axes review the full candidate. The coordinator is neither
a third review axis nor an implementer. No GitHub writes or external messages.

## Immutable source and comparisons

- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Read-only isolated checkout:
  `/workspace/scratch/ca9a61d0bf30/validation-imports`.
- #10013 stable base and merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- #10018 base and merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Import-only diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full commit list: `ad73001` SharedList implementation; `70a1477` redundant
  adapter-tactic removal; `226ebae` direct FRP imports.
- Ten files, 951 additions and 2 deletions. The original eight #10013 files
  are unchanged from round 2. No exclusions. Both supplied bases are ancestors.
- Source paths: `Applications/Sequences/SharedList/{Basic,Copy,Suffixes,Observation}.lean`,
  `Applications/Resources/SharedList.lean`, `Examples/SharedList.lean`,
  `SquareApplications.lean`, `docs/research/pfds-shared-persistence.md`, and
  `Applications/FRP/{Spec,Equivalence}.lean`.

Read candidate content through `git show` or the frozen checkout. Do not
review the concurrently changing main `conaled` or Chapter 2 worktrees. Do not
compile or mutate the isolated candidate, its dependencies, or build outputs.
Read-only status/diff/source inspection is permitted. Root owns validation.

## Requirements and retained reports

Read all four saved requirements in `/workspace/scratch/ca9a61d0bf30/session/requirements`:
`REQUEST.md`, `REQUEST-union-v2.md`, `shared-persistence.md` v2, and
`import-footprint.md` v1. Their fingerprints are in the coordinator records.
The union clarification adds the complete book and thesis to the whole task;
both sources are now available. These bounded prerequisites still do not accept
a chapter. The #10013 requirements are unchanged.

Read `shared-persistence.md` and `import-footprint.md` in `session/reviews`,
plus all four `shared-persistence-{standards,spec}-r{1,2}.md` reports. Retain
their complete findings and outcomes. Earlier axes were static-clear but
Blocked; no approval is reusable. PERSIST-VAL-001 records the one unused-tactic
linter failure, fixed in `70a1477` with focused compiler evidence. Reassess that
disposition and keep it visible; do not allocate a new ID for the same finding.

Read `session/research/shared-persistence-statement-check.md` as background,
not an acceptance review, and the implementation note from the frozen candidate.
Read `session/research/import-footprint.md` for the resource/compilation history.
Prior analysis may focus the work, but each axis must cover the whole current
fixed-base scope and affected unchanged definitions, dependencies and uses.

## Applicable guidance

From the candidate, read `AGENTS.md`, `.agents/skills/code-review/SKILL.md`,
`docs/agents/review-loop.md`, `docs/agents/architectural-quality.md`,
`docs/agents/domain.md`, `GLOSSARY.md`, `docs/adr/README.md` and relevant ADRs
(including 0001, 0002 and 0010). Follow their applicable references, README's
development-environment/build-audit rules, and any scoped guidance found in
affected paths. Read `.agents/skills/example-driven-development/SKILL.md` and
apply its statement review to every formal family. Standards also applies
`.agents/skills/code-review/heuristics.md` as subordinate investigation prompts,
not pattern-match findings.

The existing statement-review handoff covers allocation/persistence, actual
path copying, partial operations and fuel, actual suffix-root chains with
closure/reachability/distinctness, modeled counts and connected relational-square
applications. Assess intended mathematics, justified/satisfiable assumptions,
conclusions, definition semantics, vacuity and case connections. The storage
counterexample and strengthened public graph results remain material evidence.
No runtime allocation or timing, garbage collection, branch-safe amortization,
crash persistence, or full-chapter claim follows from these count models.

For #10018, independently establish that all declarations, statement/proof
bodies, examples, public entrypoint and audit roots are preserved. Check the
direct providers and affected consumers. Do not infer semantic preservation
or full integration success solely from a source-only diff. No matched
performance benchmark has been supplied, so avoid unsupported resource claims.

## Exact-candidate validation

Root's full check is running in the frozen checkout. Live log:
`/workspace/scratch/ca9a61d0bf30/active-validation/import-footprint-226ebae-full.log`.
Execution record:
`/workspace/scratch/ca9a61d0bf30/session/validation/import-footprint-226ebae-full.json`.
The command uses the pinned offline Nix closure, disables evaluation cache, and
runs `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`. Full coverage is
all 957 integrated modules plus the exhaustive audit; no acceptance gate,
toolchain, dependency pin, guard or allowlist has changed.

Neither axis may pass until root supplies terminal full-check success, the
matching `validation-imports/.lake/verification.json`, and immediate
`./check.sh --verify-candidate HEAD` evidence. Observe whether inputs and
coverage match the exact candidate. Focused and previous interrupted builds
do not substitute for this gate. Do not launch another validation process.
If static review is complete while the gate is running, return **Blocked**
with zero code findings if appropriate and leave the report ready for evidence
continuation. Validation status must remain separate from code findings.

## Deliverables by independent axis

Standards reviewer owns only:
`session/reviews/shared-persistence-standards-r3.md` and
`session/reviews/import-footprint-standards-r1.md`.
Spec reviewer owns only:
`session/reviews/shared-persistence-spec-r3.md` and
`session/reviews/import-footprint-spec-r1.md`.

Each full-scope report records exact SHAs, requirements, reviewed scope,
complete findings with stable identifiers and concrete evidence/remedies,
prior-finding dispositions, validation status and explicit outcome. The short
#10018 report can link the complete full-scope report, while explicitly giving
the narrow base, import-only findings and outcome. Keep Standards and Spec
findings separate. Use `PERSIST-STD-*` / `PERSIST-SPEC-*` for new SharedList
findings and `IMPORT-STD-*` / `IMPORT-SPEC-*` for new import findings; preserve
PERSIST-VAL-001 as the existing validation finding.

Send actionable findings promptly to the coordinator. Do not fix source, edit
requirements, modify coordinator records, claim Chapter 2 acceptance, or
perform a separate enclosing implementation/review loop. Conclude with each
ticket's base, the common candidate, findings count/worst severity and axis
outcome. Both original static-clear outcomes and all later findings remain
visible until resolved with evidence.
