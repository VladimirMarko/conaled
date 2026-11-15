# Direct toolchain operational helpers — Standards review, round 1

## Outcome

**Findings-present.** There are **two unresolved Medium findings**, DTS-001
and DTS-002. The recorded public-interface tests passed on the reviewed
candidate, but the candidate must be corrected before this axis can pass.
There is no separate evidence-access blocker.

This is the independent Standards axis of the existing implementation loop,
performed by `/root/lean_native_path_options/standards_direct_toolchain_r1`.
It does not provide the Spec outcome or accept a formal candidate, proof,
chapter, or the book/thesis workstream.

## Immutable scope

- Base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `f010b5d0fdbef9c9f007c56531c326e738557f9d`.
- Merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Retained refs: `refs/pfds-review/direct-toolchain-base-041` and
  `refs/pfds-review/direct-toolchain-r1-041`.
- Isolated source checkout:
  `/workspace/scratch/b566cace4ed6/pfds/review-direct-toolchain-041`.
- Review diff:
  `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...f010b5d0fdbef9c9f007c56531c326e738557f9d`.
- Commit: `f010b5d chore(toolchain): restore exact Lean and Lake without Nix`.

The eight-file source scope is the five direct-toolchain environment helpers,
tests and README, plus the validation runner, its refusal tests and handoff
note. The scope manifest is
`session/validation/direct-toolchain-candidate-r1-041.json`. Formal candidate
sources, previous evidence, runtime distributions/caches, tracker/status and
review/provenance records are excluded. Their obligations remain in force.

The candidate checkout was clean when read. The coordinator separately
recomputed all eight candidate and delivered file hashes against the frozen
manifest and reported exact matches. The manifest's original pending-test
field predates the completed same-candidate validation aggregate; it is not
treated as a current failure or as evidence of a different candidate.

## Applicable standards and interpretation

I read candidate `AGENTS.md`, the development-environment and build/audit
sections of `README.md`, `.agents/skills/implement/SKILL.md`,
`.agents/skills/tdd/SKILL.md` and its test/mocking references,
`.agents/skills/code-review/SKILL.md` and heuristics, the skill-mechanics
reference, `docs/agents/review-loop.md`, `GLOSSARY.md`, and ADRs 0001 and 0010.
There is no applicable `CODING_STANDARDS.md` or `CONTRIBUTING.md` in this
candidate. The separate instructions under the toolkit-authoring experiment
do not govern these files.

The controlling user clarification is
`session/requirements/REQUEST-direct-toolchain-041.md`, with
`session/environment/direct-toolchain-implementation-scope-041.md` defining
this operational scope and public test boundaries. Original `REQUEST.md` and
`REQUEST-union-v2.md` retain local-only tracking, recovery checkpoints, exact
pins, formal verification and independent review obligations.

The Nix invocation requirement is explicitly overridden. No flake changes
are present, so a Nix-only tooling check is not imposed as an unrelated gate.
The public Lean/Lake/stock-check boundaries were already authorized; no new
user permission is required for their existing tests. No library abstraction
or formal project claim is added here, so this review does not create a
separate formal statement-review or integrated-proof acceptance task.

## Findings

### DTS-001 — Preserve the fresh-validation requirement in the recovery route

- **Severity:** Medium.
- **Status:** Unresolved on round 1.
- **Type:** Documented-standard violation, not a stylistic heuristic.
- **Candidate locations:**
  `session/validation/run-direct-validation.py`, especially
  `validate_stock_record` at line 147, `full_evidence` at line 162 and command
  construction at line 244; `session/validation/direct-validation-runner-notes.md`
  at lines 42 and 74; `session/environment/README-direct-toolchain.md` at
  line 90.
- **Applicable rule:** Candidate `README.md`'s build/audit section and
  `docs/adr/0010-composition-and-proof-audit.md` require a fresh project rebuild
  after build-tooling, toolchain or dependency-configuration changes. The
  user clarification waives Nix only. The shared review procedure also
  requires retaining all applicable validation requirements rather than
  silently narrowing the acceptance route.
- **Evidence:** The new `full` route always invokes
  `./check.sh --candidate HEAD`, and retained full evidence must contain
  exactly that command. The stock record validator accepts only
  `mode: incremental`. The runner exposes no fresh route. Its handoff then
  describes independent reviews and final verification as the remaining
  prerequisites after this full gate, without preserving the applicable
  fresh-build obligation. The new profile changes the execution setup and
  build-tooling path. On inquiry, the implementer confirmed that there is no
  saved exemption from the fresh rule and that no formal full run has begun.
- **Consequence:** Following the delivered runbook can complete its recorded
  full/verify sequence without the required cache-independent project build.
  A fresh stock success record produced separately cannot be retained by the
  existing validator, because that validator rejects its mode. Operational
  smoke-test success does not discharge this future formal-validation gate.
- **Required remedy:** Provide an explicit fresh full-check route and retain
  the actual command and stock record mode in its evidence. Make verification
  bind to the selected successful record and its actual mode; the stock
  `--verify-candidate` command itself must not receive `--fresh` or `--jobs`.
  Preserve lock discipline, exact candidate/input identity and genuine
  terminal results. Document that the first full check in this new runtime
  uses fresh mode with the established serial job limit. This correction
  does not require performing an unrelated formal build before the helpers
  receive their own artifact review.
- **Disposition history:** Raised during this independent Standards review.
  The coordinator asked the implementer for an existing requirement
  disposition rather than assuming an exemption. The implementer agreed to
  correct the route. A proposed fix is not approval of the current snapshot.

### DTS-002 — Recreate the smoke-test temporary parent after checkpoint recovery

- **Severity:** Medium.
- **Status:** Unresolved on round 1.
- **Type:** Validation/recovery fixture defect with a concrete failure path;
  not a formatting or refactoring preference.
- **Candidate locations:**
  `session/environment/test-direct-toolchain.py` at line 42 and
  `session/environment/test-direct-lake-build.py` at line 30.
- **Applicable rules and contract:** The implementation and shared review
  procedures require usable artifact-appropriate checks for the delivered
  result. The TDD references place tests at the public behavior boundary and
  require meaningful test setup. The saved recovery requirements and
  candidate README exclude reproducible temporary/build material from the
  durable authored payload. The parent confirmed that `session/tools` is an
  excluded temporary directory, rather than a directory guaranteed to exist
  after recovery.
- **Evidence:** Both tests pass `root / "session/tools"` as the parent to
  Python's temporary-directory creation, without creating that parent.
  `--workspace` explicitly supports a recovered workspace. The existing
  candidate tests ran in the current workspace, where previous investigation
  had already created this directory; their success therefore does not cover
  this cold-recovery precondition.
- **Consequence:** After a valid source/checkpoint restoration without the
  excluded temporary directory, both tests fail during fixture creation,
  before they reach the public Lean/Lake behavior they are intended to
  validate. This breaks the recovery verification path despite correctly
  restored toolchain files.
- **Required remedy:** Have each test create its workspace-local temporary
  parent with parents as needed before creating the temporary project, or
  choose an already guaranteed workspace-local parent. Keep all fixture
  writes in the selected workspace and preserve cleanup/report behavior.
  Establish the corrected public test behavior in the absent-parent case;
  no private-function or fabricated compiler test is needed.
- **Disposition history:** The implementer identified the excluded-directory
  condition during review. I independently inspected both immutable test
  implementations and confirmed the missing setup and resulting failure
  path. The implementer intends to fix it; it remains unresolved on this
  candidate.

## Validation evidence and its limits

The following matching evidence was read; no compiler, build, cache operation
or existing test was rerun by this reviewer:

| Evidence | Established result | Limit |
|---|---|---|
| `session/validation/direct-toolchain-candidate-validation-r1-041.json` | All three artifact check commands returned zero on the isolated candidate; delivered sources match and the snapshot is clean. | Covers the recorded commands and prepared workspace. |
| `session/validation/direct-toolchain-candidate-cli-r1-041.json` | Exact genuine Lean 4.35.0 and Lake 5.0.0-src+eb6cafb outputs; a theorem accepted without axioms; an invalid theorem rejected with a type mismatch. | A compiler-path test, not exhaustive project proof acceptance. |
| `session/validation/direct-toolchain-candidate-lake-r1-041.json` | Lake invoked the profile compiler, compiled and linked a native executable, and that executable printed `42`. | Tiny executable integration, not the full project gate. |
| Candidate refusal tests and aggregate output | Existing evidence is not overwritten; an interrupted full record is rejected; an occupied full lock excludes a second full job. | Successful full/focused recording and final formal verification have not run. |
| CLI/Lake red and green records under `session/environment` | The native failures and the subsequent real interface successes are retained. | Historical results support the TDD sequence; isolated-candidate results are the current source-matched evidence. |
| `session/validation/direct-cache-bootstrap-041.json` and `direct-cache-get-041.json` | Actual pinned cache bootstrap and retrieval both completed with exit zero. | Dependency preparation, not formal acceptance. |
| `session/environment/direct-dependencies-after-cache-041.json` | All nine dependency revisions and clean statuses match the unchanged manifest after cache retrieval. | Source identity, not an external-cache authenticity certificate. |

The refusal tests exercise the public CLI without replacing Lean/Lake or
synthesizing passing formal evidence. The theorem and native-output tests use
independent expected results. The records keep interrupted history separate,
and the runner always states `acceptance: false`. Before/after input hashing
is correctly described as supplementary bookkeeping rather than immutable
isolation or a protection against hostile artifact substitution.

The profile preserves original release executables, the launcher forwards
arguments through a quoted shell command, the environment is scoped to child
execution, and formal sources/guards/pins are absent from the source diff.
I found no additional documented-standard violation or concrete heuristic
finding in the remaining reviewed scope.

No missing full proof audit is counted as a separate blocker for this
operational-only artifact review. Full/focused formal work and immediate
candidate verification remain future gates, including the fresh requirement
identified in DTS-001. The exact candidate must receive both independent
axes after correction; this report does not approve a later modified tip.

## Final record

- **Standards outcome:** Findings-present.
- **Unresolved findings:** 2.
- **Worst severity:** Medium.
- **Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `f010b5d0fdbef9c9f007c56531c326e738557f9d`.
- **Review actions:** Read-only candidate/evidence inspection and this report;
  no implementation edits, build/test repetition, Library access, remote
  mutation or acceptance assertion.
