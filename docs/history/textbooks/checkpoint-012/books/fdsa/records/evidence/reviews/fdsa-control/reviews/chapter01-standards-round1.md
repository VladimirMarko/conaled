# Chapter 1 Standards review — round 1

Reviewer: independent Standards subagent.

Base and merge base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Candidate: `1aabd512284fe86254278ac631eda061d311050b`.
Diff: `git diff BASE...CANDIDATE`, all nine changed files.
Commit: `1aabd51 feat(resources): formalize FDSA basics (#174)`.

Scope: FDSA-001, Chapter 1 Basics, under the full retained user request.
Source inspected in the immutable isolated checkout `conaled-ch01-review`.
The unrelated original untracked historical ZIP is excluded; no task source is
excluded. Candidate HEAD and clean working tree were independently confirmed.

## Outcome

**Blocked on required validation evidence; semantic Standards review complete.**

Concrete Standards findings: **0**. Worst code/documentation issue: **none**.
This report is not approval until the matching whole-candidate build and axiom
audit complete and the validation evidence is reconciled. The required final
candidate-record verification remains an acceptance step for the coordinator.

## Standards applied

Read the candidate's `AGENTS.md`, `README.md` environment/build/audit sections,
`docs/agents/architectural-quality.md`, domain guidance and glossary, ADR index,
ADRs 0001 and 0010, `docs/language-direction.md`, the example-driven-development
skill and worked example, and code-review heuristics. User authorization for
local tickets and Library checkpoints takes precedence over the repository's
GitHub tracker convention. No publication or whole-book completion is implied.

The retained request, FDSA-001 ticket, implementation handoff and source/statement
map supply the intended claims and case-selection evidence. No originator
review was requested as an additional gate.

## Architecture and statement assessment

1. **Existing constructions are reused.** `ListReversal.appendRun` uses the
   existing recursive `TreeFlattening.appendWithCost` and explicitly adds the
   final empty-call charge. `appendRun_cons` establishes the resulting source
   recurrence. `accumulator_exact` reuses `SymmetricCosts.reverseRun_value` and
   `reverseRun_work`; the implementation is not copied. Standard Lean/Mathlib
   lists, multisets, sets, arithmetic, updates and gcd are retained.

2. **Operations, values and costs remain separate.** `naiveRun_value` is a list
   equality with full order and multiplicity. The doubled/exact/bounded cost
   results are separate proofs over the modeled observation. The source map and
   module documentation do not infer actual Lean runtime or allocation behavior
   from extensional equality with `List.reverse`. The optional realizations do
   not strengthen capabilities of unrelated targets.

3. **The new laws use appropriate assumptions.** Control/application rules need
   only `Add`; primitive erasure uses the existing `AddZeroClass` convention.
   No commutativity is imposed on generic observation composition. The natural
   tick is explicitly a call-count convention. The source's E/T metalanguage
   is not misrepresented as a verified translator.

4. **The universe adjustment is supported by a concrete client.** In
   `Measured.lean`, `erasureSquare` now permits values in `Type (max u v)` with
   observations in `Type v`. Equal-universe specializations remain available;
   fields `impl`, `spec` and `commutes` are unchanged. New arbitrary-universe
   list squares and their composition exercise the motivating use. Existing
   caller shapes were inspected in `Resources.FoldCompiler.erasure`,
   `Resources.BinaryCounter.advanceSquare`,
   `Resources.DijkstraCosts.executionSquare` and `Examples.Resources.rowSquare`.
   Their source interfaces require no changes. The full candidate build still
   must establish compatibility of their elaboration and downstream clients.

5. **Nonvacuity and boundaries are explicit.** Euclid induction retains the
   nonzero branch condition and decreases the second natural argument.
   `gcd_common_divisor` uses it for a substantive universally quantified claim
   with a concrete satisfiable specialization. List proofs range over every
   finite list and arbitrary payload type, while strict cost improvement alone
   requires nonemptiness. Natural subtraction transport retains `n ≤ m`;
   update-away retains key inequality. The exact cost formula follows from a
   doubled identity, avoiding an unproved rounding assumption.

6. **Composition uses matching represented boundaries.** The continuation
   square consumes a measured list and uses `Resources.bind`, so pasting it
   with `naiveSquare` preserves the earlier observation. `composed_square`
   exercises square composition, `composed_run` retains the direct native
   interface, and `composed_costs` checks the independently expected total 14.
   No transport across mathematical settings is claimed by these Type-level
   specializations.

7. **Examples are connected and retained.** Empty, singleton, duplicate-bearing,
   ordered and nonempty-accumulator cases use public result/cost theorems. Cost
   rules have cases that distinguish selected from expensive unselected arms.
   The implementation record retains the initial missing connection and the
   universe/boundary mismatches found during development, without counting
   import/syntax errors as mathematical red-phase evidence. No quota per
   helper theorem is imposed; existing cases cover related declarations.

8. **Layout, provenance and public coverage are coherent.** Domain definitions
   are in `Applications`, checked uses in `Examples`, and the book sequence is
   a documentation index rather than a duplicate software taxonomy. All new
   Lean modules are imported through the two additions to the public entrypoint.
   Source date, URL, SHA-256 and source-revision provenance are recorded; full
   manuscript downloads are excluded from the source deliverable. Conventional
   commit syntax is preserved, and scope is explicitly a local chapter ticket.

## Validation evidence and remaining gate

- Independently observed candidate HEAD and clean Git status match the supplied
  snapshot. The three-dot diff is nonempty, with the stated base as merge base.
- `git diff --check BASE...CANDIDATE` passed.
- The handoff records successful focused pinned-shell builds for the exact
  committed content; those are supporting evidence, not integrated acceptance.
- The parent is running `./check.sh --fresh --jobs 4 --candidate HEAD` in the
  isolated candidate. During this review, the log showed progress through
  module 81 of 956 without a reported failure; it was still incomplete.
- Whole-project success, exhaustive audit completion and the matching
  `.lake/verification.json` have not yet been supplied to this reviewer.
- The README audit-regression applicability question is **resolved: that fixture
  suite is not an additional required gate for this purely formal/provenance
  candidate with unchanged validation tooling**. The exact rationale and limits
  are recorded below. Its result is not claimed, and this resolution does not
  replace the required exhaustive candidate audit.
- No duplicate full build or optional broad regression suite was launched by
  this reviewer. Existing Lean module-import migration warnings are not treated
  as proof failures, and no warning policy was disabled.

## Stable finding record

No concrete Standards finding IDs were issued in round 1. The pending validation
gate must be reconciled before upgrading this outcome to Passed. A changed
candidate requires a new review round against the same base, retaining this
analysis and any matching evidence.

## Audit-regression applicability disposition

This disposition was requested after the initial report. Candidate and formal
scope are unchanged. The original requirement bytes are preserved in
`chapter01-requirements.md`, SHA-256
`7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba`.

**Ruling:** the applicable mechanical acceptance gate is the isolated candidate
source-policy/coverage check, full build and exhaustive proof audit, followed by
`--verify-candidate HEAD`. The unchanged validator's four negative/positive
regression fixtures do not require a second normal full build for this change.

This is a scope determination from the instructions together, not a waiver for
convenience:

1. `AGENTS.md:31–32` explicitly directs artifact-matched validation and routes
   formal changes to the build/audit acceptance modes in README.
2. `README.md:157` identifies `./check.sh` as the routine acceptance command;
   its committed-candidate sequence at lines 170–194 names `--candidate HEAD`
   and `--verify-candidate HEAD`. It explicitly says that exhaustive auditing
   runs on every invocation. It does not attach that frequency to the
   separately described validator regression suites.
3. `docs/agents/review-loop.md:75–84` defines the integrated Lean verification
   step using the candidate command, adding fresh mode when applicable, and
   preserving/confirming the resulting verification record. ADR 0010's
   acceptance discussion likewise identifies the full build and exhaustive
   audit as the routine formal gate.
4. The sentence at `README.md:255` gives the post-build invocation and purpose
   of `test-proof-audit.py`. In this context, "After lake build" specifies the
   execution prerequisite/order for that fixture suite; it is not an instruction
   to rerun all validator fixtures after every focused Lean build. The script
   itself documents that prerequisite and requires normal project artifacts.
   It tests the auditor against an unused foreign axiom, a private forbidden
   dependency, a private admission, and unsafe source. None of the code that
   implements those acceptance decisions changes in this candidate.
5. The candidate's own `.github/workflows/fresh-verification.yml` confirms that
   fresh candidate verification is a supported acceptance route without this
   particular post-normal-build fixture suite: it runs the fresh candidate
   command, two separate infrastructure regressions, and final record
   verification, but does not run `test-proof-audit.py` or perform a second
   normal full build. This corroborates the acceptance-mode distinction; the
   scheduled workflow's additional tests are not imported as per-change gates.

The candidate changes Lean definitions/theorems, public imports for those modules,
and source provenance. It does not change the compiler/dependency pins, build
wrapper, source-policy scanner, proof-audit implementation, module-root selection
policy, fixture code, or output-integrity guard. Its added declarations and
public imports are directly covered by the required source closure and exhaustive
audit. If any of those validator inputs changed, an integrity incident cast doubt
on them, or an explicit task required the regression suite, its corresponding
checks would become applicable and this disposition could not be reused.

The semantic Standards finding count remains zero. **Full candidate validation
is still pending; the overall Standards outcome remains Blocked.**

## Routine candidate-mode applicability disposition

Narrow follow-up requested by the implementation coordinator. Candidate remains
`1aabd512284fe86254278ac631eda061d311050b`; its isolated checkout was independently
confirmed clean with that HEAD. The fixed base and saved original requirements
are unchanged. This is not a new semantic review or an acceptance decision.

**Ruling:** the routine guarded incremental command is applicable to this
mathematics/provenance-only candidate:

```sh
nix develop --command env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD
nix develop --command ./check.sh --verify-candidate HEAD
```

`README.md:170–184` expressly defines committed-candidate acceptance using the
routine candidate command and adds fresh mode when fresh validation is needed.
Its fresh-mode paragraph at lines 204–214 names build-tooling, toolchain,
dependency-configuration changes and suspected stale outputs as triggers;
periodic fresh verification is described separately. ADR 0010 explicitly
supersedes fresh-on-every-acceptance and says ordinary Lake invalidation is
sufficient for routine acceptance. AGENTS directs the applicable artifact-matched
gate, and the frozen FDSA-001 acceptance checklist requires applicable project
verification without selecting fresh mode.

This candidate does not change those tooling or pin inputs. The reported reason
for changing modes is severe memory reclamation during voluntary fresh attempts,
not evidence of stale or inconsistent project artifacts. Under that evidence,
the earlier choice to attempt fresh validation does not add a permanent fresh
requirement to the task. Routine mode still must pass the complete source-policy,
public-coverage, candidate/dependency identity, compiler-version, before/after
output-integrity, integrated-build and exhaustive-axiom checks; it is not a
focused-build substitute.

The pinned-runtime evidence in `../provenance/lake-concurrency.md` identifies
`LEAN_NUM_THREADS` as a scheduler control, not a mechanism that skips checking.
Using it does not change the repository's proof or source policy. Preserve the
actual command and scheduler setting in validation evidence. The routine command
must not use fresh-only `--jobs` or `LEAN` overrides. No project output should be
copied behind Lake's tracking to implement the mode change.

Both interrupted or superseded fresh attempts remain **non-passing** and supply
no acceptance credit. Finish or terminate the ongoing attempt cleanly before
recording the replacement run; preserve its observed status in the attempt log.
If an integrity incident or actual stale-output suspicion arises, follow the
repository runbook and reassess whether fresh validation is required. This
mode ruling cannot be used to dismiss such evidence.

**Standards remains Blocked pending a successful complete applicable candidate
check and its final identity verification. Concrete Standards findings remain
zero.**
