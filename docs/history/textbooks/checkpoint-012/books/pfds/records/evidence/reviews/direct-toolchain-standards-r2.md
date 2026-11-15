# Direct toolchain operational helpers — Standards review, round 2

## Outcome

**Passed** for the operational-helper scope on candidate
`822cb7adeed4943acaf10454e9facfc2e3ee8ceb`. Both retained Standards findings,
DTS-001 and DTS-002, are **fixed with review evidence**. There are no new or
unresolved Standards findings and no evidence-access blocker.

This is the continuing independent Standards axis by
`/root/lean_native_path_options/standards_direct_toolchain_r1`. It does not
replace the independent Spec axis and does not accept any formal candidate,
proof, chapter, or the full book/thesis workstream. A successful fresh formal
check has not been claimed or inferred.

## Immutable full scope and continuity

- Fixed base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Round-2 candidate: `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Retained candidate ref: `refs/pfds-review/direct-toolchain-r2-041`.
- Isolated checkout:
  `/workspace/scratch/b566cace4ed6/pfds/review-direct-toolchain-041-r2`.
- Full review diff:
  `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Commit: `822cb7a chore(toolchain): support fresh validation and cold recovery`.
- Full scope: eight files, 968 added lines, retaining the profile builder,
  environment launcher, two compiler/Lake smoke tests, environment README,
  formal-evidence runner, refusal tests and runner handoff.

The scope manifest is
`session/validation/direct-toolchain-candidate-r2-041.json`, SHA256
`5f556fb8f0121c55ad6c69589c247bde8bbd7ee6a467ce5e18387d9ec9b99de6`.
The coordinator confirmed all eight snapshot and delivered hashes match that
manifest. I read the full-scope diff summary, the r1-to-r2 correction diff and
the affected complete logic, and retained the unchanged-file analysis from
the previous full-scope review. The profile builder and environment launcher
remain byte-identical to their reviewed r1 versions. This is not a review
limited to only the two correction locations.

The applicable standards and saved requirements are unchanged from
`direct-toolchain-standards-r1.md`: candidate `AGENTS.md`, README environment
and build/audit rules, implementation/TDD/code-review skills and their
references, shared review procedure, and ADRs 0001 and 0010. The user's Nix
exception remains narrow. Formal sources, past evidence, runtime
distributions/caches, tracker/status and review/provenance records remain
excluded from this authored-helper diff; their independent obligations
continue.

The original r1 report is retained unchanged. No finding identifier has been
removed or renumbered.

## Retained finding dispositions

### DTS-001 — Fresh validation requirement

- **Original severity:** Medium.
- **Round-1 status:** Unresolved.
- **Round-2 status:** Fixed with review evidence.
- **Rule retained:** README and ADR 0010 require a fresh project rebuild after
  the applicable tooling/runtime setup change. Final stock verification reads
  the successful record's mode and must receive neither `--fresh` nor `--jobs`.

The corrected runner accepts `full RUN_ID --fresh` and constructs exactly
`./check.sh --candidate HEAD --fresh --jobs 1` for that route. It records a
separate `verification_mode`. `full_evidence` restricts that mode to fresh or
incremental and compares the retained command against the corresponding
exact stock command. `validate_stock_record` requires the stock record's
mode to agree with it, in addition to the existing candidate, dependency,
compiler and success conditions.

For `verify`, the runner takes the mode from the already-validated successful
full record. Its actual child command remains
`./check.sh --verify-candidate HEAD`. The CLI rejects `--fresh` on focus and
verify. The subsequent record comparison again checks the selected mode and
unchanged retained/live evidence. Existing full/focused locks, terminal-result
handling, frozen inputs and the constant `acceptance: false` remain in place.

Both the environment README and runner handoff now explicitly require the
first full check in this recovered runtime to use fresh mode with the serial
job limit. The handoff's example commands follow that route. Its old source
hashes are now labelled as historical r1 hashes rather than current identity.

The saved red test,
`session/validation/direct-validation-fresh-red-041.json`, establishes that
the old CLI rejected the newly required flag. The isolated r2 refusal suite
completed successfully and checks existing-evidence protection with and
without `--fresh`. The real full/focused/formal-verification paths have not
yet been run, and these refusal results are not presented as such. Source
inspection resolves the missing route and mode-binding defect; actual formal
success remains a separate required result after operational review.

### DTS-002 — Missing temporary parent after recovery

- **Original severity:** Medium.
- **Round-1 status:** Unresolved.
- **Round-2 status:** Fixed with review evidence.
- **Contract retained:** Recovery excludes transient directories, while the
  public smoke tests must set up their own workspace-local fixtures before
  testing Lean/Lake behavior.

Both smoke tests now create `root / "session/tools"` with parents as needed
before calling their temporary-directory API. Fixture placement stays inside
the selected `--workspace`. Existing report handling and cleanup are retained.

`session/validation/direct-toolchain-cold-red-041.json` preserves the actual
old failure during temporary-directory creation, before any Lean probe.
The r2 aggregate records `temporary_parent_absent_at_start: true` separately
for both corrected smoke-test invocations in the cold workspace. Both then
returned zero and produced their full detailed reports. The Lake trace uses
that cold workspace's newly constructed profile, rather than silently using
the old profile. This establishes the corrected public behavior under the
missing-parent condition that caused the finding.

## Validation evidence and index reconciliation

All three actual isolated-r2 test commands returned zero:

| Check | Established result |
|---|---|
| Public Lean/Lake CLI smoke test | Exact Lean 4.35.0 and bundled Lake version, a genuine theorem accepted without axioms, and a false theorem rejected with a type mismatch. |
| Lake executable smoke test | The cold profile's real compiler was invoked; native compilation and linking succeeded; the resulting executable printed `42`. |
| Validation-runner refusal suite | All three tests passed, including the existing-record case both with and without `--fresh`; no mock compiler or passing formal evidence was introduced. |

The evidence consists of:

- `session/validation/direct-toolchain-candidate-cli-r2-041.json`, SHA256
  `4b9b52f5c63e5d59e6e025b050ca4ea92d4221efcc8b161ab883337a2fe1ca22`.
- `session/validation/direct-toolchain-candidate-lake-r2-041.json`, SHA256
  `69eb08b9cfa19c683ffbb0197f38418b5e664fc45a2672214150326a7404e44b`.
- `session/environment/cold-profile-identity-041.json`, SHA256
  `da7b6f98e7d3ebd3ab53625f51f286c1893bc83aec66ba9b8ae0470ea5b30fbf`.
- Original r2 aggregate
  `session/validation/direct-toolchain-candidate-validation-r2-041.json`,
  SHA256 `d65acb992ea7ef25660873c88be52efad91477150e456150b0467fb5da329fc4`.
- Reconciled record
  `session/validation/direct-toolchain-candidate-validation-r2-reconciled-041.json`,
  SHA256 `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916`.

The original aggregate remains **failed**. It recorded successful individual
test commands and matching source hashes, but failed the clean-checkout
condition because a temporary `GIT_INDEX_FILE` value had unintentionally
survived into worktree creation, leaving that worktree's own index absent.
The subsequent repair recreated only the isolated worktree index from its
exact HEAD. The coordinator observed the index problem, then independently
confirmed the clean exact candidate and unchanged source hashes. I also
confirmed the current HEAD/ref and clean worktree status during this review.

The shared review procedure permits reuse when the validated source and other
relevant test inputs are unchanged. That condition is established here for
these artifact tests: they read the same helper bytes and operated on the
separate cold runtime/temporary fixtures; repairing the review checkout's Git
index did not alter those inputs. The original failed aggregate and explicit
reconciliation are both retained. This is a narrow reuse of the genuine
successful commands, not a retroactive claim that the earlier checkout was
clean. No formal stock candidate check, which would itself require and inspect
clean Git state, ran under the incorrect index state.

The earlier official-distribution provenance and nine clean exact dependency
pins remain the retained background evidence. No relevant dependency or
compiler pin changed in this correction. The candidate has not acquired any
formal source, guard, flake or manifest changes.

## Remaining boundaries

No new documented-standard violation or concrete heuristic defect was found
across the full eight-file scope. The tests remain at public command boundaries,
use independent expected outputs, and retain meaningful rejection cases.
The wrappers still forward genuine commands, preserve original compiler
bytes and scope their environment changes to invoked processes.

This pass covers operational helper implementation and its artifact-appropriate
validation. It does not establish a successful fresh full build, exhaustive
proof audit, focused signed-potential build, final stock candidate verification
or mathematical acceptance. Those gates must produce their own actual terminal
results with stable inputs and the required independent reviews. The first
full run in this setup must use the corrected fresh route. No missing formal
result has been relabelled as a tool-test success.

The caller must still confirm that the delivered task files match this exact
approved snapshot before accepting the operational change. Any later source
change needs the applicable follow-up review; this report does not approve a
moving tip.

## Final record

- **Standards outcome:** Passed.
- **Retained findings:** DTS-001 fixed; DTS-002 fixed.
- **New findings:** 0.
- **Unresolved findings:** 0.
- **Worst unresolved severity:** None.
- **Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- **Review actions:** Read-only source/evidence inspection and this report.
  No test, compiler, cache operation or build was repeated, and no
  implementation, prior report, tracker, Library item or remote state was
  modified.
