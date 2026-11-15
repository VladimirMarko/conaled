# Direct toolchain helpers — Spec review, round 2

**Outcome: Passed for the operational-helper scope.** DTP-001 and DTP-002 are
fixed with review evidence. There are no unresolved or new Spec findings.
This outcome does not accept a formal candidate, proof, chapter, or book/thesis
coverage milestone; the real full/focused formal gates remain pending.

Reviewer: `/root/lean_native_path_options/spec_direct_toolchain_r1`.
Review date: 2026-11-03. This continues the same independent Spec axis and
retained finding record. The round-1 report remains unchanged at
`session/reviews/direct-toolchain-spec-r1.md`.

## Immutable full scope

| Item | Identity |
|---|---|
| Base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `822cb7adeed4943acaf10454e9facfc2e3ee8ceb` |
| Merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-direct-toolchain-041-r2` |
| Retained candidate ref | `refs/pfds-review/direct-toolchain-r2-041` |
| Commit list from base | `822cb7a chore(toolchain): support fresh validation and cold recovery` |
| Superseded candidate | `f010b5d0fdbef9c9f007c56531c326e738557f9d` |

I independently resolved candidate HEAD/ref, confirmed the merge base and
observed a clean isolated checkout. The full review comparison remains:

```text
git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...822cb7adeed4943acaf10454e9facfc2e3ee8ceb
```

It contains the same eight added files, now 968 inserted lines:

- `session/environment/README-direct-toolchain.md`
- `session/environment/make-direct-toolchain-profile.py`
- `session/environment/run-direct-toolchain.py`
- `session/environment/test-direct-toolchain.py`
- `session/environment/test-direct-lake-build.py`
- `session/validation/direct-validation-runner-notes.md`
- `session/validation/run-direct-validation.py`
- `session/validation/test-direct-validation.py`

This was a full-scope reassessment: I retained the round-1 analysis of
unchanged content, inspected the complete correction diff, reread the
validation runner and its tests, and checked the effects against the stock
check/record interface and recovery requirements. The scope is not limited
to the corrective lines. The generator and environment launcher are
byte-identical to round 1. Candidate standards and project verification
scripts remain unchanged.

Formal candidate sources, runtime distributions/caches, prior evidence,
tracker/status and review/provenance records remain outside this source diff.
Their independent obligations persist. No project-source edit or runtime
test was performed by this reviewer.

## Requirements and retained identity

The full operational requirements remain the exact versions used in round 1.
I recomputed their hashes and confirmed no change:

| Requirement file | SHA256 |
|---|---|
| `session/requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `session/environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |

The Nix exception continues to leave exact version/dependency pins,
unchanged proof checking, isolated validation, independent reviews, immediate
final verification and durable local recovery intact. Candidate `AGENTS.md`,
README build/audit requirements, the code-review skill and shared review
procedure retain their round-1 applicability.

## Retained finding dispositions

### DTP-001 — Required fresh full-check path

**Original severity: High. Disposition: Fixed with review evidence.**

The new `--fresh` option is restricted to `full` at
`session/validation/run-direct-validation.py:367` and line 375. In full fresh
mode, command construction at line 255 adds the exact stock arguments
`--fresh --jobs 1` to `./check.sh --candidate HEAD`. The existing serial
resource policy is preserved.

The runner now stores `verification_mode` and requires the stock record's
mode to match it at line 151. Retained full evidence at line 171 must declare
a supported mode; its command must match that mode at line 180. Thus a
fresh record cannot be treated as incremental, or vice versa. After actual
successful execution, the saved stock record is checked against the selected
mode again at line 322.

Verify mode takes its mode from the named successful full evidence. It still
constructs only `./check.sh --verify-candidate HEAD`, adding no fresh/jobs
arguments. Existing checks bind the live verification bytes, saved bytes,
full evidence/log digests and current inputs. The documentation explicitly
requires the first full check under the recovered runtime to use the fresh
route; it does not relabel old incremental evidence.

The preserved `direct-validation-fresh-red-041.json` shows the new public
CLI case failing before the fix because the old parser did not accept
`--fresh`. The corrected candidate's public refusal tests pass, including
that fresh invocation reaching the existing-evidence refusal without
overwriting history. Source review establishes command construction and
mode binding; no fabricated successful formal record was used as a test
substitute. The actual fresh full check and later stock verification are
still subsequent formal tasks, not claimed completed by this fix.

### DTP-002 — Missing cold-recovery temporary parent

**Original severity: Medium. Disposition: Fixed with review evidence.**

Both public smoke tests now create their workspace-local `session/tools`
parent with `parents=True, exist_ok=True` before creating a temporary
project. The correction is at
`session/environment/test-direct-toolchain.py:42` and
`session/environment/test-direct-lake-build.py:30`. The existing success
cleanup and failure-evidence behavior are retained.

The preserved cold-red record shows the old test failing with the missing
temporary parent before any compiler probe. The round-2 aggregate records
`temporary_parent_absent_at_start: true` separately for each corrected
smoke test. Both then execute their real CLI/build probes successfully in
the separate cold workspace, using a newly created profile from the same
official executable bytes. This directly exercises the previously missing
recovery condition rather than relying on the parent directory created by
earlier investigations.

## Full operational assessment

The unchanged profile generator and environment launcher retain the
round-1 properties: official-distribution restoration is a documented
digest-verified precondition; original files remain untouched; wrapped
executables are copied byte for byte to regular files; shell paths are
quoted and original arguments forwarded; and real executable identities
are checked before child execution. The source does not synthesize version,
type-checking, build or success output. Scoped environment settings and
`execvpe` preserve the ordinary command boundary.

The round-2 CLI detail records actual exact Lean and Lake version outputs,
valid theorem acceptance with no axioms, and rejection of the false theorem
with the genuine type-mismatch diagnostic. The Lake detail records the
profile compiler path, native compilation/linking and the executable's
actual `42` output. These establish the intended operational paths with
limited claims.

The validation runner continues to require the exact prerequisite/focused
heads, manifest and clean pinned dependency sources. It retains source,
controller and environment identity checks before/after execution, exclusive
new evidence creation, two nonblocking validation locks, owned-child-group
cancellation and terminal-observation fields. Its full and verify routes
use the stock project checker, and its focused route remains development
evidence only. Every record keeps `acceptance: false`. The new fresh route
preserves the unchanged source-policy, build, axiom-audit and final-verifier
contract rather than weakening it.

No new Spec finding was identified in the complete eight-file scope. The
frozen-input/no-conflicting-writer discipline and honest handling of unknown
terminal results remain necessary operating conditions; this report makes
no stronger hermetic or adversarial-integrity claim.

## Validation reconciliation

The original round-2 aggregate is deliberately still **`passed: false`**:

- File: `session/validation/direct-toolchain-candidate-validation-r2-041.json`.
- SHA256: `d65acb992ea7ef25660873c88be52efad91477150e456150b0467fb5da329fc4`.
- Its three actual test commands all exited 0. Its snapshot-status field
  reported the missing-index symptoms instead of a clean checkout.

The separate reconciliation record explains that the temporary
`GIT_INDEX_FILE` setting was inadvertently carried into review-worktree
creation, leaving that worktree without its own index. The implementer
recreated only that index from exact HEAD with `git read-tree HEAD`, without
editing source files. The coordinator observed the anomaly, independently
rechecked clean exact HEAD, and recomputed all eight snapshot and delivered
hashes against the round-2 manifest. I independently confirmed the current
clean candidate identity and inspected the preserved aggregate and
reconciliation.

Reusing the runtime results is appropriate **for this operational artifact
scope**. The CLI/Lake tests execute the candidate Python helpers against
generated projects in the separate cold workspace; their relevant inputs do
not use the review worktree's index. The refusal-test fixtures copy the
candidate runner and exit at existing-evidence, interrupted-evidence or
held-lock checks, before a real checkout snapshot. The repaired index changes
none of those program inputs. This is not a waiver for a formal candidate
gate, whose clean-checkout preconditions must hold during that actual run.

The reconciliation does not overwrite or relabel the failed aggregate. It
records the reason for reuse, current clean state, matching source content,
and completed artifact commands:

| Evidence | SHA256 |
|---|---|
| `session/validation/direct-toolchain-candidate-r2-041.json` | `5f556fb8f0121c55ad6c69589c247bde8bbd7ee6a467ce5e18387d9ec9b99de6` |
| `session/validation/direct-toolchain-candidate-validation-r2-reconciled-041.json` | `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916` |
| `session/validation/direct-toolchain-candidate-cli-r2-041.json` | `4b9b52f5c63e5d59e6e025b050ca4ea92d4221efcc8b161ab883337a2fe1ca22` |
| `session/validation/direct-toolchain-candidate-lake-r2-041.json` | `69eb08b9cfa19c683ffbb0197f38418b5e664fc45a2672214150326a7404e44b` |
| `session/validation/direct-validation-fresh-red-041.json` | `30ffb9c2185a876bfdc09bd793599e8e928965783bf5a2f0bc08e944bca7aebe` |
| `session/validation/direct-toolchain-cold-red-041.json` | `f01006f8fc4add3327e6189e6f81fc894b3f267451dc3dd0966daac63e803c06` |
| `session/environment/cold-profile-identity-041.json` | `da7b6f98e7d3ebd3ab53625f51f286c1893bc83aec66ba9b8ae0470ea5b30fbf` |

The earlier completed cache bootstrap/get and nine clean pinned dependency
records remain supporting operational evidence with their original scope.
They are not substituted for a formal candidate's own full check. I ran no
tests, compiler, cache operation or build during this review.

## Final disposition

**Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
**Candidate:** `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
**Spec outcome:** Passed for operational helpers.
**Unresolved findings:** 0; worst unresolved severity: none.
**Retained findings:** DTP-001 and DTP-002 both fixed with the evidence above.
**Validation status:** applicable operational artifact checks passed and the
index anomaly is explicitly reconciled; full/focused formal candidate
validation remains unrun and unaccepted.

Any later change requires a new candidate review. This approval applies only
to the named immutable helper candidate and the stated operational scope.
