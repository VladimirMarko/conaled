# #1036 compact recovery — independent operational review

## Current operational outcome

**Standards Passed and Spec Passed** on
`80671e07ff65e00cd6410d1bad05d181ff91958c`, against fixed base
`79f798372bfcef4663544fd617465fac8866c911`. All three operational findings are
fixed. Nine exact-candidate tests passed, actual exit 0. The final round and
remaining production obligations are recorded at the end of this file.
Formal Preface/Perm acceptance remains separate and pending.

## Scope and requirements

Coordinator: `/root/formal_review`, assigned by root within the existing
implementation/review process. This operational review is distinct from the
formal Preface/Perm acceptance scope and confers no chapter approval.

- Fixed base and verified merge-base: `79f798372bfcef4663544fd617465fac8866c911`.
- Candidate: `1c5f716d0fee6742b5fa7b77eea6e1983e8aadc1`.
- Immutable source checkout: `work-state/compact-recovery-review`.
- Three new files, 786 lines added, no exclusions.
- Comparison: `git diff 79f798372bfcef4663544fd617465fac8866c911...1c5f716d0fee6742b5fa7b77eea6e1983e8aadc1`.
- Single commit: `feat(recovery): package fixed base and cumulative current checkpoints (#1036)`.
- Full explicit requirements and verbatim current user steering:
  `specs/1036-compact-recovery.md` in that exact candidate.

The current user prioritizes latest-state recovery and small frequent uploads.
The scoped format uses one immutable source base and one cumulative latest
checkpoint, without a chain of intermediate checkpoints. Historical source,
current work-state, local tickets, necessary evidence and the intact supplied
native kit remain recoverable. The change does not alter formal source,
compiler/dependency pins, proof/review gates, chapter order or GitHub policy.
The original checkpoint tool remains unchanged.

| Candidate path | SHA-256 |
| --- | --- |
| `tools/checkpoint_compact.py` | `895041297ab57b73cf78d6d4acc60f9c8e59b1d881d161f146cacd32ed711e3b` |
| `tools/test_checkpoint_compact.py` | `9ad1b7b4259671844207c23e2b80e6f60de45f763915db05ed14f6c8a22842fc` |
| `specs/1036-compact-recovery.md` | `3f62378fd12750695c4bd1564454589c5881e6cbabf92b6aa761a64c06a826c7` |

## Validation evidence

The builder reports five focused regression tests passing. Root independently
ran the suite from the exact captured candidate: actual exit 0, five tests,
1.732 seconds. Full log: `validation/1036-compact-tests.log`. Root also confirmed
all three delivered source files match the captured candidate. This is Python
recovery tooling; no Lean source changed and no formal Lean build is claimed.
Each production capture will still perform its required actual archive restore
smoke before publication and immediate upload.

## Round 1 — independent axes dispatched

Recorded: 2026-11-03T23:35:58.669505+00:00

### Standards

Reviewer: `/root/formal_review/standards`.
Outcome: pending. Review covers documented repository process, artifact-
appropriate testing, safe preservation and restore behavior, and the explicit
capture/identity contract. No new finding is recorded before the report returns.

### Spec

Reviewer: `/root/formal_review/spec`.
Outcome: pending. Review covers the full exact candidate specification,
latest-state completeness, two-artifact/no-chain contract, input identity,
active-attempt limitations, and supported rejection boundaries.

Both axes are independent of root's implementation inspection. They must return
explicit outcomes on this same candidate. Operational acceptance requires both
passing outcomes and root's final delivered-file comparison; neither this
record nor the passing fixture suite supplies acceptance by itself.

## Round 1 returned reports — changes requested

Both axes reviewed the complete immutable three-file scope. Neither axis passed.
Root accepted CR-SP-001 for correction; both findings were relayed to root and
the original tool implementer. No production checkpoint was created using this
unapproved candidate.

### Standards — CR-ST-001 (medium), unresolved

Reviewer `/root/formal_review/standards` verified the base, merge-base, clean
candidate, full scope, and clean `git diff --check`. The five-test exact-candidate
log and root's observed exit 0 are retained. Apart from the issue below, the
reviewer found no additional material Standards violation.

`tools/checkpoint_compact.py:148`, `state_files()`, calls
`os.walk(root, followlinks=False)` without an input-root directory check or an
`onerror` callback. Python's default walk ignores directory enumeration errors.
A missing root produces no files; an unreadable subtree can disappear from all
three inventories/copies, so their equality and restore smoke may still pass.
This violates the specification's requirement to preserve all saved work-state
and evidence and to fail capture rather than publish incomplete recovery.

A read-only probe of the exact candidate with a confirmed nonexistent path
returned `state_files(missing_root) == []` and
`workflow_state(missing_root) == {}`. No file or archive was created for that
probe. The reviewer also checked the installed `os.walk` error-handling contract.

Requested correction: require the shared enumeration root to be a directory,
and raise every enumeration error via `onerror`. Add regression coverage for a
missing workflow root and a simulated subtree `PermissionError`, both refusing
capture without publishing output. A simulated error avoids false confidence
from permission tests that run under a privileged test account.

The reviewer otherwise confirmed cumulative fixed-base recovery, index versus
working-overlay separation, tested file/directory/link transitions, complete
base hash/size binding, unsafe archive rejection, atomic non-overwriting
publication, and explicit active-attempt limitations. No successful mechanical
suite was repeated. No production archive, source/evidence mutation, or report
file write was performed by this reviewer.

**Standards outcome: Findings-present; one medium finding, CR-ST-001.**

### Spec — CR-SP-001 (medium), unresolved

Reviewer `/root/formal_review/spec` independently verified the base, merge-base,
clean candidate and all three files/786 added lines. Apart from the issue below,
the reviewer found no additional Spec violation.

Selected source paths in `source_state()` at lines 104–105 bypass the
`SECRET_NAMES` component check used by `state_files()` at lines 146–155. Those
paths can enter the source overlay at lines 390–396. This violates the explicit
specification at lines 49–52 that credential-like names stop capture.

A disposable fixture outside production capture trees used a plainly marked
dummy value in an untracked source `.env`. The actual probe reported:

```json
{"capture_published": true, "restore_smoke": "passed", "credential_named_source_in_overlay": true, "credential_named_source_in_source_state": true}
```

No real credential or production data was used or modified. Requested
correction: apply the same `SECRET_NAMES` rule to every component of every
selected source path, both tracked and untracked, before bundle/overlay
construction. Include a decisive regression for guarded source filename and
ancestor-directory paths, requiring failure without output publication.

The reviewer otherwise confirmed cumulative Git recovery without earlier rolling
checkpoints; source/index/working/refs/HEAD comparison; exact base identity;
rejection of unsafe archive entries; actual restore, fsck, workflow/kit checks,
kit verification and final stability before publication; and bounded active
observations marked incomplete. The five-test passing root suite was not
repeated; the additional probe addressed this concrete uncovered gap.

**Spec outcome: Blocked with one medium source finding, CR-SP-001.**

### Coordination and next round

Keep base `79f798372bfcef4663544fd617465fac8866c911` fixed. Root will capture a
corrected immutable candidate and run its exact suite. Both independent axes
must review that complete new candidate, reusing unchanged analysis and
verifying both corrections. Root's final file comparison and actual production
base/upload/restore outcomes remain separate obligations. No formal Preface/Perm
finding or gate is changed by this operational review.

## Round 2 — corrected candidate dispatched

Recorded: 2026-11-03T23:44:18.043768+00:00

- Fixed base and verified merge-base remain
  `79f798372bfcef4663544fd617465fac8866c911`.
- New candidate: `880fecaf5b8a7ec107467182a4934806df40c137`.
- Full scope: three files, 842 added lines; no exclusions.
- Delta from round 1: three files, 60 insertions and four deletions.
- New commit: `fix(recovery): reject incomplete state and credential source paths (#1036)`.

| Delivered candidate path | SHA-256 |
| --- | --- |
| `tools/checkpoint_compact.py` | `22df21b2c0543d2a36a089c0fe40a2eadadfe22b2ba60bc695f0dc71454009f2` |
| `tools/test_checkpoint_compact.py` | `69fd56e831d834943269b601595641f802f2b8f3ac76bc4394575abe6e61f871` |
| `specs/1036-compact-recovery.md` | `d9193a0f304b20f6d2a21ea68da86da1b264c4283d084d0fe0e0f84382393bf1` |

Root's exact isolated candidate test run completed with observed exit 0: all
eight tests passed in 2.221 seconds. Its separate retained log is
`validation/1036-compact-tests-round2.log`; round 1's evidence is unchanged.
Root and coordinator matched the delivered files to the reported immutable
identities. The review checkout is clean at the exact candidate.

The implementation adds required existing non-symlink work-state/kit roots,
raising directory-enumeration errors, and the shared credential-name component
check before reading every selected source path. Three new tests exercise
credential source names/ancestors, missing or symlink workflow roots, and a
simulated unreadable subtree; the specification describes those boundaries.

Both independent axes are reassessing the full candidate with retained
unchanged analysis, including both CR-ST-001 and CR-SP-001 corrections. Neither
finding is marked fixed solely from the implementer's report or passing tests;
the independent returned reports determine their disposition.

## Round 2 returned reports — one Spec correction remains

### Standards — Passed on 880fecaf

The independent Standards reviewer verified the fixed base/merge-base, clean
candidate, complete three-file/842-line scope, matching frozen identities, and
clean `git diff --check`. It reviewed the complete correction delta and
expressly retained prior unchanged-code analysis.

- CR-ST-001 is fixed: the shared enumerator rejects missing/non-directory and
  symlink roots and propagates directory enumeration errors. Inventory, copy
  and stability checks share that behavior.
- The CR-SP-001 source-path correction is corroborated: all selected components
  are checked before reading file state; tracked/untracked filename and ancestor
  regressions exercise the actual refusal.
- The eight tests/2.221s exact-candidate root log and observed exit 0 support
  the corrected cases; no Lean gate is required for this operational tool.
- No open Standards findings remain for this candidate.

**Standards outcome: Passed on
`880fecaf5b8a7ec107467182a4934806df40c137`.**
Production restore/stability and actual upload results remain subsequent root
obligations. No formal #1002 approval is implied.

### Spec — CR-SP-001 fixed; CR-SP-002 (medium), unresolved

The independent Spec reviewer verified the same full scope and hashes, retained
unchanged analysis, and reviewed the complete round 2 delta. CR-SP-001 is fixed:
`source_file_state()` checks every selected component before reading, and the
new regression exercises tracked/untracked `.env` and `nested/.aws/config` paths
with no publication. CR-ST-001's missing/unreadable workflow-root correction is
also corroborated.

CR-SP-002 concerns the order at `tools/checkpoint_compact.py:358–359`.
`capture()` resolves `args.kit` before passing it to `state_files()` at line 375.
The shared root symlink check at lines 148–151 therefore sees the symlink's
target, not the originally supplied alias. A kit-root symlink is accepted even
though the amended specification explicitly requires work-state and kit root
symlinks to abort. Retargeting that supplied alias would likewise be absent
from comparisons of the already resolved target. The work-state symlink
regression at test lines 152–161 does not exercise this kit argument path.

Requested remedy: reject a symlink in the original kit argument before
resolution, and add a regression through the actual `capture()` entrypoint
using a kit-root symlink, requiring rejection and no archive publication.
A direct enumerator test would miss this ordering issue.

The reviewer identified no further Spec issue, repeated no successful suite,
and made no source/evidence mutation.

**Spec outcome: Blocked only by CR-SP-002 (medium).**

### Coordination

Root accepted CR-SP-002 and assigned the original implementer the bounded
correction and decisive regression. The base remains fixed and all completed
analysis is retained. Overall operational acceptance is pending; Standards'
round 2 approval does not approve a subsequent changed candidate. Formal
Preface/Perm remains independently Blocked with unchanged gates.

## Round 3 — both independent operational axes Passed

Recorded: 2026-11-03T23:47:54.976412+00:00

- Fixed base and independently verified merge-base:
  `79f798372bfcef4663544fd617465fac8866c911`.
- Approved operational candidate: `80671e07ff65e00cd6410d1bad05d181ff91958c`.
- Full scope: three new files, 853 added lines, no exclusions.
- Delta from round 2: three files, 12 insertions and one deletion.
- New commit: `fix(recovery): reject kit-root symlinks before resolution (#1036)`.
- Root's actual isolated test run: exit 0; nine tests passed in 2.810 seconds.
- Complete separate log: `validation/1036-compact-tests-round3.log`.

| Approved and delivered path | SHA-256 |
| --- | --- |
| `tools/checkpoint_compact.py` | `0dcce33b9e1430a05f084a8ae6181ef003078e998f350c2d19546c982a73cab5` |
| `tools/test_checkpoint_compact.py` | `7ea374f1abc45d3e47e48c4e2d0c41ed0f0b19a4ff3841b41a4e2f1188bf65cf` |
| `specs/1036-compact-recovery.md` | `c7d76ff1e545a8aa8485392063bd4282b27cf4e9bab0622ec6fa4094496263ac` |

### Standards — Passed

Reviewer: `/root/formal_review/standards`.

The reviewer independently verified the candidate, unchanged merge-base, clean
checkout, clean `git diff --check`, complete scope, and byte-for-byte agreement
of all delivered files with the immutable candidate. Earlier Standards analysis
was expressly reused for unchanged code. The full round 3 delta—the original
kit-argument guard, actual capture-entrypoint regression, and corresponding
specification sentence—was reviewed.

CR-ST-001 remains fixed. CR-SP-001's component check remains intact and is
corroborated; final ownership of its disposition belongs to Spec. CR-SP-002's
correction is corroborated: `capture()` rejects a symlink in the original kit
argument before resolving paths. No open Standards finding or new material
Standards issue remains.

The reviewer read the nine-test/2.810s log and the new regression. That test
invokes actual capture with a real kit-root symlink, requires rejection, and
checks no output publication. All earlier regressions remain passing. Root's
observed exact-candidate runner exit 0 is retained. The reviewer repeated no
successful suite, changed no files, and generated no production archive.

**Standards outcome: Passed on 80671e07; zero unresolved findings.**

### Spec — Passed

Reviewer: `/root/formal_review/spec`.

The reviewer independently verified the candidate, fixed merge-base, clean
checkout, complete scope, clean `git diff --check`, and exact delivered-file
agreement. Prior unchanged-code analysis was expressly retained and the entire
round 3 delta was reviewed against round 2.

| Finding | Final independent disposition |
| --- | --- |
| CR-SP-001 | Fixed: every selected source component is checked before its state read; tracked/untracked filename and ancestor regressions remain passing. |
| CR-ST-001 | Fixed, corroborating Standards: required roots and raising enumeration errors prevent silent workflow omission. |
| CR-SP-002 | Fixed: original kit argument is checked before resolution; a capture-entrypoint symlink regression proves rejection with no output. |

No unresolved Spec finding remains. The complete reviewed contract still covers
one fixed immutable base plus a latest cumulative snapshot, no earlier rolling
checkpoint dependency, source/index/working state and refs/HEAD, exact base
binding, work-state and supplied-kit preservation, archive integrity/member
rejection, actual restore/fsck/kit verification, final input stability, and
non-overwriting publication. Active-attempt captures remain explicitly bounded,
potentially uncoordinated observations without terminal-success or formal-
acceptance credit.

The reviewer read the complete nine-test/2.810s log and relevant regression
code; root's actual exit 0 supplies terminal evidence. No suite was repeated
and no files were modified by the reviewer.

**Spec outcome: Passed on 80671e07; zero unresolved findings.**

### Coordination result and remaining production obligations

Both independent axes pass the same exact candidate against the fixed base.
All three historical operational findings are fixed with retained independent
review evidence. Root's final delivered-candidate comparison remains required
immediately before relying on the tool; both reviewers and the coordinator
already observed matching delivered bytes during this round.

No production base/checkpoint, restore smoke or upload is claimed by these
reviews. The first real capture must perform its built-in restore/stability
checks, the base must obtain an actual upload identity, and the current
checkpoint must be saved and exposed using that identity. The active validation
record may be captured only with its specified prefix limitations.

The current environment guide was reread and correctly names the restored
`native-kit/` directory. The earlier naming observation is resolved and requires
no further source correction.

Formal Preface/Perm candidate c988f183 remains independently Blocked on its
unchanged formal validation/incident/review sequence. This operational approval
waives none of those gates.

This review writer is frozen after return. Later candidate or production
outcomes belong in a named follow-up; completed prior outcomes remain intact.
