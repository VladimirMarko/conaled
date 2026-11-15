# Operational toolchain: round 9 review dispatch

## Existing loop, roles and immutable scope

This continues the existing operational-toolchain implementation/review loop in
`session/reviews/direct-toolchain.md`. It is not a new acceptance loop. The
coordinator `/root/direct_toolchain_validation_plan` authored an earlier original
validation helper, so coordinates identity and reconciliation only; it supplies
no independent third review. Root remains the implementer and owns execution,
formal validation, final delivery verification and checkpoint publication.

Both independent axes cover the full task, not just the added document:

- Base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `ff3f709723e5c49e5ba40798abbed7d36141a6fb`.
- Ref: `refs/pfds-review/native-toolchain-r9-043`.
- Isolated checkout: `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r9`.
- Diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...ff3f709723e5c49e5ba40798abbed7d36141a6fb`.
- Commit list: one synthetic snapshot, `ff3f7097 docs(toolchain): preserve modes in real Elan recovery snapshot (#10000)`.
- Full diff: 19 files, 3,456 inserted lines.

The manifest lists the exact 19 paths, SHA256 hashes, Git modes, six saved
requirements, exclusions and reuse links:
`session/validation/native-toolchain-candidate-r9-043.json`, SHA256
`af74d3d1ab35c9a26dd1034bf223d2479232d6e82732c05ac72b701c7f0e09ec`.

The coordinator's read-only dispatch identity receipt is
`session/validation/native-toolchain-coordinator-dispatch-r9-043.json`, SHA256
`d4ac3310ba40cf5a93d8b4a352fbbafacdc9c14a4e460e827210c16726c3549f`.
At `2026-11-03T17:47:20.312624+00:00`, candidate HEAD and retained ref matched,
merge base equalled the fixed base, isolated porcelain was empty, and all 19
committed/isolated/delivered contents and modes matched the manifest. All six
saved requirement hashes matched. The receipt records no mismatch. It is
identity evidence, not source review or a mechanical execution test.

The exact two-endpoint difference from approved round 7
`af2c53dce68ebb122c81175312d6bb30df9aac05` is one added file:
`session/environment/RECOVER-ELAN-REGRESSIONS.md`, SHA256
`b76abf471a5546faa191dd9d7dbf7639341b0028457a01c36494f54bd108d769`.
All original 18 files match round 7 in both blob and mode. This permits retaining
matching analysis; the changed candidate still requires both full-scope axes.

Formal source candidates, runtime binaries and caches, prior evidence,
requirements, tracker/status, reviews and provenance records are outside the
authored-helper diff. Their independent obligations remain. No formal source,
active controller or runtime input has changed for this appendix.

## Superseded round 8 and actual artifact evidence

Round 8 candidate `d95518fde8cfc877da9d2bfc720ed4fd1f4698ba` was superseded
before any round 8 axis review or approval. Its snapshot accidentally normalized
two native-validation Python executable modes from 100755 to 100644. The
coordinator surfaced that exact metadata discrepancy. Round 9 restores both
approved round 7 modes. No delivered helper/runtime bytes changed, and the
round 8 snapshot and actual validation remain retained without relabeling.

The current aggregate is
`session/validation/native-toolchain-candidate-validation-r9-043.json`, SHA256
`a86be8c447403d0947e7542461471e47570b69e484e4464522c3a12661221ddc`.
It establishes the corrected metadata identity and explicitly reuses
`session/validation/native-toolchain-candidate-validation-r8-043.json`, SHA256
`d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a`.

The reused round 8 evidence actually checked all three appendix shell blocks
for syntax and executed the captured cold setup block with only `PFDS_ROOT`
substituted into the existing cold reconstruction area. It downloaded and
verified the official Elan 4.2.4 archive, safely extracted the expected binary,
used genuine Elan's supported argv0 dispatch and custom toolchain link,
observed real version/link/which results, and ran the selected exact Lean
4.35.0 version through the unchanged native launcher. Inspect the aggregate's
detailed linked commands, outputs, digests and limits. All 19 round 8 blobs equal
round 9; the newly added appendix mode is unchanged. The two restored executable
modes belong to controllers that the cold Elan setup does not invoke.

For the original 18 files, retain and assess round 7's exact-input artifact
validation and completed axis analysis:

- `session/validation/native-toolchain-candidate-r7-042.json`.
- `session/validation/native-toolchain-candidate-validation-r7-042.json`.
- `session/validation/native-toolchain-final-verification-042.json`, SHA256
  `0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206`.
- `session/reviews/direct-toolchain-standards-r7-042.md`, SHA256
  `3b143b5b92f51efaa8aecfc86de2fa7a3316ce1cc320a490c81ffc2af064ca0e`.
- `session/reviews/direct-toolchain-spec-r7-042.md`, SHA256
  `c7df56778cba429b9d2c8c67e5a5f1e52f35e6a106a9ac36a2ecb0f89ac81b04`.
- `session/reviews/direct-toolchain-coordinator-r7-042.md` and retained earlier
  reports/finding dispositions linked from `direct-toolchain.md`.

Verify relevant source, standards, requirements and validation identities before
reuse. Do not describe earlier actual checks as newly run on round 9. No stock
regression suite is claimed to have run, and neither the Elan setup nor this
operational review can substitute for those suites or formal acceptance.

## Requirements, standards and independence

Read all six saved requirement/scope files in the manifest: the original
book-formalization request; union with the thesis; direct toolchain request;
implementation scope; environment handoff; and later native-toolchain request.
The user's explicit Nix exception changes the launcher requirement only.
Exact Lean/Lake versions, genuine compiler behavior, historical evidence,
isolated validation, independent review, durable recovery and all applicable
formal build/audit/final-verification gates remain.

Use candidate `AGENTS.md`, the README development/build/audit guidance,
`.agents/skills/implement/SKILL.md`, `.agents/skills/code-review/SKILL.md`,
`.agents/skills/code-review/heuristics.md`, and `docs/agents/review-loop.md`.
Read relevant linked architectural, tooling/TDD and documentation guidance,
and any applicable local standards. Candidate source and retained reports may
be read with ordinary file/Git operations. The implementation is operational
tooling and recovery documentation; no new mathematical claim is in scope.

- **Standards:** `/root/lean_native_path_options`. It explicitly confirmed that
  it authored none of the 19 scoped implementation files. Its native-path/QEMU
  analyses and old coordination/review records are outside this source scope.
- **Spec:** `/root/chapter02_continuation_plan`. It explicitly confirmed it
  authored neither the added appendix nor its Elan command recipe; its previous
  authored outputs are independent review reports outside the source scope.

`/root/recovery_audit` supplied the planned Elan recipe and is therefore not the
independent Standards reviewer for the added appendix. Its frozen round 7
assessment remains available as prior analysis with matching-input limits.

Each axis must inspect the complete 19-file task and relevant unchanged uses,
retaining matching prior analysis so attention can concentrate on the new
appendix and any affected interfaces. Assess scope, applicability and strength
of evidence, including cold reconstruction, source/archive identity, genuine
Elan selection, local state, child-local environment, native helper interaction,
and the distinction between setup completion and pending regression suites.
Do not turn a possible future output-reuse protocol into existing approval.

Retain DTS-001 (Medium), DTS-002 (Medium), DTP-001 (High) and DTP-002 (Medium)
with their fixed dispositions and closure evidence, and assess regression.
Use new stable identifiers from DTS-003 or DTP-003 if concrete new findings
arise. Keep the two axes' severities and findings separate. No earlier incomplete
round becomes approved retroactively.

## Delivery and execution limits

Perform no compiler/build/test/network/protected-path operations, source/runtime
edits, additional agent spawning, tracker updates or process control. Do not
touch the active full901 run. Read/hash/Git identity operations are allowed.
Only write the assigned complete axis report, then freeze it and send outcome,
all findings/dispositions, counts, worst unresolved severity and report SHA256.
Surface actionable findings promptly. Do not wait for unrelated formal runs to
finish before deciding the distinct operational scope.

- Standards report: `session/reviews/direct-toolchain-standards-r9-043.md`.
- Spec report: `session/reviews/direct-toolchain-spec-r9-043.md`.
- Coordinator reconciliation: `session/reviews/direct-toolchain-coordinator-r9-043.md`.

At dispatch, neither round 9 axis has returned an outcome. A completed operational
pass requires both axes on this exact candidate with no unresolved findings and
matching artifact evidence. It does not accept prerequisite10013/10018,
signed-potential10023, a chapter or the book/thesis union. Root owns the final
delivery identity receipt and checkpoint capture after reconciliation.
