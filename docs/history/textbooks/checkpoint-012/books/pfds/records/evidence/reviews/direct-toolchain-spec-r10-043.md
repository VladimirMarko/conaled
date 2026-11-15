# Operational toolchain — independent Spec continuation, round 10 (043)

**Outcome: Passed for the complete operational-toolchain scope.** DTP-003
(Medium) is fixed with matching source and genuine public-selector evidence.
DTP-001 (High) and DTP-002 (Medium) retain their earlier closures without
regression. There are no new or unresolved Spec findings. This outcome does
not accept a stock regression suite, formal source candidate, chapter, or the
book/thesis union.

Reviewer: `/root/chapter02_continuation_plan`, 2026-11-03. This continues the
same loop coordinated by `/root/direct_toolchain_validation_plan`. My confirmed
independence remains applicable: I authored no scoped implementation or Elan
recipe; my earlier authored files are independent review reports. I read the
complete r10 dispatch and updated retained finding record. I performed only
read-only file/hash/Git inspection and wrote this report. No compiler, probe,
test, build, audit, verifier, network, protected-path operation, process control,
source/runtime edit or new agent was used.

## Exact scope and retained whole-task assessment

- Fixed base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `060e6b877b8db57a30f947b996b7dfe34a5401a1`.
- Ref: `refs/pfds-review/native-toolchain-r10-043`.
- Isolated checkout: `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r10`.
- Commit: `060e6b8 docs(toolchain): select pinned Elan ahead of ambient PATH (#10000)`.
- Full three-dot scope: 19 files, 3,457 insertions, one snapshot commit.

I independently resolved HEAD/ref/merge base, observed empty isolated porcelain,
and matched the full diff file set with the manifest. All 19 committed,
isolated and delivered content hashes and executable modes agree. All original
18 files match r9 and approved r7 in both blob and mode; all 19 modes are
unchanged from r9. The endpoint delta changes only the Elan appendix's PATH
order and immediately following explanation. Its current SHA256 is
`39184174a0a2cdff195caf2515ab871584e14d67b35b19da3ee3a8c1c1b7d633`.

The complete whole-task assessment is retained in
[the frozen r9 Spec report](direct-toolchain-spec-r9-043.md), verified SHA256
`1651fad484a6c01c68e3038a980e2edce9cbe309f9fef84b1a8167731fd60526`,
including its linked complete r7 analysis, six requirements, applicable
guidance, provenance and evidence limits. This continuation incorporates that
assessment rather than narrowing acceptance to the changed line. R9 remains
Findings-present on its own candidate; only the corrected r10 finding receives
the new disposition below.

All six saved requirement/scope maps are unchanged and their actual hashes
match. The current AGENTS, README, implement/code-review/TDD guidance,
heuristics, shared review procedure, architectural/domain guidance, language
direction, glossary and ADR index match the previously assessed versions.
The three unchanged stock regression callers also match. Thus the retained
analysis still covers the original eight helpers, native adapter/launcher and
contract tests, validation controllers, recovery/comparison documents and full
checkpoint generator. The correction does not alter their exact pins, genuine
compiler behavior, owned paths, mode-bound records, isolation/resource rules,
or formal-acceptance boundaries. Formal sources, runtime binaries/caches,
historical evidence, tracker/status and review/provenance records remain
outside the authored-helper diff with their independent obligations.

The current manifest and aggregate were read completely and independently
hashed:

- `session/validation/native-toolchain-candidate-r10-043.json`: SHA256
  `37e14623d090f9bf6016132397fff42f4da4b7dc526b154348c4b15d59be0cba`.
- `session/validation/native-toolchain-candidate-validation-r10-043.json`:
  SHA256 `c0b89a23b1727f6e190019bc0f6f44dbc74a1259c2839d26e234f643bebdf874`.
- Coordinator dispatch identity receipt: SHA256
  `a733011a3323059c245fd84599a2b028b90a740ccf56eea984de727ddb3d73b6`.

The aggregate's source/mode maps match the manifest. These identity checks are
not new execution tests or a formal stock verification.

## DTP-003 — Medium — Fixed with review evidence

The reproducible-handoff defect was the checker recipe's appended Elan PATH:
the unchanged `scripts/test-check.py:372` calls bare `elan`, so an existing
earlier installation could override the just-verified executable. The corrected
`session/environment/RECOVER-ELAN-REGRESSIONS.md:114` uses
`PATH="$PFDS_ELAN_PACKAGE:$PATH"`. The following explanation identifies why the
order matters. The package supplies no Lean/Lake proxies, while the unchanged
native launcher still prepends its own compiler bin (`run-native-toolchain.py:138`)
and preserves the child's local `ELAN_HOME` and `ELAN_TOOLCHAIN`. No stock test,
timeout, compiler pin, profile, or validation controller changes.

I read the complete retained red and green records:

- `session/validation/elan-path-selection-red-r9-043.json`, SHA256
  `08a5bcf224750c9dfd154c571be36e1f2ae5fdb2fdb55d0712636c84df7682c3`.
- `session/validation/elan-path-selection-green-r10-043.json`, SHA256
  `07fca1d9243461884badf2f0e85e1ef00ef98f1cd795d9b8ab279d63431dff90`.

Their fixture source is identical and independently hashes to
`1f4d8e474c6fec2b783e0505a3bd3fe3b3e9a9408920bb6adc29c1f76fc4bc36`.
Both retain the same owned competing ambient entry. The actual command strings
differ only in PATH order. The green command's suffix exactly matches the
captured appendix block with only `python3 scripts/test-check.py` replaced by
the public selector probe. Document hashes bind the respective r9/r10 versions;
parsed stdout agrees with each record's observation.

The red run selected the owned ambient entry and exited 7 before invoking that
wrong executable. It did not manufacture a version response. The corrected
green run exited 0 and observed the verified package's real `elan` symlink,
resolving to its actual `elan-init`. It checked the official executable SHA256
`e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5`,
then invoked bare `elan --version` and bare `elan which lean` through the
effective child PATH. Those calls returned genuine Elan 4.2.4 and the custom
linked native wrapper. Invoking that selected wrapper reported Lean 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

This evidence addresses the exact selection interface missing in r9: the
verified executable wins despite the retained earlier ambient competitor,
and the ordinary selected compiler remains the pinned native wrapper. The
probe's independent expected path/hash/version assertions do not substitute
fixed output for the actual subprocess observations. The source correction
and matching evidence therefore close DTP-003 at its original Medium severity.
Neither record claims a stock-suite run or formal acceptance.

## Other retained findings and validation reuse

**DTP-001 — High — Fixed; no regression.** Full fresh execution, binding to the
actual stock record mode, and final verification without fresh/jobs flags are
unchanged. The focus override cannot change the fixed full/verify candidate.
The appendix continues to distinguish fresh private outputs from the ordinary
outputs needed for the negative-audit suite. The original r2 and matching r7
closure evidence remains applicable.

**DTP-002 — Medium — Fixed; no regression.** The public smoke tests' owned
temporary-parent creation and actual absent-parent evidence are unchanged.
The appendix's creation prerequisites/refusals and workspace-local setup are
unchanged. The PATH correction introduces no new cold-recovery prerequisite.

The aggregate records three successful syntax checks for the current shell
blocks. I independently confirmed that its first setup block and third suite
block are unchanged, and that the second block's only command change is PATH
order. The unchanged first block matches the genuinely executed cold r8 setup.
Its retained evidence SHA256 remains
`d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a`.
The original 18-file final identity/evidence receipt still hashes to
`0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206`.
These match the scoped reuse already assessed in r9. No unchanged cold setup,
compiler, metadata or controller check was repeated by this reviewer or
represented as newly executed on r10. R8 remains superseded before approval,
and historical failed or partial records remain intact.

**Applicable operational artifact validation is established.** No access or
evidence blocker remains for this operational candidate. The stock regression
suites still require their own genuine outcomes and setup; the public selector
probe does not run them. The dispatch records full901 as intentionally
interrupted with actual exit 130 and a retained partial record/interruption
sidecar, not build/audit success. Its module investigation, the signed-potential
candidate's own gates, prerequisite reviews, chapters and union coverage remain
separate. Nothing in this pass changes those states.

## Final outcome and freeze

| Spec finding | Original severity | Current disposition |
| --- | --- | --- |
| DTP-001 | High | Fixed with retained evidence; no regression |
| DTP-002 | Medium | Fixed with retained evidence; no regression |
| DTP-003 | Medium | Fixed by the exact r10 correction and matching red/green evidence |

**New findings: 0. Unresolved findings: 0. Worst unresolved severity: none.**
Spec outcome: **Passed**, on base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c` and candidate
`060e6b877b8db57a30f947b996b7dfe34a5401a1`, for the complete 19-file operational
scope and saved requirements. The parallel Standards identifiers and outcomes
remain separate; this report does not close findings on that axis.

This report is frozen when its SHA256 is sent to the coordinator. Root retains
responsibility for reading both complete outcomes, verifying final delivered
identity, and capturing/exposing/uploading the authorized recovery checkpoint.
