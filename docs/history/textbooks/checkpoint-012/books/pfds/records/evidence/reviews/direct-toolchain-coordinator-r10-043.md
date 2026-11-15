# Operational toolchain — coordinator reconciliation, r10-043

## Outcome

**The complete operational-toolchain review passes on candidate
`060e6b877b8db57a30f947b996b7dfe34a5401a1`.** Both independent axes completed
the full 19-file scope and closed their respective Medium 003 finding using the
exact PATH correction and genuine public-selector evidence. There are no new or
unresolved operational findings and no evidence-access blockers.

The coordinator read both complete continuation reports and their retained r9
assessments. Final read-only identity at
`2026-11-03T18:18:29.390442+00:00` matched the clean exact candidate/ref/base,
all 19 committed/isolated/delivered contents and modes, six saved requirements
and eleven report/evidence identities. Root retains responsibility for its
immediate final delivered-identity receipt and checkpoint 043 capture/upload.

Coordinator: `/root/direct_toolchain_validation_plan`, continuing the existing
loop in `session/reviews/direct-toolchain.md`. My earlier original-runner
authorship was disclosed. I performed coordination and identity reconciliation,
with no third Standards or Spec review and no runtime/test/build/network action.

## Immutable scope and independent outcomes

| Identity | Value |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `060e6b877b8db57a30f947b996b7dfe34a5401a1` |
| Ref | `refs/pfds-review/native-toolchain-r10-043` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r10` |
| Complete task diff | 19 files, 3,457 insertions; one snapshot commit |
| Manifest SHA256 | `37e14623d090f9bf6016132397fff42f4da4b7dc526b154348c4b15d59be0cba` |
| Aggregate SHA256 | `c0b89a23b1727f6e190019bc0f6f44dbc74a1259c2839d26e234f643bebdf874` |

The manifest is `session/validation/native-toolchain-candidate-r10-043.json`;
the artifact aggregate is
`session/validation/native-toolchain-candidate-validation-r10-043.json`.
The full comparison is the three-dot diff from the fixed base above to the
candidate. Relative to r9 `ff3f709723e5c49e5ba40798abbed7d36141a6fb`, only
`session/environment/RECOVER-ELAN-REGRESSIONS.md` changes: the real Elan directory
is prepended to ambient PATH, with the adjacent explanation corrected. All
original 18 contents and all 19 modes match their earlier reviewed identities.

The same independent reviewers continue. Neither authored scoped implementation
or the appendix/recipe. Each independently matched the whole source scope,
requirements, guidance and evidence, retained the complete r9 analysis, and
directly inspected the correction and affected interfaces. Their concise reports
incorporate those frozen full-scope assessments, as permitted by the shared
review procedure. No acceptance scope was narrowed to the changed line.

| Axis | Reviewer | Outcome | New / unresolved | Worst unresolved |
| --- | --- | --- | ---: | --- |
| Standards | `/root/lean_native_path_options` | Passed | 0 / 0 | None |
| Spec | `/root/chapter02_continuation_plan` | Passed | 0 / 0 | None |

| Complete frozen report | Bytes | SHA256 |
| --- | ---: | --- |
| `session/reviews/direct-toolchain-standards-r10-043.md` | 10,429 | `a616cf08f1176032ce5b901947f9ba6231ffac546d4206d83ed29874ad0a4500` |
| `session/reviews/direct-toolchain-spec-r10-043.md` | 10,046 | `d7dfee97019b9df1f61e59ba2b9951f750fe235faa2290b87dca2f341a3e91d0` |

Both complete reports were read before this reconciliation. Neither axis's
finding or severity is merged with the other. The r9 reports retain their
Findings-present outcomes; this new approval applies only to corrected r10.

## Finding dispositions and actual correction evidence

| Axis / ID | Original severity | R10 disposition |
| --- | --- | --- |
| Standards DTS-001 | Medium | Fixed with retained fresh-route/mode-bound evidence; no regression |
| Standards DTS-002 | Medium | Fixed with retained cold temporary-parent evidence; no regression |
| Standards DTS-003 | Medium | Fixed by r10 selector correction and actual red/green evidence |
| Spec DTP-001 | High | Fixed with retained fresh-route/mode-bound evidence; no regression |
| Spec DTP-002 | Medium | Fixed with retained cold temporary-parent evidence; no regression |
| Spec DTP-003 | Medium | Fixed by r10 selector correction and actual red/green evidence |

The appendix now uses `PATH="$PFDS_ELAN_PACKAGE:$PATH"`. The unchanged native
launcher prepends its compiler bin, which contains no Elan, so the verified
Elan package remains ahead of ambient entries for the stock test's bare lookup.
The genuine package contains no Lean/Lake proxies. Child-local Elan state and
selection remain unchanged, as do stock scripts, compiler pins, profile,
timeouts and formal validation controllers.

Both axes independently checked the complete red and green records and their
embedded identical probe source. The recorded commands differ only in PATH
order. The green command matches the corrected document's child environment
and native launcher, with only the final suite entrypoint replaced by the
explicit public selector probe. The same owned competing ambient entry remains
present in both cases.

- Red record: `session/validation/elan-path-selection-red-r9-043.json`, SHA256
  `08a5bcf224750c9dfd154c571be36e1f2ae5fdb2fdb55d0712636c84df7682c3`.
  It exits with code 7 after observing the wrong ambient entry, before invoking it.
- Green record: `session/validation/elan-path-selection-green-r10-043.json`,
  SHA256 `07fca1d9243461884badf2f0e85e1ef00ef98f1cd795d9b8ab279d63431dff90`.
  It exits with code 0, selects the official executable, checks its actual digest, invokes
  genuine bare `elan --version` and `elan which lean`, and invokes the selected
  native Lean wrapper to observe version 4.35.0 and exact compiler commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The observed real Elan is 4.2.4 with binary SHA256
`e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5`.
The fixture observes command selection and actual subprocess output; it does
not manufacture version/proof output. Both independent axes found this evidence
sufficient for their respective 003 finding. Neither describes it as execution
of a stock regression suite or a formal proof/audit result.

## Evidence reuse and requirements

The aggregate records successful syntax checks for all three current shell
blocks. The first setup block is identical to the genuinely executed r8 cold
recipe, and the third block is unchanged. The changed second block has the new
effective-child evidence. The retained actual r8 setup aggregate remains
`native-toolchain-candidate-validation-r8-043.json`, SHA256
`d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a`.

All original 18 files, modes and relevant helper/runtime inputs match their
approved r7 identities. The prior complete r9 analysis and explicit r7/r6/r2
artifact evidence retain their documented scope and limitations, including
genuine valid/false proof, Lake, native metadata-contract, controller-refusal
and recovery results. The r7 final receipt remains SHA256
`0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206`.
The reviewers did not repeat matching checks, relabel old commands as r10
executions, or convert superseded/failed/partial history into approval.

All six saved requirements and applicable guidance match the retained versions.
The user permits exact tooling without Nix and requests native execution and
reproducible recovery. That exception does not waive pins, genuine behavior,
source policy, local tracking, durable checkpoints, isolated formal checks,
audits, independent formal review or final verification. Original chapter order
and book/thesis union scope remain unchanged.

## Final identity, freeze and formal boundary

The final read-only receipt is
`session/validation/native-toolchain-coordinator-identity-r10-043.json`, SHA256
`36b61afbfc12302ca11d84ada1a8dacf3dea841ce625dde1c5a55774a13b2df1`.
At `2026-11-03T18:18:29.390442+00:00`, every expected identity matched and
the checkout was clean. This is coordinator delivery-identity evidence, not a
stock verifier invocation. Root's separate final receipt is still root-owned.
The only coordinator writes are assigned dispatch, identity, reconciliation
and retained-review records. Reviewers wrote only their assigned reports.

The full r10 operational review is complete and frozen for checkpoint 043.
Any later implementation change requires a new applicable candidate assessment
within this same loop; this outcome approves no moving tip.

The prior native full 901 was intentionally interrupted, with actual tool exit 130,
its original partial/nonterminal wrapper record and log preserved, and a separate
sidecar. It supplies no full/audit pass. Root's module-format/performance probes
and serial stock regression runs retain their actual separate outcomes. Neither
those investigations nor this operational pass closes prerequisite10013/10018,
signed-potential10023's own full/audit/record/final-verification requirement, a
chapter, or the book/thesis union. Formal acceptance remains pending its own
complete genuine evidence and reviews.
