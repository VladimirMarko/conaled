# Direct/native toolchain — independent Standards continuation, r10-043

## Outcome and retained scope

**Passed** for the complete 19-file operational candidate
`060e6b877b8db57a30f947b996b7dfe34a5401a1`. **DTS-003 is fixed with evidence**
on this candidate. DTS-001 and DTS-002 remain fixed with their original
evidence and no regression. All three retain their original **Medium**
severity. There are **zero new findings, zero unresolved findings, and zero
evidence-access blockers**.

Reviewer: `/root/lean_native_path_options`, the same independent Standards
reviewer as r9. I authored none of the 19 scoped files. This continues the
existing loop; it is not another substantive review axis. Spec's finding and
outcome remain independent.

The complete source analysis, standards, six saved requirements, exclusions,
historical evidence and finding descriptions remain in
[the frozen r9 Standards report](direct-toolchain-standards-r9-043.md), SHA256
`b40654b0be536883a61ef62c1dd9dde10868ffd4b3fa9a9297f38212b7fb2a7b`.
That report assessed all 19 files and ended Findings-present. This continuation
retains its matching full-scope analysis and directly reviews the correction
and affected command-selection interface. It does not relabel r9 as passed.

| Identity | Exact value |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `060e6b877b8db57a30f947b996b7dfe34a5401a1` |
| Retained ref | `refs/pfds-review/native-toolchain-r10-043` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r10` |
| Full three-dot diff | 19 files, 3457 insertions |
| Commit | `060e6b8 docs(toolchain): select pinned Elan ahead of ambient PATH (#10000)` |
| Manifest SHA256 | `37e14623d090f9bf6016132397fff42f4da4b7dc526b154348c4b15d59be0cba` |
| Aggregate SHA256 | `c0b89a23b1727f6e190019bc0f6f44dbc74a1259c2839d26e234f643bebdf874` |

The manifest and aggregate are respectively
`session/validation/native-toolchain-candidate-r10-043.json` and
`session/validation/native-toolchain-candidate-validation-r10-043.json`.
I independently verified the clean isolated HEAD, ref, fixed merge base,
complete nonempty path set, all 19 committed/isolated/delivered SHA256 values,
and all 19 modes. The original 18 files are byte- and mode-identical to r9 and
the applicable approved r7 inputs. Only `RECOVER-ELAN-REGRESSIONS.md` differs
from r9; its new digest is
`39184174a0a2cdff195caf2515ab871584e14d67b35b19da3ee3a8c1c1b7d633`.
Both native validation scripts retain `100755`; all other scoped modes remain
`100644`.

I read the complete r10 dispatch and new retained review history. All six
requirement hashes match r9. Candidate guidance is unchanged: the only tree
delta is the appendix correction. The previously established AGENTS/README,
implementation, code-review, review-loop, TDD and applicable ADR guidance
therefore continues to apply. The user permits Nix-free exact tooling and
prefers native execution; all formal acceptance and durability requirements
remain unchanged.

## Findings and closure evidence

### DTS-001 — Required fresh route and mode-bound verification

**Medium; fixed with retained round-2 evidence, no regression in r10.** Both
controllers, their tests, and the recovery instructions are unchanged from
the complete r9 assessment. The stock fresh full command, mode-bound saved
record, native runtime distinction, and verify command without fresh/jobs
flags remain intact. Neither this documentation correction nor its selector
probe changes any full/focus/verify gate or grants a formal pass.

### DTS-002 — Cold-recovery temporary-parent creation

**Medium; fixed with retained round-2 evidence, no regression in r10.** The
smoke helpers and native fixture runner are unchanged, including creation of
their workspace-local temporary parents. Matching actual cold CLI/Lake
evidence, and the narrowly documented index reconciliation, remain applicable
on the same terms recorded in r9. No new build or repeated mechanical check
is needed to reassess this unchanged fix.

### DTS-003 — Selection of the verified Elan in the regression command

**Medium; fixed with actual r10 closure evidence.** The original finding was
that appending the verified package to ambient PATH left stock
`scripts/test-check.py` free to select an earlier bare `elan`. Absolute setup
checks did not exercise that later selection boundary.

At `session/environment/RECOVER-ELAN-REGRESSIONS.md:111–124`, the command now
uses `PATH="$PFDS_ELAN_PACKAGE:$PATH"`. Its explanation accurately states why
the verified package takes precedence and why it supplies no Lean/Lake proxies
that could replace the native launchers. The unchanged native helper prepends
its profile `bin`, leaving the verified Elan package ahead of ambient entries.
The stock test's bare `elan which lean` call remains unchanged. This addresses
the command-selection dependency without changing the stock test, compiler
pin, profile, timeout, or formal validation controller.

I read the complete retained red and green records and their embedded public
probe source:

| Record | SHA256 | Actual result |
| --- | --- | --- |
| `session/validation/elan-path-selection-red-r9-043.json` | `08a5bcf224750c9dfd154c571be36e1f2ae5fdb2fdb55d0712636c84df7682c3` | Exit 7; earlier owned ambient entry selected; wrong executable not invoked |
| `session/validation/elan-path-selection-green-r10-043.json` | `07fca1d9243461884badf2f0e85e1ef00ef98f1cd795d9b8ab279d63431dff90` | Exit 0; verified official Elan selected; real Elan/Lean results observed |

Both records retain the same fixture source, SHA256
`1f4d8e474c6fec2b783e0505a3bd3fe3b3e9a9408920bb6adc29c1f76fc4bc36`,
and the same earlier owned ambient executable entry. I independently compared
the complete recorded command strings: their only difference is the documented
PATH ordering. The green command's child environment and native-launch portion
match the actual r10 recipe exactly, with only the final suite entrypoint
replaced by the explicitly disclosed selector probe.

The owned ambient entry is a deliberate command-lookup fixture. In the red
case the probe stops before executing it; it does not fabricate Elan behavior.
In the green case the public bare lookup selects the package's genuine `elan`
entry, resolving to its `elan-init` binary. The record preserves its actual
SHA256 `e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5`,
real `elan --version` output `elan 4.2.4 (227caca13 2026-08-25)`, and real
`elan which lean`. The selected Lean path resolves to the intended native
profile. Executing that selected compiler reports Lean 4.35.0 with exact
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

This is relevant public-interface evidence for the specific selection defect,
using the actual native launcher and real Elan/compiler after selection. It
satisfies the AGENTS artifact-appropriate validation requirement and the
code-review rule that evidence coverage and inputs must match the claimed
behavior. The fixture observes the selection rather than replacing it. It is
sufficient to close DTS-003 and is not a stock regression-suite execution or
a proof/audit result. No stronger claim is necessary for this closure.

## Applicable evidence and limits

The r10 aggregate records three successful Bash syntax checks. I verified
that its linked red/green, prior cold setup, and original operational approval
record hashes match. The first setup block is byte-identical to the genuine
cold recipe retained in `native-toolchain-candidate-validation-r8-043.json`,
SHA256 `d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a`.
The third block is also unchanged. The changed second block has its new
effective-child selector evidence, so the earlier absolute-path setup success
is no longer being used to cover an untested lookup.

All original 18 helpers, modes and relevant source inputs remain unchanged.
Their complete r9 analysis and matching r7/r6/r2 evidence retain the same
scope and qualifications. The r7 final identity/approval record remains
`native-toolchain-final-verification-042.json`, SHA256
`0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206`.
The prior native adapter limits, genuine valid/false-proof checks, Lake build
and execution, eighteen metadata-contract cases, runner refusals, and recovery
checks are not relabeled as newly executed tests. The original failed,
superseded and partial records stay preserved.

I performed only read/hash/Git identity and retained-evidence inspection, and
wrote only this report. I ran no compiler, selector probe, test, build, audit,
verifier, network retrieval, protected-path operation, or process control;
I edited no source/runtime/controller and spawned no reviewer. No additional
actionable Standards issue emerged from the correction and affected interface.

The native full 901 run's intentional interruption and retained nonterminal
partial evidence are separate from this review. Its exit 130 does not establish
a full build or audit pass. The root's module-format probes, stock regression
suites, formal source reviews, prerequisite acceptance, final verification,
chapter completion and whole-union completion retain their independent
requirements and actual outcomes. This report does not depend on waiting for
those investigations or approve them.

## Final record

- **Standards outcome:** Passed.
- **Base and merge base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `060e6b877b8db57a30f947b996b7dfe34a5401a1`.
- **Full scope:** 19 files, 3457 insertions; original scope and exclusions retained.
- **DTS-001:** Medium, fixed with retained evidence; no regression.
- **DTS-002:** Medium, fixed with retained evidence; no regression.
- **DTS-003:** Medium, fixed with actual r10 source and red/green selection evidence.
- **New findings:** 0.
- **Unresolved findings:** 0.
- **Worst unresolved severity:** None.
- **Evidence-access blockers:** 0.
- **Acceptance boundary:** Operational Standards only; independent Spec and
  caller's final delivered-identity reconciliation remain necessary. No stock
  regression-suite, formal gate, chapter, or union acceptance is inferred.

This continuation is complete and frozen for r10-043. The r9 report and all
original finding severities/history remain intact; later changes require
their own matching candidate assessment.
