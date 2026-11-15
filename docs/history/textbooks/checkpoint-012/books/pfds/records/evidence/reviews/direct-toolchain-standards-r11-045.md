# Unified native integration recovery — Standards continuation r11-045

## Outcome

**Passed** on the complete 20-file operational candidate
`4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0`, against fixed base and merge base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. There are **zero new findings,
zero unresolved findings and zero evidence-access blockers**. DTS-001,
DTS-002 and DTS-003 retain their original Medium severities and their fixed
dispositions, with the applicability qualifications below.

Reviewer: `/root/operational_review/standards`. I authored none of the scoped
implementation, supplied kit, requirements or validation evidence. This is the
replacement independent Standards axis within the existing
`session/reviews/direct-toolchain.md` loop. Spec remains independent. The
coordinator and root retain their reconciliation and exact-delivery duties.

This outcome concerns operational tooling and recovery. It does not establish
a full project build, exhaustive proof audit, stock regression-suite result,
mathematical scope acceptance, Chapter 2 completion or completion of the
book/thesis union.

## Scope, standards and identity

| Item | Exact identity |
| --- | --- |
| Fixed base / merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0` |
| Previous operational candidate | `060e6b877b8db57a30f947b996b7dfe34a5401a1` |
| Retained ref | `refs/pfds-review/native-toolchain-r11-045` |
| Isolated checkout | `/workspace/scratch/09cf0de22282/pfds/review-native-toolchain-045-r11` |
| Full comparison | `git diff 76d77a1...4f15ff6`: 20 files, 3,805 insertions |
| Complete commit range | `060e6b8`, `4f15ff6` |
| Candidate manifest | `session/validation/native-toolchain-candidate-r11-045.json` |
| Manifest SHA-256 | `235eab36d688b059c8861bef0675accd04ee6ccc79e51f601d90b99adf88ffaa` |

I independently matched the candidate/ref, fixed merge base, clean isolated
HEAD, complete nonempty changed-path set, all 20 committed/isolated/delivered
content hashes, all committed modes and all eight requirement hashes. The two
native validation scripts retain mode `100755`; all other scoped files retain
`100644`. No formal source, checker or dependency pin appears in this diff.

Sixteen predecessor files are byte-identical. The four new or changed paths
are `session/checkpoint.py`, `session/validation/run-native-validation.py`,
`session/validation/test-native-validation.py`, and
`session/environment/RECOVER-INTEGRATION.md`. I read those complete candidate
files and the affected interfaces. I retain the matching full-scope analysis
of unchanged files in the complete r9 Standards report and its r10 correction
continuation, after checking their actual hashes and source applicability:

| Retained report | SHA-256 |
| --- | --- |
| `direct-toolchain-standards-r9-043.md` | `b40654b0be536883a61ef62c1dd9dde10868ffd4b3fa9a9297f38212b7fb2a7b` |
| `direct-toolchain-standards-r10-043.md` | `a616cf08f1176032ce5b901947f9ba6231ffac546d4206d83ed29874ad0a4500` |

This covers the original QEMU profile/launch/check helpers, original validation
controller, native adapter and contract fixtures, legacy native launcher,
environment recovery/comparison guidance and Elan appendix. Their earlier
results remain historical observations on their matching inputs; they are not
relabeled as checks of the new unified profile.

Applicable guidance is the candidate's AGENTS.md, README environment and
build/audit sections, code-review skill and heuristics, shared review-and-fix
procedure and TDD guidance. The saved requirements include the six retained
operational requirements, the common-candidate requirement from checkpoint 044
and `REQUEST-recovery-045.md`. The user's explicit Nix exception, local-only
tracking and newest selection of the supplied kit override conflicting older
operational defaults; they do not waive pins, honest evidence, isolation,
independent review or formal validation. The current request for small recovery
checkpoints permits the declared reproducible upstream prerequisite. It does
not permit dropping local work or an unfinished review base.

The agreed public controller/refusal and evidence-reader seams come from the
preserved common-candidate requirement. No additional seam confirmation was
needed. No Lean declaration changes, so mathematical statement review is not
an acceptance check for this operational diff. The formal scopes keep their
own statement-review obligations.

## Retained findings

### DTS-001 — Fresh route and mode-bound verification

**Medium; fixed, no regression.** The complete new controller still constructs
`./check.sh --candidate HEAD --fresh --jobs 1` for fresh full mode and preserves
the existing incremental full mode. Stock-record checking requires the exact
selected candidate and saved mode. Verification reads that mode and executes
`./check.sh --verify-candidate HEAD` without fresh/jobs flags. The parser
rejects `--fresh` outside full. The new runbook explicitly requires the fresh
baseline for the new runtime and distinguishes fresh temporary outputs from
ordinary outputs needed by later regression work.

The earlier closure is retained for the unchanged legacy route, while the new
scope-binding analysis and current fixture evidence cover the changed route.
No old full result is silently assigned to the new candidate or runtime.

### DTS-002 — Cold-recovery temporary-parent creation

**Medium; fixed, no regression.** The original smoke/helper files are unchanged,
including their temporary-parent creation. Their retained cold evidence remains
applicable to those files. The newly selected kit has its own actual successful
setup and ten expected smoke outcomes; it is not being justified solely by
the old runtime's cold tests. The new compact source restore also ran from a
fresh destination and genuinely succeeded.

### DTS-003 — Verified Elan precedence

**Medium; fixed for the retained legacy recipe, no regression.**
`RECOVER-ELAN-REGRESSIONS.md` and the corresponding legacy native launcher are
unchanged from r10. Its corrected package-before-ambient-PATH selection and
matching actual red/green evidence retain their original meaning. This is not
an assertion that the new unified runtime has completed all stock suites. The
new integration appendix expressly requires separately applicable regression
evidence and does not transfer the historical 901 suite results automatically.

## Changed controller and environment assessment

At `run-native-validation.py:32–39`, the fixed prerequisite remains 901 in
`import-correction-r3` with the legacy native runtime. Integration binds the
existing exact 3cf candidate to `validation-pfds-integration` and the distinct
`unified-native-kit` runtime. No full/verify path or SHA override is introduced.
The existing focus-only correction option remains separate, and the parser
refuses integration scope for focus.

At lines 204–265, stock and retained full evidence are bound to the selected
scope, exact candidate, checkout, runtime and recorded verification mode.
Legacy records with no new scope field can only be considered prerequisite
records. Success additionally requires the real terminal/result flags, clean
unchanged queued/start/final inputs, exact command, dependency and compiler
checks, and matching retained log/stock-record hashes. Before verification,
the current inputs and live stock record must match the successful full's
retained bytes; both are checked again afterward. These conditions preserve
the existing distinction between evidence and acceptance.

The new runtime path fixes the supplied kit's manifest hash, runs the kit's
verification, checks project pins and obtains its full bounded doctor result.
The captured identity includes profile configuration/hash, the runtime check,
selected environment fields and the supplied archive's identity. Only the
doctor's volatile free-space observation is removed from equality. The real
profile has fixed official compiler payloads, wrappers, adapter, loader and
runtime-source identities. The recorded absent `LEAN`, `LEAN_PATH`, inherited
preload and related stale selectors agree with the kit's outer environment.
Its single compiler-thread setting is preserved. These are trusted stable
workspace checks, not a claim of hermeticity or protection from hostile local
rewrites, consistent with the repository's stated verification boundary.

The child is launched directly using the same pinned kit
`environment(state, 1)` API as its ordinary command wrapper. The controller
records the actual argv and API-based provider. It does not claim to execute
`kit run`, which would create an extra process group. Direct
`Popen(..., start_new_session=True, env=child_environment)` keeps the stock
checker in the group owned by the existing cancellation path. The stock
checker and proof/audit commands are unchanged.

Every mode now obtains both existing nonblocking full/focus locks in one fixed
order. That excludes simultaneous full and focus controller workloads,
including a predecessor controller holding either legacy lock. It does not
claim to exclude unrelated external processes; the runbook explicitly retains
the coordinator's serial-writer obligation for setup, cache and compiler work.
The integration checkout and its project `.lake`/build directories must be
real private directories. The shared exact dependency store is still checked
separately and is not presented as the universal kit's private-package layout.

Exclusive record/log creation, exact source and dependency checks, terminal
status recording, atomic updates, log/verification retention and
`acceptance: false` remain intact. Interrupted or lost-terminal observations
remain distinguishable from successful full evidence. No source policy,
proof budget, linter, axiom policy or compiler check was weakened.

## Compact recovery assessment

The checkpoint generator declares the exact immutable public baseline
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. It retains current task heads and
review refs and requires each included head to descend from that baseline.
Its prerequisite bundle is verified and must list exactly that one baseline,
so an unexpected external dependency cannot silently enter the archive.
Unrelated historical remote-tracking refs are intentionally omitted. Local
source changes, relevant untracked files, complete session records and the
supplied native-kit archive remain captured.

The generated restorer verifies payload hashes before constructing a new
destination, fetches the exact baseline SHA at depth one from the original
remote or explicit local source, verifies the resolved SHA, verifies/unbundles
the task pack, restores exact refs and worktree/index patches, and disables
the push destination. It never substitutes the current upstream branch.
The README and new recovery appendix accurately disclose the external baseline
dependency and the offline local-repository alternative. They do not claim a
self-contained offline compiler, cache or upstream-source distribution.

The actual checkpoint 045 operation supplied the necessary positive recovery
evidence: its fresh destination first fetched only the exact baseline from the
local repository, then restored the task bundle. The generator checked source,
index/worktree/untracked content, task refs and unchanged session records before
publishing the archive. This test did not exercise a network fetch of the public
baseline, and I make no claim that it did. It did test the prerequisite-bundle
restoration path without relying on an already populated destination.

I independently inspected checkpoint 045's archive manifest and matched all
20 scoped source contents plus the complete supplied kit payload. Its declared
baseline and bundle-prerequisite list agree. The unchanged per-member checksum,
explicit ignored-artifact policy, credential-name refusals and capture-stability
checks remain in effect. No additional recoverability defect was established.

## Validation evidence and limits

The final aggregate is
`session/validation/native-toolchain-candidate-validation-r11-045.json`, SHA-256
`13a3a8ed9731235fa6c10cdc3692f2fd2ba7b478c70c66476ed6c0be60ad1b25`.
Its source candidate is unchanged; the later evidence additions preserve the
actual isolated test log and durable checkpoint-creation log identities.

| Evidence | Actual result and scope |
| --- | --- |
| Isolated current controller suite | Eight public refusal/selection/locking tests passed; log SHA-256 `8881c4c4e861231743eef0925acf5f500f4f03de5a3ede9c7e1efabbfc65e2ec` |
| Retained red/green logs | Scope parsing, cross-scope/wrong-candidate evidence and fixed-checkout/serial-lock behavior failed before their corrections and passed afterward |
| Current runtime identity checks | Two equal observations; intended cleaned selectors and single-thread environment checked; all 20 delivered/isolated source hashes matched |
| Documentation validation | Four new shell blocks passed syntax checks |
| Supplied environment setup | Actual exit 0; nine clean pins, 9,031 cache files and ten expected smoke outcomes, including genuine false-proof rejection |
| Checkpoint 045 restoration | Passed; archive 9,486,734 bytes, SHA-256 `8eb968d0ac3e5776b5d2a80075042c5cc552565cf3e8218eb5dc93f3938b771d` |

The setup summary SHA-256 is
`2346adeceaeaa5990785876457b0f427a9532672daf865056c6de6de087d3549`.
I matched all 48 retained setup artifact hashes to that summary. The actual
checkpoint creation log, now durably retained at
`session/validation/checkpoint045-create.log`, has SHA-256
`07a8b1e74c002e9dcb228c3cbbc0a5f0571485f604454a355d8ac61a7ef3edbe`.
The artifact suite's deliberately incomplete fixture records never constitute
a successful project gate. The first real common-candidate fresh build/audit
remains subsequent to operational approval and root's final identity check.

I performed only read-only source/Git/hash/archive/evidence inspection and wrote
this report. I ran no compiler, project hasher, build, audit, regression suite,
verifier, network retrieval or process-control command. I did not rerun passed
mechanical tests. No additional actionable Standards finding emerged from the
full scope or its new interactions.

## Final record

- **Standards:** Passed.
- **Base / merge base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0`.
- **Full scope:** 20 files, 3,805 insertions; 16 predecessor files unchanged.
- **DTS-001 / DTS-002 / DTS-003:** Medium, fixed with retained and current applicable evidence; no regression.
- **New / unresolved findings:** 0 / 0.
- **Worst unresolved severity:** None.
- **Evidence-access blockers:** 0.
- **Boundary:** operational Standards only; independent Spec, reconciliation and root's exact-delivery check remain separate. Formal acceptance is not established.

This report is complete for r11-045. Earlier reports, severities and incomplete
formal outcomes remain unchanged. Any source correction or different runtime
input requires an appropriately matched continuation.
