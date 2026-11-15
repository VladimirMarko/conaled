# Ordinary-output migration — independent Spec review, round 1

**Outcome: Passed for the captured operational helper scope.**

Unresolved Spec findings: **0**. Worst severity: **none**. This outcome does
not accept a Lean candidate, establish a real donor receipt, or authorize
execution before the separately required donor acceptance and live preflight.

Reviewer: `/root/output_migration_review/spec`, independently assigned by
`/root/output_migration_review`. The other axis's report was not read or used
to form this result. No implementation changes or additional tests were made.

## Fixed scope and evidence identities

- Fixed bounded and original integration base:
  `27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`.
- Candidate: `2748089840723943ddc8ae58acd82f5728b2098b`.
- Independently resolved merge base equals the fixed base.
- Comparison: `git diff 27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405...2748089840723943ddc8ae58acd82f5728b2098b`.
- Exactly one task commit, `2748089`, titled
  `chore(validation): capture bounded ordinary-output handoff (#10000)`.
- Exactly three added files, 1,340 lines, no exclusions or omitted task changes.

This is the explicitly supplied synthetic workspace layout: unchanged conaled
main is nested under `conaled`, and the three operational deliverables are under
`session`. This snapshot must not be merged into a formal source branch. I read
the complete captured helper, test suite and handoff using `git show`, then
independently checked that all delivered files still have the same hashes.

| Captured and delivered file | Bytes / lines | SHA256 |
| --- | --- | --- |
| `session/validation/migrate-accepted-outputs.py` | 35,242 / 677 | `6b6f17ec3f4001965eb8a27055e50770f9124676f2d1084f7488a2453cf5b60c` |
| `session/validation/test-output-migration.py` | 19,928 / 352 | `34e38d23006a05b7687b22c029fde3298d71422e3a085591a14a2851e1db401f` |
| `session/research/output-migration-implementation.md` | 19,501 / 311 | `3a9bb1730fed711af1fdb337e8f201c2b979f2a21e8e9e7db6535bb9bfe27f6f` |

The saved requirements are `requirements/output-migration.md` v1, SHA256
`ae064e2c3b4e528e5988cc9ed2a63ba0e90bff3b90893998dd01ef73c2b5d323`.
The complete design note has SHA256
`08d3cad5cc7cf01fd6ca35d699242ad74d6efa2370960f4dda80006e0ff9d197`.
Both identities were independently checked. The supplied dispatch, candidate
manifest, retained review record, complete design and implementation handoff
were read. There are no prior Spec findings in this first round to carry over.

I also inspected the relevant unchanged stock implementation: `lake_integrity.py`,
the entire `lake-output-hashes.lean`, candidate identity/record handling in
`scripts/check.py`, the earlier Chapter 2 warmer, and the existing full/focused
lock names. Their relevant basis hashes match the supplied identities:

| Basis | SHA256 |
| --- | --- |
| Stock `lake_integrity.py` | `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f` |
| Stock `lake-output-hashes.lean` | `fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b` |
| Stock `scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| Earlier `warm-chapter02-candidate-r3.py` | `886880d620a686b7a427d5e5015439e9898dbe22432dc2f693e407b6d15dd346` |

Applicable review guidance includes candidate `conaled/AGENTS.md`, the
`code-review` skill and shared review procedure, its concrete-consequence
heuristics, and README environment/build/audit and trusted-local-record limits.
There are no new Lean definitions or mathematical claims in this scope.

## Complete requirements assessment

### 1. Actual accepted donor and exact retained evidence

`run` validates the root-authored acceptance receipt before environment probes,
Git invocations, compiler invocations or output transfer. `validate_acceptance`
requires the exact source name and SHA, explicit accepted status, successful
terminal full and final command records, clean resulting head, the stock command
modes, and the saved verification record. It binds the final verification's
digest to the same saved and live `.lake/verification.json`, and checks the
documented timestamp order.

The strict receipt represents separate report arrays for Standards and Spec.
Entries require unique scopes within each axis, `Passed`, the exact candidate,
and separately hashed report references; the scope sets must match. The
implementation handoff explicitly requires root to preserve both 10013 and
10018 reports on each axis for the intended 901 donor.

This is deliberately a trusted acceptance receipt. The helper does not infer
which scopes root should have accepted from source history, interpret the text
of a report, or independently establish reviewer independence. Root remains
responsible for the complete actual acceptance decision, including all required
scopes and immediate final verification. That boundary is consistent with the
saved requirements and README; the helper does not advertise stronger evidence.
The positive two-scope fixture and the blocked, mismatched-scope, changed-report,
changed-final-digest and changed-live-record cases exercise the supported
metadata contract. No actual successful receipt has been fabricated.

### 2. Frozen exact candidates and existing coordination

Production obtains both established full/focused locks nonblocking, validates
exact clean source/target heads, rejects shared or nonregular project build
objects, compares pinned configuration, and checks clean Git-pinned dependency
identities against the accepted donor record. The compiler version must match
the accepted record and `lean-toolchain`; the CLI requires the Nix-shell marker,
one Lean thread and no compiler override, and removes caller `LEAN_PATH`.

`stable_scope` rechecks the plan, evidence, source verification, heads,
configuration, dependency identities, tracked inventory and visible process
users before batches and again after target verification. Its lock filenames
match the existing validation runners. Process inspection excludes the helper's
own launcher ancestry and documents its visible-process and cooperative-freeze
limits. It is not claimed to defeat a writer ignoring those rules.

### 3. Unchanged real verifier and separate fixture seam

Production pins the stock guard and hash-script contents, imports the unchanged
guard, validates its layout and calls its `expected_artifacts` and
`inspect_outputs`. The latter invokes the unchanged pinned Lake hash script,
which reads artifact bytes using `Lake.computeBinFileHash` rather than trusting
replaceable `.hash` sidecars. The helper calls no repair routine.

The public transport seam accepts test boundary functions, but the CLI exposes
no option to replace the real verifier. The fixture's opaque-byte verifier is
explicitly described as synthetic, and its success is not presented as a stock
hash result, candidate gate or proof audit.

### 4. Selection and whole-module ownership

`select_groups` retains the earlier warmer's identical-source/complete-output
selection, additionally requiring tracked source on both sides. It skips a whole
module when any target artifact, corresponding sidecar or trace is already
present. Selected input and output snapshots record private regular-file
identity, length and SHA256. Unsupported traces, missing described artifacts,
unexpected verifier errors or selected-file changes stop instead of repairing
or silently classifying a mismatch as acceptable.

The pre-existing-target fixture establishes preservation of the complete donor
group and its existing destination generation while another independent group
can transfer. This policy preserves the already focused target outputs.

### 5. Fixed batching and reserve

The group allocation estimate rounds file lengths to the target filesystem's
allocation unit and includes a directory allowance. A single complete group
over 64 MiB is rejected; `groups_in_batches` packs whole groups without exceeding
that fixed cap. Before copying a batch, measured free space must cover its
estimated allocation, at least 320 MiB reserve and the separate 32 MiB journal
allowance. The caller may increase the reserve but cannot lower it. A refused
batch is not silently shrunk or retried.

The test suite checks that insufficient headroom fails before any target output
is created and preserves all source bytes. This remains an operational space
check, not a guarantee against unrelated concurrent disk consumption. Root must
make a fresh actual measurement before execution; prior planning measurements
are not execution evidence.

### 6. Complete copies before durable verification

The helper hashes the selected source artifacts using the stock adapter before
transfer. Each group records described artifacts, optional sidecars and the
trace; the trace is placed last. Destination files are created exclusively,
synced along with their parent directory, and compared for length and SHA256.
Source snapshots are rechecked before and after copying each file.

After a complete batch is copied, the unchanged stock adapter independently
checks the target batch. Full scope, source snapshots and all target snapshots
are then rechecked. The complete `target-verified` manifest is appended and
fsynced before `source-retirement-started` and before the first source unlink.
There is no path from a source/target verifier failure to retirement. The
recorded source-verification and target-verification rejection fixtures test
these distinct boundaries.

### 7. Bounded retirement preserves the retained generation

Only captured source paths under the ordinary build root enter retirement.
Reversing the capture list removes the source trace first; its directory is
synced before remaining captured artifacts are removed. Every removal rechecks
the source snapshot and matching target snapshot. Affected source directories
are synced and each completed group is journaled.

Source code, pinned configuration, dependency outputs, generated setup files,
skipped groups and source verification records are outside that set. The
success fixture checks complete byte-identical target retention, source output
retirement and preservation of setup/verification files. No hardlink, reflink,
rename migration, whole-directory move or trace rewriting occurs.

### 8. Target acceptance stays separate

The helper refuses a target already carrying a verification record, never
copies that record, and labels both its journal and completion result with
`approval_copied: false` and `acceptance: false`. The handoff requires the
target's own unchanged full gate, exhaustive audit, verification record and
independent review workflow afterward. Identical module source and matching
output hashes do not by themselves prove compatibility with all changed target
dependencies; the preserved target gate and Lake input tracking retain that
responsibility. This matches the established ordinary-output reuse policy.

### 9. Failure and interruption handling

Journal creation is exclusive and its first record/directory entry is synced.
The fixed pair journal is never overwritten, even after a completed attempt.
The CLI also rejects an unfinished journal for the same target checkout when
the donor or target SHA in a proposed new plan has changed. Invalid or truncated
prior journals stop for manual reconciliation.

Before target verification succeeds, a copy or verification failure leaves the
complete failed-batch donor and diagnostic target partial. Earlier batches may
already have completed, as documented. During retirement the complete verified
target remains; ordinary exception records retain successfully removed paths.
An abrupt process death or unavailable journal space can leave less recorded
retirement detail than actual progress, but the already durable verified target
and fixed manifests support explicit reconciliation. The implementation makes
no automatic recovery inference or destructive retry.

The partial-copy test retains a partial sidecar and never publishes its trace.
The retirement-failure test removes exactly the first trace before the injected
sidecar failure, retains the whole verified target, and establishes that a
second attempt cannot overwrite its journal. The source-change test preserves
all donor paths while detecting the external change; it correctly does not
pretend to undo the external writer.

### 10. Meaningful disposable checks

I read all 15 tests and the complete recorded output. The suite covers success,
source rejection, target rejection, partial copy, retirement failure,
pre-existing target output, reserve refusal, source mutation, symlink refusal,
missing acceptance, matching independent scopes, several mismatched evidence
cases, strict plan/path/reserve parsing, unfinished-target journal refusal and
actual CLI rejection before an external runtime can be invoked.

The CLI refusal test uses a copied helper in a disposable workspace with an
empty `PATH`, and requires no output or migration journal. The suite does not
claim to exercise actual Nix/compiler/hash invocation, actual Git/dependency
preflight, real process visibility or power-loss recovery. Those limitations
are retained explicitly in the captured handoff; they do not masquerade as
successful checks.

### 11. Captured scope and applicable validation

The complete three-file scope has an immutable reachable base/candidate pair,
and the requirement/design identities are fixed outside the diff. Root's
isolated materialization tested the exact captured helper/test/report and stock
parser, then checked all inputs remained unchanged and matched delivered bytes.
I independently repeated the read-only content/identity comparisons and the
nonempty diff/merge-base checks; I did not rerun successful tests or execute any
production path.

The raw terminal evidence is:

| Evidence | Result / SHA256 |
| --- | --- |
| `validation/output-migration-r1-fixtures.json` | Finished, exit 0; `75c388bf059a5ca9ec909e6e792e2d14560a9158d1d32b992d13991b7e7baae7` |
| `validation/output-migration-r1-fixtures.log` | 15 tests, 0.576s, OK; `709b0b75f49755f12429f441ef49f4dc56ecac120b092090060105a8dee39e4c` |

No full Lean gate is attributed to these outside-repository Python and
documentation artifacts. The capture is already preserved in checkpoint 033
according to the supplied root handoff; that preservation is distinct from
this report's independent source review. Root must preserve this report and
verify delivered bytes still match before declaring helper readiness.

## Findings and limits

There are **no unresolved Spec findings**, and no earlier finding has been
discarded. No additional disposable fixture was necessary to resolve a concrete
remaining code concern. This review made no source, cache, Git-ref, tracker,
receipt, resource-limit or compiler change and ran no real helper, compiler,
hash subprocess, candidate gate or migration. Only this assigned report was
written.

The actual 901 donor's full acceptance remains outside this result. Before any
real run, root must complete that acceptance for both required scopes, create
an honest exact receipt, preserve the evidence, freeze both checkouts and
dependencies, and satisfy the real pinned-environment, lock, process and space
preflight. A real failure must retain its journal and both generations for
explicit reconciliation. The target must then pass its own required workflow.

**Final Spec outcome: Passed — 0 unresolved findings, worst severity none.**
Base `27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`; candidate
`2748089840723943ddc8ae58acd82f5728b2098b`; complete operational scope only.
