# Optional normal-project-output capture proposal

Date: 2026-11-03. **DESIGN ONLY — UNEXECUTED.**

This proposes a separate, optional preservation of the normal project output
families in `/workspace/scratch/845aa1048b05/conaled-ch01-review`, after the
already-required Chapter 1 validation and immediate candidate verification
finish and every relevant writer has finished. It implements no capture or
restore, changes no cache policy, and supplies no acceptance result. The
source/history/control checkpoint remains complete and recoverable without
this optional artifact. Its absence or failure must not block source recovery.

## 1. Authority, inputs, and present limits

The governing preflight is `reviews/build-cache-checkpoint-preflight.md`,
7,882 bytes / 129 lines, SHA-256
`a6840ce8192882bc3728301e6042de2154dbff48cdf56607497c24fd8b568a97`.
It permits separate preservation subject to origin, complete-family,
quiescence, and acceptance-separation conditions; it does not approve an
automatic transfer implementation. Its old-candidate status paragraph is
historical. This proposal conditionally targets the later repaired candidate
`07e480f6ec9958d4975bb90151005b84f2907614` only.

Repository policy and implementation were read from that exact commit using
read-only Git commands in the pinned Nix environment. Relevant sources are:

| Pinned source | Applicable statement or implementation |
|---|---|
| `AGENTS.md`, lines 21–39 | Planning starts no implementation loop; a later implementation retains the existing workflow, applicable checks, and independent Standards/Spec requirements. |
| `README.md`, Development environment; Build and audit; Proof and execution boundary | Stable isolated inputs, full guarded build/audit, candidate record check, no shared writable project build directory, existing fresh-mode obligations. |
| ADR 0001, `docs/adr/0001-modules-and-proof-dependencies.md` | Caches are excluded from the source deliverable. |
| ADR 0010, `docs/adr/0010-composition-and-proof-audit.md` | No arbitrary local binary imports bypassing Lake dependency tracking; the exhaustive audit remains required. |
| `docs/research/lake-output-cache-mismatch.md`, especially lines 87–161 | Complete transfer is a proposal needing explicit provenance/atomicity assumptions; output consistency does not authenticate compilation or make concurrent writers safe. |
| `docs/agents/lake-integrity-incidents.md` | Preserve original incident evidence before cleanup; preserve the guard and existing recovery rules. This report diagnoses no incident. |
| `docs/agents/review-loop.md`, especially lines 11–85 | Immutable review inputs, retained review axes, isolated validation, immediate candidate verification; reuse matching evidence without another review loop. |
| `scripts/check.py`, lines 235–310, 327–339 | Exact local inventory/targets, guarded incremental build, separately executed audit, and successful candidate-record production. |
| `scripts/lake_integrity.py`, lines 16–68, 101–117 | Supported layout, trace schema, described artifact extensions, and companion paths. Its inspecting/repairing functions were read, never invoked. |

The retained launch record `provenance/chapter01-repair-attempt3-launch.json`
is 1,119 bytes, SHA-256
`d0dca2de0e09cb23b05513ac8188fe1fa2df5750cf150c31d8914e2c0bb5607e`.
It records the launch at 2026-11-02 22:08:36 UTC. The stopped observation
`provenance/chapter01-attempt3-progress-before0058.json` is 3,509 bytes,
SHA-256 `965a74e5fa107de70f471948b74c35c42f0e634ea496c5be79a3486475f7c1d7`.
At its 23:59:29 UTC observation it recorded candidate `07e480f`, an empty Git
status, a running checker in `conaled-ch01-review`, no terminal fields, and
no verification record. These are historical, partial observations, not
present liveness checks or evidence that capture prerequisites now hold.

The prebuild record `provenance/chapter01-repair-attempt3-prebuild.json`
(SHA-256 `37c5101b7719b0022ecfc86725aba2521167f0171f2480ee4cbcc572f930380b`)
was consulted for its recorded compiler identity and build-announcement
fields, not treated as a completed-validation report. It records Lean
4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release,
`x86_64-unknown-linux-gnu`, and 960 planned project targets. The final target
list and terminal evidence must still be established by the existing gate.

No active output family was enumerated, opened, hashed, copied, or assessed
for this proposal. No live log, process, or filesystem-capacity observation
was used to infer completion. No missing terminal evidence is filled in by
the current source pin, a completed module message, or an earlier attempt.

## 2. Eligibility and the writer hold

This design selects the post-success case; it does not exercise the older
preflight's allowance for separately labeled failed/partial-build evidence.
All of the following must be recorded before capture is released:

1. **Terminal full validation.** Root has the real terminal exit status zero
   and complete log of the existing normal `./check.sh --candidate HEAD`
   invocation for `07e480f`. The post-build integrity pass, exhaustive audit,
   after-build candidate checks, and successful incremental verification
   record must have completed. A lost handle, absent status, or merely quiet
   process does not meet this condition. A fresh-mode success does not attest
   these normal output families.
2. **Existing immediate verification.** The already-required
   `./check.sh --verify-candidate HEAD` succeeds for the same candidate,
   compiler, dependencies, and incremental record. It checks record/input
   agreement, not output bytes or a new audit (`scripts/check.py`, lines
   223–232). Preserve its actual result separately. The original Chapter 1
   full-validation/final-review sequence takes priority: do not insert a
   long capture between its immediate verification and acceptance, or
   replace either review axis with this artifact. Let that sequence finish
   at its existing boundary before optional capture work occupies the checkout.
3. **All previous writers are finished.** The checker, Lake, compiler/audit
   children, any editor/LSP build activity, output hash-sidecar writers,
   background copy/recovery jobs, and other processes able to mutate this
   checkout's selected families have finished. Root accounts for descendant
   lifecycles and any independently launched writer; parent exit alone is
   insufficient. Do not interrupt the current gate or install locks to obtain
   this condition.
4. **No new writer is admitted.** Root uses its existing control of task and
   process launches to hold all new output writers, source/index/ref changes
   in the origin checkout, dependency/configuration changes, cache transfer,
   cleanup, and integration affecting the origin. Relevant contributors
   acknowledge the hold. The hold begins no later than the first origin/
   family read and lasts through archive closure, checksum/readback,
   completion-record publication, and final origin checks. No permission or
   lock changes to the live checkout are proposed.
5. **One stable origin remains.** The checkout is still clean at exact
   `07e480f`; its tree, tracked input files, dependency revisions and clean
   states, toolchain, compiler/Lake identity, and supported layout agree with
   the completed gate. Record these conditions before and after capture.
   These observations support the operational hold; they do not prove that
   no transient write occurred. If exclusive coordination cannot be established,
   defer the optional capture.

Unchanged size/mtime, matching repeated checksums, a trace's existence, and
completed-module log messages are neither the hold nor a substitute for it.
The assumption is operational exclusion of writers over the entire interval.
If a writer is needed for a Chapter 1 correction or revalidation, that work
takes priority and this `07e480f` capture is not started, or is abandoned
without promotion. A successor candidate is not silently substituted.

## 3. Exact origin and claims

The origin is the normal build directory of the one review checkout:
`/workspace/scratch/845aa1048b05/conaled-ch01-review/.lake/build`.
The proposed capture must not read another checkout's outputs as replacement
members or supplement its set from a dependency cache/private fresh build.
The development checkout used here for pinned source reads is not the origin.

Record the origin's absolute checkout path, commit and tree, source checkpoint
identity, checker/guard source identities, exact command and mode, clean-state
observations, compiler/Lake executable identities and version evidence, pinned
toolchain, dependency/configuration identities, and known retained cache
lineage. Actual Lake identification must be recorded; the Lean version or a
path alone is not a new independent observation of the Lake executable.

Use the description **“normal project output families observed after the
recorded successful `07e480f` incremental gate”**. Some outputs may have been
reused from earlier compatible work under the existing gate. Do not describe
every binary as newly compiled in attempt 3, relabel earlier-candidate builds
as new compilation, or erase uncertainty about historical production.
Original trace commands and paths remain byte-for-byte intact. Unexpected
origin evidence must be reported and resolved before promoting this capture;
do not rewrite a trace to make the origin description fit.

The ordinary source/history/control checkpoint supplies the actual source,
refs, patches, requirements, and validation/review history. The auxiliary
manifest references that checkpoint's exact identity but contains no new
source-of-truth Git history. Recovery of the source checkpoint does not
require the auxiliary artifact, an upload receipt for it, or build binaries.

## 4. Family selection from the pinned implementation

Select all local incremental build targets of the completed candidate, using
the inventory/coverage semantics of `scripts/check.py`, lines 235–279 and
292–305: root Lean sources plus `SquareKit`, `Applications`, and `Examples`,
with public import coverage and `ProofAudit` handled separately. The saved
prebuild count 960 is a cross-check, not a substitute for the exact module
list. Do not select “whatever `.olean` files exist,” a completed log prefix,
only expensive modules, or all of `.lake`.

`ProofAudit` is excluded from the saved incremental target list by the
checker; its source is executed anew after the post-build guard without
creating a trusted reusable audit result. Do not invent a required
`ProofAudit.olean` family or include one left by another mode as an acceptance
artifact. This makes the selection complete for the checker’s normal local
module targets, not for every possible Lake facet or file in the directory.

For a module name `N`, let `p` replace its dots with path separators. The
allowlist and paths come from the pinned adapter, never from an arbitrary
path embedded in a trace:

| Family member | Required original path or selection rule |
|---|---|
| Trace | `.lake/build/lib/lean/p.trace`; retain the entire original file. |
| `.olean` parts | `outputs.o`, one part if `outputs.m = false`, exactly three if true: `.olean`, `.olean.server`, `.olean.private`, all under `.lake/build/lib/lean/p`. |
| Interface output | `outputs.i` describes `.lake/build/lib/lean/p.ilean`. |
| Generated C | `outputs.c` describes `.lake/build/ir/p.c`. |
| IR signature and IR | `outputs.rs` → `.lake/build/lib/lean/p.ir.sig`; `outputs.r` → `.lake/build/lib/lean/p.ir`. Both are required for module-system traces; include either when otherwise described. |
| Bitcode and local archive | `outputs.b` → `.lake/build/ir/p.bc`; `outputs.l` → `.lake/build/ir/p.ltar`, when described. |
| Associated sidecars | Preserve every existing `member-path + ".hash"` for the selected trace/output members. Record original absence explicitly; do not create missing sidecars or infer output identity from them. |

The pinned parser requires schema `2025-09-10`, Boolean `outputs.m`, only
the keys `m,o,i,rs,r,c,b,l`, and described identities in the exact form of
16 lowercase hexadecimal characters followed by the corresponding extension.
Preserve those values without editing. All described outputs must exist as
readable regular files; the successful gate already performs its own actual
Lake-hash comparisons. This capture must not invoke the project's Lean hash
helper or repairing guard to obtain, “complete,” or repair a family.

A later capture implementation may reuse the parser's source-level rules,
but must not call `guard_outputs(..., repair=True)` or run a compiler. Its
selection/serialization behavior must be reviewed explicitly. Missing,
unsupported, duplicate, unsafe-path, unreadable, or changing required members
stop the proposed complete capture; do not silently skip the module, promote
an incomplete family, or fetch a substitute. Unknown trace extensions require
reassessment rather than a broad filename glob.

Preserve selected bytes and their original relative layout beneath one
archive payload prefix, for example `payload/.lake/build/...`; the prefix
does not rewrite paths inside traces. Record file type, byte count, mode and
original timestamp as provenance metadata. Timestamps convey no immutability
claim. Do not link the archive/staging files back into the source family,
rewrite sidecars, normalize trace text, or patch absolute command paths.
Do not follow a symlink outside the allowed origin or reinterpret an
unexpected symlink/special-file family as regular output; defer that case.

### Explicit exclusions

- `.lake/packages/**`, dependency sources/build caches, compiler/toolchain
  installations, and caches belonging to any other checkout.
- `.lake/fresh-check-*` and all other private fresh/reproduction/incident
  output directories. Fresh successes and their private bytes stay distinct.
- Active temporary/lock/partial files, package/build configuration caches,
  unrelated output facets and unselected modules. Native object/shared-library
  facets are outside this guard's scope (`lake-output-cache-mismatch.md`,
  lines 145–147). An undescribed `.ltar` is not included merely because its
  extension is recognized for other traces.
- `.lake/verification.json` at its active path, cached audit results, and any
  purported portable approval record. A finalized historical verification
  record and log may be copied under a separate `evidence/` prefix or retained
  by identity in the source/control checkpoint; neither is installed as current
  acceptance metadata by this capture.
- Source/Git contents already owned by the complete ordinary checkpoint,
  except compact origin metadata needed to identify the optional artifact.

Record these selection/exclusion rules in the manifest. This is a complete
set of selected trace-described families, not a byte-for-byte archive of
the entire existing `.lake` directory.

## 5. Proposed capture, checksums, and publication

The following sequence is a proposal for a later reviewed implementation;
none of its output reads or writes has been performed here.

1. Root records the fulfilled eligibility conditions and starts the writer
   hold. Allocate a unique destination outside every checkout/cache and outside
   the ordinary source archive. Confirm space for the proposed artifact and
   any transfer staging before starting; do not reclaim protected artifacts
   or change caches to make space.
2. Under the hold, derive and record the complete target/family manifest from
   the frozen source inventory and original traces. Record origin and
   exclusions. No generated files are copied into normal project paths.
3. Stream the allowlisted original files into a new, visibly incomplete
   auxiliary archive. Compute per-member SHA-256 and byte counts over the
   exact bytes serialized. Append the internal inventory manifest only after
   all selected members have been read successfully; its status still says
   readback/publication pending. Keep original traces
   and existing sidecars together with their outputs; there is no staging
   generation assembled from multiple capture attempts.
4. Close the archive and stream-read it without extraction, checking the
   unique root, exact member inventory, original relative paths, byte counts,
   hashes, absence of excluded/duplicate members, and family completeness.
   Retain the before/after origin and writer-hold checks. Any detected change
   or inability to account for writers prevents completion.
5. Compute the closed archive's SHA-256 and byte count; keep that outer digest
   in a separate completion record so there is no self-referential checksum.
   Only then rename the unique incomplete archive to its final artifact
   name, and atomically publish the separate completion record last. That
   record is the completion marker: interruption between the two publications
   leaves an archive without a successful capture record. Atomic publication
   does not make acquisition from a live filesystem atomic. The writer hold
   is what supplies the stable read window.
6. Release the hold only after complete publication/readback, recording that
   release separately without altering the archive or its completion record.
   A later durable upload, if separately authorized, refers to this immutable archive and its
   digest; an upload receipt is separate evidence of storage, not validation.
   No upload/restore helper is specified or authorized here.

The proposed internal manifest and external provenance records contain at
least the following. Facts established after archive closure, including
readback, the outer digest, and the hold's end, belong to external records;
they cannot be inserted retrospectively into the checksummed archive.

| Category | Required fields |
|---|---|
| Scope/status | Format/version, unique capture ID, optional normal-project-family scope, internal inventory status, external complete/aborted status, explicit non-acceptance qualification. |
| Origin | Checkout path, exact commit/tree, source-checkpoint identity, input/toolchain/Lake/dependency/configuration identities, normal incremental mode, known lineage and remaining provenance limits. |
| Eligibility | Actual full-gate/verification result identities and terminal times, writer-accounting evidence, hold owner/start, no-writer admission record and final origin observations; completion records that the hold is still active, with its later release recorded separately. |
| Selection | Exact module list, parser/schema/source identities, each original trace's digest, described extensions, present/absent sidecars, intentional exclusions. |
| Payload | Unique relative member path, original absolute origin mapping, regular-file type, size, SHA-256, original mode/timestamp; no replacement expected hashes. |
| Evidence | Historical logs/verification-record paths and digests outside the active acceptance path, clearly labeled historical. |
| Completion | Stream-readback outcome and any discrepancy; the separate outer record gives closed-archive size/digest and later storage receipt, if any. |

SHA-256 detects accidental transfer/serialization changes relative to the
recorded bytes. It does not authenticate the origin of a trace, establish
that its outputs were compiled from the declared source, defeat coordinated
metadata replacement, or turn old review/audit evidence into current approval.
The guard's shorter Lake hashes have their own documented trust limits.

## 6. Interruption and refusal behavior

If the capture is interrupted, runs out of space, loses the writer hold,
encounters an unsupported/missing member, or fails readback, leave it
unpublished and explicitly incomplete. Preserve the reason and any useful
partial-capture identity outside the cache. Do not publish a successful
completion record, successful-capture receipt, or reusable-cache claim. Root decides retention
or removal of only that capture's own incomplete destination; no source,
normal output, old checkpoint, incident evidence, or dependency is cleaned up.

Do not resume by appending fresh members to an earlier partial archive after
writers have resumed, combine different attempts, manufacture missing traces,
or repair mismatches in place. A later attempt needs a new stable interval
and unique destination after the same prerequisites are met. Failed or unknown
gate results remain preserved under the existing recovery workflow; this
proposal does not silently downgrade to capturing their output families.

## 7. Review and execution boundary

This document is bounded preparation, not implementation approval. The
existing Standards preflight supports the optional-artifact concept only.
Before any implementation or execution, root must resolve the concrete
procedure against these conditions and the cited policies within the retained
workflow. If a helper/tool change is commissioned, its exact source, selection
behavior, failure handling and evidence claims require the existing applicable
Standards and Spec review under `AGENTS.md` and `review-loop.md`; reuse retained
reviewers/evidence where their inputs match. Do not create an extra Chapter 1
final-review loop merely because this proposal exists.

Artifact-appropriate validation of a future helper should cover complete
synthetic families, module-system/optional parts, exclusions, missing evidence,
and interrupted publication, without consuming or modifying the live project
outputs. No such helper, fixture, runtime test, or source change is authorized
by this report. Before an actual capture, root must separately release the
specific quiescent origin and final reviewed procedure; permission to hold
writers already exists and does not require another user confirmation.

No restore implementation or new restore policy is proposed. The existing
preflight's restore boundary remains: source recovery first, isolated matching
inputs, unchanged Lake tracking/guards, the applicable full candidate gate
and immediate verification before acceptance, and existing fresh/incident
requirements where triggered. An archive checksum or saved success record
replaces none of them. No reuse success or performance saving is promised.

## 8. Outstanding facts and stopped-task record

The design has no identified policy contradiction under its stated stable
post-success assumptions. Execution is still unavailable: actual terminal
full-gate and immediate-verification evidence, finished-writer accounting,
the sustained hold, final origin/Lake identity, actual complete family set,
storage budget, and reviewed implementation/procedure remain to be supplied.
None is inferred from this report's source inspection. Unsupported trace or
filesystem evidence would be a concrete reason to defer, not relax conditions.

Only this proposal was written. No source, output, reference, cache, checker,
configuration, archive, helper, checkout, upload, or restore was created or
changed; no compiler, project hash helper, or output-integrity function ran.
All Chapter 1 validation and final-review decisions remain with root.

### Pinned policy and implementation identities

All repository rows below are at `07e480f6ec9958d4975bb90151005b84f2907614`.

| File | SHA-256 |
|---|---|
| `AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `README.md` | `85d09c317be36c015927e948a379cdc7a11c2a8ec8ad6268cbd61708d5e11216` |
| ADR 0001 | `83226e2d3ceb121348c97840026287a36fadaf638301b80ed9255383e322cae2` |
| ADR 0010 | `f76abfe4fafa7908a5f1605c8ffe9f717430ab0831682f74cc8c734a248c3fb8` |
| `lake-output-cache-mismatch.md` | `ff8090ec9d2d6b6c94cf94c9bc6dd66bff99c057e25ee0e8d807fae3d3770093` |
| `lake-integrity-incidents.md` | `af2791fe85d0f559356a73899c02a61dd4012599e3ae70b203c14e27483d4b11` |
| `review-loop.md` | `0561fafdb97423533dd3d85ba71ab89b09c4e148c1312035846fdf80be45e64c` |
| `scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| `scripts/lake_integrity.py` | `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f` |
| `check.sh` | `d4a16262232c26dd48191217c1113cbbeda7dbc8ea0826505ca1bf767d0f8acd` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f` |
| `lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |

The manifest pins Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Batteries to
`66e469188fe07963e5cf666c7d4433f45b8131c5`; all nine dependency pins, not only
these two, are conditional capture inputs. Their actual post-gate clean
identities must match the existing candidate verification. The source pin
does not substitute for that terminal evidence.
