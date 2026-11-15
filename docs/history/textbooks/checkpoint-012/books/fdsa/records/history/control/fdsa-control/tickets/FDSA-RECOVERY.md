# FDSA-RECOVERY — Durable recovery checkpoints

State: active. Recurring cross-cutting obligation.

Create each checkpoint with `checkpoint.py`; upload it immediately and expose
the saved link. Each archive includes complete Git history, task source edits,
local tracker, governing request, source provenance, reviews, validation logs,
status and restore instructions. No dependency on previous checkpoints or the
chat history is allowed. Do not include downloaded book manuscripts or caches.

Checkpoint 0001 is saved and recovery-tested; see `../checkpoints.json` and
`../reviews/recovery-0001.md`. Its bundled history includes all refs. The initial
convenience restore script restored active work correctly but did not restore
all alternate ref names. The current script explicitly restores advertised refs
and removes clone-generated extras; that correction was tested by re-bundling.

Before acceptance checkpoints, preserve the final candidate verification JSON
and both independent review outcomes outside transient build directories.

## Optional recovery of expensive build state

The retained Standards reviewer assessed this narrow question in
`../reviews/build-cache-checkpoint-preflight.md` on 2026-11-02. Root adopted its
post-completion capture recommendation. A separate optional recovery artifact
may preserve normal project outputs, their original traces and complete
artifact families, together with exact source/toolchain/dependency origin.
The ordinary source/history/control checkpoint remains complete without it
and continues to exclude caches. No capture or restore has been implemented.

Wait for the active gate and all its output writers to finish. Existing log
lines or timestamps do not establish an immutable active-build subset. Do not
interrupt or mutate the gate to obtain a live snapshot. A failed or partial
historical build must remain labeled as such; no old verification record may
be installed as current acceptance. Any future restored state must still pass
the unchanged full guarded candidate command, exhaustive audit, final candidate
verification and applicable fresh/incident procedures. Read the complete
preflight before designing any capture or restore operation.

## Inactive working-copy recovery, 2026-11-02

Root independently rechecked and removed nineteen clean inactive draft copies.
Every exact branch/commit remains locally and in successful checkpoints0051/0052;
no project build outputs or shared packages were removed. Restore the needed
working copy using the recorded branch, then the ignored package link. See
`../provenance/inactive-worktree-storage-triage.md` and the completed removal JSON.
A normal Git removal left a deregistered directory tree; its zero-file/known
package-link residue was inspected before empty-directory cleanup. The original
error and exact subsequent outcomes remain in the record. Free space rose from
362147840 to 2057371648 bytes during the overall operation (concurrent build
writes mean this is an observed difference, not exact reclaimed allocation).

## Checkpoint0053 saved

The complete ordinary-merge draft is committed at 5f409e7 and included with all
refs and local tracking in conaled-fdsa-0053-ordinary-merge-draft.tar.gz.
Successful receipt: `libfile_7bebe01eeb0c8191b221356411b5863b`, 74124359 bytes,
SHA-256 `675ba3eb2caced3392855e78e01aa2a5f8689b166533080e8e4735e68257551e`.
This checkpoint also preserves the full completed inactive-worktree-removal
record. Its own receipt enters the next archive. No build-cache capture has
run while the C1 gate remains active.

## Checkpoint0054 saved before continuation

Full second-interruption evidence, the retained recovery disposition and
reviewed unexecuted helpers accompany all source refs/tickets in checkpoint0054.
Successful receipt: `libfile_ec03fe0e3c68819181acaad8bbc6e184`, 74506205 bytes,
SHA-256 `a8ebb8440a86730053538746e732d14febb63d661bd024376eba393a6294f0b2`.
The archive was exposed and saved before restarting the unchanged full gate.
Its own receipt enters the next archive. No optional build-cache archive exists.

## Additional duplicate removal before attempt3

The saved XM01 working copy was removed using normal Git worktree removal;
its exact5f409e7 branch remains and both0053/0054 receipts preserve the source.
The reappeared old recovery-test copy was independently compared, then root
rechecked all1570 source files against baseline Git blobs, all8 restored control
files, all14 extracted manifest entries and both identical bundles before
removing only that disposable directory. No Git-clean claim was made for its
absent restored metadata. The original checkpoint0001 archive and retained
recovery review remain, along with all source refs and all build/dependency
caches. Both completed action journals are in provenance/storage-recovery-pre-
attempt3-*.json and will enter the next archive.

The sole unchanged guarded attempt3 launched after the immediate identity and
no-writer checks at22:08:36. Its intent, recorder and log are separate from both
unknown prior attempts. No checkpoint receipt or historical outcome changed.

## Checkpoint0055 saved before XS01 source release

The complete source/history/control archive includes the frozen search scope,
all three stopped preflights and readiness, the clean original base, reviewed
attempt3 launch/prebuild evidence, both unknown prior outcomes, and completed
duplicate-removal records. Successful receipt:libfile_67c639b745dc8191804635de32bea2af,
74608516 bytes, SHA-256
`f3204d8ebf2ec73f4763f2e03620cc37061ae8180ed88da0b025bff89d998f79`.
It was exposed and saved immediately after creation. Its own receipt enters
the next archive. No optional build-cache capture or chapter acceptance.

## Saved source and scope checkpoints 0056–0058

Checkpoint0056 preserves the complete committed XS01 draft 863aedb. Checkpoint0057
preserves the complete frozen XT08 pre-code scope and author readiness before
the exact source release. Checkpoint0058 preserves the complete committed XT08
draft `7b8ab2bee299c937256bf9ce7e82977333d07134`, all retained refs, local tickets,
requirements, source assessments and historical validation evidence. Every
archive was exposed immediately after creation and successfully uploaded.
Their full receipts and identities are in
`provenance/checkpoint0056-save-receipt.json`,
`provenance/checkpoint0057-save-receipt.json` and
`provenance/checkpoint0058-save-receipt.json`,
with all 58 records retained in checkpoints.json.

Latest saved archive: conaled-fdsa-0058-leftmost-draft.tar.gz, 74,800,311 bytes,
SHA-256 `018f8340d00d5fb79f2ea21f71955506eaebe9147bf76047525f472d98ea14ad`,
Library identity `libfile_78ea82f15b5c819193387ff716e24906`. Its own receipt is
post-creation evidence and enters the next archive.

The bounded streaming content inspection is recorded in
provenance/checkpoint0058-content-check.json: 28,532 bytes /567 lines, SHA-256
`ed217c5b4a28b8a80834ac266a1c5b053bb3fb30d325524df6c0755c79d2b8ad`.
Root read the complete record. It reports no discrepancy across all 577
manifest payload checksums, the expected single root, the bundle header's 49
advertised refs and all 26 recorded task branch heads. The archived fixed XT08
scope, five source identities, original base, local ticket, prior receipt and
57-entry historical ledger are consistent. The actual saved 0058 receipt
postdates the archive as required. No Git object-pack decoding, extraction,
fresh checkout or end-to-end restore was performed by this bounded inspection.
The earlier tested recovery helper remains unchanged.

The archived C1 log is an exact 167,106-byte partial prefix, with both earlier
unknown outcomes retained and no terminal success or verification record.
No chapter or shared unit is accepted. Neither the content inspection nor an
uploaded archive substitutes for the required project and review gates.

A later read-only host observation at 2026-11-03 00:12:33 UTC again found the
same current C1 wrapper/checker/Lake and Lifecycle compiler on clean 07e480f,
with the same log prefix and no terminal or verification fields. Its separate
record is provenance/chapter01-attempt3-progress-after0058.json. This observation,
the updated handoff header, the 0058 receipt and content report enter the next
checkpoint. No build-cache capture or restore has been implemented.

## Unexecuted post-success capture proposal

The complete proposal is reviews/build-cache-capture-proposal.md, 24,922 bytes /
368 lines, SHA-256
`e4a2f57a418df2ff82728690b09d072f06337a51e87eff27121207640791b047`.
Root read it in full against the complete retained Standards preflight and
recorded the bounded disposition in build-cache-capture-proposal-assessment.md.
No concrete contradiction was found under its post-success, complete-family
and sustained-writer-hold conditions. Actual evidence and a reviewed concrete
procedure remain pending; no capture/helper/restore is released or performed.
The user's existing upload permission remains sufficient for any completed
recovery artifact. All C1 gates and the immediate acceptance checkpoint keep
priority; the optional artifact is unnecessary for source recovery.

## Checkpoint0059 — insertion readiness and current reconciliation

The new archive is saved successfully as
conaled-fdsa-0059-insertion-readiness.tar.gz: 74,858,995 bytes, SHA-256
`d90ce2805ccfe22deaf3ae3ef833b33e23cd10a44a3dfbf15c1ff2e696cc3326`,
saved identity `libfile_1e0f4e8ea7648191ba3c3ffff46cfe76`. It was exposed
immediately after creation and uploaded using the existing user permission.
The59-entry ledger preserves all earlier candidate/base/failure fields.
Its own receipt, provenance/checkpoint0059-save-receipt.json, postdates the
archive and belongs in the next checkpoint.

It saves all earlier source refs and controls, all three stopped/root-read
XI01 reports with the decision to defer thin insertion observations to active
Chapter2, the XT09 report-only task, current handoff documents, the optional
unexecuted capture proposal/assessment, and0058's receipt/content inspection.
The00:40:46 source/log observation and00:41:30 host reconciliation are both
preserved: a negative in-command process visibility observation was not a
termination result; the original wrapper/checker/Lake/LifecycleSafety process
identities were subsequently confirmed. No restart, new compiler or cache
intervention was taken. No chapter, appendix or shared unit is accepted.

The completed bounded0059 inspection is
provenance/checkpoint0059-content-check.json, 12,779 bytes /235 lines, SHA-256
`020ddf20d876f3abfed495cbb5d61cb1fc78362521fa99a720144ec337341043`.
Root read the complete record. All591 payload checksums match across647
members; names/root/types are safe, all49 bundle-header refs match0058, and
the complete XI01 identities, prior receipt and58-entry historical ledger
are retained. The bundle's packed bytes differ from0058, so no whole-pack
byte identity or object-pack decoding is claimed. The checkpoint helper's
original bundle verification succeeded.

The initial inspection exited1 at an overly strict assertion that an active
log must exactly equal the earlier observation. The archived log is167,226
bytes, SHA-25656eeb09e7b15d5edb999deda75ec47a36d568247971b16dbb177ae1da009e122:
its first167,163 bytes exactly match the00:41:30 observation, followed only
by successful LifecycleSafety completion. That initial inspection failure
and its corrected prefix comparison are retained in the result record. The
archive and validation evidence were not modified. No terminal result or
acceptance is inferred. The0059 receipt and content report enter the next
checkpoint; the source recovery helper remains unchanged.

A subsequent task-local read resolved the process-observation ambiguity.
provenance/chapter01-attempt3-process-reader-qualification.json records that
the original stat/cmdline reads succeed while the auxiliary children files
are unavailable. Root's broad exception handler conflated that auxiliary
read failure with whole-process absence. The earlier observations are kept;
the new record supplies the concrete qualification, without blaming Nix,
restarting the gate or replacing attempts1/2's separate historical evidence.
At00:48:39 the same wrapper/checker/Lake and new LifecycleProgress compiler
684574/start10042248 were present. The full gate remains pending.

Checkpoint0060 is created, immediately exposed and saved successfully:
74,913,995 bytes, SHA-256
`1044b9ec8d8f6bcb506fc6acf66932d035f065265fb86e25a8e84538652fd71f`,
saved identity `libfile_07029487567c8191810b2110d28d6c7b`, with local metadata
applied. The ledger now contains60 successful records, preserving every prior
field. Its own receipt enters the next archive. The saved state precedes source
release; no validation or acceptance follows from the checkpoint.

Checkpoint0061 is created, immediately exposed and saved successfully:
74,943,064 bytes, SHA-256
`75ecd431703cafa6f67592549d33a1d90bd420a0ee7a66214ee34ce6ed1cb3c2`,
saved identity `libfile_cb2ef4d52b78819194659207c77525fd`, with local metadata
applied. The ledger now contains61 successful records, preserving all prior
fields. Its own receipt enters the next archive. The saved source draft and
source assessments do not change any validation or acceptance status.

## Checkpoint0062 — logarithm scope before source authoring

conaled-fdsa-0062-logarithm-bounds-precode.tar.gz was created at01:57:42 UTC,
immediately exposed and saved successfully:75,025,250 bytes, SHA-256
`368087e29f70f92994996d30778b5136d811f3833a1f65dabd57dd5b7cae0aad`,
saved identity libfile_95ea6e348d80819193de7cf3d1db2c9d, with local metadata
applied. The62-entry ledger preserves every previous entry and field. Its
own1222-byte receipt (SHA-256
`3f333c4945bf0b6ae0a9c7a964be242d26f7bfe1c289c55ddaf53d02555539be`)
postdates the archive and enters the next checkpoint.

The archive preserves all source refs, frozen XL01 requirements/three final
reports and their corrected snapshots, clean original07e480f/readiness,0061
receipt/content inspection and the01:56:10 partial C1 observation. Its bounded
inspection passed at02:01:32 UTC; root read all180 result lines. All625 payload
checksums match across681 safe members; the self-contained v2 bundle retains
all51 prior refs and adds only the two logarithm original-base refs. Required
immutable control identities match, archived ledger61 ends at0061, and the
C1 log exactly matches the167418-byte observed prefix with no terminal fields.
There was no extraction, object-pack decode, new restore, compiler or cache
operation. The10173-byte content report has SHA-256
`37c799528469779c5c34a416d2ce1909c1fc0aa47b18e72ecd5349b2a0381a3e`.

After the saved pre-code boundary and immediate exact baseline recheck, the
separate XL01 source release occurred at02:02:33 UTC. That release and later
source edits belong to the next checkpoint;0062 itself contains the ready
pre-code state. No chapter, appendix or shared unit is accepted.

## Checkpoint0063 preparation — 2026-11-03

The complete stopped XL01 five-path draft is committed locally at
 a601ad713368daf8e18d5a5537a83d47138491fa (parent07e480f), so the all-ref
bundle captures it. The next self-contained archive includes all older refs,
source/tracker/history,0062 save receipt/content inspection, separate XL01
release and final source assessment records. The02:18:00 partial C1 observation
records FRP.Feedback completion and Reactive compilation under the same
original wrapper/checker/Lake identities; it is not terminal/full success.
All earlier actual failures and unknown outcomes remain. No cache artifact,
cache action, cleanup or GitHub write is part of this checkpoint.

## Checkpoint0063 saved — 2026-11-03

Created02:19:08 UTC; exposed immediately. Saved receipt recorded02:32:13 UTC:
libfile_e3b80e2e60d48191a50022f279b09afc,75,055,255 bytes,
SHA-2561ed33919b386923c37001ea91a4b60341393c52e4bb7ab46e789e40cfa2defec.
The first byte-transfer helper was blocked by explicit local dial-tcp operation-
not-permitted errors and reported zero transferred bytes; finalization had not
been requested. Exact owned transfer PID718822/start10629548 was terminated
after parent/argv checks, and the original helper collected a definite failed
item. A retry with permitted network access reused the same unchanged prepared
object/session; no second preparation was called and one finalization succeeded.
Its successful helper applied local identity. No C1 process/source/cache action.
The private transport details are not included in public control evidence.

All632 manifested payloads and53 refs passed closed-archive inspection. Root
read all226 lines; only the two XL01 refs advanced. The source bundle and local
tracking are self-contained. Receipt1,565 bytes SHA-256
d6fc2b91c80dd96846946d73638fed5386c0d3ff6ab3efbe5b1ddf33c95f5a4f;
inspection13,452 bytes SHA-256fd2fe2304ef934d9d7ece20e14121ca598220610d07d6507fdf1254db3169cce.
These records, upload-recovery evidence and later planning/log reads enter the
next checkpoint. No chapter, appendix or shared unit is accepted.

## Checkpoint0064 preparation — 2026-11-03

Next archive will preserve the three stopped C02-101 readiness reports, full
root assessment and identity/source/scope checks;0063 receipt/content check/
network-recovery evidence; root's complete1021-line log-prefix readback; latest
02:38:54 C1 partial observation; and all existing source refs/history/tracking.
No new source branch or implementation is selected. Current C1 is still the
sole validator, with ReactiveCompiler in progress and no terminal verification.
Archive creation/exposure/save does not accept any chapter or shared unit.

## Checkpoint0064 saved and inspected — 2026-11-03

Archive75,106,587 bytes,SHA-256e514f145a815321ce6c2c6ff34cc85855b3380832d9365ec315acd5f8b40f5ed,
saved as libfile_b6ab5a1795a08191850ba4d5e8ce6d7b; receipt recorded02:41:42 UTC.
All645 payload hashes, safe701-member archive and53 unchanged refs pass;
complete bundle72,305,027 bytes is byte-identical to0063. Root read the full
315-line inspection. The captured partial C1 log includes the expected1023
lines and one later ReactiveCompiler completion, for167645 bytes/1024 lines.
No full validation, terminal result or acceptance follows.

Own receipt2,086 bytes,SHA-25601e84fc67e33361dfced300127ecb3217c1a44878bf7297e1b83994779c9ebf4,
and content check18,590 bytes,SHA-2568056b171535c816189deff416f780a1781a5c1a2ceac70e6f6408156cf3efcb9,
postdate the archive and enter the next one. All prior ledger entries remain
unchanged. No cache or cleanup action, source/ref change or GitHub write ran.


## Checkpoint 0065 restored; 0066 recovery preparation — 2026-11-03

The user-attached 0065 archive is 75143952 bytes, SHA-256
`f9bf165a4561d0746373226b8825aee855ee734dbe4bb34c04ceff109d16b9a1`.
All 654 payload checksums pass. All 45 named refs are exactly restored; the
53 advertised heads comprise those refs plus eight duplicate object IDs for
HEAD/worktree heads. Every such object remains reachable from a retained ref.
The attached Library identity is recorded as attachment provenance, not as an
invented receipt for the original conversation's save.

0066 will capture the complete restored source/history/control, corrected
current handoff, original historical handoff snapshots, verified primary-source
retrieval, independent Chapter 1 recovery diagnostic and precise environment
blocker. No source, pin, review requirement or acceptance state is weakened.
The installer, portable binaries and copyrighted PDF are regenerable research/
bootstrap inputs and are not included in this source checkpoint.


## Checkpoint 0066 saved and inspected — 2026-11-03

conaled-fdsa-0066-workspace-recovery.tar.gz is saved as libfile_83054193060881919d15cb2bdcab1d9b.
Size 75201854 bytes; SHA-256 3dd83ee2d689536a0c65afec29e4974d979cce541ba93b24377e0b24a3e6abff.
All 667 payload checksums pass; all 45 original named refs are unchanged.
The self-contained bundle passes verification; its 47 advertised heads include
the retained named refs plus current main/review heads. The prior 64 ledger
entries are unchanged and the archive records attached checkpoint 0065 as
attachment provenance. No formal acceptance follows. The new save receipt
and closed-archive inspection postdate the archive and enter a future checkpoint.


## Checkpoint 0067 preparation — direct-toolchain exception

Preserve the user's explicit permission to omit Nix, verified official Lean
release identity, exact nine-dependency acquisition, actual smoke results and
source-confirmed `/proc/<own PID>/exe` startup blocker. Include the post-0066
receipt/content inspection and the complete existing Git history and local
tracking. No project source, pin, proof policy or mathematical scope changed.
The binaries and ignored dependency caches remain regenerable exclusions.


Checkpoint 0067 is saved as libfile_e4e5f5a888608191a42f300e3ac95d68, 75223020 bytes,
SHA-256 3b87c09192605c123a162bf4a9bdfb380936e0be3d1737cbb10c9c53688218f6. Closed-archive inspection passes.
Own receipt/inspection postdate the archive; no acceptance follows.

## Checkpoint 0081 preparation — current-host resource blocker

The exact attached 0080 was verified in memory. This host reports zero available
workspace bytes, so source restoration and compiler setup are deferred. A
bounded control-only successor preserves source.pack, every worktree payload,
all refs and native-kit files byte-for-byte while recording current user
steering, resource observations and corrected handoff text. Its original
restore_compact.py remains unchanged. The one external baseline asset retains
the same URL and exact byte/Git identities; no checkpoint chain is introduced.
No source validation, new review verdict, integration or formal acceptance is
claimed. Closed-archive byte comparison/hash checks precede immediate upload;
its save receipt necessarily postdates its creation.
