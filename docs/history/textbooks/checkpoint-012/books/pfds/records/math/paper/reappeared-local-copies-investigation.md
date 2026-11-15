# Reappeared historical local copies: bounded read-only investigation

Assessor: /root/obsolete_worktree_assessment.
Observation window: 2026-11-03, approximately 03:20:57–03:22 UTC.
The investigation was requested after root observed historical copies present
despite retained successful cleanup records. This report is the only file
written. No source, cache, ref, process, resource setting, cleanup record or
archive was changed. No compiler, stock hash subprocess, remote service or
unrelated account/file was accessed.

## Finding

The two historical Chapter 1 directories and checkpoint001 are currently
present. This is confirmed by direct reads and matching default/elevated
metadata observations, not inferred solely from a directory-size listing.

Every one of the 1,571 recorded source files in each directory has the same
size, SHA256 and modification time as the saved pre-removal inventory.
However, every recorded source file and both directory roots have different
inode identities and newer change times. The .git pointers have the same
bytes but new inode identities. There are no new source files or build outputs.

The observed checkpoint001 has the exact size and SHA256 of its saved identity
and of the file recorded removed in cleanup-r3 and cleanup-r6. Its current
presence conflicts with the retained local_copy_retained=false bookkeeping.
Checkpoint005 is the protected user-provided recovery archive and is expected
to remain. Checkpoints032,033,034 are absent, consistent with their cleanup
records. The three more recently removed candidate materializations remain
absent.

No explicit recreation of the two named historical directories or archive001
was found in the inspected task-owned scripts or records. The cause, actor and
mechanism of the discrepancy remain unknown. These observations do not identify
an active candidate source change.

## Retained cleanup evidence

The historical source cleanup record is
validation/obsolete-chapter01-source-cleanup.json, 1,499,472 bytes, SHA256
b05c8b237aebc5810158164088f87ccd3eff45da328fe75b140bf3ad9edf3349.

It records:

- created_utc 2026-11-03T02:58:17.474572+00:00.
- Both exact historical paths in removed; status finished.
- Empty process_users and refs_unchanged=true.
- Full pre-removal source hashes and filesystem identity tuples.
- Available bytes before 238,297,088 and after 419,590,144.
- Source preservation through saved checkpoint033 and the exact
  pfds/ch01-union reference at 1ce161412a2cfb725f27525ff98d400209163316.

The associated script, validation/reclaim-obsolete-chapter01-copies.py,
has SHA256 feb002f4d0ae8c68fa1f4515f6bda5c2206606bb9aef1add4caae3e73bd03e51.
It checks exact source bytes, saved refs and absence of process users, invokes
shutil.rmtree on each exact directory, appends that directory to the removal
record, and records unchanged refs and finished status. It has no recreation
path. It does not record a separate final timestamp or an independent delayed
absence observation; do not turn its created_utc field into an exact deletion
completion time.

Archive001 has two retained removal records:

| Record | Recorded UTC | Relevant scope |
| --- | --- | --- |
| redundant-checkpoint-cleanup-r3.json | 01:33:20.595695 | Saved exact archive duplicates001–004 |
| redundant-checkpoint-cleanup-r6.json | 02:51:30.972337 | Saved exact archive duplicates001 and032; already notes001 unexpectedly present despite the older flag |
| redundant-checkpoint-cleanup-r7.json | 03:09:48.931681 | Saved exact archive duplicates033 and034 |

All three records retain identities and sizes; r3/r6 do not retain a previous
inode identity for archive001. Therefore this investigation can compare its
current bytes to the removed archive identity but cannot prove an archive inode
change from those records.

Record SHA256s:

- r3: fcb141414c06c3f7d406199306f16059470fc38626c267e2ed1d486296df7417.
- r6: 264b6d02b3cb3a861a84f5004c638a427c96884c4baf7c2b0e946f9034acb4f2.
- r7: 89661f352673ae8f4eb411c2c3da3c4bb9d4cc326028fd4952fa29835f775efe.

## Complete historical-source comparison

At 03:21:26 UTC the assessor began reading every file named in the retained
pre-removal inventory. Each current file was checked for stable device, inode,
mode, link count, size, nanosecond modification time and change time before and
after reading; all captured identities were checked again at the end. Current
byte lengths and SHA256s matched every saved record. A complete tree walk found
only the expected source files and the historical .git pointer.

| Property | review-ch01 | review-ch01-r2 |
| --- | --- | --- |
| Historical candidate | 99340c79b9123e64f4b5cea313a8dbdf00af740c | cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833 |
| Recorded source files compared | 1,571 | 1,571 |
| Source files with identical size/SHA256 | 1,571 | 1,571 |
| Source files with identical mtime | 1,571 | 1,571 |
| Source files with the same device/inode pair | 0 | 0 |
| Source files with the same ctime | 0 | 0 |
| Source bytes | 87,452,094 | 87,452,613 |
| Files including .git | 1,572 | 1,572 |
| Extra paths beyond recorded source | .git only | .git only |
| Current allocated bytes | 91,668,480 | 91,672,576 |

Both roots are regular directories on observed device27, mode16877
(directory0755), link count10 and size4096. The root observations are:

| Field | review-ch01 before / now | review-ch01-r2 before / now |
| --- | --- | --- |
| Inode | 3432219 / 3562557 | 3432415 / 3561400 |
| mtime_ns | 1793586226364272501 / unchanged | 1793586539759185622 / unchanged |
| ctime_ns | 1793634310538569182 / 1793674713342540751 | 1793634310538569182 / 1793674713338540794 |
| Current root ctime UTC | 02:58:33.342541 | 02:58:33.338541 |
| Current source-file ctime UTC range | 02:58:33.182543–02:58:33.210542 | 02:58:33.158430–02:58:33.182543 |

These newer ctimes follow the cleanup record's created_utc value. A ctime is
filesystem metadata-change time, not a provenance record or reliable creation
time. The timestamp relationship alone does not establish what recreated or
rematerialized the paths, or when a successful deletion became visible elsewhere.

The .git pointers still refer to the absent administration directories
conaled/.git/worktrees/review-ch01 and
conaled/.git/worktrees/review-ch01-r2. The pointers themselves are:

| Property | review-ch01/.git | review-ch01-r2/.git |
| --- | --- | --- |
| Bytes | 75 | 78 |
| Prior / current inode | 3437467 / 3563546 | 3432342 / 3561969 |
| Current ctime_ns | 1793674713182542489 | 1793674713158542750 |
| SHA256, unchanged | 12d5135f44090c7d25f47e2752764d63ec76421179305370962c492e4b264a11 | 70db59a7899a71e55bcd136c9e75e156628bfe4272d2ad6af2431881f1a49902 |

The aggregate tracked-source digests still match the earlier assessor results:

- review-ch01: 52247c7a044064e4cb3f015339b205b9d005cb7031c1a002f11983fc93112ab7.
- review-ch01-r2: c71d7cffc0685921dd59cfae0ff424e4ac4dbdeffec47c90bba586db016083d5.

These digests use the recorded Git order and path, NUL, mode, NUL, SHA256,
newline. No current file changed while being read. There were no ordinary build
outputs in either tree. The small 4,096-byte allocation difference for the first
directory does not correspond to a file-content difference.

## Current checkpoint files

The checkpoints directory contains exactly the following two ordinary files
at the observed point:

| File | Bytes | Current device/inode | SHA256 |
| --- | ---: | --- | --- |
| conaled-pfds-checkpoint-001.tar.gz | 71,851,746 | 27 / 2252330 | f4db5d8f707399e597e94279dd5068d4a688d092f691b70a6dbd0b581bb40525 |
| conaled-pfds-checkpoint-005.tar.gz | 71,966,495 | 27 / 2281307 | 820c967ff0111dc8138d435ad991cea04fc8bca3964eb1db3711f9557f21326c |

Both entire files were hashed with stable before/after metadata. Their hashes
match the local checkpoint ledger. Archive001 has mtime_ns1793586036756011111
(2026-11-02T02:20:36.756011 UTC) and
ctime_ns1793674313598829049 (2026-11-03T02:51:53.598829 UTC).
Archive005 has mtime_ns1793589844739339422
(2026-11-02T03:24:04.739340 UTC) and ctime_ns1793589867195171380
(2026-11-02T03:24:27.195171 UTC). Archive005 was not a cleanup target.

No archive was opened for extraction, overwritten, uploaded or removed.
The inspection establishes current file identity, not a new recovery test.

## Default/elevated observation and surviving removals

The initial default metadata observation at 03:20:57.636477 UTC reported
551,915,520 free bytes. A separate authorized elevated read-only metadata
observation at 03:21:58.581763 UTC reported 548,139,008 free bytes.
The two observations returned the same complete identity tuples for both
historical directories, both .git pointers and archives001/005. At both points:

- review-ch01 and review-ch01-r2 existed.
- Archives001 and005 existed.
- Archives032,033,034 did not exist.
- validation-cache-counts, purity-correction and
  validation-persistent-accounting did not exist.

This rules out a current default/elevated disagreement for those measured
paths. It does not identify how the earlier deletion and later appearance
occurred. The different free-space samples were taken at different times while
authorized builds were active; no causal allocation claim is made.

The later candidate cleanup records remain intact:

- duplicate-candidate-materializations-cleanup.json SHA256
  e18974a6b564f39f398c0c3ebdbdb2b15bb4b1982a5ecbc54167b162eefc17bd,
  completed 03:17:45.803347 UTC, refs_unchanged and active_inputs_changed=false.
- duplicate-persistent-candidate-cleanup.json SHA256
  9f25e877426854b6ba600c4ea3e50ddc0297f880bf5c72857efa9f35f8e7e58d,
  completed 03:03:15.680204 UTC, refs_unchanged and
  active_inputs_changed=false.

Their named candidate paths remain absent. The recorded flags are attributed
to those cleanup records, not presented as a new exhaustive active-input audit.

## Search for an explicit task recreation

The assessor searched task-owned Python/shell scripts and relevant text records
under session for the two exact historical path names and archive001's name,
then inspected the matching cleanup code and records. Matches were historical
review locations, earlier source-accounting/cleanup notes, checkpoint identity
records, and the explicit removal script. No matching command or executed
recreation record was found.

The ordinary worktree-reclamation scripts contain restore_argv values built
with git worktree add, but those values are recovery instructions saved into
records. The inspected scripts execute git worktree remove, not their stored
restore commands. Those scripts do not target these two historical directories
for recreation.

The checkpoint writer, session/checkpoint.py (SHA256
617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab), was
inspected as the known archive-generation path. It creates a numbered archive
only when explicitly invoked for that number; its recovery self-test clones
the main repository into a new temporary destination. It has no instruction
to recreate these historical review directories. Its general ability to create
a numbered checkpoint is not evidence that checkpoint001 was regenerated.

This is a bounded search of retained task records, not an operating-system
audit log. It cannot exclude an unrecorded external action or identify an actor.
No host-wide or unrelated-account inspection was undertaken.

## Disposition

Preserve the discrepancy and exact observations. No additional deletion is
necessary for this investigation, and none was attempted. Do not rewrite the
older successful cleanup records or infer that their scripts silently failed.
Equally, do not claim an identified restoration mechanism from the new inodes
and preserved timestamps alone.

Within the inspected historical paths, all source contents remain identical to
their recorded pre-cleanup versions. No evidence here demonstrates a change to
the active body-counts or import-correction-r3 source. Those active source
closures were neither modified nor recursively audited by this investigation.
Their existing frozen-input checks and eventual terminal candidate gates remain
the appropriate evidence for their own integrity and acceptance.
