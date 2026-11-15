# Duplicate inactive candidate materializations: read-only assessment

Assessor: /root/obsolete_worktree_assessment. Task assigned by root under the
existing local recovery/validation work. Final fresh output comparison ended
2026-11-03T03:14:57.061555+00:00. This report is the only file written by this
assessment. No removal, output transfer, compiler, stock hash subprocess, Git
mutation, remote access, resource change, or acceptance action occurred.

## Result and scope

Both inspected checkouts are clean at their exact retained branch tips. Every
complete ordinary output, sidecar and trace is byte-identical to a currently
retained private copy in body-counts and matches its original warming manifest.
Every tracked source/configuration file matches its Git blob. There are no
unique source files, approval records, complete ordinary output groups, or
generated setup files in these two materializations.

Two kinds of small generated/control files are not identical to body-counts:
each worktree's .git pointer and a Python bytecode cache for the unchanged stock
guard. These are explicitly identified below, not silently classified as
byte-identical duplicates. The shared package target is a symlink and was not
traversed or included in reclaimable allocation.

| Candidate materialization | Exact HEAD | Retained branch |
| --- | --- | --- |
| validation-cache-counts | 3dd930c3e3989f3e5530463f3ac937a629551335 | refs/heads/pfds/cache-counts-review-r1 |
| purity-correction | 361f5f3f6bb3de1974510ce355883dac2bf25333 | refs/heads/pfds/pure-suspensions-review-r2 |

Both candidates are ancestors of the final observed body-counts HEAD
6971fd2a9647d077594ad66f24b5d0f29641cc5b, with branch refs/heads/pfds/body-counts.
This ancestry was checked with ordinary read-only Git commands. Neither
candidate has .lake/verification.json; neither is accepted by this assessment.

| Measure | validation-cache-counts | purity-correction |
| --- | ---: | ---: |
| Complete ordinary module groups | 116 | 69 |
| Complete ordinary files, including sidecars and traces | 812 | 483 |
| Complete ordinary logical bytes | 87,102,765 | 65,698,972 |
| Complete ordinary file allocation | 89,501,696 | 67,117,056 |
| Entire .lake/build allocation, including directories | 89,645,056 | 67,215,360 |
| Tracked blobs compared against exact Git objects | 1,706 | 1,695 |
| Tracked source/configuration logical bytes | 88,739,702 | 88,650,680 |
| Entire materialization allocation, excluding shared package target | 182,927,360 | 160,374,784 |

Combined allocation is 343,302,144 bytes. This is an observed filesystem
allocation, not a guarantee of exactly that much free space after cleanup:
other active builds can allocate concurrently. The 69-group purity output set,
including every recorded file identity, is a subset of the 116-group cache-count
set. Both sets are also subsets of the retained body-counts warming manifest.
No output relocation is necessary to preserve these ordinary outputs at the
observed point.

## Exact comparison method and target update

The first complete inventory ended at 2026-11-03T03:14:03.824121+00:00, with
body-counts at cf3a9750ded32e9f876556794518771a6e92e882. Root then reported the
finished focused-r3 failure and a new isolated tactic-scheduling correction.
The assessor resolved the new full HEAD and independently confirmed that the
entire cf3-to-6971 endpoint difference is only
Examples/SuspensionPureBodyCounts.lean. This is a new 10022 client outside both
older module/output sets.

The assessor therefore repeated every older output, corresponding module-source
and nine configuration-file comparison against the new exact target
6971fd2a9647d077594ad66f24b5d0f29641cc5b. That fresh comparison ended at
03:14:57.061555 UTC. The target was clean and retained the same HEAD throughout
that second comparison. This report does not claim that the whole target
remained at cf3 throughout the assessment.

The stock Python guard was read and imported with Python bytecode generation
disabled. Only its nonmutating validate_layout and expected_artifacts functions
were called. Its SHA256 was
293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f.
No inspect_outputs, guard_outputs, Lean adapter, compiler, repair, or other
external hash subprocess was invoked.

For each inactive checkout the assessor:

1. Required the exact HEAD, named branch and clean complete porcelain status.
2. Enumerated every saved trace in the private project build, used the unchanged
   parser to enumerate its required output files, and included each present
   corresponding .hash sidecar and the trace itself.
3. Required the resulting module and file sets to equal the complete historical
   warming manifest, without missing or additional groups.
4. Read each source and body-counts file, compared complete bytes, and checked
   its size and SHA256 against the historical copied-file manifest. Also
   required those identities to equal the body-counts warming manifest.
5. Compared the corresponding 116 or 69 Lean source files and the nine pinned
   configuration/tooling files against body-counts. Required the target's
   parsed trace output identities to equal those of the older checkout.
6. Compared every tracked source blob against git cat-file --batch output,
   including executable-mode agreement. Every tracked object was an ordinary
   regular file with link count one; no tracked bytes differed.
7. Walked each checkout without following symlinks, accounting for every file
   outside tracked source and complete outputs. The exhaustive extras are below.
8. Required each read file's device, inode, mode, link count, size, nanosecond
   modification time and change time to remain stable during its read and at
   the end of the comparison. Rechecked exact clean candidate identities.

All captured inputs and outputs were stable. There were zero differing or
missing tracked blobs, mismatched complete output bytes, parser failures,
additional build files, or unexpected nonregular filesystem objects.
This demonstrates observed byte identity; it does not replace stock hash
verification or a candidate's own full build and exhaustive proof audit.

## Retained per-file manifests

The existing warming records contain the full per-file paths, sizes and SHA256s.
All listed entries were checked against both current copies; those records were
not modified.

| Record under session/validation | SHA256 |
| --- | --- |
| pure-cache-counts-focused-output-copy.json | 733e35fe7b78f20d868ded691291d0899047005d5ba48df4e29a734359cc918c |
| pure-suspension-r2-focused-output-copy.json | 633e6cfcfd68d2d4ef92f38858cf83aa4295480b02a0aeca39438f5a37813ccf |
| body-entry-counts-focused-output-copy.json | 6f3372f17f70d1cec330546ae20cedccb12bb6fdd562c6ea9d53d3f28ac3ccf1 |

The first record preserves 116 groups / 812 files / 87,102,765 bytes at 3dd.
The second preserves 69 groups / 483 files / 65,698,972 bytes, copied from the
older ea8 candidate into the exact 361 documentation correction. The third
preserves 125 groups / 875 files / 89,351,399 bytes copied from 577 into the
body-counts baseline; current subset equality was freshly checked rather than
inferred solely from that historical record.

Additional aggregate identities:

| Inventory | validation-cache-counts SHA256 | purity-correction SHA256 |
| --- | --- | --- |
| Sorted complete ordinary output file inventory | 58afd57649a960a131268c6e3c2296165972c5048fb13344e5b81c8f101931e9 | 05a4630e286c8a2d60638e074aa8abe4a5f4efb4a7ca14a44f6c2fe553a65cb1 |
| Sorted corresponding module-source inventory | d06438d7b4df01fe58cec5438caa6858dc27c409f51232dd637e49b75fcb2468 | c1a1e0cc8f7f122ccb17f98984923dcbca10edc1fb4c23cd0b87e7768ba61a0b |
| Entire tracked Git-ordered source inventory | bd8ad8c114d75b42ae1bcc018c47f1a2a79bf5d06be571e495ee357857be235e | 711f927011b47bbe7489312d31409a8b8d8a293166eb8aa52262a55f9b009e59 |

The first two aggregate digests use SHA256 of compact, sorted-key JSON plus
newline for a path-sorted list of objects with keys path, bytes and sha256.
The tracked-source digest uses Git tree order and concatenated UTF-8 records:
path, NUL, Git mode, NUL, file SHA256, newline.

The nine byte-identical configuration/tooling files are lean-toolchain,
lakefile.toml, lake-manifest.json, flake.nix, flake.lock,
scripts/lake_integrity.py, scripts/lake-output-hashes.lean, scripts/check.py
and .envrc. Their exact contents are retained Git blobs. There is no proposed
configuration, pin, guard, verification-policy or compiler-resource change.

## Exhaustive extras and their recovery

| Checkout | Extra path | Bytes / allocation | Identity or disposition |
| --- | --- | ---: | --- |
| validation-cache-counts | .git | 87 / 4,096 | SHA256 840fd4b7869f74d8cfe7b721f76c7dd96eeeb6643e26f360581e46f8f002e5d3; worktree-local administrative pointer, regenerated by ordinary git worktree add |
| validation-cache-counts | scripts/__pycache__/lake_integrity.cpython-313.pyc | 9,335 / 12,288 | SHA256 1343ef856bb8936eb27c742498a8d350cdca82981f259e1a07013e4209cb0ab8; generated Python bytecode, not byte-identical to body-counts |
| purity-correction | .git | 81 / 4,096 | SHA256 5613e7718ce66dd62f50b9e195b1ff2f7aaa787d3fa5cafa081efd3e393a7c3e; worktree-local administrative pointer, regenerated by ordinary git worktree add |
| purity-correction | scripts/__pycache__/lake_integrity.cpython-313.pyc | 9,329 / 12,288 | SHA256 258651b04830e96f748478dc91327805a61c0109ac57f5ef2f09bff07c93e4e2; generated Python bytecode, not byte-identical to body-counts |
| Both | .lake/packages | Symlink, zero allocated bytes observed | Exact target /workspace/scratch/ca9a61d0bf30/conaled/.lake/packages; shared target must remain intact |

There are no other extras. In particular, no unique generated setup files,
validation record, local task record, untracked source or build output is hidden
by these classifications. Deleting a generated Python cache would explicitly
discard those reproducible bytes; this report does not call them preserved.
The unchanged scripts/lake_integrity.py source recreates the bytecode when
needed. Recreating worktree metadata does not require deleting or moving any
retained branch or common Git object.

## Durable source evidence and its limits

Checkpoint026's retained ledger entry explicitly names both exact candidates,
records successful real restoration and saved status, and has the following
identity:

- Filename: conaled-pfds-checkpoint-026.tar.gz.
- Library identity: libfile_bca00d367b388191a74593d7415fa959.
- Upload identity: file_00000000e0d8820aaea85b98649c89fd, version 0.
- Archive size: 74,085,507 bytes.
- Archive SHA256: b0a3e6849b5530296aefa4eaab1059e3992475ec16c5cc13d4fc9d394d61ad5e.
- session/checkpoint026-upload.json SHA256:
  b0446149e22456745457ea5ba13405df767aecfe1ce57e0f390283c92d4026ed.

The matching local upload receipt reports succeeded and agrees on identity,
filename, size and version. Checkpoint027 repeats both candidate identities and
preserves their later independent reports. The current refs still resolve
exactly to the same candidates; both remain ancestors of current body-counts.
Checkpoint034's saved ledger and matching upload receipt were also read:
libfile_2f46479608248191aecc24bc5734e606, 75,644,086 bytes, SHA256
c4231531348f274b9998e64e393c906a179d1dd38de0e41de23293f7069a9b55.

These archives' local duplicates have been reclaimed. The assessor did not
inspect an unavailable archive manifest, retrieve a remote archive, or assert
an independent archive restoration test. The durable evidence here is the
retained ledger/receipts, previously recorded restoration results, exact current
Git objects and refs, and the candidate captures:

- validation/pure-cache-counts-candidate-r1.json SHA256
  14764869f0f8d659d8b894b5ec13d04658ffc9acd8c85085ade0e718a31a93a9.
- validation/pure-suspension-candidate-r2.json SHA256
  95179e677edbd6bb1613769487496c753a6b1860da565bd372176fdb26effe17.

## Preconditions before root decides cleanup

The inspected paths remain future validation materializations, so source
removal is an operational decision, not an acceptance or review disposition.
Root must freshly check process users, exact clean heads, unchanged branches,
source inventory and retained output identities before removing either path.
The assessor did not claim process quiescence from a clean Git status.

If root removes the inactive materializations, retain their named branches,
candidate captures, requirements, all review reports, failed and successful
focused records, and full-gate blockers in session. Use ordinary worktree
removal without forcing unexplained changes. Do not follow the shared packages
symlink during cleanup. Do not delete any body-counts output or the active
import-correction-r3 tree.

To resume either candidate later, materialize its retained named branch at
the same recorded path, require the exact clean HEAD, restore the shared pinned
package link and a private project build directory, and reestablish ordinary
outputs only through a separately checked, stable-source reuse procedure or
normal rebuilding. The current body-counts subset is sufficient at the observed
point, but any future reuse must recheck its identity and stock output hashes;
this read-only assessment does not authorize a transfer from an active writer.
The saved supplementary ordinary-output archive also records a 3dd namespace,
but it was not fetched or revalidated here.

Every candidate still requires its own pinned stock full build, exhaustive
audit, matching verification record, both retained independent review axes and
final candidate verification. No predecessor or body-counts approval can be
substituted. Prepared runner paths will require those exact materializations
to exist again; deleting a worktree does not satisfy or waive their gates.
