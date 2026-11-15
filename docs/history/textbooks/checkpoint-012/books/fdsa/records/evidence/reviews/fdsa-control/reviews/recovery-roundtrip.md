# Recovery round trip with uncommitted source changes

Date: 2026-11-02. Reviewer: independent architecture/recovery agent.
Assignment: validate the current checkpoint and fixed restore scripts against
dirty index/working-tree state and checksum corruption. This is a cross-cutting
recovery acceptance test, not a chapter mathematics review.

## Outcome

**PASS.** The synthetic source repository and restored repository agree exactly
on active commit, branch, status, index contents, staged patches, unstaged patches,
all source file bytes, and the entire advertised named-ref map. Local task control
files are byte-identical. Corruption is rejected before the destination is created.
No concrete recovery bug was found in this assigned scope.

The real conaled checkout, its index and refs, and the original checkpoint 0001
archive were not modified. All fixture mutations occurred beneath a newly created
isolated test workspace. No network requests, Library uploads or Lean builds were
part of this test.

## Exact versions tested

Copied from the current control directory at test start:

| Script | SHA-256 |
|---|---|
| `checkpoint.py` | `8dc344a611d95014079544c47d0cfaddd401e4b6e4bfee76ebee00850fbebbaa` |
| `restore.py` | `d7e4d48cbf605e1fa5408f92fc3e3827f68af6c279a9cd47f325b064fbf34714` |

Runtime: Python 3.12.14 and Git 2.51.1.

Fixture workspace:
`/workspace/scratch/845aa1048b05/fdsa-recovery-roundtrip-wz9s0bbm/`.
Machine-readable evidence is preserved alongside this report in
`recovery-roundtrip-results.json`. Temporary fixture paths are supplementary;
the report and evidence carry the outcome into subsequent checkpoints.

## Fixture and reproduction

Create a new workspace containing sibling `conaled/` and `fdsa-control/`
directories, then copy the two tested scripts into `fdsa-control/`. Supply a
small request/status file and local ticket index/body so control-file recovery
is exercised as well as source recovery.

The synthetic Git repository uses branch `work/fdsa-book` and contains:

1. A committed text file with multiple independently editable lines, plus a
   binary file containing bytes 0 through 63.
2. A baseline branch and annotated tag at the first commit.
3. A separate commit with the same base tree and its own parent history,
   reachable through a remote-tracking ref and a custom `refs/review/` ref.
4. A second active-branch commit so the current HEAD differs from both the
   saved baseline and alternate history.
5. A staged edit to the first text line, followed by a different unstaged edit
   to the fourth line in the same file.
6. A staged binary edit to byte 5, followed by a different unstaged edit to byte
   20 in that same binary file. Both patches contain Git binary-patch records.
7. An untracked Lean text file under a directory containing a space, and an
   untracked binary file.

The exact source status was:

```text
MM blob.bin
MM state.txt
?? new sources/
?? untracked.bin
```

Source identities:

| Role | Commit/object |
|---|---|
| Baseline commit | `e047b59241f9c5ce1939a226249540aaf281a169` |
| Active HEAD | `9e1bbc615971e0cb33295b87db25472711df4164` |
| Alternate history tip | `6477b106b8f4262ef41df4b5a0ed9f9777a11209` |
| Annotated tag object | `f111eb349f89c69286c22e1b0d24f3073fae7e4c` |

The source advertised these five named refs:

- `refs/heads/master`
- `refs/heads/work/fdsa-book`
- `refs/remotes/origin/preserved-other`
- `refs/review/preserved-candidate`
- `refs/tags/preserved-baseline`

Run `python3 fdsa-control/checkpoint.py roundtrip-fixture` in the synthetic
workspace. Extract the resulting archive to a separate directory, verify its
checksums, and run its included `restore.py` into an absent destination.

## Verified assertions

| Check | Result |
|---|---|
| Checkpoint creation succeeds and does not change the synthetic source state | Passed |
| All 12 generated payload checksum entries verify | Passed |
| Restored active HEAD and branch exactly match source | Passed |
| `git status --porcelain=v1 -z` byte equality | Passed |
| `git diff --cached --binary` byte equality | Passed |
| `git diff --binary` byte equality | Passed |
| `git ls-files --stage -z` byte equality | Passed |
| Every tracked/untracked source file's bytes match | Passed |
| Entire `for-each-ref` name/object map matches, with no clone-created extras | Passed |
| Annotated tag object and separate alternate commit history survive | Passed |
| Every local control file is byte-identical | Passed |
| `git fsck --full` in the restored repository | Passed, exit 0 |
| Included bundle verifies as complete self-contained history | Passed |

The generated synthetic archive was 7,110 bytes with SHA-256
`411855b76999cf9effdb2dfe10943951e724f60c279588b3b8758d8cee750c29`.
It is a disposable test fixture, not a user checkpoint or project source artifact.

## Corruption rejection

Copy the extracted checkpoint into a separate corruption-test directory. Append
bytes to its `staged.patch` without changing `SHA256SUMS`, then invoke its
`restore.py` with a new absent destination.

Observed result:

```text
exit status: 1
stderr: Checksum mismatch: staged.patch
destination exists: false
```

The intact source state and successful restored state remained unchanged. This
shows that corruption of a checksummed patch is rejected during preflight before
any destination write, not merely discovered after partial source restoration.

## Scope and limits

This test exercises the current scripts' supported trusted-checkpoint path with
text and binary changes, separate index/working-tree content, untracked files,
ordinary and nonstandard named refs, and an independently altered payload.
It is not a proof of arbitrary archive security, operating-system crash atomicity,
preservation of every possible filesystem metadata field, or simultaneous-writer
snapshot consistency. Checkpoint capture still requires the coordinator to keep
the source and control files stable during capture.
