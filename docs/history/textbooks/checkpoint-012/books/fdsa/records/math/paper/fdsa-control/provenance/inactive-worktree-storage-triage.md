# Inactive draft worktree storage triage

Snapshot: `2026-11-02T21:04:45.522159+00:00`.

**19 inactive draft working copies are candidates for coordinator re-verification and Git worktree removal. No worktree was removed.**

Their tracked source files total **1,664,865,590 logical bytes** and **1,732,837,376 allocated bytes** (1.614 GiB allocated). These counts exclude `.git`, `.lake`, shared packages, directory overhead, and the common Git object store. No tracked files had multiple hard links.

## Common verification results

- All 19 were clean under pinned Nix Git, including all nonignored untracked files.
- Each branch ref resolves to the exact HEAD listed below.
- Every complete 40-character HEAD matches both its candidate record and an exact candidate field in checkpoint 0051’s ledger entry.
- No `.lake/build` path exists in any candidate.
- Each ignored `.lake` is a real directory containing only one symlink, `packages`, targeting `/workspace/scratch/845aa1048b05/conaled/.lake/packages`.
- Git reports no other ignored entries; no uncertain local files or project build outputs were found.
- None of the candidates is locked. Author inactivity is the coordinator’s supplied condition; this task did not inspect processes.

The machine-readable evidence retains exact status output, source counts, link targets, candidate-record paths/matching lines, receipt fields, and restoration commands:
[inactive-worktree-storage-triage.json](inactive-worktree-storage-triage.json).

## Durable receipt

Checkpoint: `conaled-fdsa-0051-priority-queue-draft`.
Library identity: `libfile_75cece5073888191a8250103a888c321`.
File identity: `file_00000000c3c881f4ab119ba81e7fa5da`.
Recorded SHA-256: `bfa60088a749fd610256a5b4d953be54fc2e36ab96244a810cace45081a5bcf5`.

The `succeeded` result in `library-helpers/upload-0051/result.json` matches the checkpoint ledger’s exact filename and both identities. This triage did not rehash or unpack the checkpoint. The latest checkpoint archive remains untouched.

## Exact candidates

| Worktree path | Branch | Exact HEAD | Source logical bytes | Source allocated bytes |
| --- | --- | --- | ---: | ---: |
| `/workspace/scratch/845aa1048b05/conaled-accumulated-work` | `refs/heads/work/fdsa-accumulated-work` | `7c6bc92c276d39e84351324c442869b8ffa6758c` | 87,556,786 | 91,054,080 |
| `/workspace/scratch/845aa1048b05/conaled-adt-refinement` | `refs/heads/work/fdsa-adt-refinement` | `20a5b5537a704be016d09e4eb31db0dad8a12d61` | 87,609,878 | 91,119,616 |
| `/workspace/scratch/845aa1048b05/conaled-affine-recurrence` | `refs/heads/work/fdsa-affine-recurrence` | `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2` | 87,599,906 | 91,095,040 |
| `/workspace/scratch/845aa1048b05/conaled-builder-costs` | `refs/heads/work/fdsa-builder-costs` | `62809ced86c561c7a6cce8b71e727177a3f17fb8` | 87,549,070 | 91,045,888 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-expectation` | `refs/heads/work/fdsa-permutation-expectation` | `11923e9ffd17246b6f22c5594002a1ba0434e43c` | 87,680,602 | 91,226,112 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-joint` | `refs/heads/work/fdsa-permutation-joint` | `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e` | 87,731,111 | 91,287,552 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-minimum` | `refs/heads/work/fdsa-permutation-minimum` | `ff3dd88082c6283df40bcd86a4363841a0360b12` | 87,543,531 | 91,295,744 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-order` | `refs/heads/work/fdsa-permutation-order` | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` | 87,580,443 | 91,369,472 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-placement` | `refs/heads/work/fdsa-permutation-placement` | `49d6d4700b41f2837ae4cc5e74d23fc1eff8afbe` | 87,804,358 | 91,504,640 |
| `/workspace/scratch/845aa1048b05/conaled-permutation-tail` | `refs/heads/work/fdsa-permutation-tail` | `a0597381f02eddd074ee96cabaa974f2062285f8` | 87,634,261 | 91,152,384 |
| `/workspace/scratch/845aa1048b05/conaled-priority-observations` | `refs/heads/work/fdsa-priority-observations` | `c088beeb89aa18df45a56f6f1d6b6ff4ad374905` | 87,613,221 | 91,115,520 |
| `/workspace/scratch/845aa1048b05/conaled-three-way-partition` | `refs/heads/work/fdsa-three-way-partition` | `de5410286bbefd841dff50bef55c2e52d2ebbd2a` | 87,547,866 | 91,045,888 |
| `/workspace/scratch/845aa1048b05/conaled-tree-accumulator` | `refs/heads/work/fdsa-tree-accumulator` | `b035f1151ab4f0c7d7380818576cfe97dae434c4` | 87,645,201 | 91,295,744 |
| `/workspace/scratch/845aa1048b05/conaled-tree-cache` | `refs/heads/work/fdsa-tree-cache` | `64c6b777d828ecfe83234fc2aed94600a1f24297` | 87,561,486 | 91,090,944 |
| `/workspace/scratch/845aa1048b05/conaled-tree-fold` | `refs/heads/work/fdsa-tree-fold` | `b0fce71fa00b2ff6250b09002176bdc75baf1f46` | 87,610,084 | 91,271,168 |
| `/workspace/scratch/845aa1048b05/conaled-tree-order` | `refs/heads/work/fdsa-tree-order` | `66eae34815a177c6b4bf5120e05202ebb8876c91` | 87,673,380 | 91,193,344 |
| `/workspace/scratch/845aa1048b05/conaled-tree-rotations` | `refs/heads/work/fdsa-tree-rotations` | `28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2` | 87,632,063 | 91,140,096 |
| `/workspace/scratch/845aa1048b05/conaled-tree-shape` | `refs/heads/work/fdsa-tree-shape` | `974a97321a8ec174b56104c7e6efaaca881b6639` | 87,602,208 | 91,156,480 |
| `/workspace/scratch/845aa1048b05/conaled-tree-traversal-work` | `refs/heads/work/fdsa-tree-traversal-work` | `317aae79ff98b90b5525c6dd53bcd815bc6c6e1a` | 87,690,135 | 91,377,664 |

## Preserved and excluded

- `/workspace/scratch/845aa1048b05/conaled`
- `/workspace/scratch/845aa1048b05/conaled-ch01-cost-models`
- `/workspace/scratch/845aa1048b05/conaled-ch01-review`
- `/workspace/scratch/845aa1048b05/conaled-insertion-costs`
- `/workspace/scratch/845aa1048b05/conaled-ordinary-merge`

The reappeared checkpoint 0001, the main historical `.checkpoint-233.zip.n7UlkJ`, checkpoint 0051, common Git history/refs, dependency caches, and all active build state are outside the removal candidates. No unrelated host paths, processes, or Nix-store contents were inspected or changed.

## Prospective recovery

These are recovery instructions only; none was executed. Keep all branch refs and commits in the common repository. From the main repository, enter the pinned shell using:

```sh
cd /workspace/scratch/845aa1048b05/conaled
/root/.nix-profile/bin/nix --extra-experimental-features 'nix-command flakes' --option build-users-group '' develop
```

Inside that shell, restore only the needed working copy with its corresponding command:

```sh
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-accumulated-work work/fdsa-accumulated-work
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-adt-refinement work/fdsa-adt-refinement
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-affine-recurrence work/fdsa-affine-recurrence
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-builder-costs work/fdsa-builder-costs
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-expectation work/fdsa-permutation-expectation
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-joint work/fdsa-permutation-joint
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-minimum work/fdsa-permutation-minimum
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-order work/fdsa-permutation-order
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-placement work/fdsa-permutation-placement
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-permutation-tail work/fdsa-permutation-tail
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-priority-observations work/fdsa-priority-observations
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-three-way-partition work/fdsa-three-way-partition
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-accumulator work/fdsa-tree-accumulator
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-cache work/fdsa-tree-cache
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-fold work/fdsa-tree-fold
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-order work/fdsa-tree-order
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-rotations work/fdsa-tree-rotations
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-shape work/fdsa-tree-shape
git -C /workspace/scratch/845aa1048b05/conaled worktree add /workspace/scratch/845aa1048b05/conaled-tree-traversal-work work/fdsa-tree-traversal-work
```

Then run `git -C <exact-worktree-path> rev-parse HEAD` and compare with the exact HEAD in the table. If a retained branch has intentionally advanced, do not reset it to restore an old snapshot; use `git worktree add --detach <exact-worktree-path> <exact-recorded-HEAD>` for that snapshot instead.

Git does not restore ignored `.lake` state. When the main dependency checkout exists, recreate only the ignored link for the chosen restored worktree:

```sh
mkdir -p <exact-worktree-path>/.lake
ln -s /workspace/scratch/845aa1048b05/conaled/.lake/packages <exact-worktree-path>/.lake/packages
```

After complete workspace loss, first restore checkpoint 0051 using its included recovery instructions, retain its Git refs/commits, and restore the pinned dependencies through the project README before recreating a package link.

## Coordinator decision boundary

Recheck the selected path’s exact branch/HEAD, clean state, and `.lake` shape immediately before removal. Remove only the working copy through Git; retain branch refs, the common Git directory, all commits, shared packages, and the latest durable archive. The snapshot is not permission to remove a path whose state has since changed.

This triage made no deletion, branch/commit/index mutation, cache modification, toolchain change, project build, or process intervention.
