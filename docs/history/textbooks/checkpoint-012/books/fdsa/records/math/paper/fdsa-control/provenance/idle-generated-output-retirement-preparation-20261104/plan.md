# Idle generated-output retirement — bounded preparation

Recorded 4 November 2026. This is a read-only resource assessment. No payload was cleared, no compiler/cache command ran, and no process was inspected or polled. The final 279 package and Order/Tail preparation remain unchanged.

## Decision and measured boundary

The three idle task worktrees contain **17,092 regular single-link generated files**, totaling **917,383,326 apparent bytes** and **972,529,664 allocated file bytes (about 0.906 GiB)**. These are potential payload savings, not a forecast of filesystem availability. The observations do not explain the wider filesystem decline.

The first no-follow inventory completed at **12:17:35 UTC**. It covered 16 literal generated roots; ten contain files and six contain directories only. All file and directory identities, topology digests, timestamps and counts are in `receipt.json`. Directory blocks are not included in the proposed payload reclaim. The other ten inspected idle task worktrees had no `.lake` root.

All paths below are relative to `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/`. The receipt supplies the full absolute allowed paths. Only these ten nonempty `.lake/build` roots are proposed for payload retirement; no parent directory, source checkout or wildcard is authorized.

| Worktree / literal generated root | Files | Allocated file bytes |
|---|---:|---:|
| `conaled-ch02-quicksort/.lake/build` | 24 | 2,453,504 |
| `conaled-ch02-quicksort/.lake/packages/mathlib/.lake/build` | 8,000 | 366,149,632 |
| `conaled-ch02-natural-runs/.lake/build` | 24 | 3,661,824 |
| `conaled-ch02-natural-runs/.lake/packages/LeanSearchClient/.lake/build` | 60 | 5,107,712 |
| `conaled-ch02-natural-runs/.lake/packages/Qq/.lake/build` | 210 | 21,684,224 |
| `conaled-ch02-natural-runs/.lake/packages/aesop/.lake/build` | 1,980 | 137,449,472 |
| `conaled-ch02-natural-runs/.lake/packages/batteries/.lake/build` | 2,925 | 150,294,528 |
| `conaled-ch02-natural-runs/.lake/packages/importGraph/.lake/build` | 525 | 35,078,144 |
| `conaled-ch02-natural-runs/.lake/packages/mathlib/.lake/build` | 3,240 | 237,690,880 |
| `conaled-ordinary-merge/.lake/build` | 104 | 12,959,744 |

The corresponding six ordinary-merge dependency build roots for LeanSearchClient, Qq, aesop, batteries, importGraph and mathlib are empty of files. Their directory metadata was observed, but clearing them would reclaim no file payload, so they are excluded from mutation. Cli and temporary package-source directories are also excluded. The nonempty totals are quicksort **368,603,136**, natural-runs **590,966,784**, and ordinary-merge **12,959,744** allocated bytes.

Preserve the entire F worktree `conaled-ch01-review`, accepted `conaled`, retired central `conaled-ch02-top-down`, compiler/native state, all source and dependency checkouts, Git data, exact pins, profile/adapter, compressed cache archives, original task checkpoints and baseline partials. No protected output tree was traversed for this assessment.

## Ownership, closure and evidence

The saved private-copy record shows quicksort dependencies were copied before builders, with a separate sample inode from F. Recorded atomic ownership transfers subsequently moved the idle dependency tree quicksort → ordinary-merge at 04:05:33 and ordinary-merge → natural-runs at 04:21:27; each records that the former owner had closed all commands. These establish the development lineage, not present completeness of the residual dependency directories.

The bounded provenance search found 16 completed doctor/build/type commands associated with these exact three project paths. Every saved native start has its matching closed native result, where those records are present. All associated complete control logs match their recorded lengths and hashes. Latest saved command terminals are quicksort **04:03:25**, ordinary-merge **04:14:39**, and natural-runs **04:27:39**. Current idleness is the coordinator's explicit assignment; absence of additional saved commands is not independently treated as process-liveness proof. Root must keep exclusive ownership during any later action.

An earlier old-path cleanup attempt at 04:07:53 failed before mutation when `du` saw disappearing synchronization temporary entries. Its exact failure record remains preserved and bound in the receipt. No deletion is assumed to persist because an earlier ownership transfer reported a source path absent.

The fresh inventory found no symlink, special file, multiply linked leaf or repeated inode among the scoped roots. All path components were opened without following links, and opened-directory metadata was matched to the preceding stat. Saved F/private qualification and the later saved F root samples remain evidence of separation; no new exhaustive scan of F was performed or claimed. Current scoped leaves are regular with one link, and all scoped generated-root identities are distinct from the available saved F project/mathlib root samples. No source/configuration search path was changed.

No candidate log, result/start/verification/audit JSON, or non-setup JSON appeared under the allowed roots. All observed suffixes are generated compiler payloads, including hashes and traces; all **19 JSON files** have `.setup.json` names. Actual validation logs, printed types, source/type assessments and immutable source history already reside outside these roots and remain preserved. This is a complete filename/type inventory, not an arbitrary-content semantic audit of each binary.

## Concrete stability issue found

The second separate inventory stopped on its first root's ancestor-chain comparison before any mutation. The generated root identity itself matched. A subsequent bounded ancestor diagnostic found only `/workspace` and `/workspace/scratch` had different device numbers: 38 in the first inventory and 52 in that diagnostic, with the same inodes 22/23. From the task root `b4a17a285e23` onward, every observed device/inode remained identical. The diagnostic is not a retrospective capture of all fields from the failed command; the remaining roots were not inspected by that failed second attempt.

The failed guard is retained in `receipt.json`. It creates no evidence of changed payload content or sharing with F. Root explicitly approved cross-command ancestor equality beginning at the stable authorized task root `/workspace/scratch/b4a17a285e23` (device 27, inode 2889817), including every descendant through each generated root. Every absolute prefix still receives fresh descriptor-relative no-follow validation in every command; external `/workspace` and `/workspace/scratch` identities are recorded observationally. All file metadata, directory identity/topology, allowed paths, permissions and F exclusions remain unchanged.

A **new full second inventory**, completed at **12:21:08 UTC**, then inspected all 16 roots and all 17,092 files under that explicit boundary. Every compared root, stable ancestor, file metadata/file set and directory identity/topology field matched the first inventory; directory timestamps also happened to match. The new command exited 0. This is a new complete successful comparison, not retrospective success for the failed attempt. The external prefix device was 51 in that new command. Available space was separately observed as **3,770,912,768 bytes**; no cause or future-capacity inference is drawn.

## Later root-owned action, if selected

Reuse the completed central retirement method and its recorded narrow directory-timestamp refinement. This preparation does not replay its historical command bodies or authorize a subagent mutation.

1. Bind the exact idle source/refs/pins, held command/review evidence and coordinator ownership. Confirm that no writer has resumed in any selected tree. Keep every protected F/accepted/central/runtime path excluded.
2. Apply the recorded stable-task-root boundary while freshly validating every external prefix without following links. Require two complete separate inventories to match every file path and `[mode, device, inode, nlink, size, mtime_ns, ctime_ns, blocks]`, and every directory path/topology and `[mode, device, inode, nlink, size, blocks]`. Record directory timestamps observationally, as the existing refinement specifies. Reject symlinks, specials, multiple links, aliases, changed filesystem boundaries or unexpected evidence files. The preparation's two matching inventories establish its present boundary; execution still needs the immediate complete comparison below.
3. Preserve the matched preflight and all unique evidence in the next verified, uploaded and exposed checkpoint before mutation. Root binds that exact checkpoint and the chosen literal roots. This author has made no future checkpoint claim.
4. Immediately repeat the complete comparison. A mismatch stops before mutation. Mark the selected worktrees' output sets `retiring_unusable` before clearing any payload. Preserve that unusable state after partial failure; it is not a statement that any source or theorem became invalid.
5. Open each leaf descriptor-relative to its verified parent with `O_NOFOLLOW`, without `O_CREAT` or `O_TRUNC`. Match opened `fstat` to all expected regular-single-link file metadata, then clear its payload with `ftruncate(fd, 0)` and verify the resulting size. Include generated trace/hash/setup payloads. Never clear a file before the opened identity check. Keep bounded progress and complete failure/terminal records outside the selected roots.
6. After that command actually closes, use a new command to check persistent zero regular-file logical/allocated payload, unchanged identities/topology and no new payload. Preserve source/refs/pins/runtime, record available space separately, and keep the output sets retired/unusable. Directory entries may remain. If payload reappears, record the difference and stop rather than repeating blind deletion.

## Supported regeneration boundary

These residual package directories are not currently certified complete private dependency environments. QuickSort presently has only a residual mathlib package entry, and natural-runs/ordinary-merge also lack some of the nine required package entries. Retirement therefore does not remove an otherwise demonstrated ready-to-build cache. No source contents or dependency Git state were inspected or altered in this task.

Later use requires the unchanged kit's exact clean/private dependency acquisition or verification, supported cache hydration and regeneration of the required project outputs. If a residual source checkout is incomplete, wrong or dirty, the kit preserves and rejects it; use its documented recovery route rather than overwriting pins or transplanting F artifacts. `cache --project PATH [MODULE ...]` is the supported helper; offline unpack only restores available archives and does not certify completeness. Near-empty full hydration retains its roughly 8 GiB additional-space estimate and reserve; no guard may be bypassed. The approximately 0.906 GiB possible reclaim does not promise that a later regeneration will fit.

Cleared traces cannot serve as evidence that an `.ltar` payload is already decompressed. A supported successful hydration still needs actual coverage and project-output checks. Regenerating outputs is distinct from a repository `check.sh --fresh` decision: retain the README's actual fresh triggers, exact environment profile, proof restrictions, full candidate/audit gates, both independent axes and immediate verification. Historical focused/type evidence remains historical and is not a substitute for matching future output qualification.

## Read boundary

Read completely: prior central plan and refinement, relevant ownership/failed-cleanup records and listed closed result records. Structured inspection/hash verification covered the 16 matching command records and their complete preserved logs. Read the existing executed central method bodies; bounded kit reads covered recovery, private dependency, cache, resource and locking provisions. Fresh filesystem reads were limited to the idle task-root location survey, the 16 generated roots' metadata and the later ancestor diagnostic. No F/native-state/accepted/central output traversal, binary evaluation, compiler command, source/ref/pin mutation or process polling occurred. Receipt hashes bind all evidence and the final author-readback boundary.
