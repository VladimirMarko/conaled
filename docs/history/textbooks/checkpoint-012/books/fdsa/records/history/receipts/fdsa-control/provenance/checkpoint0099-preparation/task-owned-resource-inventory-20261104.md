# Bounded task-owned resource inventory — 4 November 2026

Author: shared-acceptance-sequence agent. Read-only investigation requested by root after checkpoint 0099 was verified, uploaded and exposed. This new report is the only written artifact. No cleanup, compiler command, cache operation, process polling, source/ref/index edit, or acceptance action was performed.

## Concrete result

Seven redundant compiler-download payloads are exact copies or prefixes of the retained official Lean 4.35.0 archive. Their combined apparent length is **1,552,879,839 bytes**; their observed allocated file blocks total **1,552,900,096 bytes (about 1.446 GiB)**. These seven files are potential reclamation candidates only. Root expressly prefers retaining the complete canonical compiler archive, and this report follows that preference.

The block count estimates the identified payload allocation, not a guaranteed increase in filesystem availability: allocation sharing, filesystem behavior and other activity were not investigated. No deletion or truncation was authorized to this agent. Root reports that deletion persistence has been unreliable; any later authorized reclamation should target only these exact confirmed redundant payloads and verify persistence in a separate command. That would be a new action, not something established by this report.

At **2026-11-04T11:08:51.808866+00:00**, `statvfs` on BASE reported:

| Measure | Bytes |
| --- | ---: |
| Available to this workspace | 5,272,121,344 |
| Raw filesystem free blocks | 8,724,869,120 |
| Filesystem total | 67,586,535,424 |

The inventory does **not** identify the cause of the filesystem-wide decline. It does not attribute that decline to any compiler, user, process, or residual file.

## Exact candidate inventory

All filenames in the following table are relative to this exact directory:

`/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-native-state/downloads/`

The retained reference file is `lean-4.35.0-linux.tar.zst`: **594,481,375 bytes**, allocated **594,489,344 bytes**, SHA-256 **`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`**. This agrees with the immutable kit pin and the acquisition receipt. It is **not** proposed for reclamation.

| Candidate filename | Bytes | Allocated bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `lean-4.35.0-linux.tar.zst.part` | 594,481,375 | 594,489,344 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` |
| `.lean-4.35.0-linux.tar.zst.part.O9mtQz` | 265,027,584 | 265,031,680 | `bc7ddc7dfce2eb56e08d2e43afc76979a39e357fc122a5bf198c960ed7781515` |
| `.lean-4.35.0-linux.tar.zst.part.O9mtQz.OZKp6B` | 135,790,592 | 135,790,592 | `9dad621588d2b38e2f3406acf707852d598ec5f8570832accf012398e335f39c` |
| `.lean-4.35.0-linux.tar.zst.part.O9mtQz.OZKp6B.fHsWTU` | 134,217,728 | 134,217,728 | `2d0cdb1ff92244ce3dc0c2488d47ac314af021ff5a6af0d0a6777900d1270464` |
| `.lean-4.35.0-linux.tar.zst.part.O9mtQz.OZKp6B.fHsWTU.KJ28ta` | 114,032,640 | 114,032,640 | `cac4d1b8b578e15b517dd37723d0e682ef4abd9dcb91f2d0522662adfce791aa` |
| `.lean-4.35.0-linux.tar.zst.part.ulYNRt` | 100,139,008 | 100,143,104 | `7915539d009ccc19476a08ccedc2757c5cb288198758fd2b7f59342d2d198c8d` |
| `.lean-4.35.0-linux.tar.zst.part.zRmy8Q` | 209,190,912 | 209,195,008 | `3775d074a7be08e1cc54683fb23dc327633a4c5f822c12a4b12ef0f662313755` |

The direct reads completed at **2026-11-04T11:08:17.298785+00:00**. Every candidate was a regular file, `st_nlink = 1`, on device 27. The canonical file's inode was 2903100; candidate inodes in table order were 2889776, 2916693, 2891234, 2891233, 2891232, 2903101 and 2904308. All were distinct. Size, modification time, inode and change time stayed unchanged across each full read. File modification times fall within 03:40:59–03:44:11 UTC on 4 November 2026; timestamps alone are not used to infer which operation created them.

Each candidate was compared byte-for-byte, in bounded streaming reads, against exactly its own length from the start of the canonical archive. Every comparison passed. The `.part` file is therefore a full duplicate; the other six are exact prefixes. Each candidate was also fully hashed. **There is no unique payload content in these seven files**: reconstruct candidate bytes by taking exactly the listed length from the retained canonical archive. Their directory/name/length/hash identities are retained here. The precise historical writer of the residual filenames was not established, and no process inspection was performed.

## Provenance and why these are not runtime inputs

The immutable kit identifies the archive at:

`https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`

`conaled-native-state/toolchains/lean-4.35.0-linux.acquisition.json` is 2,273 bytes, SHA-256 `90358ca752d3468f49573794d7e01111938a2a5db0415567ac788cefe69db61f`. Its recorded acquisition time is 03:41:20.752101 UTC; it records the same compressed size/hash, extraction of 18,571 members and 3,137,937,793 regular-file bytes, and verification of 47 recorded official files. Its explicit scope is preserved: those current-file checks are not a new whole-tree attestation.

The successful environment setup terminal record is `fdsa-control/provenance/unified-native-recovery-20261104-attempt4-serial/result.json` (1,214 bytes; SHA-256 `86a99a7346413678147bf89b717509d0072d6398b1535054f4bf53ed4d08856c`). It records actual setup exit 0 at 03:53:20.340644 UTC, exact foundation candidate `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, and unchanged clean source. This is historical environment evidence, not foundation acceptance.

The checked acquisition source `lib/acquire.py` lines 335–378 first checks the installed target at lines 345–348, verifies it and returns it. Only the installation branch that follows opens a supplied/downloaded archive. `lib/runtime.py` lines 59–102 resolves the profile's installed toolchain, checks watched runtime files and forms the runtime/search paths from that installation. F and central execution use this installed profile/toolchain and their existing private dependency/project outputs; no claim is made that a central compiler is currently live. They do not consume these duplicate archive payloads. Neither the installation, profile, wrappers, cache helper, active caches nor project outputs is a reclamation candidate here.

The kit's `docs/RECOVERY.md` expressly advises avoiding duplicate compiler archives and deleting/archiving only positively identified replaceable artifacts. It also preserves interrupted gate evidence and prohibits changing tools, source pins or resource settings during a recorded gate. No such change is proposed.

## Other inspected areas and exclusions

- The direct children of `conaled-native-state/toolchains` were the installed release directory, its acquisition receipt and its lock file. No additional extraction staging directory appeared at that level. The installed release was not traversed or modified.
- `conaled-native-state/tmp` contained the historical `smoke-nayqx9y7` fixture. Bounded metadata traversal found 25 files, 4,447,757 apparent bytes and 4,530,176 allocated file bytes; the largest is its 4,401,080-byte native smoke executable. This small original qualification fixture is **retained**, not proposed for reclamation. The state-level `conaled-native-state/last-smoke.json` is 9,280 bytes with SHA-256 `2ffe684a0d37f8ecc70978623a74a4305ffe4957cc8e6703f072b3ab9e416829`; the secured `fdsa-control/provenance/unified-native-recovery-20261104-qualified/smoke-result.json` has the exact same size/hash. That receipt records completion at 03:53:20.287515 UTC and includes the expected rejection of the false-proof smoke case. No smoke was rerun.
- The two retry download-configuration directories each contain a 17-byte curl configuration (one 4,096-byte allocated block). They are negligible and retained. Configuration contents were not needed for this inventory.
- `BASE/recovery-regenerable-artifacts` was inspected only at its direct directory-name level. The fully read preserved records `fdsa-control/provenance/recovery-20261104-restored/partial-baseline-copies-moved.json` and `partial-baseline-prefix-exclusions.json` identify its three baseline ZIP prefixes. Those baseline partials and their historical source paths are **explicitly excluded and preserved**. They were not traversed, hashed again, or proposed for reclamation.
- All original checkpoint archives, including contents under `BASE/checkpoints`, are preserved and excluded. This inventory does not assess whether an older archive could be removed.
- All repository/worktree source trees, installed compiler/runtime contents, active dependency/project caches, compressed dependency caches, executable/profile outputs and live logs are excluded from reclaim candidates. No directory walk was made through those areas. The task-owned zeroed `recovery-validation-0082` tree was neither inspected nor revisited.
- At the workspace top level, only direct regular-file names matching the recognized task terms `fdsa`, `conaled`, `lean`, `native`, `recovery` or `checkpoint` were considered; no such direct regular files were found. No unrelated subtree or Library content was accessed. This bounded search is not an assertion that no other large task file exists outside the inspected areas.

## Read boundary and source identities

Complete reads for this assessment: all eight download files; the acquisition and last-smoke receipts; the secured setup result; the two baseline-prefix control records; and the kit's complete `docs/RECOVERY.md`. Bounded reads: relevant kit README/pin search results, `lib/acquire.py` lines 20–47 and 335–381, and `lib/runtime.py` lines 54–112. The fixture inspection was metadata-only; its Lean source and binary were not reread or executed. Other current project sources and mathematical proofs were not assessed.

| Kit source | SHA-256 |
| --- | --- |
| `lib/acquire.py` | `2d537f9656979f95a441c813640d67a804a544a4d12b698c4f8d965f93627297` |
| `lib/runtime.py` | `e790d472353e8d9467d696d2b1f7ae245c731d61e90cbfbcc7a2a576ad4fd695` |
| `docs/RECOVERY.md` | `a831215f53ae5380c36c4a4c9fcf6cc239fff3f020d5a951dc14402d0ef5eba4` |
| `README.md` | `fa1b4482615a39394754688c85d36d6d5dd2ddf30b1cd194cef99561906b2365` |
| `pins.json` | `84f0fb3fc2b392d0249ca078dfc0beb0896dd3764af93acfe25eeda9d0e41bd4` |

All kit paths above are under `BASE/fdsa-control/tooling/unified-native-kit-4.35.0/`; BASE is `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104`.

No review finding was opened or resolved, no accepted/candidate ref was changed, and the existing foundation/shared-unit/Chapter 2 acceptance sequence is unaffected. This report does not revise the earlier XP01 development-route plan or claim that any current development assembly has succeeded. Root owns any later reclamation decision and validation. The author stops at this saved boundary and holds further writes.
