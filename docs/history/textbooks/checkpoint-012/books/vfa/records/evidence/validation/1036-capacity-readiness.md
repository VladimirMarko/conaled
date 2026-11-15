# Capacity readiness — prospective source assessment

Recorded 2026-11-04 UTC. Prospective assessment only: no completed gate, deletion authorization, waiver or acceptance. Only this note was written; no compiler, cache operation, deletion, source edit or capacity-check bypass occurred.

## Scope and historical observations

Workspace root: `/workspace/scratch/60f07f0e98c8`.

- `R`: `restored/conaled-vfa-checkpoint-042-native-j1-validation-readiness`.
- `N`: `native-state`; `K`: `restored/conaled-native-kit-4.35.0`.
- `D`: `R/vfa-validation`, the dedicated dependency store.
- `C`: `R/vfa-native-kit-validation`, candidate `c988f183887896c00b09aaff9077a6ea7fb8d68f`.

Root reported at **2026-11-04 00:54:13 UTC**: physical free space about **1.894 GB**, ordinary available space **0**; candidate total **370,479,104 bytes**, including private `.lake` **205,852,672 bytes**. These are historical root observations, not a current availability guarantee. The full fresh attempt remained active at 477/953 in root's handoff. No cause is attributed to the wider filesystem's decreasing free space.

Earlier bounded inventories found `N` about 3.31 GB and `D/.lake` about 7.58 GB. Root had already removed completed download archives. `f_bfree` measures physical free blocks; `f_bavail` describes ordinary available allocation. They are not interchangeable for the collector's check.

## Exact narrow finding: standalone cache executable

At 00:55 UTC, `N/bin/mathlib-cache` was a regular, non-symlink file with one hard link: **119,669,648 logical bytes**, **119,672,832 allocated bytes**. The retained successful `N/cache-relink.json` records SHA-256 `a8b0bf258ad991ba40561bffcbcadc88ad429eef6e4ac2cd8ae99b229590d624`, matching size and exit 0. This assessment read the receipt; it did not rerun the linker or rehash the executable.

The current installed `N/profile/config.json` contains no reference to `mathlib-cache`; no profile symlink points to it. Its tools are `lake`, `lean`, `leanc`, `leanir`; watched official files are the Lean/Init/Lake shared runtime libraries, not this cache executable.

Exact kit source separates its use from formal execution:

- `K/conaled_native.py:305–352`: `relink_cache` creates/reuses the standalone executable with a fixed expected digest.
- `:355–389,518–528`: explicit cache setup/recovery calls it through `_cache-exec`.
- `:278–302,587–598`: ordinary `run` verifies the installed profile and launches the requested command; it neither references this executable nor relinks it.
- `C/scripts/check.py:281–329`: the current fresh branch compiles/audits directly with Lean and extracted dependency search paths. It does not invoke cache acquisition or unpacking.

**Therefore, if no setup/cache writer is active, unlinking only `N/bin/mathlib-cache` would not change any current fresh source, dependency, compiler, profile or launch input, even while fresh is active.** The later guarded build, managed ProofAudit and regression commands likewise do not use it. Its absence alone would not force another fresh baseline. A future explicit cache/setup operation would have to relink it and satisfy that operation's own capacity check. This is a source-supported disposability finding, not authorization to delete it; root is retaining it for now.

The completed `N/tmp/smoke-prtm_583` fixture totals about 4.56 MB. Its build outputs are separate from formal inputs; preserve its result, sources and logs as evidence. No blanket `N/tmp` cleanup is supported. These small recoveries do not establish sufficient headroom.

## No large safe dependency-pruning population established

Across all nine dependency `.lake/build` trees, the bounded file inventory found:

| Artifact class | Allocated bytes | Disposition |
| --- | ---: | --- |
| `.olean.private` | 3,880,890,368 | Retain |
| `.olean` | 1,899,036,672 | Retain |
| `.c` | 524,877,824 | Retain |
| `.ilean` | 315,052,032 | Retain |
| `.ir` | 306,016,256 | Retain |
| `.olean.server` | 126,349,312 | Retain |

The remaining classes were signatures, traces and hash sidecars. No separate native object/static/shared-library or bitcode population was found. Official runtime files and kit link inputs were excluded from any pruning proposal.

Pinned Lake `Lake/Build/Module.lean` requires `.olean`, `.ilean`, `.c`, and module-system server/private/signature/IR artifacts in `leanArts`; bitcode is additionally required when LLVM applies. Imports request this same facet. Missing required members can cause reconstruction even when artifact caching is disabled. Mathlib's lakefile also sets `restoreAllArtifacts := true`. The existing formal-review coordinator independently confirmed this facet analysis and that the current lakefiles do not enable the relevant native precompilation/plugin routes.

Separate generated native-object/library facets could have supplied unused files, but none was present. Pruning an apparently unused Mathlib module subtree remains speculative without an established complete import/execution closure. No such pruning is recommended here.

## Installed runtime reuse and remaining gate

An empty `N/downloads` does **not** make ordinary kit `run` download the installer. Its source path is `check_project → environment/verify_profile → log_command`; no distribution acquisition or profile preparation occurs. Even `K/lib/acquire.py:335–348` returns an already verified installed distribution before examining archive/download availability. Preserve the complete installed distribution and profile.

After actual fresh completion and its normal temporary-output cleanup, remeasure availability. The unchanged collector `R/work-state/validation/1034-pre-guard-assess.py:379–380` requires `shutil.disk_usage(out).free >= selected evidence bytes + 64 MiB`. Physical free blocks, prospective cleanup and historical observations do not satisfy this prerequisite. All formal, incident-preservation and review gates remain required.
