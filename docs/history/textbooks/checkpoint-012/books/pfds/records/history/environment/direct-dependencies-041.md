# Direct pinned dependency source restoration

Completed on 2026-11-03. This follows the user’s explicit clarification that Nix is optional for continued development. The exact Lean/library pins and all existing validation requirements remain binding.

## Result

All nine public Git source checkouts specified in `conaled/lake-manifest.json` were restored under `dependency-store-041`. Every HEAD exactly matches its pinned revision, every worktree is clean, and the manifest bytes are unchanged. The source writer has finished and the checkouts are frozen for the parent’s dependency-cache setup.

| Package | Exact revision | State |
| --- | --- | --- |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Clean, exact |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` | Clean, exact |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` | Clean, exact |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` | Clean, exact |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` | Clean, exact |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` | Clean, exact |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` | Clean, exact |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` | Clean, exact |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` | Clean, exact |

## Method and evidence

Each fresh checkout uses a shallow public fetch of the exact recorded commit (`git fetch --depth=1 --no-tags origin <revision>`) followed by a detached checkout. No branch tip or alternate version was substituted. Each repository’s push URL is disabled locally. No global Git configuration was changed.

Independent network fetches were performed concurrently; no compiler or build process ran. Exact command arrays, exit codes, per-package source counts, timestamps, URLs and verification results are retained in `environment/direct-dependencies-041.json`. Per-package raw fetch logs and the reproducible restoration helper are in `session/tools/dependencies-041`, excluded from checkpoint payloads under the existing temporary-tool-input policy.

Manifest SHA256: `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`.

## Handoff and limits

The parent may now provide `dependency-store-041` as the package-source directory for the isolated project checkouts and perform one controlled cache-restoration operation with the exact pinned Lean/Lake release. Keep this shared source set stable while any candidate validation runs. Project build directories must remain private to their individual checkouts.

No `.lake` link was installed in a project by this assignment. No source or lockfile in `conaled` or `signed-potential` was edited. No Lean compiler, Lake command, dependency-cache build, project build, proof audit, acceptance verifier, Library operation, or GitHub write was performed. This is source recovery only; it establishes neither compiled dependencies nor candidate acceptance.

The dependency store is reproducible runtime state outside the source checkpoint. Its Git revisions, source URLs and checks are retained in the environment record; recreate or reverify it after workspace loss rather than assuming these directories are present.
