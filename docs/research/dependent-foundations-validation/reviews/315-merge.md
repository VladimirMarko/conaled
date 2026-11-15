# #315 exact-candidate integration

Root explicitly assigned the separate merger role after independent review passed. Integration used only a fast-forward; no source changes, conflict resolutions or merge commit were introduced.

- Target checkout: `/tmp/conaled-314-320/integration`.
- Target branch: `integration/dependent-foundations-314-320`.
- Before: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
- Before tree: `d38d7d450009a49f30c825dd3d1da07c1b5c0fb3`.
- Approved and integrated candidate: `bb77d67171e6cb610e43149394c8a9b9a0deab3f`.
- After tree: `b63e5284ff39e5c8ea9e2b9da20100cd3857657c`.

Before mutation, both the source candidate checkout and integration checkout were clean. The target branch and exact expected base were checked. Both independent final reports (`315-standards-bb77d67.md`, `315-spec-bb77d67.md`) pass the full fixed-base scope with zero unresolved findings. The source checkout HEAD and tree matched the approved candidate.

Immediately before landing, `direnv exec . ./check.sh --verify-candidate HEAD` succeeded in the validated source checkout. The retained log `315-merge-pre-verify.log` matches the approved candidate and its incremental acceptance receipt. Full build/exhaustive audit, all four audit fixtures, toolchain and dependency evidence remain in the corrected-candidate records linked by `315-review.md` and `315-handoff.md`.

`git merge --ff-only bb77d67171e6cb610e43149394c8a9b9a0deab3f` succeeded; output is retained in `315-merge-command.log`. The landing command asserted the expected branch, clean target, exact base and ancestor relationship before merging. Afterward it asserted exact candidate HEAD, identical reviewed tree and clean working tree. All checks passed.

No full rebuild was repeated because integration preserves the exact validated commit, source tree and tracked toolchain/dependency inputs. No acceptance claim is made for separate build artifacts in the integration checkout. The target's unchanged `.envrc` was read and allowed to load the repository's prescribed Nix shell before Git operations.

Master was not changed. No push or issue closure was performed. The higher-model adoption and old-API migration limits remain as reviewed.
