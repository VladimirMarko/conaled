# Recover current FDSA work

This compact archive preserves all task source, every reachable Git commit/ref,
current worktree edits, local tickets, requirements, reviews, evidence, and the
complete supplied unified native environment kit. It requires no earlier task
checkpoint or conversation. It is NOT a completely offline archive: one unchanged
67,920,919-byte public baseline ZIP is externalized with exact byte and Git pins.
The restore downloads it from its immutable URL, or accepts an exact local copy.

1. Extract this archive and verify `sha256sum -c SHA256SUMS`.
2. Run `python3 fdsa-control/restore_compact.py /absolute/new/workspace`.
   The destination must be absent or empty. For an offline baseline-asset seed,
   append `--asset /absolute/path/to/checkpoint-233.zip`. A mismatched asset fails.
   Restore inserts the verified blob, installs the object pack, checks every ref
   and Git integrity, then recreates source worktrees and their saved edits.
3. Read `fdsa-control/REQUEST.md`, `CURRENT.md`, `STATUS.md`, and `tickets/INDEX.md`.
   Partial/running logs and environment smoke tests are not chapter acceptance.
4. Follow `fdsa-control/ENVIRONMENT.md`. The unified native kit is included in
   `fdsa-control/tooling/unified-native-kit-4.35.0/`; acquire its exact compiler and
   dependencies, then resume the first unaccepted chapter and preserved reviews.
5. Keep changes and tickets local. No GitHub mutation/push is authorized.

The original book PDF is not redistributed; its URL, edition, size, and SHA-256
are recorded in source provenance. Historical process IDs are not live evidence.
The externalized ZIP is pre-existing public repository material, not new task
work. All task recovery information remains in this archive; there is no delta
chain and no dependence on previous recovery checkpoints.
