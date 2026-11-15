# Bounded compact recovery review and correction

The independent source-recovery agent read both compact scripts and confirmed
no blocker for the actual clean two-worktree snapshot. It verified the candidate
HEAD inventory, refs and symbolic refs, patch/untracked restoration, exact one
external ZIP identity, native-kit manifest, and final HEAD/status/ref/fsck checks.

It found a future dirty-content capture race in using only porcelain status as
the before/after guard and a fail-closed restore limitation for intent-to-add
index entries. Root added SHA-256 fingerprints for the staged/unstaged binary
patches and included untracked content/modes/link targets, plus explicit rejection
of intent-to-add and unmerged index states before capture. Source writers should
still pause during the bounded capture; no finite before/after check proves
absence of transient changes that are later restored.

The dirty recovery fixture passed actual blank restoration of staged plus
unstaged text, binary edits, untracked binary payload, detached-worktree dirty
content, both exact patches, and intent-to-add rejection before archive creation.
See dirty-recovery-test.json. The actual 0070 blank recovery passed all 45 refs
and both source worktrees; the external URL was independently fetched and
verified by length, SHA-256 and Git blob hash.

These are recovery checks, not mathematical review or chapter acceptance.
