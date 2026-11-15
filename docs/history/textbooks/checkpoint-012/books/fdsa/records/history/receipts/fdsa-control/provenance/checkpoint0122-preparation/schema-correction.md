# Checkpoint 0122: separate v2 schema correction

**Prepared only, unexecuted.** Root found these concrete metadata mismatches while reading the original verifier, before any verifier execution. All five original preparation files and their receipt remain byte-for-byte unchanged. `verify-checkpoint-v2.py` is the proposed corrected successor; `verify-checkpoint-v2.diff` is the exact complete difference from the preserved original. This note supersedes only the original README's inaccurate schema assumptions and incomplete own-preparation capture instruction.

## Actual source of the correction

The entire held `chapter02-acceptance-20261104/fast_forward_once.py` was read: **92 lines, 5,682 bytes, SHA-256 `a757f35a2b629ad8a7d13eb98dd1b355e8a8510ad382fc0b0e6a2fc80dba00b1`**. The entire real preflight was read: **189 lines, 11,404 bytes, SHA-256 `3d26b78b50c38f7b389f2839d3232857d89efc510acadce9458b9dc34786ebc0`**. The author did not execute that script, inspect a prospective result as if it existed, or fabricate any final binding.

The original verifier treated `refs_before` and future `refs_after` as dictionaries. The actual preflight and held FF method use raw `for-each-ref` string lists. V2 compares both 67-entry raw lists exactly, permits only the one `work/fdsa-book` L-to-Q replacement, and compares the actual saved after-list with the same whole-command `.strip().splitlines()` serialization used by the held method. It then represents those already-checked fields as dictionaries solely to compare with the existing format-2 manifest. The optional empty symref field on the last string is accounted for explicitly; no source, proof, trace, statement or raw output is normalized.

The actual held method writes `actual_exit`, `previous_accepted_commit`, `accepted_commit`, `accepted_tree`, `all_other66_refs_preserved`, `all_other14_worktree_heads_statuses_preserved`, and `unrelated_file_preserved`. V2 uses those names, binds the actual method/start/exit/result/log records, and independently checks the exact before/after reference transition. It checks all fifteen saved worktree HEAD/status/branch rows against the actual capture state, allowing only the main HEAD to change L-to-Q. Qualified Q remains clean, main tracked tree/index remain clean, and the known unrelated baseline partial retains its exact original pin and bytes. Verification completion must precede FF start; FF completion must precede the archive manifest time.

Root specified that the immediate closure uses `complete_closed_log`; the original verifier incorrectly read `complete_log_closed` there. V2 corrects that immediate field only. The existing full-check closure's distinct `complete_log_closed` spelling stays unchanged. The actual native start/result/output copies remain explicitly captured, with exact immediate command, qualified directory, one thread, closed success, no timeout or recorder error, complete outer log and matching retained Q full-verification identity.

All archive streaming hashes, format-2/restorer/public-baseline/native-kit constraints, held controls, historical L/Q records, eleven receiving runs, stable postcomparison, final-axis bindings and mathematical acceptance requirements are unchanged. This is metadata-schema reconciliation, not a weakened gate or an executed validation result.

## Required exception to excluding this preparation directory

The earlier capture pattern excluded the whole current preparation directory from `capture-control-identities.json`, because creation and verification products change during those operations. The new verifier consumes fixed bindings within this directory, so **root must explicitly include these ten fixed files in that held identity map** even when the remaining changing preparation products are excluded:

```text
verify-checkpoint.py
final-bindings.template.json
resource-observation.json
README.md
receipt.json
verify-checkpoint-v2.py
verify-checkpoint-v2.diff
schema-correction.md
schema-correction-receipt.json
final-bindings.json
```

The last file must be created separately by root from the fourteen real final-file identities. The unresolved template stays unchanged. V2 checks every listed fixed file against both its held identity and archived payload. Changing creation/verification logs, terminal records, `integrity.json`, upload records and the capture identity file itself are not made recursive members of this fixed-file map. Their actual closure records retain the normal existing recording boundary; this exception does not alter the checkpoint creator or archive format.

## Readback and scope

The held method and preflight were completely read at `bc2f2a`. V2 received static `ast.parse` only, with no import or execution. Its complete source and exact diff were read at `88970e`, with the truncated source portion covered explicitly by the bounded lines 254–310 read at `340bed`; the oversized read alone receives no full-source credit. The correction note and receipt receive a complete saved-file readback before handoff. No optional fixture tests, current comparison, source/ref/cache/runtime mutation, checkpoint verification, restore, fsck, final binding, acceptance record or global-control edit was performed by this author.
