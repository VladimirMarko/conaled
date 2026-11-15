# Bounded ordinary-output migration: implementation handoff

Frozen author handoff under root's existing 10000 recovery/validation work,
2026-11-03. No real transfer is authorized by this author report. Root owns
subsequent capture, independent operational review, real donor acceptance and
execution. The helper is prepared for checkpoint 033; it has not been used on a
real candidate.

Owned files are migrate-accepted-outputs.py, test-output-migration.py and this
report. Disposable tests use self-created directories under the workspace.
No real source, cache, ref, tracker or review record may be changed here.

## Fixed preparation and source basis

The complete specification is root's assignment and
research/ordinary-output-handoff-design.md, SHA256
08d3cad5cc7cf01fd6ca35d699242ad74d6efa2370960f4dda80006e0ff9d197.
The existing warm-chapter02-candidate-r3.py basis has SHA256
886880d620a686b7a427d5e5015439e9898dbe22432dc2f693e407b6d15dd346.
Stock lake_integrity.py SHA256 is
293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f;
lake-output-hashes.lean is
fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b;
scripts/check.py is
80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29.

AGENTS, README environment/build/audit, implement, shared review loop, integrity
incident guidance and TDD/tests/mocking guidance were read. This assignment
continues root's loop; it does not start another implementation/review workflow.
The explicitly assigned test seams are the public filesystem-transfer lifecycle,
its external verifier/I/O failure boundaries, and acceptance/plan input checks.
The parent confirmed the receipt design and multi-report independent-axis scope.
No additional user confirmation is required for these already assigned tests.

The prior warmer identifies source 901f734161920a76f3b399a575805b9a1d31e971
and target 99a29dcd02eb529fbefbb675e244a8c47b78cdef. These are historical
basis identities, not an acceptance claim or a prescribed future plan. The new
helper takes exact heads from a root-authored plan. The author has not selected
or accepted a real donor or target.

All five basis hashes above were re-read after implementation and still match.
The design, warmer, stock guard, hash script and stock check script were not
modified.

## Implementation and retained boundaries

The CLI requires an exact, trusted root-authored acceptance receipt before any
environment probe, Git call, compiler invocation or output mutation. It accepts
only a basename within session/validation. Source and target are direct named
workspace checkouts with exact full Git SHAs; the caller cannot supply arbitrary
absolute paths, output destinations, guard implementations or journal names.
JSON readers reject duplicate keys, non-finite constants, unexpected receipt or
plan fields and unsafe relative paths. Hashed evidence is confined to session
validation/reviews, bounded in size and rechecked for stable content/identity.

After acceptance bookkeeping passes, production requires the pinned Nix shell,
LEAN_NUM_THREADS=1, no LEAN override and removal of caller LEAN_PATH. It acquires
the established full-build and focused-build locks nonblocking, checks exact
clean checkout heads, rejects shared/hardlinked/nonregular/symlinked project
build outputs, and compares both checkouts' pinned configuration and clean
dependency identities. The saved compiler string must match lean --version and
lean-toolchain. Stock lake_integrity.py and lake-output-hashes.lean are pinned to
the hashes above, imported unchanged, and used through validate_layout,
expected_artifacts and inspect_outputs. The public fixture seam does not expose
a production CLI switch to replace those checks.

Visible checkout users are checked through /proc cwd/argv and workspace-owned
file descriptors/mappings, excluding the helper and launcher ancestors. Root
must freeze both checkouts and dependencies for the whole operation. The locks,
process checks and metadata receipt are trusted local operational bookkeeping;
they do not authenticate review content, prove process isolation or defend
against hostile writers that ignore the freeze protocol.

Selection retains the prior identical-source/complete-output rule and requires
the source module to be tracked on both sides. Any pre-existing target ordinary
artifact, sidecar or trace skips that entire module; skipped donor groups remain.
Changed source modules between candidates are skipped under this established
selection rule. A captured module or output changing during a selected transfer
is an error. Unknown parser/hash errors stop without classification or repair.
The helper does not rewrite a trace or invoke guard repair.

Complete groups are packed into fixed batches of at most 67,108,864 bytes
(64 MiB), using rounded file allocation plus directory allowance. A complete
group larger than the cap is rejected. The reserve floor is 335,544,320 bytes
(320 MiB); the caller may increase it but cannot decrease it. Before any batch
copy, measured free space must cover the reserve, that complete batch and an
additional fixed 33,554,432-byte (32 MiB) journal budget. Thus a full 64 MiB batch
requires 436,207,616 free bytes (416 MiB). A smaller actual batch uses its own
calculated amount. Rejection reports both measured free and required bytes; it
does not reduce the reserve or automatically shrink/retry a refused batch.

The transfer sequence is:

1. Create an exclusive journal and fix the selected module/file manifests.
   Check all selected source artifacts with the unchanged stock hash adapter.
2. Before each batch, recheck acceptance evidence, heads, tracked source
   inventory, configuration, dependencies, source verification record, process
   users, source-file snapshots and target absence, then fsync the planned
   manifests and measured space requirement.
3. Copy artifacts and optional corresponding sidecars exclusively into private
   target files. Each file and parent directory is synced. Copy the module trace
   last. Preserve original descriptors, file size, SHA256 and identity. Compare
   target bytes and source stability after every copy.
4. Independently run the unchanged stock target hash adapter for the fixed
   batch. Recheck the full scope, source files and target files. Append/fsync the
   complete target-verified manifest before recording retirement start.
5. Retire only corresponding captured source files, checking source and target
   snapshots immediately before deletion. Remove and sync the source trace
   first, then its captured sidecars/artifacts. Sync the affected source
   directories and record each retired group. Keep the verified target intact.

Source code, configuration, dependencies, generated setup files, skipped groups
and source verification records are outside the retirement set. The target does
not receive a verification record, audit success or acceptance. Its own unchanged
full stock candidate gate remains required after migration. No hardlinks,
reflinks, whole-directory move, file-rename migration or trace editing is used.

## Root-authored plan and receipt contract

No actual plan or acceptance receipt was created. The following is an explicit
schema illustration with invalid placeholders, not an executable instruction or
fabricated acceptance:

```json
{
  "schema": 1,
  "source": {"checkout": "<donor-name>", "candidate": "<40 lowercase hex digits>"},
  "target": {"checkout": "<target-name>", "candidate": "<40 lowercase hex digits>"},
  "accepted_donor": {
    "path": "validation/<root-accepted-donor-receipt>.json",
    "sha256": "<exact receipt SHA256>"
  },
  "reserve_bytes": 335544320
}
```

Checkout names match [a-z][a-z0-9-]{0,63}; the source and target must differ.
reserve_bytes is optional and defaults to the 320 MiB floor. The plan basename
ends in .json and cannot contain a slash. Captured plan bytes must stay stable.

The receipt has exactly these fields:

| Field | Required meaning |
| --- | --- |
| schema | Integer 1. |
| candidate, checkout | Exact donor SHA and checkout name from the plan. |
| accepted | Boolean true, recorded by root after actual gates and reviews. |
| accepted_at | Explicit timezone-aware ISO timestamp. |
| full_check | Reference object with path and SHA256 of the saved full command record. |
| verification | Reference object with path and SHA256 of the saved stock verification JSON. |
| final_verification | Reference object with path and SHA256 of the saved immediate final verification command record. |
| reviews | Object with standards and spec arrays, each nonempty. |

Each review entry has exactly scope, outcome, candidate and report. The outcome
must be Passed, candidate must be the exact donor SHA, and report is its own
path/SHA256 reference. Scope values must be unique within each axis, and both
axes must cover identical scope sets. The intended 901 donor has two separately
preserved scopes, 10013 and 10018: keep both separate Standards reports and both
separate Spec reports and their exact hashes. Do not collapse them into one
report per axis. This verifies root's recorded identities and outcomes, not the
semantic contents or independence of the reports; root's acceptance workflow
remains responsible for that decision.

Both full and final command records must identify the exact candidate and
checkout, status finished, integer exit_code 0, exact head_after and clean_after
true. argv must contain one ./check.sh followed by the required stock command.
The full command is --candidate HEAD with an optional --fresh before or after;
the final command is --verify-candidate HEAD. The full record must have
verification_record_exists true and verification_evidence equal to the receipt's
saved verification path. Additional original wrapper metadata is retained and
permitted; the helper does not rewrite these command records.

The preserved stock verification record must have format 1, result passed,
the exact candidate, a dependency map, a nonempty compiler string, mode matching
the full command, and completed_at. The final command record additionally binds
verification_sha256 to the same saved verification SHA256. The live donor
.lake/verification.json must have exactly that hash. Timestamp order is checked:
verification completed_at <= full ended_at <= final ended_at <= accepted_at.
Root must perform final verification immediately before acceptance; the helper
checks chronology rather than inventing a maximum elapsed time or accepting a
different live record.

Only after actual donor acceptance and independent operational review should
root, in the already pinned Nix environment, run:

```sh
LEAN_NUM_THREADS=1 python3 /workspace/scratch/ca9a61d0bf30/session/validation/migrate-accepted-outputs.py PLAN-BASENAME.json
```

PLAN-BASENAME.json is a placeholder for a real reviewed plan. This command has
not been executed against the workspace candidates. Root should preserve the
terminal record as well as the helper journal. Preflight refusal occurs before
journal creation and is reported on stderr; post-start errors are journaled.

## Journal and interruption behavior

The journal name is fixed from source checkout/full SHA and target checkout/full
SHA under session/validation. A pre-existing pair journal is never overwritten,
including a completed one. All output-migration-*.jsonl journals in that directory
are examined before a CLI attempt. Invalid/truncated journals stop for manual
reconciliation. An unfinished journal naming the same target checkout blocks a
new plan even if a head or donor identity has changed. There is no retry flag,
attempt-name override or silent treatment of owned partial target outputs as an
unrelated pre-existing generation.

States include started, selected, source-verified, planned, copied,
target-verified, source-retirement-started, source-retired, completed and failed.
The planned record contains all source-input/output snapshots and original Lake
descriptors. The target-verified record contains all complete target snapshots
and is fsynced before any retirement. File/parent syncing protects the copied
generation before the journal advertises target success. Normal exception
records preserve the exact successfully removed paths. Abrupt process death can
leave fewer retirement records than removals; the complete verified target and
fixed manifests support root's read-only reconciliation. No automatic inference
or repair is attempted.

A copy or target-verification failure leaves every source file in that failed
batch present; earlier completed batches may already be retired. A source change
caused by an external fixture writer is detected, but naturally the helper
cannot undo that writer's change. A retirement failure retains the whole verified
target, possibly with a partially retired donor. A journal failure also stops;
if even the failed record cannot be appended, the exception reports that fact
and the existing journal is retained. The journal cap is 32 MiB, and exceeding
it stops. Manual reconciliation must preserve evidence and complete target
copies, rather than deleting the failed journal and rerunning this helper.

## Fixture development and terminal evidence

Tests use only self-created disposable directories under the workspace. They
import the stock expected_artifacts parser with Python bytecode writes disabled,
but use a separately literal, opaque-byte fixture verifier. Fixture traces have
synthetic descriptors. No fixture result is a Lake hash check, full candidate
gate, audit result, accepted donor or operational approval. The CLI rejection
test copies the helper under a disposable session/validation directory, creates
only synthetic metadata and runs that copy with an empty PATH; it rejects missing
acceptance before it could invoke Git, Lean or Nix. Temporary fixtures are
automatically removed.

Actual observed red/green history:

| Stage | Observed result |
| --- | --- |
| Initial complete-handoff test against unimplemented public transport seam | 1 test, exit 1; NotImplementedError: The bounded transfer lifecycle is not implemented yet. |
| Implement transport lifecycle | 1 test, 0.084s, OK. |
| Add target-verifier rejection | 2 tests, exit 1; expected final failed journal state, observed copied. |
| Add durable terminal failure record | 2 tests, 0.203s, OK. |
| Add assigned filesystem failure cases | 9 tests, 0.399s, OK. |
| Add missing-receipt check against unimplemented acceptance reader | 10 tests, exit 1; expected Missing accepted donor receipt, observed NotImplementedError from the reader. |
| Implement strict acceptance/plan readers | 10 tests, 0.400s, OK. |
| Add production preflight/CLI | 10 tests, 0.470s, OK. |
| Add minimal positive/mismatched metadata, plan/restart and CLI refusal fixtures | 15 tests, 0.569s, OK. |
| Final recheck after stable plan-read and durable trace-first retirement tightening | 15 tests, 0.569s, OK. |

The final command was:

```sh
python3 session/validation/test-output-migration.py
```

Complete final terminal output, exit code 0:

```text
test_acceptance_binds_both_axes_separate_scopes_and_exact_stock_record (__main__.MigrationTests.test_acceptance_binds_both_axes_separate_scopes_and_exact_stock_record) ... ok
test_cli_refuses_missing_acceptance_before_any_external_runtime_or_output_touch (__main__.MigrationTests.test_cli_refuses_missing_acceptance_before_any_external_runtime_or_output_touch) ... ok
test_copy_failure_keeps_all_donor_files_and_preserves_partial_target_for_diagnosis (__main__.MigrationTests.test_copy_failure_keeps_all_donor_files_and_preserves_partial_target_for_diagnosis) ... ok
test_existing_target_generation_is_skipped_as_a_whole (__main__.MigrationTests.test_existing_target_generation_is_skipped_as_a_whole) ... ok
test_incomplete_reviews_changed_reports_and_mismatched_final_record_reject (__main__.MigrationTests.test_incomplete_reviews_changed_reports_and_mismatched_final_record_reject) ... ok
test_insufficient_reserve_refuses_before_creating_any_target_output (__main__.MigrationTests.test_insufficient_reserve_refuses_before_creating_any_target_output) ... ok
test_missing_accepted_donor_receipt_is_rejected_without_transfer (__main__.MigrationTests.test_missing_accepted_donor_receipt_is_rejected_without_transfer) ... ok
test_plan_reader_confines_paths_rejects_duplicate_keys_and_preserves_reserve_floor (__main__.MigrationTests.test_plan_reader_confines_paths_rejects_duplicate_keys_and_preserves_reserve_floor) ... ok
test_retirement_failure_preserves_verified_target_and_exact_known_progress (__main__.MigrationTests.test_retirement_failure_preserves_verified_target_and_exact_known_progress) ... ok
test_source_change_during_copy_stops_without_retiring_any_donor_path (__main__.MigrationTests.test_source_change_during_copy_stops_without_retiring_any_donor_path) ... ok
test_source_verification_failure_leaves_both_generations_untouched (__main__.MigrationTests.test_source_verification_failure_leaves_both_generations_untouched) ... ok
test_success_retains_every_verified_target_byte_and_unrelated_source_record (__main__.MigrationTests.test_success_retains_every_verified_target_byte_and_unrelated_source_record) ... ok
test_symlinked_target_build_is_rejected_before_journal_or_copy (__main__.MigrationTests.test_symlinked_target_build_is_rejected_before_journal_or_copy) ... ok
test_target_verification_failure_preserves_complete_source_and_failed_journal (__main__.MigrationTests.test_target_verification_failure_preserves_complete_source_and_failed_journal) ... ok
test_unfinished_target_journal_blocks_changed_plan_identity (__main__.MigrationTests.test_unfinished_target_journal_blocks_changed_plan_identity) ... ok

----------------------------------------------------------------------
Ran 15 tests in 0.569s

OK
```

The retirement-failure fixture records exactly the first source trace as removed
before a deliberate sidecar deletion error, retains all target bytes and refuses
to overwrite the prior journal on retry. The copy-failure fixture retains the
whole donor, preserves a partial sidecar at the target and never publishes its
trace. The target-verification rejection fixture preserves a complete donor and
copied target with no retirement start. These are intentional meaningful failure
boundaries, not mocked stock acceptance.

## Frozen file identities and remaining limits

| Owned file | Bytes | SHA256 |
| --- | ---: | --- |
| session/validation/migrate-accepted-outputs.py | 35242 | 6b6f17ec3f4001965eb8a27055e50770f9124676f2d1084f7488a2453cf5b60c |
| session/validation/test-output-migration.py | 19928 | 34e38d23006a05b7687b22c029fde3298d71422e3a085591a14a2851e1db401f |

The report's own exact hash is sent separately to root after this final write.
These files are frozen for independent operational review and checkpoint capture.

Not exercised by this author: a real Nix/compiler/hash invocation, real candidate
acceptance/verification metadata, actual Git/dependency preflight, real /proc
quiescence or established-lock contention, a power-loss recovery, or an actual
ordinary-output migration. The source and target stock gates remain untouched.
The implementation author has not independently approved this helper. Root's
two review axes, actual donor acceptance, fresh scope/space capture and checkpoint
preservation are still required before any real transfer. There is no actual
accepted-donor receipt in this handoff, and the running 901 full check was not
interfered with.
