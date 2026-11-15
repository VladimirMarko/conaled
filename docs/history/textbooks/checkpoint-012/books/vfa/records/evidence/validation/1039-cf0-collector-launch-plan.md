# Prepared collector launch — cf0 candidate (superseded before execution)

The cf0 fresh attempt failed at937; this collector command was never eligible
to run. Rebind candidate, provenance and unused output paths after local1040
and a new complete fresh success. See1040-fresh-failure.json.

Operational preparation returned by the retained recovery-metadata assistant on
2026-11-04. No collector, compiler, cache scan, or live-session operation was
performed for this preparation. This document is a plan, not gate evidence.

Use the unchanged collector, SHA256
`a2c40a0a4d786101442bfe923177e245b66b46e9c5bf5544dcbe00e766fb602c`.
Only launch after the current fresh attempt actually succeeds and its complete
kit result/output, execution-API terminal outcome, and byte-identical fresh
verification record are preserved. The current live prefix is insufficient.

Proposed unused destinations, checked absent at preparation time; recheck before
launch and do not precreate the collector's artifact directory:

- `validation/1002-candidate-cf0a687-pre-guard-artifacts1`
- `validation/1002-candidate-cf0a687-pre-guard-run1`

```sh
vfa_recovery='/workspace/scratch/60f07f0e98c8/conaled-vfa'
vfa_work_state="$vfa_recovery/work-state"
vfa_fresh="$vfa_work_state/validation/1002-candidate-cf0a687-summation-fresh1"
python3 -B "$vfa_recovery/native-kit/conaled_native.py" \
  --state '/workspace/scratch/60f07f0e98c8/native-state' \
  run --project "$vfa_recovery/vfa-summation-validation" --threads 1 -- \
  /usr/bin/timeout --signal=TERM --kill-after=5s 900s \
  python3 -B "$vfa_work_state/validation/1034-pre-guard-assess.py" \
  --root "$vfa_recovery/vfa-summation-validation" \
  --dependency-root "$vfa_recovery/vfa-validation/.lake/packages" \
  --candidate cf0a687265c1929ffd3ff6f15fa18febe0fb61b5 \
  --out "$vfa_work_state/validation/1002-candidate-cf0a687-pre-guard-artifacts1" \
  --provenance "$vfa_fresh/launch.json" \
  --provenance "$vfa_fresh/start.json" \
  --provenance "$vfa_fresh/output.log" \
  --provenance "$vfa_fresh/result.json" \
  --provenance "$vfa_fresh/terminal.json" \
  --provenance "$vfa_fresh/fresh-verification.json" \
  --provenance "$vfa_work_state/validation/1039-environment-ready.json" \
  --provenance "$vfa_work_state/validation/1039-candidate.json" \
  --provenance "$vfa_work_state/validation/1039-new-worktree-isolation.json" \
  --provenance "$vfa_work_state/validation/1039-cache-scope.json" \
  --provenance "$vfa_work_state/validation/1038-environment/project-smoke-result.json" \
  --provenance "$vfa_work_state/validation/1038-doctor.json" \
  --max-entries 100000 --max-copy-bytes 268435456
```

Invoke directly with `tty:true`; timeout is inside the kit's `run --` command.
No historical outer recorder. Save actual launch and terminal records, and the
kit's unique start/output/result, under the separate run directory.

At launch, current available capacity must cover selected raw evidence plus
64 MiB reserve. Preserve the 256 MiB total-copy and 100000-entry limits. Require
actual success, `assessment_complete`, `preservation_complete`, and
`inspection.completed` true, `observed_changes: []`, and equal before/after
identities. Exit zero alone does not mean no discrepancies.

Classify every reported discrepancy and all four historical families before
repair: Applications.Resources.BoundedSummary, Examples.BoundedSummary,
Applications.Sequences.ByteBuffer, Examples.ByteBuffer. Cold missing managed
outputs are not corruption. Newly material incident evidence must be durably
preserved before a repairing guard.

Keep the accepted isolation boundary: the old checkout and shared dependencies,
compiler/profile remain frozen; old-descendant quiescence remains unknown.
There is no competing writer into current assessed inputs. The collector does
not establish quiescence. No old project output or verification record is reused.

The collector also preserves current verification, toolchain/manifest/Lake
configuration, checker/guard/hash-helper, and its own source automatically.
The remaining guarded audit, managed audit prerequisite, four regressions,
retained two-axis evidence review, immediate verification and acceptance
checkpoint are unchanged; see ../tooling/ACTIVE-NATIVE.md.
