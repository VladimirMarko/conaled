# #358 setup runner Standards review

Outcome: **Passed** for the bounded instrumentation implementation and supplied stub tests. Zero findings. Real frozen-wrapper smoke checks remain a dispatch gate.

Reviewed `/tmp/conaled-362-orchestration/run_attempt.py`, `test_runner.py` and `runner-unit-results.json`. This is environment setup already contemplated by the frozen protocol. It does not change mathematical tasks, arm outcomes, permitted assistance or the attempt checker. This review does not reopen or replace the interface freeze review.

The runner validates a direct existing `attempts/*.lean` source, exclusively creates a per-name receipt before invoking a check, records waiting/running/finished status, acquires the common exclusive flock before starting the unchanged checker command, and holds it through checker completion. `time.monotonic()` separates pre-acquisition waiting from checking. UTC start/finish and monotonic durations retain ordering and elapsed time; acquisition time is represented by start plus the recorded wait duration. The checker receives an argument list without shell interpolation. Its ordinary success/failure exit code is recorded and returned. The wrapper's own archives retain source bytes and diagnostics.

The supplied tests use a fake direnv and establish success propagation, failure exit 7 propagation, contended-lock exclusion and duplicate-name rejection preserving the original receipt. The contended observation records about 0.672 seconds waiting and 0.00255 seconds checking. These tests exercise instrumentation only and explicitly say so. The checked files and evidence hashes appear below; later changes require review of the changed implementation.

Peak RSS is labeled Linux RUSAGE_CHILDREN high-water memory rather than aggregate concurrent RSS. Each invocation starts a fresh runner process and launches one checker child. The metric includes the launcher/checker process chain and available inherited descendant accounting; it is an observation of that invocation, not a Lean-only or total simultaneous-memory measurement. The current Linux host matches its KiB labeling.

An interrupted or failed-to-launch invocation may leave a waiting/running receipt without completion fields. Preserve it as incomplete evidence; do not infer zero duration or successful checking, and use a fresh attempt name. Receipt updates are not claimed crash-atomic. These limits are acceptable for the cooperative trial setup and do not weaken the required preservation of failures.

Before dispatch, include the identical runner and invocation instructions in both frozen public handoffs, retain its source hash, and run both real-wrapper success and deliberate-failure smoke checks through this runner. Confirm those receipts match the wrapper archives and unchanged public manifests. The existing smoke utility invokes check_attempt.py directly, so its receipts alone would not establish the runner-to-real-wrapper connection. Preserve the controlled lock-wait evidence already supplied. Author active time must still include editing, reading, reporting and checking; this runner measures checker/lock intervals only and does not implement the full stage budget clock.

SHA-256 identities:

- run_attempt.py: `1f5662f07ee9c4753576b8e8d6504e9bf76d3412c3ea13563ea86276120e57da`
- test_runner.py: `aa9c6de1690f6c6447b3ce3a73faa1641e44517b4756311b7d6f6f88dbf4d1ce`
- runner-unit-results.json: `913e7aa83432946ce994398e610ccc740d6a9d915e178a4488eaee2bd114aa1d`
