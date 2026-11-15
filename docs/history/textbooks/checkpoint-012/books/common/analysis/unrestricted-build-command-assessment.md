# Full build without agent-selected resource caps

Read-only command audit, 14 November 2026. Candidate:
`18235331da1fe343d09080ca4c41173f9b4d9963`.

The user's latest instruction supersedes the earlier recommendation to select
2 or 4 launcher threads. Use the runtime's normal hardware-based defaults;
do not replace the old cap with an explicit 9-CPU setting.

## Exact command

After root completes the existing pinned setup, with these task-specific path
variables set to the actual kit, runtime state and isolated candidate checkout:

```sh
python3 -B "$CONALED_KIT/conaled_native.py" \
  --state "$CONALED_NATIVE_STATE" \
  run --project "$CONALED_CANDIDATE_DIR" -- \
  env -u LEAN_NUM_THREADS PYTHONDONTWRITEBYTECODE=1 \
  ./check.sh --candidate HEAD
```

The native-kit CLI accepts positive integers for `--threads`, defaults to 1,
and has no automatic/unset mode. Omitting the option alone retains the cap;
`--threads 0` and `--threads auto` are invalid. The command above removes
`LEAN_NUM_THREADS` **after** the kit injects it. The later tool wrappers call
`child_environment`, which preserves its absence; they do not reinsert it.
The installed GNU `env` supports `-u`.

Do not use `env -i`: the remaining environment selects the pinned tools and
required native compatibility paths. Keep `PYTHONDONTWRITEBYTECODE=1` to
avoid generated Python files beside tracked sources; it is not a compute cap.

## Audit results

- **Threads:** `LEAN_NUM_THREADS` is the only thread-control variable injected
  by the kit. The inspected caller environment contains none of the selected
  Lean, OpenMP, BLAS, Rayon, Cargo/Make or general job-control variables.
  Without it, Lake's ordinary executable runtime selects detected hardware
  concurrency. Lean's CLI uses its separate hardware-based default unless
  `lean -j` is supplied; this command supplies none. Neither runtime setting
  is a universal child-process or OS-thread ceiling.
- **Checker jobs:** `scripts/check.py` calculates a default of up to four
  jobs, but only the fresh-mode branch uses it. The normal incremental branch
  delegates scheduling to Lake. Do not add `--jobs` or select `--fresh`
  merely to change resources.
- **Memory and CPU time:** neither the inspected kit nor checker applies
  `setrlimit`, `ulimit`, a Lean memory limit or a CPU-time budget to this
  build. Current address-space, data-size and CPU-time limits report unlimited.
- **Affinity and deadlines:** no agent-applied affinity or priority wrapper is
  present. The launcher passes no timeout to its normal `run` path; checker
  subprocess calls have no timeout. The launcher's short selector poll interval
  is not a build deadline. Do not add an outer `timeout`, recorder deadline,
  `taskset`, `nice` or `prlimit` restriction.
- **Unchanged controls:** retain the project ownership lock, clean isolated
  candidate, exact pins, source/coverage checks, integrity guards, required
  cache policy and exhaustive audit. Leave platform, sandbox and security
  controls untouched. Normal OS process/stack limits are not known agent-set
  build restrictions and were not changed.

## Recording caveat

The frozen launcher's start/result JSON will still record
`"lean_threads": "1"`, because it observes the environment before the child
`env -u` executes. Preserve that historical-kit output unchanged. Record the
exact argv and the effective setting `LEAN_NUM_THREADS absent; hardware default`
in the new run's supplemental evidence; do not report the pre-child metadata
as an effective cap.

For stronger direct evidence, root may put a short read-only observation before
execing `./check.sh` in the same child process chain: assert that
`LEAN_NUM_THREADS` is absent, print only selected resource variables and
CPU/memory resource limits, flush, then `os.execv` the unchanged checker.
This observation must not impose a time or resource limit. No such command or
build was executed in this audit.

Removing our restriction does not remove host quotas or guarantee faster
execution. Preserve actual terminal evidence, including any resource failure
or interruption; do not infer either success or a cause from lost handles.
The existing receiving validation gate remains pending unless this exact
candidate completes all required validation and review.

## Evidence

The companion JSON binds the inspected frozen launcher/runtime and candidate
checker/configuration bytes. Pinned Lean/Lake scheduling semantics were already
verified in `build-resource-assessment-evidence.json`. This audit performed no
setup, network access, build, source/checkpoint edit, Git write or host-control
change; it wrote only these intake records.

