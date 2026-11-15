# Local validation recorder

This small Linux/POSIX, standard-library Python program records one explicitly
requested command. It implements local requirement 1029, whose frozen source is
`work-state/specs/1029-validation-recorder.md`, SHA256
`a6b39abad520d7b1ed3dc7edb5134399d4f174b496f396798b124e4d17633b48`.
The immutable empty review base is
`e39c76640edbd242762cf41f341d35eae35ee786`.

The recorder changes neither the command's checks nor its success criteria.
Candidate/mode labels are caller descriptions, not candidate, compiler, artifact
or acceptance verification. A recorded child exit 0 is not formal acceptance.

## Launch once, then monitor with short calls

The interface is:

```text
python3 -B recorder.py --cwd /absolute/existing/directory \
  --attempt-dir /absolute/new/attempt --candidate LABEL --mode LABEL \
  [--env KEY=VALUE ...] [--heartbeat-seconds 30] [--cleanup-grace-seconds 5] \
  -- executable argument ...
```

The attempt's parent must already exist. The recorder refuses any existing
attempt location, creates its directory with mode 0700 and its files with
mode 0600, and leaves earlier attempts alone. Values in explicitly supplied
`--env` entries are recorded verbatim. The remaining inherited environment is
passed through without being dumped or silently modified. The requested argv
is passed directly to `Popen(shell=False)`; no shell is used by the recorder.

Use the ordinary foreground `exec_command` lifecycle with a short initial yield
(for example 1000 ms), retaining its returned session identifier. The enclosing
`functions.exec` call should await that one launch and return. Subsequent short
calls read the files; they need no long-lived JavaScript monitoring cell or
child-output forwarding loop. The recorder normally emits no tool output.
Exceptions also receive a best-effort stderr diagnostic.

Root alone may launch the formal fresh2 retry after independent recorder review
and the required uploaded checkpoint. An illustrative invocation from the
already configured pinned Nix development shell is below; this README does not
execute it or authorize an earlier launch:

```sh
python3 -B /workspace/scratch/0c54f2db1fdf/work-state/validation-recorder/recorder.py \
  --cwd /workspace/scratch/0c54f2db1fdf/vfa-validation \
  --attempt-dir /workspace/scratch/0c54f2db1fdf/work-state/validation/1002-candidate-3279bac-fresh2 \
  --candidate 3279bacaec4087cc0d6b7e6b8ae862109cb2dfec --mode fresh \
  --env LEAN_NUM_THREADS=1 --env "PATH=$PATH" --env "NIX_CONFIG=$NIX_CONFIG" \
  -- /root/.nix-profile/bin/nix develop --command \
  ./check.sh --fresh --jobs 1 --candidate HEAD
```

Supply the established Nix environment; the recorder does not construct or
change it. Keep one job and one Lean worker for this recording-only retry.
Neither that concurrency choice nor this recorder is a demonstrated performance
or process-survival fix. The earlier four-worker run was intentionally stopped
for paging; fresh1's unknown disappearance establishes no concurrency cause.

## Files and interpretation

| File | Meaning |
| --- | --- |
| `launch.json` | Immutable requested argv/configuration, original recorder invocation, driver PID/group/session, recorder source path/hash, actual Python executable/version. |
| `run.json` | Atomic state transitions: starting, running, finished. No periodic rewrites while running. Includes owned child PID/group/session, actual return or null, recorder outcome and errors. |
| `heartbeat.log` | Append-only JSON lines, normally every 30 seconds and once after observed child exit. Sequence, UTC, monotonic elapsed time and actual `poll()` result. |
| `child.log` | Direct combined child stdout/stderr in a regular file. Child buffering still applies; silence is not evidence of inactivity. |
| `errors.log` | Append-only JSON diagnostics when recordable. Final-state/close failures also receive best-effort stderr and failed-state recording. |

The launch and transition records use temporary-file write, flush, `fsync`,
atomic replacement and directory `fsync`. Heartbeats are synchronised after
appending; log files are synchronised before normal completion. These operations
provide local filesystem recording, not a guarantee against storage/hardware
failure or workspace loss. A partially written heartbeat can remain on failure.

`finished` describes the recorder's observation ending. Inspect the separate
fields; it does not by itself assert that any child or descendant is quiescent:

- `recorder_outcome: completed` means normal observation/recording completed,
  including for a failing child. `child_returncode` is the raw `wait()` result.
- Normal recorder exit codes preserve a nonnegative child return; a negative
  raw return `-N` maps to wrapper exit `128+N`. The raw value remains separate.
- `recorder_outcome: interrupted` records a handled SIGINT/SIGTERM request and
  exits `128+signal`, independently of how the child responds during cleanup.
- Recording or launch failure gives outcome `failed` and exit 125. A child may
  itself return 125; the outcome fields distinguish those cases.
- A null child return stays unknown. `child_status` distinguishes absence of a
  retained child handle, an unreaped handle, an actually reaped child and an
  unresolved cleanup result. `descendant_quiescence_verified` is always false.

A short monitor can read `run.json`, inspect the tail of `child.log`, and use
only complete valid heartbeat records. This example reports discarded malformed
records and an incomplete tail instead of treating them as success:

```sh
python3 - /absolute/attempt <<'PY'
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
attempt = Path(sys.argv[1])
print((attempt / "run.json").read_text())
records, malformed, partial = [], 0, False
for line in (attempt / "heartbeat.log").read_bytes().splitlines(keepends=True):
    if not line.endswith(b"\n"):
        partial = True
        continue
    try:
        item = json.loads(line)
        stamp = datetime.fromisoformat(item["recorded_utc"])
        if item["schema"] != 1 or not isinstance(item["sequence"], int):
            raise ValueError("unsupported heartbeat")
        if stamp.tzinfo is None or "child_poll_returncode" not in item:
            raise ValueError("incomplete heartbeat")
        records.append(item)
    except (ValueError, KeyError, TypeError):
        malformed += 1
last = records[-1] if records else None
age = None if last is None else (
    datetime.now(timezone.utc) - datetime.fromisoformat(last["recorded_utc"])
).total_seconds()
print(json.dumps({"last_valid": last, "wall_clock_age_seconds": age,
                  "malformed_complete_records": malformed, "incomplete_tail": partial}, indent=2))
PY
```

Missing/unreadable files are also an incomplete observation. A heartbeat proves
only that the recorder recently ran and made that child poll; it does not show
Lean elaboration progress. Wall-clock age may be affected by clock adjustments.
A stale heartbeat or stale running record never authorizes an automatic retry.

## Interruption and recovery limits

The child receives closed stdin and its own process group/session. The recorder
remains an ordinary tool-owned foreground process. Creating that child group is
for scoped cleanup, not daemonization or a claim of detached survival.

SIGINT/SIGTERM handlers remember the first signal without raising inside
`Popen`; ordinary control boundaries then perform cleanup. On interruption or
recording failure, cleanup may send TERM to the child's recorded group only
while the direct child is still unreaped and its group/session equal its PID.
After one grace interval it may similarly send KILL and wait one more interval.
Default waits total at most 10 seconds, plus the main loop's at-most 0.25 second
polling interval and ordinary OS calls. Filesystem or process-creation syscalls
can themselves block; this is not a hard real-time shutdown guarantee.

The recorder refuses launch if SIGCHLD has a nondefault disposition: automatic
reaping could discard the actual return and defeat the unreaped-PID boundary.
It does not silently reset that inherited setting. The recorder is the sole
waiter for its child. Its unreaped PID cannot be
reused between the ownership check and signalling. Once reaped, no further
group signal is sent. Descendants may outlive the leader, ignore TERM, escape
the group or retain log descriptors; no universal quiescence claim follows.
The cleanup result records sent signals, errors and the actual wait result or
null. There is no automatic retry or downstream formal command.

SIGKILL, a lost recorder/workspace, or unrecordable storage failure can leave
partial files and an unknown actual child return. If even failure reporting
cannot be stored, only the nonzero recorder/tool outcome or stderr may survive;
do not interpret an older state snapshot as proof of successful recording.
Preserve original records and report uncertainty. Reassess ownership and current
inputs through the established workflow before any retry; never signal a PID
merely because an old file names it.

Local files survive an output-handle loss only while the filesystem survives.
Uploaded recovery checkpoints supply workspace-loss durability. Active logs
follow the existing growing-log snapshot policy; this recorder changes no
checkpoint policy. A captured heartbeat/run state is historical after restore.
All separate fresh, guarded, ProofAudit, regression, independent review and
final candidate-verification gates remain required.

## Focused tests

Run the captured candidate in a clean isolated recorder checkout, using the
existing pinned conaled development shell:

```sh
nix develop /workspace/scratch/0c54f2db1fdf/conaled --command \
  python3 -B -m unittest discover -s tests -v
```

Tests use short real Python processes and private temporary directories within
that checkout. They cover direct output, closed stdin, literal argv/explicit
environment recording, zero/nonzero/negative raw returns, heartbeat/state
separation, interruption, refusal to overwrite, launch failure and bounded
cleanup after a genuine per-process file-size-limit write failure. An inherited
SIGCHLD-ignore case checks refusal rather than a fabricated zero return. The write-failure test
uses Linux `resource`/SIGXFSZ behavior and verifies an unrelated sentinel stays
alive. No Lean compiler, project validation, shared disk exhaustion or mocks are
used. Exact candidate commands/results are retained outside this source diff
under `work-state/validation/1029-tests-*` for the existing review loop.
