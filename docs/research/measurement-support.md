# Bounded measurement support

#195 Phase 1 extracts the process and recording behavior used by
`scripts/benchmark-order-certificate.py` and
`scripts/probes/run-disk-feasibility.py` into `scripts/measurement.py`. Both
public invocations remain available. The numerical launcher still exercises
the historical #49 feasibility probe against existing project artifacts; it
does not replace the completed disk driver or renew the historical measurements.

The shared interface takes a command vector, working directory, environment,
limits, an evidence prefix and caller metadata. It observes one child attempt,
retains bounded raw stdout/stderr files and returns a receipt. Workload selection,
Lean source handling, tolerance decisions and runtime-output interpretation stay
in the clients. No benchmark framework or build system is introduced.

## Attempts and publication

`run_attempt` exclusively creates `PREFIX.meta.json` with a started observation
before launching. It then exclusively opens `PREFIX.stdout` and `PREFIX.stderr`.
Existing files are not truncated. A failed record or log reservation prevents
launch. The numerical command also reserves `NAME.setup/` and writes a provisional
setup record before inspecting inputs. Use a new name for each invocation,
including after a failed setup. The benchmark uses a new private temporary
directory for each invocation and retains its `results.json` and legacy `.log`
files alongside individual records in `attempts/`.

After observation, a temporary file replaces the owned metadata path. Every disk
payload says `publication: unknown` and `success: false`: the bytes being written
cannot confirm completion of their own write. The returned receipt reports
`publication: confirmed` only after replacement returns. The numerical CLI prints
that receipt; the benchmark prints PASS only after its aggregate publication
returns. Child observations inside the benchmark aggregate retain their returned
receipts. A failed publication yields a non-successful result and never retries
the child. Missing receipts are unknown, including when stdout itself fails.
A process killed between writes can leave a started record or the previous
provisional observation. These are incomplete evidence, not successful attempts.

Process status distinguishes `exited`, `nonzero`, `signal`, `timeout`,
`spawn_failed`, `interrupted`, `observation_failed` and `recording_failed`.
Return codes and signal numbers remain separate fields. A signal does not identify
OOM or CPU exhaustion. Cleanup is confirmed only when the direct child was reaped,
or no child was launched; bounded cleanup that cannot observe reaping remains
unknown. Keyboard interruption during a known child's wait triggers cleanup and
retains an interrupted observation. Uncatchable termination and interrupted
process creation cannot promise a final receipt.

Output distinguishes complete, missing, overflow, invalid UTF-8 and incomplete
cleanup observations. Raw bytes remain in the log files; invalid text is not
silently replaced or interpreted. Reaching the exact byte cap is conservatively
reported as overflow because completeness is not established. The numerical
client additionally rejects missing/malformed terminal events or inconsistent
exit codes. Neither client substitutes zeros for absent measurements.

Atomic replacement is local bookkeeping. It does not imply fsync, crash durability,
authentication or delivery of the returned receipt. The caller must own the
evidence directory exclusively. Concurrent mutation, hostile symlinks and programs
that modify the recorder's files are outside the supported execution contract;
a controlled child does exercise a real publication failure in the test suite.

## Limits and timing

The support targets Linux and single-threaded Python callers. It sets a new process
session, CPU limits, an optional address-space limit and `RLIMIT_FSIZE`. The file
size cap applies to each regular file the child writes, including generated Lean
outputs, not only stdout/stderr. There is no total directory-size guarantee.
The benchmark keeps its 60-second wall/CPU and Lean `-M4096` limits and adds an
8 MiB per-file cap. The numerical launcher retains 16 GiB address space,
15/16-second CPU limits, 25-second wall observation and 8 MiB per file.

On timeout or interruption the runner sends SIGKILL to the new process group and
allows two seconds for direct-child reaping. These are observation budgets under
OS scheduling and syscall assumptions, not unconditional real-time deadlines.
Normal completion confirms only the direct child's exit. Cooperative commands
must not leave background descendants; escaping sessions, arbitrary descendant
cleanup, stuck kernel operations and hostile children are not supported.

`wall_seconds` uses Python's monotonic clock from log setup through process
observation and cleanup. It excludes input hashing, log decoding and metadata
publication. `publication_seconds` in a returned receipt measures its publication
call; a previously returned value can appear in a later aggregate payload.
`max_rss_kib` comes from `wait4` for this child, under Linux's resource accounting;
it is not a cumulative maximum across earlier compiler probes. It includes
startup/imports and is not packet memory or an allocation count. It is absent
when termination was not observed.

The benchmark records source preflight, dependency resolution, build, audit,
import baseline, kernel checking and execution as separate phases. Generated
kernel-proof invocations include import, elaboration and audit overhead.
The runtime invocation includes startup/elaboration; its six inner nanosecond
observations include list construction and checking. The numerical invocation
likewise includes startup/import/elaboration, while retained `step_ns` and
`elapsed_ns` have the scopes stated in the historical checkpoint. Setup and
whole orchestration intervals are separate fields. Whole orchestration excludes
its final aggregate publication. No baseline subtraction or operation-count
conversion produces a claimed pure runtime.

## Inputs and client outcomes

Both clients record SHA-256 identities of integrated project source files,
runner/helper sources, toolchain declaration, Lake configuration/manifest and
flake lock. The benchmark also captures and hashes its local import closure,
generated proof/runtime/audit sources and private inventory helper. It calls the
existing `lean-source-info.lean` parser/policy checker and resolves dependency
paths through Lake. No Python code parses Lean source. The copied audit keeps
its existing exhaustive implementation and uses the real `project_sources.py`
in its private working directory.

Compiler version is checked against `lean-toolchain`. Records include Python/OS,
CPU information where available, affinity, declared caps and PATH/LEAN_PATH.
Arbitrary environment variables are not dumped. Before/after source hashes detect
observed changes, but do not establish coherent snapshots or detect edits that
were restored. Dependencies and their existing artifacts must remain stable and
trusted; manifest identity does not verify artifact provenance. The benchmark
uses fresh private project outputs; the numerical probe uses existing outputs.
Neither receipt is `check.sh --candidate` acceptance evidence.

The numerical CLI preserves the existing process-based exit convention: a valid
zero-exit checked rejection or missed tolerance can still return zero. Read
`numerical.outcome` for `meets_tolerance`, `misses_tolerance`, `checked_rejection`
or `bit_cutoff`. A cutoff retains the accepted prefix and returns nonzero.
Malformed output, input changes and recording failures also return nonzero.
Events retain exact rational budgets/clocks and integer timings as strings.
The parser validates terminal shape, step order, counts and tolerance agreement;
it does not prove the child truthful or replace the numerical correctness proofs.

## Validation and remaining acceptance

Run the lightweight public-interface suite in the pinned shell:

```sh
direnv exec . python3 scripts/test-measurement.py
```

It uses real small children for completion, nonzero exit, signal, partial-output
timeout, failed spawn, file caps, invalid UTF-8, collision and publication failure.
A marker checks that publication failure does not rerun the command. Explicitly
labelled OS-boundary injections exercise interruption and unavailable cleanup
observation; the test supervisor reaps its fixture afterward. Public CLI fixtures
use external Lean/Lake stand-ins to test native-preflight wiring, private audit
inventory, failure retention, source changes and numerical outcomes. The suite
also replays retained checkpoint stdout and exit codes through the numerical CLI
stand-in without rerunning rational computations. These tests do not establish that Lean accepts the generated sources.

A real benchmark run and bounded actual numerical cases, with the corresponding
source identity and applicable build/audit evidence, remain acceptance requirements.
They must use the coordinator's execution slot and stable dependency artifacts.
Historical timing tables are unchanged and supply no validation of this refactor.
Independent Standards/Spec review belongs to the enclosing implementation loop.

## Deferred Lean migration

Phase 2 remains deferred. #194's checked interaction models and #216's controlled
child pilot do not refine this Python adapter. A future bounded contract must
explain reservation before launch, possible spawn failure or interruption,
observed exit versus timeout, partial output, bounded but uncertain cleanup,
input identity observations, provisional publication and a missing final receipt.
It must justify the OS/process/clock/filesystem adapter obligations before any
production migration. Translating subprocess calls to Lean is insufficient.

The #423 author-attempt recorder has its own frozen trial protocol. This work
neither changes that recorder nor requires the trial to adopt shared support.
