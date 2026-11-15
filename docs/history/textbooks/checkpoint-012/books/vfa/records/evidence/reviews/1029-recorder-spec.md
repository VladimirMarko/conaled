# Local 1029 — independent Spec review

## Outcome and immutable scope

**Spec: Passed. Zero unresolved findings; worst severity: none.** This is the
operational recorder review only. It accepts no chapter, does not authorize a
formal retry by this reviewer, and does not replace the independent Standards
outcome or root's final delivered-content verification and recovery checkpoint.

- Reviewer: `/root/reuse_survey`, 2026-11-02.
- Fixed empty base and verified merge base:
  `e39c76640edbd242762cf41f341d35eae35ee786`.
- Frozen candidate: `f2dd147823effc78974d7b2e5363c993afb0f278`.
- Repository: `/workspace/scratch/0c54f2db1fdf/work-state/validation-recorder`.
- Isolated validation checkout:
  `/workspace/scratch/0c54f2db1fdf/validation-recorder-validation`.
- Full requirements: `work-state/specs/1029-validation-recorder.md`, 4,975 bytes,
  SHA-256 `a6b39abad520d7b1ed3dc7edb5134399d4f174b496f396798b124e4d17633b48`.
- Scope: the entire four-file, 711-line addition from the empty base, using
  `git diff e39c76640edbd242762cf41f341d35eae35ee786...f2dd147823effc78974d7b2e5363c993afb0f278`.
  No unrelated exclusions. All four candidate files were read in full via
  `git show`, along with the saved requirements and validation records.

Both recorder checkout HEADs equal the candidate and both porcelain status
outputs were empty at independent inspection. Each candidate blob, delivered
file, isolated file and recorded digest agreed:

| File | SHA-256 |
| --- | --- |
| `.gitignore` | `05665bc48c874ad36466eea0e797421c88243f7dd9d12e6184016987ff2afa83` |
| `README.md` | `56bc60e710a98e8f8a574c5ec2f8abf013c094f186f287ff64037b0cac6bfdd4` |
| `recorder.py` | `8e5211cd4fd0e6a2eff593af32bea41409675e3165a86946d36dc4156640614a` |
| `tests/test_recorder.py` | `646564267c3ab0a09014d92e1c26d32c89b7f6a9eec63222407cdc91b422043e` |

Applicable guidance read: conaled `AGENTS.md`, implementation workflow,
`docs/agents/review-loop.md`, code-review skill, and README development,
build/audit and execution-boundary sections. This continues the existing 1029
loop; it does not open another implementation or formal-review loop.

## Requirement-by-requirement assessment

### 1. Explicit invocation, environment and identity

Satisfied. `recorder.py:117–142` requires a command vector, existing absolute
working directory, absolute attempt directory with an existing parent, and
candidate/mode labels. Environment entries must have distinct nonempty keys
and contain no NUL. `record` saves the exact requested argv, paths, labels,
explicit environment changes and timing settings, plus recorder invocation,
PID/group/session, actual source hash/path and Python executable/version
(`183–201`). Only supplied changes are overlaid on the inherited environment;
the inherited environment is not dumped (`203–210`). `Popen` receives the vector
with `shell=False`. README explicitly states that labels are descriptions,
not candidate/compiler/artifact verification.

The real-process test at `tests/test_recorder.py:45–86` checks a shell-looking
argument remains literal, explicit configuration is retained, an inherited
sentinel value is absent from launch metadata, and the expected Python identity
and raw nonzero child result are recorded. No environment sanitization beyond
the requested overlay is claimed; callers must supply the established context.

### 2. New private attempt and preservation of earlier attempts

Satisfied. The no-overwrite boundary is `Path.mkdir(mode=0o700)` without
`exist_ok` (`174–178`), including refusal of a pre-existing symlink. Logs are
new exclusive regular files opened with mode 0600 (`51–53`, `179–181`); atomic
JSON uses private `mkstemp` files. If the directory already exists,
`attempt_created` remains false and the final-state path cannot overwrite its
records. The refusal test (`144–156`) preserves exact earlier bytes and verifies
that the requested child never creates its independent marker.

### 3. One owned child and ordinary tool lifecycle

Satisfied. There is one `Popen` call, closed input through `DEVNULL`, and direct
combined stdout/stderr to the opened regular `child.log` (`208–214`). The
successful `start_new_session=True` launch supplies the recorded child
PID/group/session identity. The direct-output test observes actual fd types,
EOF on stdin, both output streams and exit 7. README instructs one ordinary
foreground `exec_command` launch with a short yield and subsequent short file
reads. There is no JavaScript forwarding loop, daemon, service change,
automatic retry or downstream formal operation. Creating the child group is
expressly for cleanup, not a detached-survival guarantee.

### 4. Heartbeat and unchanged checkpoint policy

Satisfied. The default interval is 30 seconds. Each appended JSON line contains
UTC, sequence, monotonic elapsed time and the actual `poll()` result
(`218–236`); it is synchronised after writing. Running-state JSON is not
rewritten for heartbeats. README describes complete-record reading, discarded
malformed/incomplete tails, clock caveats, stale-heartbeat uncertainty and the
fact that a poll is not elaboration progress.

The heartbeat/interruption test (`186–218`) observes at least three genuine
heartbeats, increasing sequence/elapsed observations, null live-child polls,
and unchanged `run.json` bytes and mtime while the child is running. Static
inspection of existing `work-state/tools/checkpoint.py:63–67,118–141,166–167`
confirms that `.log` files are excluded from workflow-stability fingerprints
and copied under the existing prefix-log policy. Ordinary JSON records remain
covered. A launch/terminal transition during capture may therefore cause the
existing stability check to reject that capture; the recorder does not hide
such transitions or change checkpoint policy.

### 5. Atomic critical records and actual child outcome

Satisfied. `atomic_json` writes, flushes, fsyncs, atomically replaces and fsyncs
the containing directory (`36–48`). Launch and starting/running/final states
use it. The raw return is obtained through `wait()` (`231–234`), retained
separately from `recorder_outcome` and wrapper exit mapping (`240–242`).
Zero, nonzero and negative signal returns are exercised by real children;
normal observation of a failing child is correctly distinct from recorder
failure. Handled interruption also stays distinct even when the child responds
to cleanup by returning zero. README warns that a recorded child exit zero
does not establish formal acceptance.

### 6. Recording failures, interruption and owned cleanup

Satisfied within the explicitly documented local-process/filesystem limits.
Exceptions produce failed/interrupted recorder outcomes, best-effort diagnostics
and bounded owned-child cleanup (`243–253`). Signal handlers retain the request
without raising asynchronously inside `Popen`, allowing the returned handle to
be retained first (`145–160`). `stop_owned_child` signals only before the direct
child has been reaped, verifies that its group/session equal its PID, and uses
one TERM grace followed, if necessary, by one KILL grace (`86–114`). It never
signals a group merely because a saved record names it. Nondefault SIGCHLD
disposition is refused before launch (`206–207`), preserving the sole-waiter,
unreaped-child ownership assumption.

Unknown status remains null; cleanup uncertainty is explicit. Descendant
quiescence is always false. Close/final-state write failures select failure
exit 125, with one bounded best-effort failed-state update and stderr fallback
(`254–287`). README accurately warns that storage failure can defeat even
failure recording, that syscalls can block beyond nominal grace intervals,
and that descendants can outlive or escape the leader's group. These are not
claims of hard real-time shutdown or universal quiescence.

The write-failure test (`88–123`) uses an actual per-process file-size limit,
observes TERM followed by the child's raw SIGKILL result, verifies failure
outcome/diagnostics and bounded completion, and confirms an unrelated sentinel
remains alive. Additional tests cover launch failure, inherited SIGCHLD-ignore
refusal and controlled interruption. No mocked successful recording replaces
these process-boundary observations.

### 7. Small implementation and meaningful isolated checks

Satisfied. The 292-line implementation uses only Python standard-library
modules. Seven focused real-process tests exercise the specified behavioral
boundaries plus overwrite, launch-failure and automatic-reaping cases. They
use private temporary directories within the isolated recorder checkout and
short Python children; no Lean compiler or project validation is a test input.
The captured candidate's exact successful test evidence is established below.
No additional reviewer test run was necessary to resolve a remaining risk.

### 8. Monitoring and recovery documentation

Satisfied. README provides the explicit CLI, short launch/monitor workflow,
complete-heartbeat parsing example, output-field and raw/wrapper-return
interpretation, bounded cleanup assumptions, stale-status recovery, and limits
if the recorder, handles, storage or workspace disappear. It separates local
files from uploaded-checkpoint durability. It forbids treating stale state as
permission to retry and requires ownership/input reassessment before retry.

## Intended formal retry and provenance boundaries

The illustrative fresh2 launch uses the unchanged isolated formal candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, a new attempt directory, pinned Nix
invocation, `LEAN_NUM_THREADS=1`, and
`./check.sh --fresh --jobs 1 --candidate HEAD`. Root alone may launch after
independent recorder review and the required uploaded checkpoint. The caller
supplies the established Nix environment; the recorder neither verifies nor
constructs it. This review does not validate a real fresh2 attempt or authorize
the implementer/reviewer to start one.

The source scope changes only the four recorder-repository files. It does not
rewrite the historical fresh1 record, assign its unknown return or cause, or
install its partial outputs. README expressly avoids attributing fresh1's
disappearance to concurrency and avoids a performance/survival claim. All
fresh, guarded incremental, managed audit, regression, independent-review and
final-candidate gates remain separate. The pre-guard incident-preservation plan
remains prospective. Recorder checks supply no chapter credit.

## Validation evidence and independent identity checks

The full recorded invocation was:

```sh
nix develop /workspace/scratch/0c54f2db1fdf/conaled --command \
  python3 -B -m unittest discover -s tests -v
```

It ran in the isolated recorder checkout on the exact candidate using pinned
Python 3.13.15. `1029-tests-final.json` records actual exit 0, 3.009770782 seconds,
and clean before/after status. The complete log reports seven tests passed
(`Ran 7 tests in 2.852s`, `OK`). Independent inspection confirmed:

- Candidate record SHA-256:
  `4896ffd734ac4ee78435a9d9c633e3e7dadee40ed48d966157767f70214e8477`.
- Final result record SHA-256:
  `af3810480d76696a7a4457fef4fe89e38be2356dbc9765355a85a30aa78fe08e`.
- Final log SHA-256:
  `ba2654353226241b24e0682c2e2a73b810c49ddab63bea107d786f83314a78a0`.
- Current conaled `flake.nix` SHA-256
  `0dc6835949ecc2a9e28e9fff16aeb4fa46eca74d1a92132d9a3a236974409f37`
  and `flake.lock` SHA-256
  `8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f`
  match the captured evidence.
- All four source identities agree across candidate blobs, implementation,
  isolated checkout and candidate record; fixed base is empty and is the
  verified merge base.

The earlier red1/green1, red2/green2, red3/green3 and red4 records and logs were
also read completely; every log digest matched its record. They preserve the
initial absent implementation, missing TERM grace, conflated interruption and
SIGCHLD-ignore fabricated-zero failures, with subsequent correction evidence.
They are development history, not substitutes for the final candidate pass.

No reviewer compiler, test, real formal retry, process probe, active-output or
cache inspection was run. Only this review report was written. Successful
recorded tests and static inspection do not prove survival under SIGKILL,
workspace loss, arbitrary disk failure, hostile concurrent mutation, or every
descendant lifecycle. Those limitations are stated by the candidate and are
consistent with this bounded operational contract.

## Findings and disposition

No missing/partial requirement or incorrect implementation was established.
There are no Spec finding identifiers to carry forward from this first review
round, and no unresolved Spec blocker. **Spec Passed for base
`e39c76640edbd242762cf41f341d35eae35ee786` and candidate
`f2dd147823effc78974d7b2e5363c993afb0f278` only.** Root must retain the separate
Standards outcome, confirm final delivered content, and preserve/upload the
required complete checkpoint before any formal retry.
