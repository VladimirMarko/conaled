# Local 1029 — independent Standards and operational review

## Disposition

**Passed.** Review of the full frozen candidate is complete. There are **zero
unresolved Standards findings**; worst severity: none. Applicable isolated
validation is established by the matching retained evidence below. This is the
Standards axis only and does not substitute for the independent Spec disposition.
It confers no formal chapter credit and does not itself authorize a formal retry.

Reviewer: `/root/cache_review`. Round: 1. Review completed on 2026-11-02.
The implementation was not edited and the tests were not rerun during review.

## Immutable scope and requirements

| Item | Identity |
| --- | --- |
| Repository | `/workspace/scratch/0c54f2db1fdf/work-state/validation-recorder` |
| Fixed empty base | `e39c76640edbd242762cf41f341d35eae35ee786` |
| Candidate | `f2dd147823effc78974d7b2e5363c993afb0f278` |
| Candidate tree | `48d91899c4b9696a4f5f6ecee67addcadc209572` |
| Merge base | `e39c76640edbd242762cf41f341d35eae35ee786` |
| Isolated validation checkout | `/workspace/scratch/0c54f2db1fdf/validation-recorder-validation` |
| Requirements | `work-state/specs/1029-validation-recorder.md` |
| Requirements SHA-256 | `a6b39abad520d7b1ed3dc7edb5134399d4f174b496f396798b124e4d17633b48` |

The reviewer independently resolved both commits, confirmed the empty base tree
and base ancestry, and read every file in the nonempty full task diff:

```sh
git diff e39c76640edbd242762cf41f341d35eae35ee786...f2dd147823effc78974d7b2e5363c993afb0f278
```

Scope is the four added files below, with no task-file exclusions. Candidate
source was read through `git show` at the full immutable SHA. Both the operational
checkout and isolated checkout had the candidate HEAD and empty porcelain
status. All four isolated file hashes independently matched the candidate blobs
and the supplied candidate record.

| File | SHA-256 |
| --- | --- |
| `.gitignore` | `05665bc48c874ad36466eea0e797421c88243f7dd9d12e6184016987ff2afa83` |
| `README.md` | `56bc60e710a98e8f8a574c5ec2f8abf013c094f186f287ff64037b0cac6bfdd4` |
| `recorder.py` | `8e5211cd4fd0e6a2eff593af32bea41409675e3165a86946d36dc4156640614a` |
| `tests/test_recorder.py` | `646564267c3ab0a09014d92e1c26d32c89b7f6a9eec63222407cdc91b422043e` |

The eight commits since the fixed base were inspected. Their subjects use the
repository's Conventional Commit form and local `(#1029)` reference. The supplied
local-ticket requirement supersedes the repository's GitHub tracker direction.

## Applicable standards

The review used the complete saved requirements and these conaled pointers:

- `AGENTS.md`;
- README development-environment and build/audit sections;
- `.agents/skills/code-review/SKILL.md` and `heuristics.md`;
- `docs/agents/review-loop.md`;
- `.agents/skills/implement/SKILL.md`;
- `.agents/skills/tdd/SKILL.md`.

Root-level `CODING_STANDARDS.md` and `CONTRIBUTING.md` are absent. This is a small
operational Python command, not a Lean definition or library abstraction. The
artifact-appropriate check is its focused real-process suite in the pinned
development environment. Integrated Lean verification and statement review are
not recorder tests; the existing formal acceptance requirements remain separate.

## Semantic and operational assessment

**Invocation and confidentiality.** Argument parsing requires an explicit command
vector, an absolute existing working directory, and an absolute attempt path
whose parent exists. The command reaches `Popen` without a shell. Only supplied
environment changes are serialized; the inherited environment is passed through
without enumeration in the records. The launch record also retains recorder
argv, source path/hash, Python identity and driver identities. Candidate/mode
labels are accurately documented as descriptions rather than verification.

**Output ownership and direct logging.** Exclusive directory creation refuses an
existing attempt, including an existing symlink, before launching a child. New
logs use exclusive creation, append mode and private permissions. Child stdout
and stderr go directly to the regular child log; stdin is `/dev/null`. The child
has its own session and process group for scoped cleanup. No forwarding loop,
daemon, service change, auto-retry or downstream formal command is introduced.

**Heartbeat and critical records.** Heartbeats append complete JSON lines with
sequence, UTC, monotonic elapsed time and the actual child poll result, using a
30-second default. The running JSON is not periodically rewritten. Atomic JSON
updates use a same-directory temporary file, file flush/fsync, replacement and
directory fsync; creation of the attempt directory is also synchronized through
its parent. The README distinguishes a partial tail, stale observation and
missing/unreadable files from a complete result, and makes no elaboration-progress
or workspace-survival inference from a heartbeat.

**Actual outcomes.** The authoritative child value is obtained from `wait()` and
stored separately from recorder outcome and wrapper exit code. Negative signal
returns remain negative in the record. Normal child failure, handled interruption,
recording failure, launch failure and an unknown child status remain distinct.
The SIGCHLD-default prerequisite avoids accepting the demonstrated automatic-
reaping case that otherwise loses the child's actual return. A completed zero
return is expressly not a formal acceptance decision.

**Cleanup boundary.** Signal handlers remember a request rather than raising
during `Popen`, so the ordinary control path retains the child handle before
cleanup. Cleanup checks that the child is still unreaped and still has the
created group/session identity before signalling its group. It offers TERM and
then KILL with separate bounded waits, records signal/error/wait outcomes, and
does not signal after reaping. The source and documentation consistently retain
`descendant_quiescence_verified: false`; escaped or surviving descendants are
not represented as absent. A timeout or ownership failure can leave status
unresolved without inventing a raw return.

**Recording failures and recovery.** Exceptions produce failed or interrupted
outcomes as appropriate, a nonzero recorder result, best-effort diagnostics and
owned-child cleanup. Close and final-state-write errors do not silently become
successful recorder outcomes. A bounded final-state retry attempts to preserve
failure when replacement/synchronization fails. The documented limit remains
honest when storage cannot retain even that failure report. Recovery instructions
require renewed ownership assessment before retry, preserve prior attempts,
distinguish local recording from uploaded checkpoints, and leave the one-worker
fresh command and all later formal gates unchanged.

No heuristic prompted a supported finding requiring an additional abstraction,
new test category, or broader scope.

## Validation evidence and methodology

The retained final command was run in the clean isolated recorder checkout:

```sh
nix develop /workspace/scratch/0c54f2db1fdf/conaled --command \
  python3 -B -m unittest discover -s tests -v
```

The saved result records candidate `f2dd147823effc78974d7b2e5363c993afb0f278`,
Python 3.13.15 at the pinned Nix store path, raw return **0**, all **seven tests
passed**, and empty before/after checkout status. The final suite took 2.852
seconds as reported by unittest; the encompassing recorded interval was about
3.010 seconds. The candidate record also retains successful `git diff --check`.

| Evidence | Independently verified SHA-256 |
| --- | --- |
| `validation/1029-candidate.json` | `4896ffd734ac4ee78435a9d9c633e3e7dadee40ed48d966157767f70214e8477` |
| `validation/1029-tests-final.json` | `af3810480d76696a7a4457fef4fe89e38be2356dbc9765355a85a30aa78fe08e` |
| `validation/1029-tests-final.log` | `ba2654353226241b24e0682c2e2a73b810c49ddab63bea107d786f83314a78a0` |

The Nix input hashes were independently checked against the candidate record:
`flake.nix` is `0dc6835949ecc2a9e28e9fff16aeb4fa46eca74d1a92132d9a3a236974409f37`;
`flake.lock` is `8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f`.

The tests exercise the public command/file boundary with actual short processes:
literal argv, explicit environment recording without inherited-value disclosure,
regular stdout/stderr descriptors, EOF stdin, zero/nonzero/negative returns,
exclusive attempt creation, launch failure, append-only heartbeat behavior with
stable running-state bytes, and interruption distinct from a cooperative zero
child exit. A real per-process file-size limit creates a recording failure; the
test observes TERM before KILL, a bounded result, the actual negative child
return, and an unrelated sentinel remaining alive. The SIGCHLD-ignore test checks
refusal instead of a fabricated zero. These are meaningful behavior checks, not
mocks of internal recorder functions.

All four saved red records, all three intermediate green records, and the final
green record were read together with their complete logs. Each log digest matched
its associated JSON record. The failures are retained as failures: missing initial
implementation, absent TERM grace, interruption conflated with failure, and
automatic reaping returning a fabricated zero. Subsequent commits and final
evidence support the corresponding corrections. The final candidate's successful
suite is the acceptance evidence; earlier snapshots supply development provenance.

## Findings and limits

**Findings: none.** There are no unresolved IDs from an earlier recorder review
round and no blocked validation requirement for this operational candidate.

The review reuses matching saved tests and does not claim they exhaust OS failure
or scheduling behavior. It does not establish hard real-time cleanup, universal
descendant quiescence, power-loss guarantees, supervisor survival, workspace-loss
durability without an uploaded checkpoint, or any formal result. These limits are
explicit in the candidate rather than concealed by a successful recorder status.

No additional tests, Lean/compiler/helper commands, formal retry, process survey,
active-log inspection, cache/archive reads, or implementation edits were performed
by this reviewer. This report is outside the source diff. Root must retain both
independent outcomes, verify the accepted task bytes still match the candidate,
and create/upload the required complete checkpoint before any real fresh2 launch.

**Final Standards outcome: Passed — base
`e39c76640edbd242762cf41f341d35eae35ee786`, candidate
`f2dd147823effc78974d7b2e5363c993afb0f278`, zero unresolved findings, worst severity
none.**
