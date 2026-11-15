# Paired-journal cohort 01 results

Both independent authors completed the frozen task and passed the same private
oracle. The conclusion is **refine the facade**: it preserves the required
mathematics, but facade/native path conversion imposed additional repair work
in this trial. The successful facade submission uses the permitted baseline
path constructor while retaining facade section transport, recovery and decoded
transport. This is one paired task with one author per arm, not evidence of a
general performance advantage for either route.

The immutable release was `a5c17c25e9753f5dcb1d3be2119a8d4bd747ef24`.
[release-01.json](release-01.json) records empty-history author assignments,
accepted protocol reviews, validation, exposure hashes and copied warm caches.
The original cohort README and freeze manifest remain unchanged; their
pre-release status is historical. This directory supplies the subsequent result.

| Observation | Direct | Facade |
|---|---|---|
| Complete submitted construction and changed invariant | Passed | Passed |
| Common frozen oracle | Passed | Passed |
| Compiler passes through the public checker | 2 | 4 |
| Native paths | Baseline `uaStructureIdentity.symm` | Baseline `uaStructureIdentity.symm` after facade conversion timeouts |
| Sections and decoded transport | Baseline APIs | Facade APIs |
| Mathematical assistance | None | None |
| Heartbeat changes during author execution | None | None |

The direct first pass reached all native constructions but failed on an
`IsEmpty` declaration's reducibility warning and concrete predicate decisions.
The second pass repaired declaration form and unfolding. The facade first
three passes encountered default-heartbeat exhaustion at the facade/native
path boundary, with endpoint annotations and inferred result types tried in
turn. Its fourth pass used baseline native path construction. The concrete
predicate examples also needed unfolding. All failed sources and complete logs
are retained, including cascading diagnostics. A compiler pass is a recorded
validation invocation, not a measured unit of author work.

Both authors received the same queue-only clarification while the shared lock
was occupied by #567's full audit. [coordination-messages.jsonl](coordination-messages.jsonl)
retains its text. There was no mathematical hint, private fallback recipe or
interface/source change during author execution. Reported source exposure and
role separation are cooperative experimental controls, not security guarantees.
Model identity, sampling configuration and token counts were unavailable.
Host load and temperature were not measured. Queue timestamps and durations
remain in the raw records but do not establish author speed.

## Evidence and reproduction

- [authors/manifest.json](authors/manifest.json) hashes every frozen submission,
  attempt source, log and author effort record. The direct final source is
  attempt 02; the facade final source is attempt 04.
- [authors/direct/effort.md](authors/direct/effort.md) and
  [authors/facade/effort.md](authors/facade/effort.md) describe actual helpers,
  local repairs, native dependencies and unavailable telemetry.
- [preparation/](preparation/) contains the final private oracle and both
  feasibility solutions in readable form. The complete original
  [preparation-private-archive.tar.gz](preparation-private-archive.tar.gz)
  preserves all preparation failures and repairs, with every member hash in
  the unchanged freeze manifest. It includes the failed raised-heartbeat
  diagnostic; final feasibility and author execution used default limits.
- [author-oracle-replay-identity.json](author-oracle-replay-identity.json) and
  [author-oracle-replay-01.log](author-oracle-replay-01.log) retain the original
  common-oracle replay. The raw oracle-body hash includes its final newline;
  the freeze body's hash omits it. The bodies are otherwise byte-identical.
- [native-dependencies.md](native-dependencies.md) records source/statement
  review and the exact mechanical adaptations used for integrated audit.

From the repository root, verify the evidence without invoking Lean:

```sh
direnv exec . python3 experiments/univalent-package-authoring/cohort-01/results/reproduce.py
```

With built project dependencies, replay both unchanged submissions and both
private feasibility solutions:

```sh
direnv exec . python3 experiments/univalent-package-authoring/cohort-01/results/reproduce.py --run
```

The script obtains the shared lock, pins CPU 0 and nice 10, and enters the
repository's Nix environment. It writes scratch modules and logs to a new
printed temporary directory. `--output /absolute/new/directory` chooses that
location. In an isolated worktree whose `.envrc` is not authorized, pass
`--environment /path/to/authorized/checkout` with the same pinned environment.
The replay changes only each oracle's first import for the author
arms. It does not rerun failed attempts or claim their diagnostics must remain
identical on a newer compiler. Exact historical failures are the retained logs.
For historical replays use the release commit and its pinned toolchain; later
library changes may affect old sources.

The five modules in `Examples/UnivalentAuthorTrial/` retain the task, both
successful submissions and both oracle instances in the normal build and
exhaustive audit. Only imports and author/oracle namespace names change; the
script checks these transformations byte for byte. Archived sources remain
unchanged. Full candidate acceptance and independent review are coordinated
separately; an archive or focused replay is not itself integrated acceptance.

## Follow-up

A bounded follow-up should repair elaboration across the facade/native path
boundary without changing the admitted map, original contraction, native path
family or recovery contract. Retain these failures as regressions, check the
explicit baseline-typed `NativePath` annotation and recovery expression under
default limits, and preserve both complete oracle outcomes. The current cohort
must remain frozen. A new usability claim requires a separately frozen fresh
task and independent authors after the repair; reusing this published solved
task would test regression only. General family admission, higher witness
coherence, source conversion and broad frontend adoption remain separate work.
