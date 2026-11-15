# Output migration — independent Standards review, round 1

**Outcome: Passed for the frozen operational-helper scope.** There are **zero
unresolved Standards findings**; worst severity: none. This outcome does not
accept either formal candidate, establish a successful production migration, or
permit bypassing the donor/target gates. Root must still reconcile both review
axes and verify the delivered helper bytes before treating this scope as ready.

Reviewer: `/root/output_migration_review/standards`, independently assigned by
`/root/output_migration_review`. I did not implement these files, read the other
axis's report, run another review loop, or run a compiler, real hash adapter,
real helper invocation, candidate gate, or transfer. My only written artifact is
this report. All inspection of implementation and applicable repository guidance
used the captured Git candidate.

## Exact scope and identity

- Fixed bounded base and original integration base:
  `27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`.
- Candidate: `2748089840723943ddc8ae58acd82f5728b2098b`.
- Independently resolved merge-base:
  `27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`.
- Diff: `git diff 27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405...2748089840723943ddc8ae58acd82f5728b2098b`.
- One task commit: `2748089840723943ddc8ae58acd82f5728b2098b`,
  `chore(validation): capture bounded ordinary-output handoff (#10000)`.
- Complete three-file scope, 1,340 additions; no exclusions or omitted live task
  changes. Both snapshot refs remain reachable.

The baseline and candidate each contain an unchanged `conaled` subtree with
tree ID `3d8e9a8be8d9baf90d12643a8fe6e08565a4e751`, independently matched to
main commit `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. The candidate adds the
three operational files at their actual workspace-relative paths under
`session`. This synthetic workspace-layout snapshot is a review and recovery
object, not a commit to merge into a formal source branch.

| Complete reviewed file | Lines | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| `session/validation/migrate-accepted-outputs.py` | 677 | 35,242 | `6b6f17ec3f4001965eb8a27055e50770f9124676f2d1084f7488a2453cf5b60c` |
| `session/validation/test-output-migration.py` | 352 | 19,928 | `34e38d23006a05b7687b22c029fde3298d71422e3a085591a14a2851e1db401f` |
| `session/research/output-migration-implementation.md` | 311 | 19,501 | `3a9bb1730fed711af1fdb337e8f201c2b979f2a21e8e9e7db6535bb9bfe27f6f` |

I read all three files and independently checked their captured hashes against
the manifest, the isolated fixture record and the live frozen deliverables.
Every comparison matched. Requirements v1 are
`session/requirements/output-migration.md`, SHA256
`ae064e2c3b4e528e5988cc9ed2a63ba0e90bff3b90893998dd01ef73c2b5d323`.
The complete preparatory design has SHA256
`08d3cad5cc7cf01fd6ca35d699242ad74d6efa2370960f4dda80006e0ff9d197`.
Both requirements and design were read in full and matched their saved hashes.

## Applicable standards

I read the candidate's `conaled/AGENTS.md`, `README.md` development-environment
and build/audit sections, `docs/agents/review-loop.md`,
`docs/agents/lake-integrity-incidents.md`, the `code-review` skill and its
heuristics, and the `tdd` skill with its `tests.md` and `mocking.md` references.
There is no candidate `CODING_STANDARDS.md` or `CONTRIBUTING.md`.

The applicable requirements are stable and isolated candidate identity,
artifact-appropriate validation, unchanged stock guard behavior, retained
failure evidence, meaningful tests at agreed public/system boundaries, honest
scope reporting, and independent review of exact bytes. The user's local-ticket
exception supersedes GitHub tracker writes. No new Lean definition, theorem,
proof setting, dependency pin, flake configuration, integrated build tool or
public Lean entrypoint changes in this scope. A separate integrated Lean gate
would not establish the filesystem-helper properties under review.

## Assessment

### Acceptance and environment boundaries

`validate_acceptance` binds exact source identity to terminal successful full
and final command records, the saved and live stock verification digest, and
hashed separate review reports. It rejects incomplete or mismatched axes and
requires nonempty, equal, unique scope sets. The handoff correctly leaves root
responsible for supplying the actual two 901 scopes, 10013 and 10018, and for
assessing report contents and reviewer independence. The helper's metadata is
not represented as authenticating those judgments.

The expected stock record format and fields agree with the unchanged
`conaled/scripts/check.py` read from this candidate. Chronology is checked,
while the requirement to perform final verification immediately before actual
acceptance remains explicit. The helper does not invent acceptance or create a
target verification record.

The production path checks the declared Nix-shell context and serial-thread
setting, rejects a compiler override, removes caller `LEAN_PATH`, takes both
established locks, and checks exact clean heads, private build files, matching
configuration, clean pinned dependencies and compiler identity. Repeated scope
checks preserve this bookkeeping through the batches. The documented frozen
checkout discipline remains necessary: cooperative locks, visible `/proc`
inspection and before/after checks are not represented as immutable snapshots
or defenses against hostile writers.

### Stock adapter and source policy remain intact

I inspected the unchanged adapter's `validate_layout`, `expected_artifacts`,
`inspect_outputs` and extension/path mapping, as well as the old warmer that
supplies the selection basis. The helper uses the pinned adapter directly;
there is no production option to inject the fixture verifier, rewrite expected
hashes, edit a trace or call guard repair. Parser and hash errors propagate into
a stopped attempt with evidence. Missing or changed modules and pre-existing
target generations are handled conservatively without replacing target bytes.

Independent basis-hash checks matched:

| Basis file | SHA256 |
| --- | --- |
| `conaled/scripts/lake_integrity.py` | `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f` |
| `conaled/scripts/lake-output-hashes.lean` | `fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b` |
| `conaled/scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| `session/validation/warm-chapter02-candidate-r3.py` | `886880d620a686b7a427d5e5015439e9898dbe22432dc2f693e407b6d15dd346` |

Selection checks identical tracked module source and complete saved outputs.
It does not claim to establish every transitive compilation input's equivalence.
The target's own stock dependency tracking, complete build and audit remain
mandatory, as required by the README's limits on ordinary output reuse.

### Copy, retirement and recovery ordering

The lifecycle has an explicit filesystem seam and keeps the production verifier
separate from disposable test injection. Copying is exclusive and checks source
identity/content and destination bytes. Files and parent directories are synced;
the trace is copied last within each group. Each batch is independently checked
by the stock target adapter, its snapshots are rechecked, and the complete
target-verified record is synced before source retirement starts.

Retirement reverses the capture order so the source trace is first; its parent
directory is synced before other removals. Only captured ordinary output paths
are removed, after source and peer-target identity checks. Setup files, source,
configuration, dependencies, skipped groups and verification records are outside
the retirement set. There is no rename migration or hardlink/reflink shortcut.

The reserve cannot be lowered below 320 MiB; groups exceeding the fixed 64 MiB
cap are rejected, and the next batch requires its calculated allocation plus
the reserve and a separate 32 MiB journal allowance. Refusal does not shrink the
batch silently or erase earlier completed handoffs.

Exclusive journals, fixed pair identities and unfinished-target detection stop
automatic retry over owned partial files. Normal failures preserve their known
retired-path list; abrupt death may leave fewer progress records than removals,
which is expressly documented. Complete verified target snapshots and fixed
manifests support later manual reconciliation. The implementation neither
claims power-loss recovery was tested nor silently repairs an incomplete run.

### Test design and maintainability

The retained test seams are the transfer lifecycle, external verifier/I/O
failures, metadata input readers and early CLI refusal. The fixtures use known
literal bytes as their expected values and real disposable filesystem effects.
Verifier, copy and removal injections sit at the named system boundaries;
tests do not replace production guard logic. Tests inspect public outputs and
the durable journal that forms part of the recovery contract, rather than
requiring an incidental internal call graph.

The author records an observed red/green development history and honestly
identifies unexercised real-environment behavior. The full captured suite checks
success, source/target verifier refusal, partial copy, retirement interruption,
existing target generations, reserve refusal, source changes, symlink refusal,
missing/mismatched acceptance, separate review scopes, plan parsing, prior
journals and actual CLI refusal before an external runtime call. The last case
uses an empty `PATH` and a copied helper under the disposable root.

I found no concrete maintainability consequence warranting a heuristic finding.
The script's separate metadata, preflight, filesystem and journal functions
serve the specified local workflow; the JSON receipt remains a documented
operational boundary rather than a competing proof or validation system.

## Validation evidence and its limits

The captured isolated fixture record is terminal `finished`, exit code 0, with
15 tests completing in 0.576 seconds. Its candidate is exactly the reviewed
commit, and all four recorded inputs—the three deliverables plus the unchanged
stock parser—match Git and the current frozen files. I reused this successful
evidence rather than rerunning it.

| Evidence | SHA256 |
| --- | --- |
| `session/validation/output-migration-r1-fixtures.json` | `75c388bf059a5ca9ec909e6e792e2d14560a9158d1d32b992d13991b7e7baae7` |
| `session/validation/output-migration-r1-fixtures.log` | `709b0b75f49755f12429f441ef49f4dc56ecac120b092090060105a8dee39e4c` |

This is artifact-appropriate disposable Python evidence for files outside the
integrated Lean repository. It is not evidence that the real Nix/compiler,
Git/dependency, lock-contention or `/proc` preflight has run successfully. It
does not exercise a real stock output hash computation, actual candidate
acceptance, a multi-batch production run, or power-loss recovery. Those limits
are stated rather than converted into hypothetical successes. The production
path must run its unchanged pinned-environment and current-space checks after
actual donor acceptance; the target must subsequently pass its own full gate
and independent acceptance workflow.

No observed integrity incident was diagnosed or concealed by this review.
Any actual unexplained parser/hash failure during later use must be retained
and routed through the existing local incident process, without weakening or
repairing the guard in place.

## Findings and disposition

There are no unresolved Standards findings and no prior Standards finding IDs
to carry forward in this first round. No additional fixture request is needed
to resolve a concrete Standards risk in the reviewed candidate. Both captured
and live deliverable identities matched at review time; root retains the final
delivery identity check and the independent Spec-axis reconciliation.

**Standards: Passed. Findings: 0. Worst severity: none.** Fixed base
`27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`; candidate
`2748089840723943ddc8ae58acd82f5728b2098b`. This report is frozen for the retained
review loop and the next durability checkpoint.
