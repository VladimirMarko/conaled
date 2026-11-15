# Bounded pre-guard assessment for the current VFA candidate

This is prospective execution preparation for the accepted
[1025 preservation plan](1025-pre-guard-preservation-plan.json). It does not
claim that fresh4 completed, that artifacts are consistent, or that either
formal review axis passed. Candidate:
`c988f183887896c00b09aaff9077a6ea7fb8d68f`; enclosing fixed review base:
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The new [collector](1034-pre-guard-assess.py) stays outside the candidate tree.
Its exact preparation checks are recorded separately in
[1034-pre-guard-helper-checks.json](1034-pre-guard-helper-checks.json).
The executable helper SHA-256 is
`a2c40a0a4d786101442bfe923177e245b66b46e9c5bf5544dcbe00e766fb602c`.
Twenty-two focused synthetic checks passed without invoking Lean or reading any
real project artifact directory. The [static advisory](1034-pre-guard-helper-static-advisory.json)
records six preparation defects, their corrections, and the narrow follow-ups;
it is not a formal Standards/Spec approval.

## Prerequisite and one bounded launch

**Do not run this while fresh4 or any writer is active.** Root must first
establish the actual fresh completion, preserve its terminal outcome and full
log, and coordinate stable idle inputs. The collector requires the current
matching `mode: fresh` success record; it copies that record before inspection.
It cannot independently establish process quiescence or infer a lost raw return.
The historical record-protocol clarification remains applicable; unknown actual
outcomes must remain unknown.

Set `vfa_root` to the restored recovery root. The command below uses the already
accepted native environment, `LEAN_NUM_THREADS=1` for Lake's task pool, the
existing recorder, and GNU `timeout`. This variable does not bound the Lean
CLI's internal workers. It does not use Nix or the unrelated ADWH source from the supplied
guide. Keep the prepared native overlay and pinned inputs intact.

```sh
vfa_root=/workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation
python3 -B "$vfa_root/work-state/validation-recorder/recorder.py" \
  --cwd "$vfa_root/vfa-native-validation" \
  --attempt-dir "$vfa_root/work-state/validation/1002-c988f18-pre-guard-assessment-run1" \
  --candidate c988f183887896c00b09aaff9077a6ea7fb8d68f --mode pre-guard-assessment \
  --env LEAN_NUM_THREADS=1 \
  -- /usr/bin/timeout --signal=TERM --kill-after=5s 900s \
  python3 -B "$vfa_root/work-state/tooling/pinned_native_toolchain.py" -- \
  python3 -B "$vfa_root/work-state/validation/1034-pre-guard-assess.py" \
  --root "$vfa_root/vfa-native-validation" \
  --dependency-root "$vfa_root/vfa-validation/.lake/packages" \
  --candidate c988f183887896c00b09aaff9077a6ea7fb8d68f \
  --out "$vfa_root/work-state/validation/1002-c988f18-pre-guard-artifacts1" \
  --provenance "$vfa_root/work-state/validation/1002-candidate-c988f18-native-fresh4/run.json" \
  --provenance "$vfa_root/work-state/validation/1002-candidate-c988f18-native-fresh4/launch.json" \
  --provenance "$vfa_root/work-state/validation/1002-candidate-c988f18-native-fresh4/child.log" \
  --provenance "$vfa_root/work-state/validation/1033-native-environment/acceptance.json" \
  --provenance "$vfa_root/work-state/validation/1033-native-environment/launcher-description2.json" \
  --provenance "$vfa_root/work-state/validation/1033-native-environment/native-candidate-isolation.json" \
  --provenance "$vfa_root/work-state/validation/1002-native-fresh4-preflight.json" \
  --max-entries 100000 --max-copy-bytes 268435456
```

Launch once using a short tool yield and retain its session handle. The recorder
attempt and preservation destination must both be new. Repeated invocation does
not overwrite an earlier attempt. On relocation only `vfa_root` changes.

The assessed project checkout is **`vfa-native-validation`** at the candidate
above. The older `vfa-validation` checkout supplies only the nine shared,
pinned dependency directories through the native checkout's explicit package
symlinks. The two project build directories are separate. `--dependency-root`
is required and is bound to this recovery's exact `vfa-validation/.lake/packages`
directory; each manifest package must resolve to its same-named directory
there. A different target, redirected package root, or redirected target
directory is rejected. Clean Git state and the exact manifest revision remain
required for every dependency before and after assessment. The isolation
record describes the layout when created at the older candidate; the fresh4
preflight supplies the current candidate context. Both records are preserved
as provenance, without treating their historical observations as live checks.

Do not use `timeout --foreground`: the Lean hash helper must remain in the
owned command group. The 900-second TERM deadline and five-second KILL grace
bound this command's normal process lifecycle, including the inspector's
otherwise unbounded child. Filesystem/kernel stalls are not a hard real-time
guarantee. `timeout` status 124, a signal status, a recorder interruption, any
nonzero exit, or a missing/false final `assessment_complete` means incomplete.
Record the actual observed return, not an inferred replacement.

## Scope and interpretation

The collector calls only the unchanged `validate_layout`, `inspect_outputs`
and read-only `expected_artifacts` parser. It does not invoke `check.main`,
`guard_outputs`, Lake builds, cleanup, cache installation, or acceptance.
The guard and Lean hash-helper sources are verified against their accepted
SHA-256 identities before import/execution. `inspect_outputs` uses the pinned
Lake 16-hex hash algorithm, distinct from preservation SHA-256 digests.

The target set is root Lean sources plus recursive `SquareKit`, `Applications`
and `Examples`, excluding only `ProofAudit`. Candidate and clean dependency
identities are compared with the fresh record before inspection and rechecked
after copying. Live Lean/Lake versions, launcher file identities, selected
environment values, source/configuration bytes, exact commands and supplied
fresh/environment evidence are retained. Git optional writes and fsmonitor
hooks are disabled; Python bytecode writes are disabled. No full environment
or credential dump is taken.

The physical inventory covers **all entries** under the project's
`.lake/build/lib/lean` and `.lake/build/ir`. It separately reports untraced
members, modules absent from integrated sources, orphan sidecars, outputs not
described by a usable trace, and unrecognized files. `ProofAudit` remains an
inventoried source excluded from normal guard targets, not an unexplained
module orphan. Compound suffixes such as `.olean.private.hash` are parsed in
the correct order. Unexpected links/special files are recorded without
traversal and stop the assessment before the guard can follow them.

Preservation always selects the four known BoundedSummary/ByteBuffer families,
including consistent survivors, plus every diagnostic or physical suspect and
every unrecognized file. It copies raw artifact parts, traces, sidecars and
available setup files byte-for-byte outside managed caches, retaining source
and copy SHA-256 values and before/after metadata. Optional fixed members that
are absent are explicitly listed; absence alone establishes neither an
obligation to produce that member nor its build history. Source bytes for
selected integrated families are also retained.

The configured limits are 100,000 inventory entries and 256 MiB of copied
evidence. The collector refuses insufficient capacity rather than exhausting
the filesystem. Limits or errors produce an incomplete assessment; no files
are silently omitted from a completed preservation claim. `copies.jsonl`
and `commands.jsonl` retain completed observations during interruption;
`selection.json` identifies intended raw coverage before copying.

`inspection.json` separates API completion from its discrepancy map and
hashed **artifact** count. A complete assessment can exit zero while reporting
many discrepancies. A fresh build leaves incremental project caches unchanged,
so cold missing outputs can be ordinary. Root must classify the evidence using
actual history before any repairing guard. A failed inspector never becomes
an empty successful diagnostic.

Before/after metadata and identity checks do not freeze inputs, authenticate
trace provenance, establish external dependency-cache integrity, or prove
absence of writers. Ordinary reads can update access times. "Non-repairing"
means no intentional candidate/cache-content mutation; new evidence and the
inspector's temporary manifest are written under the new evidence directory.
The already accepted outer native launcher may validate/create its separate
runtime overlay; that environment preparation is outside the collector.

The origin of the four historical mismatches remains unresolved. Current
survivors or regenerated copies cannot reconstruct the lost pre-invalidation
artifacts. Newly material incident evidence must be durably preserved before
repair. The guarded incremental check and audit, managed `+ProofAudit` build,
regressions, both independent formal reviews, and final candidate verification
all remain required. Unexpected managed-audit rebuilding still requires
re-establishing corresponding guard evidence. This collector changes no gate.
