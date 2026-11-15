# Preface/Perm: remaining gate readiness under the unified native kit

Recorded: 2026-11-04 UTC. Prepared by the existing formal review coordinator from a bounded read-only readiness pass and saved on root's explicit instruction. **Status: prospective analysis; Standards Blocked; Spec Blocked.** This note is not a completed validation result, a new review loop, or an acceptance decision. No compiler, collector, regression, cache action, or formal source edit was performed for this note. Its only new filesystem artifact is this evidence file.

At the save request, root reported the current fresh attempt at approximately 460/953 ordinary modules with no errors. That progress report establishes no gate completion. All later results must be recorded from their actual executions.

## 1. Fixed scope and retained findings

| Item | Identity or status |
| --- | --- |
| Formal fixed base / merge-base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Exact formal candidate | `c988f183887896c00b09aaff9077a6ea7fb8d68f` |
| Full review scope | 25 files, +496/-17, no exclusions |
| Current isolated checkout | `vfa-native-kit-validation` under the restored recovery root |
| Dependency source | Same root's `vfa-validation/.lake/packages`, containing the nine real clean pinned repositories |
| Current fresh evidence | `validation/1002-candidate-c988f18-unified-fresh1/` |
| ST-001 | Fixed; unchanged |
| ST-002 | Open: historical BoundedSummary/ByteBuffer artifact incident assessment and successful recovery evidence remain |
| SP-VAL-001 | Open: completed exact-candidate validation remains |
| Formal axes | Both Blocked; no Preface/Perm acceptance and no authorization to advance to Sort from this note |

The independent Standards and Spec axes already completed the current source review, reusing unchanged earlier analysis. Their latest source delta was only `import Lean` to `import Init` in `Squares.lean` and `Dependent.lean`; they found no new source findings. Their retained records are `reviews/1002-Perm.md`, `reviews/1002-unified-continuation-brief.md`, and `reviews/1002-unified-source-review.md`. The operational compact-checkpoint review and successful restore smokes are separate from formal acceptance.

The authoritative requirements remain `REQUIREMENTS.md`, `AMENDMENTS.md`, `specs/1002-Perm.md`, and `specs/1002-full-requirements.md`, with the existing preservation plan and record-protocol clarification cited below. This note translates the remaining execution sequence to the unchanged user-selected unified kit; it changes no proof or acceptance requirement.

## 2. Environment and ownership

In the current session, the recovery root is:

```text
/workspace/scratch/60f07f0e98c8/restored/conaled-vfa-checkpoint-042-native-j1-validation-readiness
```

The current kit and runtime state are:

```text
/workspace/scratch/60f07f0e98c8/restored/conaled-native-kit-4.35.0
/workspace/scratch/60f07f0e98c8/native-state
```

A compact recovery restores the complete kit under `native-kit/` inside its restored root. Follow `tooling/UNIFIED-NATIVE.md` and rebind the paths to that restore; old absolute paths, process IDs, and tool-session handles do not establish a live environment. Provisioning and project doctor target the real `vfa-validation` checkout. Formal execution targets `vfa-native-kit-validation`, whose `.lake/packages` parent is real and whose nine package entries individually link to the same-named real dependency directories. Its project `.lake/build` is private.

Root owns all compiler, cache, process, source, acceptance, and upload actions. Keep both checkouts and the shared dependencies under sole writer ownership during gates. The kit locks by project path, so the two paths do not themselves provide a shared lock. No cache hydration or directory moves may occur while validation uses these inputs. No GitHub write is authorized.

Every remaining gate uses the same unchanged kit's `run --project ... --threads 1 --` route. This sets `LEAN_NUM_THREADS=1`; the kit does not inject Lean CLI `-j1`. The fresh checker's `--jobs 1` limits its external compiler concurrency. Neither option is an OS-thread or RSS bound. Do not relabel this run as the historical native-j1 attempt.

Expected compiler identity:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

## 3. Fresh gate: completion and evidence to preserve

The current payload is:

```sh
./check.sh --candidate HEAD --fresh --jobs 1
```

It started at `2026-11-03T23:29:01.187276+00:00`. Its source/coverage/version checks reported 954 local modules: 953 ordinary modules followed by the exhaustive `ProofAudit` driver. Partial module progress, the historical focused foundation checks, and native environment smokes do not replace completion of this gate.

Before beginning the collector or any later candidate check, retain:

1. The complete actual launch, recorder result, heartbeat, direct child log, errors, and terminal outcome where available, attributed to this attempt and exact candidate.
2. Completion of all 953 ordinary module compilations and the fresh exhaustive audit; the checker must complete cleanup and its final stable-input identity check.
3. A separate attempt-specific copy of the newly produced `.lake/verification.json`, with `format: 1`, `result: "passed"`, `mode: "fresh"`, the exact candidate, all nine exact dependency revisions, the full compiler string, and its attributable `completed_at` value.
4. Root's establishment of stable idle inputs before non-repairing preservation and later operations.

The checker removes its active verification record at the beginning of a new candidate validation. Preserve the fresh record before the guarded check replaces it. Do not move an old success record back into the active path to satisfy a later prerequisite.

If the original wait/terminal status becomes unavailable, retain that uncertainty. `reviews/1002-fresh2-record-protocol-clarification.md` permits an authentically attributable fresh success record, corroborating compilation/audit chronology, and successful supported `./check.sh --verify-candidate HEAD` to establish recorded fresh completion while the original raw exit remains unknown. This conditional route does not authorize inventing exit zero or relying on an unattributed matching JSON file. It changes no later gate.

## 4. Non-repairing collector: exact nesting, capacity, and evidence

The collector remains the unchanged `validation/1034-pre-guard-assess.py`, SHA-256:

```text
a2c40a0a4d786101442bfe923177e245b66b46e9c5bf5544dcbe00e766fb602c
```

Its retained scope and limits are in `validation/1034-pre-guard-assessment-handoff.md` and `validation/1025-pre-guard-preservation-plan.json`. The old handoff's outer timeout was for an older exec-style native wrapper. For the unified kit, put GNU timeout **after the kit's `run ... --`**, so timeout and the collector's descendants are in the payload's owned process group. The kit launches that payload using `subprocess.Popen(..., start_new_session=True)`; a timeout outside the kit would not establish the same descendant bound. Do not use `timeout --foreground`.

The following is a prospective current-session invocation. Execute only after actual fresh completion, preservation of its record, stable idle inputs, and a fresh capacity measurement. Both destination names must be unused; if a prior launch exists, allocate new names and retain the earlier attempt. On compact restore, adjust the recovery, kit, and state paths and provide the actual newly established provenance.

```sh
vfa_root=/workspace/scratch/60f07f0e98c8/restored/conaled-vfa-checkpoint-042-native-j1-validation-readiness
vfa_kit=/workspace/scratch/60f07f0e98c8/restored/conaled-native-kit-4.35.0
vfa_state=/workspace/scratch/60f07f0e98c8/native-state
vfa_fresh="$vfa_root/work-state/validation/1002-candidate-c988f18-unified-fresh1"

python3 -B "$vfa_root/work-state/validation-recorder/recorder.py" \
  --cwd "$vfa_root/vfa-native-kit-validation" \
  --attempt-dir "$vfa_root/work-state/validation/1002-c988f18-unified-pre-guard-assessment-run1" \
  --candidate c988f183887896c00b09aaff9077a6ea7fb8d68f \
  --mode pre-guard-assessment \
  -- python3 -B "$vfa_kit/conaled_native.py" --state "$vfa_state" \
  run --project "$vfa_root/vfa-native-kit-validation" --threads 1 -- \
  /usr/bin/timeout --signal=TERM --kill-after=5s 900s \
  python3 -B "$vfa_root/work-state/validation/1034-pre-guard-assess.py" \
  --root "$vfa_root/vfa-native-kit-validation" \
  --dependency-root "$vfa_root/vfa-validation/.lake/packages" \
  --candidate c988f183887896c00b09aaff9077a6ea7fb8d68f \
  --out "$vfa_root/work-state/validation/1002-c988f18-unified-pre-guard-artifacts1" \
  --provenance "$vfa_fresh/run.json" \
  --provenance "$vfa_fresh/launch.json" \
  --provenance "$vfa_fresh/child.log" \
  --provenance "$vfa_root/work-state/validation/1036-doctor.json" \
  --provenance "$vfa_root/work-state/validation/1036-isolation.json" \
  --provenance "$vfa_root/work-state/validation/1036-unified-setup/last-smoke.json" \
  --provenance "$vfa_root/work-state/validation/1036-runtime-route-decision.md" \
  --max-entries 100000 --max-copy-bytes 268435456
```

Retain the kit's command evidence as well as the outer recorder's actual result. The 900-second TERM deadline and five-second KILL grace apply to the collector payload; they are not a hard real-time guarantee against filesystem/kernel stalls. A timeout, interruption, signal termination, nonzero result, or missing final completion flag leaves this gate incomplete.

### Capacity prerequisite

The actual refusal condition in the collector is:

```python
shutil.disk_usage(out).free < selected_raw_bytes + 64 * 1024 * 1024
```

Thus available bytes must cover the selected evidence plus **64 MiB reserve**. The copied-evidence limit remains **268,435,456 bytes (256 MiB)** and the inventory limit remains **100,000 entries**. `shutil.disk_usage(...).free` reflects available blocks in this environment; total physically free blocks alone do not establish that the gate will pass.

Root's last reported measurement during the readiness pass was about 3.63 GB physically free but only 178 MB available at 00:07:49 UTC. This is historical context, not a current preflight result. Fresh temporary-output cleanup should return space after successful completion; remeasure before launching the collector. The retained cleanup account is `validation/1036-capacity-recovery.json`. No capacity requirement is waived and no cache deletion is authorized by this note.

### Result interpretation and preserved scope

The current active verification record must be a matching **fresh** success record. The collector validates the exact dependency-root relationship, clean candidate/dependency identities and compiler identity; it does not establish process quiescence by itself.

Required result fields and evidence are:

- Actual successful execution with `assessment_complete: true`, `preservation_complete: true`, and `inspection.completed: true`.
- Equal before/after identities and `observed_changes: []`.
- Complete target inventory, physical inventory, inspection diagnostics, selection, missing-member account, byte-preservation copies and digest/metadata records. Retain completed journals even if an attempt is interrupted.
- Raw selected evidence outside managed caches, including the four known families even when current members are consistent or absent: `Applications.Resources.BoundedSummary`, `Examples.BoundedSummary`, `Applications.Sequences.ByteBuffer`, and `Examples.ByteBuffer`.
- Every new diagnostic or physical suspect and unrecognized file selected by the unchanged collector, including relevant traces, sidecars, artifacts and available setup information.

Exit zero means assessment and preservation completed; it does not mean zero discrepancies. Fresh mode uses temporary project outputs and leaves the incremental project cache cold or unchanged, so missing ordinary outputs/traces may be expected. Classify findings against actual history before repair. Current survivors or regenerated artifacts do not reconstruct the lost original mismatch bytes. Durably preserve newly material incident evidence before any repairing action.

## 5. Guarded candidate validation

After completed preservation and incident disposition permit it, the payload is:

```sh
./check.sh --candidate HEAD
```

Retain the exact invocation, complete output and actual result. The evidence must show the pre-build guard's classified invalidations, successful Lake build of every ordinary inventoried module, the post-build guard with **zero inconsistent modules**, and a **newly executed** exhaustive `ProofAudit.lean` audit. Preserve the new matching `mode: "incremental"` verification record separately from the fresh record.

Cold missing traces/outputs are not by themselves integrity incidents. Unexpected mismatch or malformed evidence for already built modules, repeated invalidation, or a known artifact recurrence requires the existing local incident procedure and preservation of surviving raw evidence before further repair. Similar diagnostic wording alone does not establish a common cause. Root's saved public issue #272 record, `validation/1036-upstream-272-issue.json`, was open with zero comments and `updated_at: 2026-10-30T19:45:18Z`; it does not waive current local evidence. The user-authorized no-GitHub-write exception remains in force.

## 6. Why the managed ProofAudit prerequisite should reuse ordinary outputs

The managed prerequisite payload is:

```sh
env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit
```

Retain its exact command, unchanged candidate/environment identity, complete log and actual successful result. It supplies a Lake-managed `ProofAudit.olean` for the regression's explicit `import ProofAudit`.

The preceding guarded checker intentionally omits `ProofAudit` from Lake's module targets and invokes `lake env lean ProofAudit.lean` without `-o`. The fresh checker writes the audit artifact only into its private temporary output, which is removed before completion. Neither preceding gate leaves the managed audit module required by the regression. These behaviors are in the unchanged candidate's `scripts/check.py` and `scripts/test-proof-audit.py`.

The pinned Lean 4.35.0 Lake source supports reuse of the ordinary modules:

| Source definition | Consequence |
| --- | --- |
| `Lake/CLI/Build.lean`: `resolveModuleTarget` and explicit module target resolution | `+Module` without a facet suffix uses the module's `leanArts` facet. |
| `Lake/Build/Module.lean`: `fetchImportInfo`, `computeExportInfo` | Imports request `exportInfo`, which itself fetches the imported module's same `leanArts` facet. |
| `Lake/CLI/Main.lean`: `--rehash`; `Lake/Build/Common.lean`: hash checking | `--rehash` disables trusting stored hashes; it recomputes hashes and may rewrite sidecars. It does not unconditionally compile every module. |
| `Lake/Build/Package.lean`: `maybeFetchBuildCache`; `Lake/Config/Monad.lean`: artifact-cache predicates | `--no-cache` and `LAKE_ARTIFACT_CACHE=false` disable the relevant cache-fetch/cache-write routes under this configuration; they do not prohibit reuse of valid local outputs. |
| `Lake/Build/Module.lean`: `Module.recBuildLean` / `fetchCore`; `Lake/Build/Common.lean`: `SavedTrace.replayIfUpToDate'` | An up-to-date local module can be reused and its saved diagnostics replayed. |

The reviewed sources are inside the official pinned toolchain at `toolchains/lean-4.35.0-linux/src/lean/lake` under the runtime state. The guarded checker already requests every ordinary `+Module` using the same no-cache/rehash settings. The unchanged `lakefile.toml` includes `ProofAudit` in the library globs and gives it no different options requiring a separate ordinary-module build.

**Conclusion from source analysis:** after stable successful guarded validation, this prerequisite should reuse valid ordinary module outputs. Compilation of the previously unbuilt `ProofAudit` itself is expected. Normal-module recompilation is not inherent in changing the final target to `+ProofAudit`. Module names, replayed diagnostics, or changed hash-sidecar timestamps alone do not prove that the compiler rebuilt them. Establish what actually happened from the command evidence and relevant output/trace identities.

Running this prerequisite immediately after fresh and before the guarded build would encounter cold ordinary managed outputs and could build the import closure. That is not the required sequence here.

### Response to unexpected managed rebuilding

The existing `managed_audit_qualification` in `validation/1025-pre-guard-preservation-plan.json` requires guard evidence to be reestablished if managed `+ProofAudit` unexpectedly rebuilds project dependencies after guarded success. The existing Standards and Spec axes confirmed that the appropriate response is:

1. Preserve the actual command, result, diagnostics, input identities, and relevant surviving traces, sidecars and artifacts before cleanup or repair. Record ordinary recompilation separately from the expected audit-module compilation or log replay.
2. Investigate changed inputs, build options, traces and artifacts through the existing local incident record. Do not infer a fresh corruption cause merely from recompilation or a familiar error string.
3. Rerun the **full guarded** `./check.sh --candidate HEAD` on the same exact candidate before relying on those changed dependencies in the regression. Require a clean post-build guard, newly executed audit, and new matching incremental record; preserve this repeat separately from the first guarded run.
4. Supply the investigation and renewed evidence to both existing reviewers, then continue the required regression and final verification sequence.

`--verify-candidate` alone compares recorded inputs; it does not rerun the integrity guard or audit and cannot reestablish those gates. The initial collector requires a current fresh record, so it cannot simply be rerun after an incremental record has replaced it. Never restore the saved fresh record into the active path to force that collector to run. Retain the fresh copy as historical evidence and use the applicable incident-preservation procedure for a later anomaly. Expected ProofAudit-only compilation or diagnostic replay does not itself add a new gate.

## 7. Required audit regression: all four cases

After the managed prerequisite and any necessary renewed guard evidence, use the same kit for:

```sh
lake env python3 scripts/test-proof-audit.py
```

Retain actual successful process completion and all four stdout lines in this order:

```text
PASS: unused-external-axiom
PASS: private-transitive-axiom
PASS: private-admission
PASS: source-unsafe
```

The unchanged harness first compiles each fixture. It prints a PASS line only after checking the corresponding audit result:

| Case | Internal required predicate |
| --- | --- |
| `unused-external-axiom` | Audit return code zero and output contains `Proof audit PASSED`. |
| `private-transitive-axiom` | Audit return code nonzero and output contains `Forbidden transitive axioms in '_private.Applications.AuditProbe`. The private suffix intentionally need not be fixed. |
| `private-admission` | Audit return code nonzero and output contains `sorryAx`. |
| `source-unsafe` | Audit return code nonzero and output contains `Proof audit FAILED: unsafe declarations with source ranges`. |

A fixture compilation failure or incorrect rejection raises an exception. Successful inner compiler/audit transcripts are captured by the harness, so a valid success log is not required to print the raw rejection diagnostics as well as the four PASS lines. The required evidence is the unchanged harness, its successful outer result, and all four case results.

The repository describes `test-check.py` and `test-proof-audit-roots.py` as additional suites. The retained formal review explicitly found no per-change mandate for this formal-only diff; `scripts/`, `ProofAudit.lean`, `check.sh`, and `lakefile.toml` remain unchanged from the fixed formal base. This readiness pass adds no helper-suite requirement.

## 8. Reviews, final verification, and acceptance

Return actual completed fresh, preservation, guarded, managed-audit and regression evidence to the existing independent Standards and Spec reviewers. Reuse their completed unchanged-source analysis; do not start a new enclosing loop. ST-002 still needs its evidence-based incident disposition, and SP-VAL-001 still needs completed validation. Neither can be closed by this note or by the compact-checkpoint operational approval.

Only after both formal axes pass the exact candidate, run the same kit payload:

```sh
./check.sh --verify-candidate HEAD
```

Retain its actual successful comparison with the current matching verification record **immediately before acceptance**, together with final clean candidate and dependency identities. Then root may record Preface/Perm acceptance and create/upload the acceptance checkpoint before proceeding to Sort. Any source or relevant input change requires the existing candidate/review protocol; this checklist is bound to the candidate above.

## 9. Retained evidence and analysis references

Paths here are relative to `work-state` unless stated otherwise:

- `tooling/UNIFIED-NATIVE.md`: current kit route, isolated dependency layout and unchanged gate sequence.
- `validation/1036-isolation.json`, `validation/1036-doctor.json`, `validation/1036-unified-setup/`: current environment and layout provenance.
- `validation/1036-runtime-route-decision.md`: selected unchanged runtime route.
- `validation/1036-capacity-recovery.json`: actual bounded cleanup account; not a future capacity waiver.
- `validation/1025-pre-guard-preservation-plan.json`: required preservation/disposition and managed-rebuild qualification.
- `validation/1034-pre-guard-assess.py`, `validation/1034-pre-guard-assessment-handoff.md`, `validation/1034-pre-guard-helper-checks.json`: unchanged collector, scope, limits and preparation evidence.
- `reviews/1002-fresh2-record-protocol-clarification.md`: supported conditional fresh-record route when original raw terminal status is unavailable.
- `reviews/1002-Perm.md`, `reviews/1002-unified-source-review.md`: existing independent review findings and source analysis.
- `validation/1036-upstream-272-issue.json`: root's actual saved public issue response for incident guidance.
- Candidate-relative `scripts/check.py`, `scripts/test-proof-audit.py`, `lakefile.toml`, `README.md` and `docs/agents/review-loop.md`: unchanged command and acceptance behavior.
- Official toolchain-relative Lake source named in section 6; unchanged kit `conaled_native.py` payload launcher using `start_new_session=True`.

This note records prospective readiness only. **Formal Standards and Spec remain Blocked until their required actual evidence passes review.**
