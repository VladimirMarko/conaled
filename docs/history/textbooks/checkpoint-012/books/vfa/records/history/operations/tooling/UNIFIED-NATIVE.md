# Supplied unified native provisioning environment

**Current entry point:** [ACTIVE-NATIVE.md](ACTIVE-NATIVE.md). The unchanged supplied kit now both provisions and directly supervises validation and diagnostic commands in `vfa-summation-validation`, invoked with `tty:true`. Older outer-recorder recipes are superseded by the current entry point.

The user supplied the unified native kit on 3 November 2026 and requested it as the preferred environment. Use the complete `native-kit/` directory delivered by the compact restore. Its unmodified 1.0.0 CLI verifies its own SHA256SUMS and acquires the official complete Lean 4.35.0 distribution. Read its README and docs/PROJECTS.md. The active execution choice and its evidence are recorded in ACTIVE-NATIVE.md.

The cf0 attempt completed unsuccessfully at Monitor (937), after936 successful
ordinary modules. Local1040 adds one order import in candidate
eae9e110adc7ba1cc28386448a6deef23e406c13. The complete corrected Monitor source
passed; all116 actual modules in its consumer diagnostic then completed with
actual terminal/kit exit0. See1040-focused-summary.json. The
updated empty-restore recipe below uses that candidate and its verified675-root
selector list. The eae9 full fresh in
validation/1002-candidate-eae9e11-monitor-fresh1 completed actual execution-API/kit
exit1 at2026-11-04T13:49:27.706305Z after754successfulmodules. Attempted755failed to
create its private .olean output; ordinary available capacity was zero. No proof
error or exact OS errno was reported. Session30015 is closed. No audit or fresh
verification exists, and the private fresh directory is absent. Recover adequate
stable ordinary capacity before rerunning the full gate. No acceptance is claimed.
See validation/1040-eae9-fresh-output-failure.json,1040-fresh-failure.json and
1040-environment-ready.json. Preserve the separate unused-path reappearance
incident and the accepted bounded-reconciliation protocol before acceptance.

## Restore and provision

Restore source and work-state using this checkpoint's restore command and its exact fixed recovery base. The kit is included in each current checkpoint. Set `RECOVERY` to that restored root, `KIT` to its `native-kit` directory and `STATE` to a writable separate directory without whitespace or colons. Keep STATE outside source and kit. All dependencies and toolchain downloads remain excluded from recovery archives.

```sh
python3 "$KIT/conaled_native.py" verify
git clone --no-hardlinks "$RECOVERY/conaled" "$RECOVERY/vfa-validation"
git -C "$RECOVERY/vfa-validation" checkout --detach eae9e110adc7ba1cc28386448a6deef23e406c13
python3 "$KIT/conaled_native.py" --state "$STATE" setup --project "$RECOVERY/vfa-validation" --threads 1 --skip-cache
```

The last command authenticates the complete official distribution, creates the
native profile, acquires all nine exact clean dependency repositories, and runs
valid/invalid proof and native executable smokes. `--skip-cache` omits the project
Mathlib smoke at this stage. Require an actual successful exit.

### Targeted dependency hydration

For candidate `eae9e110adc7ba1cc28386448a6deef23e406c13`, use the verified selector file
`work-state/validation/1040-targeted-cache-roots.txt`: 675 names, 20,023 bytes,
SHA-256 `4c3d3b24611077cfd37bea609e755a8db92806ade64897aa49337f8fd2cb7c6e`.
Its roots are all direct external project imports, every formerly cached
non-Mathlib module and the auxiliary smoke root, excluding official core and the
setup-only Cache namespace. The corrected closure has 3,932 modules
(3,526 Mathlib and 406 non-Mathlib). Do not substitute the full Mathlib umbrella.
All nine complete pinned source checkouts remain necessary for hashing.

The new explicit `Mathlib.Data.Nat.Size` import requires exactly one additional
artifact family relative to c988. Its other121 transitive dependencies already
belonged to the earlier closure. `validation/1038-cache-scope.json` rederived the
corrected source/root identity and cross-checked all3931 existing metadata nodes
against pinned source. `1038-cache-result.json` records successful acquisition of
the one missing family and the new node's matching source/metadata imports.
The earlier1037 selector and3931-module evidence remain historical, not a claim
that changed source has unchanged inputs. On a fresh restore acquire all675 roots;
on this live transition only `Mathlib.Data.Nat.Size` needed retrieval.

The preceding cf0 correction added three explicit summation imports. All three were
already in the3932-module artifact closure; two are new direct selectors and
Ring.Defs was already a selector elsewhere. The revised674 roots, all954 local
source identities and all3932 source/metadata edge comparisons are recorded in
validation/1039-cache-scope.json. No new acquisition was needed in that transition.
Do not relabel the earlier671/672-selector evidence as this candidate's roots.

The current eae9 correction adds Mathlib.Order.Lattice to Monitor. Its additional
selector raises the list to675 while retaining the exact3932-module closure.
Validation1040-cache-scope.json retains all954current local source hashes, all
3932source/ilean explicit-import comparisons, and ninecleanpins before/after.
No new artifact acquisition was needed.

Invoke the unchanged kit's `cache --project ... --threads 1` command with each
line as a separate positional module argument. A Python argv list avoids shell
splitting; verify the selector hash and candidate identity before using it.
The cache roots are candidate-specific and must be re-derived for new imports.
The equivalent single-stage setup supports repeated `--module NAME` arguments.

The initial c988 setup attempt received HTTP 429 rate limits after downloading/decompressing
1,227 of 3,931 entries. Preserve its raw result and successful artifacts; a
partial download is not setup success. Respect backoff and use only the pinned
tool's supported controls. Retain actual final diagnostics and ensure every
required module is present before formal validation. See the 1037 cache records.
ProofWidgets' pinned checkout includes tracked widget JS and its Lake trace;
retain those inputs and ordinary extra-dependency behavior.

For a respectful retry, a dedicated task-local directory may contain a `.curlrc`
with exactly `parallel-max = 1`. Set `CURL_HOME` to that directory for the cache
process only. This bounds simultaneous transfers; it is not a request-rate limit.
Keep the pinned client's retries and server Retry-After handling. Use ordinary
get so completed archives are reused. Allow the documented cooldown before one
continuation; if HTTP429 persists, record it and pause further batches. Do not
change endpoints, pins or the kit. See validation/1037-cache-retry-plan.json and
the exact saved tooling/scoped-cache-curlrc. Do not export this setting into
formal validation; it is an acquisition-only control.

After successful cache hydration, complete these separate checks:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" smoke --project "$RECOVERY/vfa-validation" --threads 1
python3 "$KIT/conaled_native.py" --state "$STATE" doctor --project "$RECOVERY/vfa-validation" --full
```

Preserve both actual outcomes and the complete kit log records under work-state.
These checks establish environment readiness only, not chapter acceptance.

## Isolated formal candidate

Create a clean detached Git worktree at `vfa-summation-validation` and check out the same exact candidate. Give it a real `.lake/packages` parent and nine individual package links pointing to the same-named real directories under `vfa-validation/.lake/packages`. The provisioning checkout is dedicated to this one formal candidate; no other checkout may write those dependency trees while a candidate gate runs. Project `.lake/build` outputs remain private to the candidate.

This is the established VFA-specific dependency-store arrangement, retained to use the unchanged non-repairing incident collector. The kit's `setup`, `cache`, `deps`, and project `doctor` commands must target the real provisioning checkout; they deliberately reject symlinked package stores. The kit's `run` command supports the isolated candidate and the project checker validates its exact resolved dependency revisions. The kit locks are per project path, so root must enforce sole writer ownership across both paths. Never hydrate caches or move directories during validation.

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" doctor --full --project "$RECOVERY/vfa-validation"
python3 "$KIT/conaled_native.py" --state "$STATE" run --project "$RECOVERY/vfa-summation-validation" --threads 1 -- ./check.sh --candidate HEAD --fresh --jobs 1
```

Invoke each long gate directly with execution API `tty:true`, using the kit's existing start/output/result records and actual terminal outcome. Mirror those records into work-state for every checkpoint, marking live log snapshots incomplete. The outer validation recorder is not used for this baseline; see `validation/1036-direct-kit-recording-assessment.md`. This kit sets `LEAN_NUM_THREADS=1` but adds no Lean CLI `-j1`. `--jobs 1` bounds the fresh checker's external compiler jobs only. Do not describe the run as native-j1 or as an OS-thread/RSS bound. The compiler/checker/proof policies are unchanged.

## Current live isolation after the interrupted4adc attempt

The current active checkout is vfa-summation-validation at eae9. The earlier
vfa-unified-pty-validation stays frozen at4adc, with unknown descendant status,
no kit final result and no acceptance credit. Its sources, HEAD, links, outputs
and evidence must not be retargeted or cleaned. The existing provisioning root
vfa-validation also remains4adc in this live environment; only its unchanged
real nine package trees are shared. Its root project source is not imported by
current validation. On an empty restore the commands above create both current
source checkouts directly at eae9; old private outputs are not restored.

Standards accepted the disjoint proof/source output boundaries while shared
compiler/profile/package inputs remain stable. See
reviews/1002-summation-findings-and-isolation.md, validation/1039-new-worktree-isolation.json and1040-candidate.json.
The known old fresh command uses direct Lean with old-root output paths and no
cache/setup/repairing guard. No old-output reuse or child-quiescence claim is
made. The kit's general TMPDIR remains state-wide; proof outputs are private.

## Preserve every formal gate

After actual fresh success, save `.lake/verification.json` separately. With idle stable inputs, invoke the unchanged `validation/1034-pre-guard-assess.py` through the same kit with the new candidate root and exact `vfa-validation/.lake/packages` dependency root, new evidence destination, and current run/environment provenance. Preserve/classify its results before the repairing guard.

Then run the separate guarded `./check.sh --candidate HEAD`; save its distinct successful record. Complete `env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit` and `lake env python3 scripts/test-proof-audit.py`. Investigate unexpected invalidations/rebuilding through the existing local incident record. Obtain both independent formal axes on the exact candidate, then immediately run `./check.sh --verify-candidate HEAD`. Only then accept Preface/Perm, upload the acceptance checkpoint, and proceed to Sort.

No previous partial log or historical PID/session proves current execution or acceptance. Source/toolchain/dependency pins and every proof/build/review gate remain required. No GitHub writes are authorized.
