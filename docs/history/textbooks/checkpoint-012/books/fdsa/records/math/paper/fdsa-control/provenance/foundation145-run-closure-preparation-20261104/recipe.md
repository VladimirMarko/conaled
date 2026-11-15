# Exact F145 execution and foundation acceptance closure

Prepared 4 November 2026; **not executed**. No live F output was inspected or captured, no process was polled, and no compiler, cache, source or ref action occurred. This note reuses the existing tools and 145-name input without creating maintained tooling.

## Immutable scope and prerequisite terminal

The candidate is F `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` in `conaled-ch01-review`, branch `work/fdsa-foundation-integration`. Accepted R remains `07e480f6ec9958d4975bb90151005b84f2907614`; the included original foundation prefix is exactly `c80eec92f5458eccfd1c34c8314d666c2a1e3847`. Retain the full nine-path, four-unit scope: X002, Appendix A, XB01 / Appendix B.1 and Appendix C. The historical `shared-foundations-validation.json` describes a later old prefix including XP01 and must not supply this candidate binding.

Root must first obtain the **actual terminal** of the existing normal full check, `chapter02-foundation-full-attempt2-recovered-20261104`, and secure its complete closed outer/native records. Its recorded command is the qualified one-thread `./check.sh --candidate HEAD`. Do not restart it from a historical session ID or substitute the interrupted attempt1, a focused pass, old Chapter 1 verification, current C2 output or a module-count estimate.

On successful closure, reconcile actual source-policy/public-import coverage, guarded complete build, before/after integrity, exhaustive kernel audit, clean exact-F candidate/dependencies and the newly emitted matching `.lake/verification.json`. Read all terminal diagnostics and record actual whole-project declaration/theorem/module counts and the permitted axiom union only: `propext`, `Classical.choice`, `Quot.sound`. A result or recorder disagreement stays visible and unresolved. No fresh trigger was identified by the existing axes: README at F lines157–218 retains the ordinary full gate and its real fresh triggers; missing cold outputs alone do not trigger another expensive fresh baseline.

Keep F exclusively idle after that command closes while running the following statement sequence. This recipe assumes the successful matching full gate; a failed gate instead requires diagnosis and continuation under the same scope.

## Exact prepared input and static closure

Reuse `provenance/foundation-complete-public-statements-prepared-20261104/Statements.lean`: **7,518 bytes, 156 lines, 145 distinct checks**, SHA-256 `01210adfe5074fde16d88ef78510456fc28915d7951752ba71850a7231c12cb4`. The existing inventory SHA-256 is `d39aa500144f7893088e8e69cb32514d75191d100e7b9fc1405e14055a94fefa`. The input enables explicit arguments, full names and universes.

| Import root | Public checks | Positions | Local closure size |
|---|---:|---:|---:|
| `Applications.Resources.InsertionSort` | 19 | 1–19 | 7 |
| `Applications.Resources.ListCalls` | 34 | 20–53 | 9 |
| `Examples.FunctionalNotation` | 30 | 54–83 | 4 |
| `Examples.InsertionCosts` | 16 | 84–99 | 9 |
| `Examples.ListCalls` | 16 | 100–115 | 19 |
| `Examples.ListLibrary` | 30 | 116–145 | 1 |

The union has **29 local source paths and 32 distinct direct external imports**. The receipt maps all 29 exact F blobs, verified with immutable Git reads against the retained independent closure inventory. The earlier cross-candidate inventory's 30 source fingerprints include both versions of Sorting.Merge; that is not 30 local paths in F. Do not predeclare an object-file count: capture the actual existing suffixes. No additional accepted-C1 type recheck is introduced. Private, anonymous and generated obligations remain covered by the full source and exhaustive audit scope.

## Actual helper behavior

`capture_statement_inputs.py` accepts required `--project`, `--candidate`, `--program`, `--output`, and optional `--compare`. It refuses an existing output, requires clean exact HEAD, checks ten configuration inputs, all nine exact clean dependency revisions and twelve runtime fingerprints from its fixed foundation110 reference. It imports the repository source reader with bytecode writing disabled, walks the program's local import closure, requires each local `.olean`, and fingerprints existing `.olean`, `.olean.hash`, `.olean.private`, `.olean.server` and `.trace` files. It captures 145 unique names and actual source/blob identities. This is a supplementary observation, not loaded-object qualification, a full audit or acceptance.

`--compare` compares the complete `identity` objects, records the pre-observation's identity/hash, writes the post-observation, and exits nonzero if identities changed. Preserve and investigate a mismatch; do not overwrite or normalize it. Actual capture should reconcile to the 29-path static union, six roots and intended 145-name order. External loaded objects still require the existing qualified-environment/evidence assessment.

## Command recipe — only after the prerequisite closure

Use genuinely unused run/observation names. The recorder creates its own new directory and refuses reuse; pre/post observations therefore belong in a separate directory. This block is a prepared command sequence, not a record that it ran.

```bash
set -euo pipefail
FDSA_BASE=/workspace/scratch/b4a17a285e23/fdsa-restored-20261104
FDSA_CTRL="$FDSA_BASE/fdsa-control"
FDSA_PROJECT="$FDSA_BASE/conaled-ch01-review"
FDSA_F=f17cc6b1a2bf44215b16202ed0fcee2b5c130761
FDSA_KIT="$FDSA_CTRL/tooling/unified-native-kit-4.35.0"
FDSA_STATE="$FDSA_BASE/conaled-native-state"
FDSA_PROGRAM="$FDSA_CTRL/provenance/foundation-complete-public-statements-prepared-20261104/Statements.lean"
FDSA_RUN_NAME=foundation-complete-public-statements145-20261104-attempt1
FDSA_OBS="$FDSA_CTRL/provenance/foundation145-input-observations-20261104-attempt1"
test ! -e "$FDSA_CTRL/provenance/$FDSA_RUN_NAME"
test ! -e "$FDSA_OBS"

python3 "$FDSA_CTRL/tooling/capture_statement_inputs.py" \
  --project "$FDSA_PROJECT" --candidate "$FDSA_F" \
  --program "$FDSA_PROGRAM" --output "$FDSA_OBS/pre-inputs.json"

python3 "$FDSA_CTRL/tooling/record_command.py" \
  --name "$FDSA_RUN_NAME" --cwd "$FDSA_PROJECT" --candidate "$FDSA_F" -- \
  python3 "$FDSA_KIT/conaled_native.py" --state "$FDSA_STATE" \
  run --project "$FDSA_PROJECT" --threads 1 -- \
  lake env lean "$FDSA_PROGRAM"

python3 "$FDSA_CTRL/tooling/capture_statement_inputs.py" \
  --project "$FDSA_PROJECT" --candidate "$FDSA_F" \
  --program "$FDSA_PROGRAM" --output "$FDSA_OBS/post-inputs.json" \
  --compare "$FDSA_OBS/pre-inputs.json"
```

Keep the recorder foreground in its owned execution session; root may yield and resume that actual session while communicating. The native CLI has **no `--stdin-file` option**, and the outer recorder sets stdin to DEVNULL. Passing the absolute program filename is the already exercised actual815/actual20 pattern. Do not insert a shell stdin workaround or modify the input. The three commands are sequential; no other writer may change source/configuration/dependencies/project outputs between captures. After a failed command, preserve its actual terminal and records before any manually chosen diagnostic/post-capture; `set -e` deliberately does not turn failure into a successful three-stage sequence.

## Secure the actual terminal, native copies and full output

The outer recorder supplies `request.json`, `start.json`, `full.log`, the actual `result.json` and final HEAD/status; its progress records do not establish liveness or success. After real closure, bind the owned execution exit, outer exit, exact native exit, source status and complete log bytes/hashes. Preserve recorder/bookkeeping errors and signal/timeout outcomes.

The native run emits its exact result path in the closed outer log, for example `[result] exit=0, …; /…/conaled-native-state/logs/<exact-run>/result.json`. For a normal completed invocation, select that exact terminal line and require a unique matching result path; do not select the newest directory by time. Copy that directory's **start.json, result.json and output.log** into a new `native-records/` under the run record, retaining original absolute paths and exact byte/hash identities. Copy before interpreting success. Reconcile native cwd, command and start/completion with the outer request/result. Missing or conflicting native terminal evidence remains unresolved; a launch failure may have a different explicit failure line and must not be coerced into this success pattern.

All 145 complete output blocks need actual preserved native ranges and hashes, in the prepared name order, for both reviewers to read. Count the full blocks and diagnose truncation/missing declarations or unexpected errors. A prepared name list or successful exit alone is not complete type assessment. Bind both actual pre/post observations and require `unchanged: true`; retain actual runtime, dependency and source identities, rather than copying hypothetical future values.

**Recorder detail:** after any command, `record_command.py` copies an existing `.lake/verification.json` if present. Thus a verification file copied into the F145 or final-verify record is inherited from the successful full candidate gate; it is not a newly produced audit or an acceptance result of the type command. Preserve its provenance and compare it to the full-gate record.

## Continue both existing independent axes

Continue the existing complete reports, rather than replacing them with this operational note:

- `reviews/shared-foundations-standards.md`, `shared-foundations-standards-recovery-preflight-20261104.md`, `shared-foundations-standards-continuation-20261104.md`; supporting `provenance/foundation-standards-terminal-continuation-20261104/` and `shared-foundations-standards-continuation-20261104/identity-and-preparation.json`.
- `reviews/shared-foundations-spec.md`, `shared-foundations-spec-recovery-preflight-20261104.md`, `shared-foundations-spec-recovered-terminal.md`, `shared-foundations-spec-continuation-20261104.md`; supporting `provenance/foundation-spec-terminal-continuation-20261104/` and `foundation-spec-current-continuation-20261104/`.
- Original `reviews/shared-foundations-round1.md` and all four frozen requirement files. Preserve FDN-ELAB-001/002 source dispositions, then resolve their complete-candidate confirmation and every actual new diagnostic under the same full scope.

Both axes currently retain completed source assessments with zero concrete source findings, but remain **Blocked** pending actual full terminal/audit/verification and complete F145 evidence. Each must assess the real full logs, all 145 actual types, exact inputs/loaded-object qualification and all unresolved findings. This note grants no review credit. The possible110-name cross-candidate reuse analysis remains separate; it neither reduces this input nor supplies evidence in advance.

## Immediate qualified verification and exact local fast-forward

Only after both full-scope axes pass the same exact F, with all applicable evidence gates satisfied and no unresolved findings, root runs one newly named recorded command:

```bash
python3 "$FDSA_CTRL/tooling/record_command.py" \
  --name foundation-immediate-verification-20261104-attempt1 \
  --cwd "$FDSA_PROJECT" --candidate "$FDSA_F" -- \
  python3 "$FDSA_KIT/conaled_native.py" --state "$FDSA_STATE" \
  run --project "$FDSA_PROJECT" --threads 1 -- \
  ./check.sh --verify-candidate HEAD
```

Use no `--fresh`, `--jobs`, `LEAN` override or enclosing `lake env` for the checker. README says verification uses the mode in the success record and does not compile or repeat the audit. Secure its actual matching exit and record, then immediately fast-forward the accepted integration branch to **the exact approved F**. Accepted `conaled` must remain on `work/fdsa-book` at R with its tracked working tree and index matching R, and F must be its descendant. Preserve the recorded unrelated untracked exclusions, status and fingerprints; they must be unchanged and nonconflicting with the fast-forward. In particular, `REQUEST.md` lines70–77 preserves `docs/history/algorithm-design-haskell/.checkpoint-233.zip.n7UlkJ` in place. Do not demand an empty global status or delete that file. The isolated F candidate must still be fully clean and approved under its mandatory candidate gates.

The intended local Git action is `git -C "$FDSA_BASE/conaled" merge --ff-only "$FDSA_F"`, with no overwrite of unrelated files. No source/build mutation belongs between final verification and integration; if candidate identity, tracked accepted-base state or an exclusion fingerprint/conflict check changes, stop and reconcile. This preserves the existing unrelated-file handling, not a new clean-candidate waiver.

Only after the exact local fast-forward should root update the four local units' acceptance/coverage and global controls, bind the accepted commit plus both review results and actual audit/type/verification evidence, then create, verify, upload and expose the acceptance checkpoint. No GitHub mutation or push. If any source correction is necessary, preserve the failed evidence and review/build the actual successor under the same complete four-unit scope.

## Preparation read boundary

Read the full capture helper, full outer recorder, complete F145 input/inventory, both current continuation reports and their source/evidence metadata; bounded reads covered native log/CLI/run dispatch and immutable-F README acceptance provisions. The static closure union came from the completed independent closure record and all 29 blobs were checked against immutable F through Git. The actual815/actual20 request and closed-record examples establish the filename invocation and copying pattern; they are not F evidence. No live F log/progress/output, runtime binary or dependency cache was read or captured. The receipt records exact inputs and current helper/report identities.
