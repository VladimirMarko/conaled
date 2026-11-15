# Monitor correction: retained source review and completed focused evidence

## Identity, scope, and review continuity

This supplements the same Preface/Perm implementation/review loop. Coordinator:
`/root/formal_review`. The two original independent reviewers remain:

- Standards: `/root/formal_review/standards`.
- Spec: `/root/formal_review/spec`.

Both axes explicitly reuse all completed unchanged-source analysis through the
parent candidate `cf0a687265c1929ffd3ff6f15fa18febe0fb61b5`, including the earlier
full-source analyses and retained finding dispositions. No new enclosing review,
scope exclusion, or gate waiver is introduced.

| Item | Independently verified by both axes |
|---|---|
| Candidate | `eae9e110adc7ba1cc28386448a6deef23e406c13` |
| Fixed base and merge-base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Full enclosing scope | 26 files, +501/-17, no exclusions |
| Source and validation checkouts | `conaled` and `vfa-summation-validation`, clean at the candidate |
| Whitespace check | `git diff --check` has no findings |
| Delta from parent | One added import prefix in `SquareKit/Temporal/Monitor.lean` |

The corrected Monitor file is exactly `import Mathlib.Order.Lattice\n` followed
by every byte of its parent version. Its SHA-256 is
`88661c0eed00ec67418891c32ebcec3e4c42f603b654c5946f0773f3adbec46f`.
All statements, assumptions, executable definitions, constructors, cases, proof
bodies, examples, and VFA coverage remain unchanged. See
`validation/1040-candidate.json` and `specs/1040-monitor-order-imports.md`.

## Independent Standards assessment

The explicit lattice import implements the correction justified in
`reviews/1002-monitor-import-diagnosis.md`. Its pinned public import chain supplies
`LE.le.trans` and `lt_self_iff_false`; the lattice instance with `inf := min` and
the generated `[simp] le_inf_iff` rule supply the existing min-bound simplification.
This repairs the earlier task's narrowing of `Mathlib.Tactic`, with no proof-body
or mathematical change.

Standards initially closed ST-006 using the actual complete corrected Monitor
subprocess return of zero. It independently reproduced the first 1,539 output
bytes in both preserved and raw kit logs, with SHA-256
`b7f4229171ea6aab011b91c4c08806321b8ad684777ba48ace644efa4e7dac00`:

```text
[focused 1/116] SquareKit.Temporal.Monitor
[focused result] SquareKit.Temporal.Monitor exit=0
```

The reviewed helper emits that result only after the actual complete-source Lean
subprocess returns. The completed 116-module evidence below now corroborates
this disposition. **ST-006 is Fixed on eae9e110.** No new Standards source finding
was identified.

## Independent Spec assessment

Spec independently verified the pinned declarations, import connections, exact
one-line change, and preservation of every previous source byte. The correction
adds no premise and weakens no conclusion.

The original semantic boundaries remain intact: satisfaction uses infinite
traces; optional observations require the stated agreement premise; bounded-until
waiting excludes the terminal index; conclusive verdicts retain their
observed-prefix conditions. The retention theorem still counts stored frames
bounded by `horizon + 1`, with no added byte-storage or upstream-log claim.
Cases, chapter scope, and VFA coverage are unchanged.

Spec found no further source correction necessary. It independently corroborated
the complete Monitor result and then assessed the completed 116-module evidence.
**No new Spec finding was identified.** Its retained SP-VAL-001 remains open.

## Completed actual 116-module diagnostic

The exact completed attempt is `validation/1040-focused-remaining2/`. Both axes
independently assessed its launch, start, result, terminal, frozen helper,
`focused-results.json`, full output, and `validation/1040-focused-summary.json`.

| Evidence | Verified outcome |
|---|---|
| Recorded execution-API terminal | Exit 0, owned session 95892 |
| Kit result | Exit 0; `passed:true`; `timed_out:false`; `recorder_error:null` |
| Helper result | Exit 0 |
| Kit completion | `2026-11-04T11:43:31.173047+00:00` |
| Elapsed time | `1386.3700588810025` seconds |
| Actual modules | Exactly 116 distinct modules, all return codes 0 |
| Order | Exactly the frozen inventory order; Monitor first, Verification last |
| Final output | 19,584 bytes |
| Output SHA-256 | `c936a404155689f5754904d708e5c87c0e6c5806fe88a56728de0aee41879472` |

Every recorded compiler command names the expected actual source and private
diagnostic output. The complete log has exactly the corresponding ordered start
and result markers, with no missing, duplicated, reordered, or additional module
result. Launch/start/result commands and project, candidate, inventory, private
output, and result paths agree. The helper's recorded interval lies within the
kit's interval. Standards additionally verified that preserved start, output,
and result files are byte-identical to their named raw kit originals.

For all 116 sources, both axes independently matched the helper's identical before
and after hashes to the frozen inventory and current files in both source and
validation checkouts. Both checkouts remain clean at the exact candidate. The
helper's recorded final HEAD and status agree. Its frozen source remains identical
to the current helper and launch hash.

| Binding | SHA-256 |
|---|---|
| `1040-focused-module-order.json` | `2231da3c5d748178f4321bca67bb525dbd5d49c96fdea91a8c34267eb2e31adc` |
| Frozen/current diagnostic helper | `f538c368e7bcd13be7db43b0afc6280ec7109d1ea953e454904afdab394bd1bd` |
| `focused-results.json` (72,423 bytes) | `16d312ffadba8b8ad81fa6ebf1a1eba9ec5a414c02f923315c17d73c63436b0d` |

The complete output retains the earlier 1,539-byte Monitor-success prefix and its
hash exactly. Verification's selected axiom reports and evaluation results
`(43, false)`, `8`, and `(8, 8)` appear before its successful return. Spec counted
23 nonfatal linter warnings and no Lean error diagnostics.

The diagnostic checks Monitor and the selected remaining consumers with their
local prerequisite union. Verification is included. The import-only public
aggregator is outside this focused scope; the separate exhaustive ProofAudit
driver also remains for the formal gates. Neither is excluded from the enclosing
formal requirements. The helper's LEAN_PATH contains only its private diagnostic
outputs followed by the eight dependency artifact directories; it includes no
managed or quarantined old project outputs.

**Both axes find the completed focused evidence satisfactory, with no material
inconsistency or correction required. This is diagnostic success only.** It cannot
be combined with the prior failed fresh run's 936 successful modules to assert
full fresh success.

## Preserved failed preflight and environment provenance

The earlier `1040-focused-remaining1` attempt remains a diagnostic preflight
failure: execution API and kit exit 1, no timeout/recorder error, and zero compiler
invocations. Its mistaken assertion expected nine artifact directories because
there were nine pinned repositories; the actual library output count is eight.
The assertion failed before private-output creation or the compiler loop.

Standards verified the original script and raw records remain preserved. Its
241-byte output has SHA-256
`6deb94eeb91741cc6c3693b7ba24f4bb2495183c4b27e71c20beb5fece4db2f5`.
The helper-only correction changes that count assertion to a nonempty-directory
check and records the actual directories. It changes no formal checker, pin,
source, or acceptance requirement. The successful second attempt does not erase
or relabel the first failure.

The current static inventory has 675 selectors and the unchanged 3,932 dependency
artifact families. Only `Mathlib.Order.Lattice` is added as a selector; its artifact
family was already present, so no acquisition was needed.

- `1040-cache-scope.json` SHA-256:
  `22c15d333688b8d4f5c30a937261cfd4adcb11801617c7afabb434621532fcb8`.
- `1040-targeted-cache-roots.txt`: 20,023 bytes, SHA-256
  `4c3d3b24611077cfd37bea609e755a8db92806ade64897aa49337f8fd2cb7c6e`.

Both axes reproduced these identities and retained the inventory's static scope
limitations. `1040-environment-ready.json` explicitly reuses prior unchanged
setup/smoke/doctor evidence; no new execution is inferred. The existing isolation
assessment remains in force: the old 4adc checkout is quarantined with descendant
status unknown, shared installed compiler/profile/package inputs remain stable,
and new diagnostic outputs are private. No process-quiescence or artifact-
authenticity conclusion follows from the static inventory.

## Findings and overall outcomes

| Finding | Retained disposition |
|---|---|
| ST-001 | Fixed. |
| ST-002 | Open, Medium; bounded artifact-incident preservation/recovery assessment remains required. |
| ST-003 | Fixed by actual complete IndefiniteService elaboration in the preserved failed cf0 fresh run. |
| ST-004 / ST-005 | Fixed. |
| ST-006 | Fixed on eae9e110; corroborated by completed 116-module diagnostic. |
| SP-VAL-001 | Open on the independent Spec axis. |

**Standards outcome: Blocked.** One Standards finding remains open, with worst
severity Medium. **Spec outcome: Blocked.** No new source finding or further source
correction is requested by either axis. The focused prerequisite is complete.

The exact candidate still requires a new complete fresh build and exhaustive
audit; unchanged non-repairing collector and classification; guarded build,
postguard, new audit, and distinct record; managed no-cache rehashed `+ProofAudit`;
all four regressions; both final independent evidence reviews; immediate candidate
verification; and the uploaded acceptance checkpoint before the next chapter.
Earlier failed runs and the successful diagnostic supply no integrated credit.

Both original reviewer threads remain available for that evidence review. They
performed no compiler, cache, runtime, process-control, source-writing, or
evidence-writing operation. The coordinator wrote only this authorized supplement
after root supplied the completed result and opened the report write window.
