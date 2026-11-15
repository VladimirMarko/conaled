# Corrected shared/import prerequisite review continuation

This dispatch continues the existing linked10013/10018 review loop; it is not a
new acceptance scope or a third assessment. Both ordinary axes review the full
changed candidate, retaining prior analysis and stable findings. No GitHub writes.

## Immutable scope

- Candidate: 324962e733886e66d6cd92af6cb68627ed4c8f1d.
- Isolated checkout: import-correction; branch pfds/import-footprint-r2.
-10013 fixed base/merge base: cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833.
-10018 fixed base/merge base: 70a1477d822efd4fdcec2007280f650bb4695eda.
- Entire linked diff: git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...324962e733886e66d6cd92af6cb68627ed4c8f1d.
- Narrow import diff: git diff 70a1477d822efd4fdcec2007280f650bb4695eda...324962e733886e66d6cd92af6cb68627ed4c8f1d.
- Entire scope13files/4commits; narrow scope5files/2commits; no exclusions.
- Candidate/clean status and both ancestry facts checked at preparation.
- Manifest: validation/import-footprint-candidate-r2.json.

## Requirements fingerprints

| File under requirements/ | SHA256 |
| --- | --- |
| REQUEST.md | b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499 |
| REQUEST-union-v2.md | 3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c |
| shared-persistence.md | 177e80e0beda3ec144279c104d2fa3b968e916b0104db7f2e5d3c7c81a4bec76 |
| import-footprint.md | cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d |

## Entire commit list

```
ad730010ab1929bbd7a16a035c7990a6f328b178 feat(persistence): model shared lists and path copying (#10013)
70a1477d822efd4fdcec2007280f650bb4695eda fix(persistence): remove redundant adapter tactic (#10013)
226ebaef53b9eba97bef4b3b6ca364fdea488c69 refactor(frp): import only the required mathematics and tactics (#10018)
324962e733886e66d6cd92af6cb68627ed4c8f1d fix(frp): import direct providers in affected consumers (#10018)
```

## Entire changed-file list

- Applications/FRP/Demand.lean
- Applications/FRP/Equivalence.lean
- Applications/FRP/Finite.lean
- Applications/FRP/Spec.lean
- Applications/Resources/SharedList.lean
- Applications/Sequences/SharedList/Basic.lean
- Applications/Sequences/SharedList/Copy.lean
- Applications/Sequences/SharedList/Observation.lean
- Applications/Sequences/SharedList/Suffixes.lean
- Examples/FRP.lean
- Examples/SharedList.lean
- SquareApplications.lean
- docs/research/pfds-shared-persistence.md

## Retained findings and changed content

Read reviews/shared-persistence.md and import-footprint.md plus their earlier
axis reports. PERSIST-VAL-001 retains its prior fixed-with-compiler-evidence
disposition; do not erase or silently rerank it. New full-build findings
IMPORT-VAL-001..003 have candidate import-only repairs: Demand imports
Mathlib.Order.SuccPred.Nat; Finite imports Mathlib.Data.Set.Finite.Lattice;
Examples/FRP imports Mathlib.Algebra.Order.Archimedean.Real.Basic.
Independent reviewers must establish dispositions from actual candidate/evidence.
All non-import bytes equal prior226ebae; source comparison is preserved in
research/import-footprint-r2-source-comparison.json. Focused1134-job pass is
validation/import-footprint-r2-focused-r2.json. It is not the full gate.

Inspect the whole SharedList contracts/examples/statement intent and public
integration, plus changed imports and affected consumers. Both axes use the
repository statement-review guidance and standards/architecture pointers.
Earlier static-clear reports are retained analysis, not approval of324962e.

## Full validation status and ownership

Original226 runs are interrupted, with no terminal success or verification record.
Their concrete diagnostics/logs remain. Corrected324's stock full candidate check
started2026-11-02T21:44:59Z and is owned by root. Live log:
active-validation/import-footprint-324962e-full-r1.log. Automatic execution record:
validation/import-footprint-324962e-full-r1.json. The guard-checked ordinary output
copy is separately recorded in validation/import-footprint-r2-cache-copy.json;
no approval record was copied. All stock guards and exhaustive audit remain.

Reviewers must neither compile nor mutate this frozen checkout, its external
dependencies or build outputs. Report complete static findings if useful while
the gate runs, but required validation must be terminal-green with an exact
.lake/verification.json before a passing assessment. Root supplies final verify
evidence and repeats it immediately before acceptance. Missing required evidence
means Blocked; retain any implementation findings alongside that outcome.

Expected next reports: shared-persistence-standards-r4.md and -spec-r4.md;
linked import-footprint-standards-r2.md and -spec-r2.md. Reuse the coordinator
records and stable finding IDs. No chapter acceptance follows from this scope.
