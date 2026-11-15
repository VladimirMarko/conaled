# Linked prerequisite successor901f734 — full review dispatch

Continue the existing10013/10018 loop and retained reviewer pair. This is the
next immutable candidate after observed full-build finding IMPORT-VAL-004.
Do not erase the partial324 review or any earlier finding/disposition.
No GitHub writes; root owns all compilation and source corrections.

## Pinned complete scope

- Candidate: 901f734161920a76f3b399a575805b9a1d31e971.
- Checkout: import-correction-r3; branch pfds/import-footprint-r3; clean/frozen.
-10013 unchanged base and merge base: cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833.
-10018 unchanged base and merge base: 70a1477d822efd4fdcec2007280f650bb4695eda.
- Full diff: git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...901f734161920a76f3b399a575805b9a1d31e971.
- Narrow diff: git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971.
- Full scope14files/5commits; narrow import scope6files/3commits; no exclusions.
- Exact file hashes, commit lists and requirement hashes:
  validation/import-footprint-candidate-r3.json.

### Complete commit list

```
ad730010ab1929bbd7a16a035c7990a6f328b178 feat(persistence): model shared lists and path copying (#10013)
70a1477d822efd4fdcec2007280f650bb4695eda fix(persistence): remove redundant adapter tactic (#10013)
226ebaef53b9eba97bef4b3b6ca364fdea488c69 refactor(frp): import only the required mathematics and tactics (#10018)
324962e733886e66d6cd92af6cb68627ed4c8f1d fix(frp): import direct providers in affected consumers (#10018)
901f734161920a76f3b399a575805b9a1d31e971 fix(frp): import the natural size power theorem directly (#10018)
```

### Complete changed-file list

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
- Examples/IndefiniteService.lean
- Examples/SharedList.lean
- SquareApplications.lean
- docs/research/pfds-shared-persistence.md

## Requirements and prior evidence

Read saved requirements/REQUEST.md, REQUEST-union-v2.md, shared-persistence.md v2
and import-footprint.md v1. Their unchanged SHA256 values are:

- REQUEST.md: b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499
- REQUEST-union-v2.md: 3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c
- shared-persistence.md: 177e80e0beda3ec144279c104d2fa3b968e916b0104db7f2e5d3c7c81a4bec76
- import-footprint.md: cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d

Read reviews/shared-persistence.md and import-footprint.md and retained reports.
PERSIST-VAL-001 remains fixed with prior compiler/review evidence; reassess if new
evidence requires, never erase it. IMPORT-VAL-001..003 have focused repairs in324,
but its interrupted partial Standards review did not finalize their disposition.
IMPORT-VAL-004 is the missing Nat.size_pow provider found by full324; exact log
and source identity are in validation/import-footprint-324962e-observed-errors.json.

901 adds one import Mathlib.Data.Nat.Size in Examples/IndefiniteService. All
other bytes match324. Its pinned provider declares Nat.size_pow at
Mathlib/Data/Nat/Size.lean:94. Independently assess preservation for all six
changed import consumers from the fixed10018 base, not merely the latest line.
The SharedList implementation/cases are unchanged, but remain within the full
scope and requirements. Read their recorded intended statements and meaningful
connected applications; both axes use repository statement-review guidance.

The new focused target is Examples.IndefiniteService. Its immutable closure,
pinned command, source/provider comparisons and result will be preserved in
validation/import-footprint-r3-focused-r1.{json,log},
validation/import-footprint-r3-fixed-base-comparison.json and
research/import-footprint-r3.md once terminal. At dispatch preparation it is still
running. Earlier1134-job focused evidence is retained as development evidence,
not reused approval of the complete successor.

## Validation and review scheduling

Full324 still compiles unrelated remaining modules after its known failure.
It remains frozen, with live record validation/import-footprint-324962e-full-r1.json.
No compiler or source edit by reviewers is authorized. Root will preserve its
terminal failure, reuse only complete guard-checked ordinary outputs into901's
private build, then run the unchanged stock ./check.sh --candidate HEAD on901.
No previous candidate's success/approval record can approve901.

Full901 validation, exact matching .lake/verification.json, both independent
reviews and immediate final verify remain required. Report actual findings while
blocked; no static-clear or Passed result from an unfinished review or a focused
check. Expected next reports are shared-persistence-standards-r5.md and -spec-r5.md,
with linked import-footprint-standards-r3.md and -spec-r3.md. Retain both axes as
independent; use prior analysis where valid without reducing the full scope.

The coordinator reconciles their separate results and stable findings; it does
not add a third assessment. Root handles any correction in another immutable
candidate, retaining these same fixed bases and the entire finding history.
This prerequisite scope neither approves Chapter2 nor advances the book frontier.
