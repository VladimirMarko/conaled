# C03-RANDOM-MEAN-ELAB-003: connected mean-example normalization

Candidate `bf6e86970ea873d8b890cdceedcfd262bbacbb80`, tree `3fff7fa2cac77072c9a7f325e655667ecbe0779d`, parent `35d02bac718a7fdc84161dfa802fbc757c62b648`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `fix(selection): normalize connected mean examples (#174)`.
This examples-only correction is **uncompiled**. Root remains sole compiler owner.

## Actual checked boundary

Mean focused attempt 3 closed with actual exit 1 at the parent: owned session
89256, terminal `ec928e`, root closure `aa5eec`. The complete log and closure
were read in `8b5ba1`. The 8,626-byte outer log has SHA-256
`89a49ef47764b4a615698ea8bf574d138bf8d2abc432487121f49929543f813c`.
It reports `Applications.Resources.RandomSelectionMean` built in 13 seconds,
then two example errors. This is actual core-module progress, not a passing
pair or full candidate check. All 14 attempt records and 86 previous author
records remain unchanged. Do not poll the closed session again.

## Exact changes and preserved meaning

Only `Examples/RandomSelectionMean.lean` changes, with eight insertions and one
deletion in two proof bodies:

- `duplicate_source_law`: after the existing actual duplicate execution and
  `PMF.map_comp`, `rfl` reduces function composition and the actual source-cost
  projection. The law remains the same uniform occurrence pushforward of
  `i : Fin 2` to `12+i`, for arbitrary repeated value x.
- `two_key_scan_step`: after `scanExpectation_cons`, `change` exposes the
  definitionally equal `Fin 2` sum of the same actual `stepRun` branches.
  `Fin.sum_univ_two` then expands the two choices, followed by the existing
  partition calculation. The result is still `2 + (1/2)*E[W on [0]]` for
  rank zero on `[0,1]`, with only the pivot-one child continuing.

Every one of the 108 public headers and 13 authored private helper headers and
bodies is unchanged. All definitions, imports, options and numeric expectations
are unchanged. The successfully built mean core and all original four source
files are byte-identical. Existing empty, invalid, singleton, duplicate, pair,
actual-cost and generic-integrability cases are all retained. The full claim and
case assessment is preserved in `precommit-assessment.json`.

Mean core SHA-256: `5a7d396ed0d451c0b0ec51493c004b721c804c69263ad7c659f023cab3ddda8f`.
New examples: 5962 bytes, SHA-256
`b9c83ac6e4dda31c6c70d6ccbf021cfcad5ca8317f5a3bf1133788fc559bb7af`, Git blob `ae7113072d39c3549208b52feae61e884c5735d5`.
The complete diff is `source.diff`, SHA-256
`59c6a9ed94d7e9e43ac5de7d9a7d7b8f484551c8d0541e71ac13fe58832d8bed`.

## Root-only focused target and complete inspection input

```text
lake build Applications.Resources.RandomSelectionMean Examples.RandomSelectionMean
```

`Statements108-mean-correction3.lean` is the unchanged complete explicit-@ input,
SHA-256 `a323a5014823dfdacd05249b5829b83d51eb2741cd8964601d02ba6aecb9f46e`. Its companion preparation JSON binds all 108
targets and all six source blobs to this candidate/tree. No author type program
has run, and no new actual elaborated-type output is claimed.

Source-preservation and whitespace checks exited 0 in `18ef30`. Actual staging,
staged whitespace check and commit exited 0 in `285c55`. These are source and
record checks; the next actual focused terminal remains pending. The full
candidate check/audit, both independent axes and immediate verification remain
mandatory. Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Hold

All six sources and own provenance are held until root's actual terminal or
explicit release. No drift/tail or other probability extension was written.
Exact natural-w >= tail constants, positive-length domain and empty countercase
remain; the worst-case and pivot-policy families remain required. The inaccessible
Karp primary-source limitation is unchanged. No finding closure or acceptance
is claimed.
