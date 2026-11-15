# C03-RANDOM-MEAN-ELAB-002: explicit empty-scan observation

Candidate `35d02bac718a7fdc84161dfa802fbc757c62b648`, tree `7bbe5251363e6a40e7b15e7b059313db44c41fc4`, parent `ffc6707febff782a386615a20a0ef3dee9112b2d`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `fix(selection): specialize empty scan expectation (#174)`.
The correction is **uncompiled**; root remains the sole compiler owner.

## Actual evidence

Mean focused attempt 2 closed with actual exit 1 at the parent, owned session
33800, terminal `4cd799`, root closure `8d3ff9`. The entire closed log and closure
were read in `f4511d`. Its outer log has 8,004 bytes and SHA-256
`259a7f867680dd9b1c62afaa714e9537e40e28b82269af206a20ea84b6d84ece`.
All 14 records and all 75 prior author records are preserved. The only reported
error was the unresolved scan observation in `scanExpectation_nil`; disappearance
of the other four errors does not establish a successful core or examples build.

## Source, statement and case preservation

Only `Applications/Resources/RandomSelectionMean.lean` changes: two inserted
lines and one deleted line, solely within `scanExpectation_nil`.
The proof now passes the explicit observation
`fun result : Outcome α => (scanVolume result.2.1 : ℝ≥0∞)` to the existing
`workExpectation_nil`, then simplifies `scanVolume_nil` and `Nat.cast_zero`.
The intended result remains the actual empty scan expectation zero for every
ordered payload and zero-based worker rank. There is no inhabited-payload or
valid-rank requirement and no alternate execution/probability model.

All 108 public headers, all 13 authored private helpers, every executable
and observation definition, and all imports/options are unchanged. The other
five source files are byte-identical. Every original case and its expected
result is retained, including the invalid worker extension, duplicated values,
actual pair distributions, source costs and same-run mean bridge. The complete
prior claim/case assessment and exact new header comparison are included in
`precommit-assessment.json`.

New core: 16493 bytes, SHA-256
`5a7d396ed0d451c0b0ec51493c004b721c804c69263ad7c659f023cab3ddda8f`, Git blob `b777b0de341a7cb0df0b1b4a2542904250959de1`.
Exact diff is `source.diff`; its SHA-256 is
`6111d0c76aa40b20e93578ab1cce088059a15b047fcb56dc25a21256c6be1b08`.

## Root-only focus and type input

```text
lake build Applications.Resources.RandomSelectionMean Examples.RandomSelectionMean
```

`Statements108-mean-correction2.lean` contains all 108 explicit-@ targets in
original order, with full printing. It is byte-identical to the prior input,
SHA-256 `a323a5014823dfdacd05249b5829b83d51eb2741cd8964601d02ba6aecb9f46e`. The companion preparation JSON binds it to this
exact candidate/tree and all six source blobs. No author type execution occurred.

Actual source preservation and whitespace check exited 0 in `8afd3e`; staging,
staged whitespace check and commit exited 0 in `d29102`. These checks provide
no new Lean, audit or type-output credit. Full candidate validation, both review
axes and immediate verification remain required. The fixed task base is
`2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Hold and retained continuation

All six sources and own provenance are held for root's actual terminal or
explicit release. No drift, linear-bound, tail, worst-case or pivot-policy source
extension was written. The exact future >= tail retains n>0: at n=0 its event
has probability 1, so the proposed right side fails for positive w. This empty
countercase must remain visible; replacing >= with > is not authorized. The
original constants, duplicate cases and Karp primary-source limitation remain.
No finding closure or acceptance is claimed.
