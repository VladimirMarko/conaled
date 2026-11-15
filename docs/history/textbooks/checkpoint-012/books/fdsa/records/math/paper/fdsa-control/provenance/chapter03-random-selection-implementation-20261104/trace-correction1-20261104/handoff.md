# C03-RANDOM-TRACE-ELAB-001: infer the actual value congruence

## Immutable correction and hold

- Candidate: `2b5ff20504d8811587859e6eb3351cb1598a4504`
- Tree: `77b3133a78f81a22093c13d90b573a707b797f99`
- Parent: `0fa717b8c150e0ae6edb9d538dd2b86d73f02b2d`
- Branch: `work/fdsa-ch03-random-selection`
- Status: clean. All source and provenance writes are held after this handoff.
- Commit: `fix(selection): infer actual prepend value congruence (#174)`; actual exit 0, tool `3b73a9`.

Root remains the sole serial qualified compiler owner. No author Lean/Lake, check, audit, environment, dependency, cache or output action occurred. The successor is uncompiled.

## Actual failure and execution-transport boundary

The complete first trace log and completed native/outer recorder results were read in `5b9708`, with the closed-recorder marker read in `ec9355`. They establish an actual native command exit 1 and recorded-child exit 1. The original execution transport returned Unknown process id on polling historical session 81642, so its terminal remains unavailable. No owned-terminal receipt or credit is fabricated; that session was not polled by this author and must not be polled again.

- Full outer log: 13,204 bytes, SHA256 `9ca4d210228b920bd657ba8f4c8ca2738e3049361159260ce8319d17c04bacab`.
- Native log: 12,920 bytes, SHA256 `67287412d131b49023f193b4c422f8140ad3108e840a12ad58df29eb7d732bf2`.
- Transport reconciliation: 6,118 bytes, SHA256 `3d3e6864685ddf0cc75e6c92fafb4e8370eac810f452dca633ac8c6420d5e602`.

The complete native body matches the outer log's recorded prefix/body/suffix exactly. The single reported core diagnostic was line 30 in `prepend_injective`: backward elaboration of `congrArg` expected `h : r = s`, while the actual hypothesis proves equality of the prepended outcomes. The core did not build and the example module was not built.

## Exact proof-only change

Only the first component proof in `prepend_injective` changed:

```lean
  · have hv := congrArg (fun z : Outcome α => z.1) h
    exact hv
```

This first synthesizes the same value-projection congruence from the actual hypothesis, then checks the inferred result against the value-equality goal. Definitional reduction of the existing `prepend` supplies that equality. The trace-tail and natural source-addition cancellation proofs are unchanged.

The theorem still quantifies every payload type and every fixed natural size, occurrence index and source cost. It requires no order, distinctness, valid rank, PMF support, inhabited payload or countability. No definition, hypothesis, conclusion, bound, trace or source observation changed. No simplifier/linter suppression was introduced.

The exact diff is one file, two inserted lines and one removed line. `source.diff` is 690 bytes, SHA256 `b8155211222ded207feef2f877d5c69aa9ecf3dc762ac41ed8795724fd215b19`. The corrected core was read completely with the exact diff in `5f6200`. Its current size is 7,823 bytes, SHA256 `146f81f9db7782fd30f54848bee87038a2f9a1edcb4c2c776e854494bc80729e`, blob `84f42a374c0066da45c42431a0145a78cab2a718`.

## Preservation and statement/case assessment

All 307 authored headers and their source contexts remain exact: 289 public names, 18 private helpers and 25 definitions. All 15 other source files are byte-identical, including all 14 pre-trace files and the entire trace example module. All 23 trace-stage public claims and all independent expected cases remain unchanged. The full unsorted interior-rank, signed, duplicate, singleton, empty/invalid, fixed-state and unsupported-outcome cases are retained.

`precommit-assessment.json` retains the complete declaration inventory and previous claim/case reviews, records the exact one-line replacement, and explains the changed elaboration step without claiming actual elaborated output. Assessment readout: `0164c9`. All 274 prior own records and all 12 first-trace run records are preserved, along with the transport incident.

The source-level checked-use finding `C03-RANDOM-TRACE-CONNECTION-001` remains separate and pending actual compilation of its client. Its newly added `middle_path_supported` example is unchanged; no acceptance credit is inferred from this proof correction. No independent Standards/Spec reports were edited or their conclusions reused.

The candidate-bound input `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter03-random-selection-implementation-20261104/trace-correction1-20261104/Statements289-trace-correction1.lean` is byte-identical to the preceding 289-name input, including every name, order and print option: 16,690 bytes, SHA256 `e13e022e1727aeb2ec1cc896906a639530fa1c67a5cb5afed990b192dca23db2`. The preparation record binds it to the exact candidate and all 16 source blobs.

## Next root check and remaining scope

Requested newly named focused pair:

- `Applications.Resources.RandomSelectionTrace`
- `Examples.RandomSelectionTrace`

There is no successor focused pass, actual type output, full check, audit, independent acceptance outcome, immediate verification or Chapter 3 acceptance yet. The original Karp source remains inaccessible; no source recovery or quotation is invented.

The universal endpoint stage remains pending and held: every arbitrary distinct input and every valid worker rank; target retained to singleton under minima while rank positive and maxima at zero; exact actual projected trace probability 1/n!; triangular scan attainment; unbounded Nat family; and actual source-cost lower/upper transport.
