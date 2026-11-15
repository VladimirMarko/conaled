# Import footprint — independent Standards review, round 1

Date: 2026-11-02.
Reviewer: `/root/prerequisite_review/standards`.

**Standards: Blocked pending exact-candidate full validation.** Static review
is complete with **0 unresolved code/prose findings**, no worst severity and
no heuristic-only change request. No new `IMPORT-STD` identifier is allocated.

## Pinned scope and full linked review

- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Sole narrow-scope commit: `226ebae`, replacing only the aggregate imports
  in `Applications/FRP/Spec.lean` and `Applications/FRP/Equivalence.lean`.
- Read-only isolated checkout:
  `/workspace/scratch/ca9a61d0bf30/validation-imports`; exact candidate `HEAD`
  and empty porcelain status observed. No exclusions.
- Requirements: `import-footprint.md` version 1, saved original request and
  union clarification; linked SharedList requirements remain version 2.

This same independent Standards assessment also covers the complete ten-file
candidate against #10013's stable base
`cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`. Its full architectural and statement
assessment, applicable standards, source evidence and prior-finding disposition
are in [`shared-persistence-standards-r3.md`](shared-persistence-standards-r3.md).
These reports record two ticket scopes for one independent axis.

## Standards assessment

The exact Git-object comparison confirms that every non-import byte in the two
FRP files is unchanged. All statements, proof bodies, definitions, examples and
scope explanations are preserved. Every selected provider exists in the pinned
Mathlib source, and the real-number, finite-set, order and tactic facilities
correspond to uses in the affected modules. Existing local imports remain.
There is no all-library replacement shim or new abstraction.

I read both complete FRP files and inspected the three direct consumers,
`Applications.FRP.Finite`, `Applications.FRP.Frontier` and `Examples.FRP`.
Their finite-history bridge, complete-prefix semantics and square-composition
cases remain unchanged. No concrete missing provider or changed mathematical
meaning was established by static inspection. The narrower elaboration
environment still requires complete compilation of affected consumers.

The delta leaves the public entrypoint, all other declaration sources,
toolchain and dependency configuration, source policy, integrity guards,
verification scripts, exhaustive audit-root selection and axiom allowlist
unchanged. All 957 project modules remain required. Source preservation and
focused compilation do not establish a matched memory/timing improvement;
none is claimed here.

The linked PERSIST-VAL-001 finding remains fixed by the retained adapter
correction and its specific focused compiler evidence. No prior finding or
Blocked outcome is erased or renamed. Both full sources are available, but
this prerequisite accepts no chapter and does not approve concurrent Chapter 2
work outside the frozen candidate.

## Required validation and continuation

At final inspection, `session/validation/import-footprint-226ebae-full.json`
still reported this exact candidate as `running` with `acceptance: false`.
The active log `active-validation/import-footprint-226ebae-full.log` established
source/coverage/version checks and the 957-module build scope, then showed
ongoing compilation. `.lake/verification.json` was absent.

A passing outcome requires successful terminal full-build/exhaustive-audit
completion, a matching `.lake/verification.json`, and final
`./check.sh --verify-candidate HEAD` evidence for
`226ebaef53b9eba97bef4b3b6ca364fdea488c69`. Focused runs, historical interrupted
checks and partial logs do not meet those requirements. This reviewer ran no
compilation and changed no candidate, dependency or build output.

The completed static review can be retained while the missing evidence is
assessed on the unchanged candidate. A changed candidate requires a new full
linked round. Report writes respected the checkpoint hold and began only after
the coordinator relayed release.

**Result:** base `70a1477d822efd4fdcec2007280f650bb4695eda`, candidate
`226ebaef53b9eba97bef4b3b6ca364fdea488c69`; 0 unresolved code/prose findings,
no worst severity; **Standards Blocked on exact validation**.
