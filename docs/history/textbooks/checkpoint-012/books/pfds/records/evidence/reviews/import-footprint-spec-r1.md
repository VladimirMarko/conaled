# Import footprint — independent Spec review, round 1

Date: 2026-11-02.
Reviewer: `/root/prerequisite_review/spec`.

**Spec: Blocked pending exact-candidate full validation.** Static review is
complete with **0 unresolved implementation findings**, no worst severity and
no new `IMPORT-SPEC` identifier.

## Pinned scope and linked full review

- #10018 fixed base and confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Sole narrow-scope commit: `226ebae`, changing only the import lists in
  `Applications/FRP/Spec.lean` and `Applications/FRP/Equivalence.lean`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-imports`;
  observed exact `HEAD`, clean worktree, no exclusions.
- Requirements: `import-footprint.md` version 1 plus saved original request and
  book/thesis union clarification. The linked #10013 requirements remain v2.

This axis also reviewed the complete ten-file candidate against #10013's
stable base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`. The complete scope,
statement review, dependencies, preserved prior outcomes and PERSIST-VAL-001
disposition are in
[`shared-persistence-spec-r3.md`](shared-persistence-spec-r3.md). This is one
independent Spec review with two explicit ticket scopes, not a duplicate axis.

## Spec assessment

The exact Git-object comparison confirms that all non-import bytes in both
FRP files are identical at the narrow base and candidate. Every declaration,
statement, proof body, example and explanatory assumption is preserved. The
changed providers correspond to the real-number, finite-set, ordering and
arithmetic-tactic facilities used in those modules, and all provider paths
exist in the pinned dependency source.

Relevant unchanged direct consumers in `Applications.FRP.Finite`,
`Applications.FRP.Frontier` and `Examples.FRP` were inspected. The candidate
retains their finite-batch correspondence, prefix protocols and connected
square examples. Narrowing imports changes the elaboration environment, so
full integration compilation remains a necessary gate even though source
statements are unchanged. No concrete missing provider or changed meaning was
found by static inspection.

The delta preserves the public entrypoint, every other project source,
verification scripts, toolchain/dependency configuration, guard, source
policy, exhaustive audit-root selection and axiom allowlist. No gate was
weakened. Neither source reduction nor the earlier focused build establishes
a matched performance improvement; this report makes no memory or timing claim.

PERSIST-VAL-001 remains fixed by the unchanged adapter correction and the
recorded focused compiler evidence; it is not renamed or erased. There are no
new #10018 or linked #10013 Spec implementation findings. The complete book
and thesis are available, but this prerequisite accepts no chapter and does
not approve the live Chapter 2 changes outside the frozen candidate.

## Required validation remains open

The execution record `session/validation/import-footprint-226ebae-full.json`
still reports the exact candidate as `running`, with `acceptance: false`.
The live log `active-validation/import-footprint-226ebae-full.log` reports all
957 project modules as the build scope and continuing compilation, without a
terminal complete build/audit result. `.lake/verification.json` was absent at
inspection. This reviewer ran no compilation and changed no candidate or
dependency input.

Before this axis may pass, supply successful terminal full-check/audit output,
the matching `.lake/verification.json`, and final
`./check.sh --verify-candidate HEAD` evidence for
`226ebaef53b9eba97bef4b3b6ca364fdea488c69`. Focused and prior interrupted checks
are not substitutes. The completed static review can be retained while those
evidence items are assessed on this unchanged candidate; a changed candidate
needs a new full-scope round.

**Result:** base `70a1477d822efd4fdcec2007280f650bb4695eda`, candidate
`226ebaef53b9eba97bef4b3b6ca364fdea488c69`; 0 unresolved implementation findings,
no worst severity; **Spec Blocked on exact validation**.
