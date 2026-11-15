# Shared persistence and import prerequisite — Standards round 4, partial

Date: 2026-11-02.
Reviewer: `/root/prerequisite_review/standards`.

## Status: PARTIAL / Blocked

This round was paused at the coordinator's request after root reported a new
full-check compiler diagnostic, IMPORT-VAL-004. The full-scope Standards
assessment and validation-evidence reconciliation are **incomplete**. This
report is neither a static-clear result nor approval of the candidate. No
guessed successor candidate has been reviewed.

The existing linked loop, all earlier axis outcomes and stable findings remain
preserved. This partial record is continuation evidence for local #10013
round 4 and #10018 round 2; it accepts no chapter or concurrent Chapter 2 work.

## Immutable scope checked before pause

- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Prior candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/import-correction`.
  Observed `HEAD` equals the candidate and porcelain status is empty.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Full scope: 13 files, four commits, 954 additions and 2 deletions.
  Narrow scope: five files, two commits, 15 additions and 2 deletions.
  No exclusions or unrelated changes.
- Commit sequence: `ad73001`, `70a1477`, `226ebae`, `324962e`.
  The latest commit adds one import to each of
  `Applications/FRP/Demand.lean`, `Applications/FRP/Finite.lean`, and
  `Examples/FRP.lean`; all other files are unchanged from `226ebae`.

The original SharedList files, applicable repository standards and four saved
requirements remain unchanged. Earlier full-scope analysis in
`shared-persistence-standards-r3.md` is retained as evidence, not approval of
this changed candidate. The current main checkout and Chapter 2 integrations
are outside this frozen scope.

## Work retained at the pause

I read the new dispatch, appended coordinator round records, candidate
manifest, correction investigation and non-import-byte comparison. The exact
Git delta independently confirms the three import additions. I inspected the
Demand proof/client source and the actual pinned providers for successor
simplification and finite unions.

The inspected provider facts support the proposed mechanisms:

- `Mathlib.Order.SuccPred.Nat` supplies `Nat.instSuccAddOrder` and imports the
  successor/addition API containing the `[simp]` theorem `Order.lt_add_one_iff`.
  This is relevant to the existing strict-successor goal after `simp_all [next]`.
- `Mathlib.Data.Set.Finite.Lattice` defines `Set.Finite.biUnion`, the finite
  union theorem used by `Finite.finiteHistory`.

The investigation and saved comparison report that all non-import bytes in
the three consumers are preserved and that the second focused client batch
passed. Full independent matching of the focused run's input hashes to the
captured candidate, cache-copy provenance assessment, the Archimedean provider
assessment, and the complete new-round full-scope review were not finished
before the hold. They are not represented here as completed checks.

## Stable finding dispositions at the pause

| Finding | Evidence and current disposition |
| --- | --- |
| PERSIST-VAL-001 | **Retained fixed with compiler evidence.** The adapter tactic correction and SharedList sources are unchanged from the previously reviewed candidate. Earlier focused compiler evidence and all historical outcomes remain preserved. |
| IMPORT-VAL-001 | Candidate adds `Mathlib.Order.SuccPred.Nat` to Demand. Provider mechanism inspected as above. **Proposed repair; this round's complete evidence reconciliation/disposition remains pending.** |
| IMPORT-VAL-002 | Candidate adds `Mathlib.Data.Set.Finite.Lattice` to Finite. Actual `Set.Finite.biUnion` provider inspected. **Proposed repair; this round's complete evidence reconciliation/disposition remains pending.** |
| IMPORT-VAL-003 | Candidate adds `Mathlib.Algebra.Order.Archimedean.Real.Basic` to the FRP example. **Proposed repair; provider/input-evidence review remains incomplete at pause.** |
| IMPORT-VAL-004 | **Unresolved validation failure.** The coordinator relayed root's running full-check diagnostic at `Examples/IndefiniteService.lean:104:6`: unknown constant `Nat.size_pow`, with unsolved goals at `101:56`. Exact diagnostic reconciliation and any repair await root's supplied evidence/new immutable candidate. |

IMPORT-VAL-004 is recorded as a reported compiler failure, not an invented
semantic defect or a reason to alter requirements. No source repair was made
by this reviewer. No new Standards-specific finding ID is allocated from the
unfinished assessment; that does not establish absence of Standards findings.

Before this pause report returned, the coordinator independently located the
exact diagnostic in the active `324962e` full log at lines 1035–1040. The
unsolved goal has `bound : ℕ`, `h : ∀ n, n.size ≤ bound`,
`large : (2 ^ bound).size ≤ bound`, and goal `False`, following the unknown
`Nat.size_pow` error. This diagnostic location/context is coordinator-supplied
evidence; this paused axis has not independently assessed its provider repair.

## Validation and continuation

Root owns the running full check for `324962e`, recorded in
`session/validation/import-footprint-324962e-full-r1.json`, with live log
`active-validation/import-footprint-324962e-full-r1.log`. No terminal full
success, matching `.lake/verification.json`, or final candidate verification
has been supplied. The new concrete compiler diagnostic also prevents a
passing result. The old `226ebae` runs and focused correction builds do not
establish acceptance of this candidate.

No compilation or mutation of the frozen source, dependencies, or build outputs
was performed. The reviewer is paused. Resume only on the coordinator's exact
candidate/manifest and diagnostic handoff, preserve this partial result and all
stable findings, and review the complete fixed-base scope of any changed
candidate. Do not convert the partial source inspection or focused claims into
approval.

## Result at pause

| Scope | Fixed base | Candidate | Finding status | Standards outcome |
| --- | --- | --- | --- | --- |
| #10013, round 4 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `324962e733886e66d6cd92af6cb68627ed4c8f1d` | One newly reported unresolved validation failure; three prior import repairs still awaiting complete reviewer disposition; PERSIST-VAL-001 retained fixed. Standards assessment incomplete. | **PARTIAL / Blocked** |
| #10018, round 2 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `324962e733886e66d6cd92af6cb68627ed4c8f1d` | Same retained validation findings; IMPORT-VAL-004 blocks acceptance. No completed severity assessment of code/prose findings. | **PARTIAL / Blocked** |
