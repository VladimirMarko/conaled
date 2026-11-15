# Local 10023 — independent Spec review, round 2

**Outcome: Blocked. Unresolved static code/prose findings: 0. Unresolved
validation findings: 1, Blocking (`SIGNED-POT-SPEC-VAL-001`).**

Reviewer: `/root/signed_potential_review/spec`, 2026-11-03. This continues the
same independent Spec axis and finding record. The previous source finding
is fixed at source level; no compiler, full build or axiom-audit success is
claimed.

## Complete fixed-base scope

- Fixed base and merge base:
  `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Corrected candidate: `d24c443ba22019613b1ce646d6eed7279c791ad6`.
- Previous candidate: `9c47a052ef96b528a85660d4c632704ca03144fe`.
- Full comparison: `git diff 5e048f781aa04be9ce993f1e7455bdc82df22bff...d24c443ba22019613b1ce646d6eed7279c791ad6`;
  six files, three commits (`6797860`, `9c47a05`, `d24c443`), no exclusions.
- Requirements: `requirements/signed-potential.md`, version 1, SHA-256
  `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`;
  `REQUEST.md` and `REQUEST-union-v2.md` remain governing requests.
- Frozen source checkout:
  `/workspace/scratch/b566cace4ed6/pfds/signed-potential`.

Independently confirmed the new HEAD, ancestor/merge base, nonempty complete
diff and clean checkout. Compared all six changed source files with their Git
blobs at the new candidate. The five files other than
`Examples/SignedPotential.lean` are byte-identical to round 1. The latter
differs by exactly the two requested `noncomputable` qualifiers: adding them
to the two old declaration lines reproduces the entire new file byte-for-byte.
Its new SHA-256 is
`745400e50b758413a9087c64a9a9fe99a268236afb46618be02ecd5d82c034fc`.

Read `validation/signed-potential-recovery-review-r2.json`, the exact retained
`validation/signed-potential-noncomputable-correction.patch`, and
`research/signed-potential-noncomputable-correction-r1.md`. Their stated scope
matches the immutable source comparison. The source-diff check is recorded
as exit 0; this is not Lean validation.

## Reused analysis and full-scope reassessment

The complete first-round report remains unchanged at
`reviews/signed-potential-spec-r1.md`, SHA-256
`63de2736975bbf679e6b4c70fc33b3e5acb45e6466780fc580daefa25329efbd`.
The same requirements, applicable repository standards, unchanged core/source
dependencies and author handoff justify reusing its detailed mathematical
analysis. This is reuse of matching source-level analysis, **not reuse of a
passing review or candidate validation**: round 1 was Blocked and remains a
historical report of the earlier candidate.

The following reassessment covers the entire fixed-base task, including the
new annotations and unchanged material:

| Requirement family | Corrected-candidate assessment |
| --- | --- |
| Existing executor and same-state budget | `Resources.run` and measured sequencing remain the existing implementations. `budget` still charges the current state and follows the actual first projection. Independent step/charge codomains, empty/cons behavior and explicit argument order are unchanged. No duplicate executor or trajectory was introduced. |
| Budget append and transport | `budget_append` starts its suffix at the preceding run's final state and retains only the algebra needed for its statement. `budget_map` maps the same charge accumulation through an additive homomorphism. `budget_congr_state` compares actual next-state projections without an unnecessary observation-algebra assumption. |
| Exact noncommutative telescope | The local equation and global boundary ordering remain cost plus final potential equals initial potential plus charge. The induction uses association in execution order, with an additive monoid and no commutativity, cancellation, order or positivity assumption. The free-additive-monoid word example still exercises ordered output before remaining potential. |
| Ordered telescope and final boundary | `run_potential` still uses a preorder with monotone addition on both sides. The cost-only result still explicitly assumes nonnegativity at the actual final state and retains initial potential. Nat wrappers discharge the terminal premise without changing their old meanings or call order. |
| Savings and debt identities | Savings remains cost plus after minus before; debt remains complete cost plus before minus after. Balance/run laws use `AddCommGroup`, and debt reuses the savings theorem at negative potential. Terminal debt is retained. No truncated Nat subtraction, source execution theorem or persistent global-credit claim is substituted. |
| Int and terminal-counterexample cases | The cost-1 savings sequence retains potentials 0, 3, 0 and charges 4, -2, with total 2. Prefix and release-only cases preserve both boundaries. The separate cost-1/final-minus-1 case still derives charge 0 through the public exact law and refutes dropping a negative terminal potential. No proof or expectation changed. |
| Fractional Real savings | `Examples.SignedPotential.FractionalSavings.step` now explicitly describes a noncomputable mathematical step, while its body remains cost 1/2 and state 3/2 or 0. Charges 2 and -1, total 1, exact-budget connection, and the supplied final-nonnegativity proof are unchanged. |
| Debt-sign case | `Examples.SignedPotential.DebtSign.step` now has the same mathematical-specification status. Its cost 1/2 and debt change 0 to 1/4 still distinguish savings charge 3/4 from debt charge 1/4. The actual public debt theorem supplies both one-step and paid-pair accounts, and the remaining-debt qualification is preserved. |
| Actual counter reobservation | The ordinary Nat-to-Real observer still calls `BinaryCounter.incWithCost`, preserving the state and casting the original measured cost through `reweight_run`. Its local write law feeds the generic telescope and ordered bound; its budget uses the shared transport lemmas. Four increments retain writes 1+2+1+3=7, final one-bit potential 1 and balance 7+1=8. No broad noncomputability annotation was added to this separate additive client. |
| Independently typed charges | The Nat-observation/free-word-charge case still uses `budget_append` at the actual intermediate state, yielding `[0,1]`. The annotation fix does not alter observation or charge type inference in this case. |
| Existing Nat clients | BinaryCounter, SymmetricCosts, RandomAccess.End, FIFOContracts and their example sources remain unchanged. Their required Nat statements, boundary distinctions and public calls are retained. Actual elaboration of the whole affected closure remains an unresolved validation obligation, including the existing dummy-zero inference in FIFOContracts. |
| Public integration and stated limits | Both new example imports and the signed-core import path remain public. The stable API guide still distinguishes algebraic identities from operational debt/forcing obligations and chapter algorithms. No axiom, admission, native proof shortcut, proof-budget override or changed expected observation is introduced by the correction. The required exhaustive audit has not run. |

The two `noncomputable` qualifiers alter code-generation intent only. They do
not replace the mathematical definitions by assumptions, alter their result
types, or change any theorem statement or proof term. The specified cases
continue to use the same public laws with their actual hypotheses established
in the source. No new mathematical discrepancy was found on the complete
corrected scope.

## Finding dispositions

### SIGNED-POT-SPEC-001 — Fixed with source-review evidence

**Previous severity: High. Current status: fixed at source level in
`d24c443ba22019613b1ce646d6eed7279c791ad6`.**

The earlier ordinary definitions of
`Examples.SignedPotential.FractionalSavings.step` and
`Examples.SignedPotential.DebtSign.step` requested executable definitions
through noncomputable Real division. Both are now explicitly
`noncomputable def`, exactly as requested. Their types, bodies, theorem
statements, proofs and independently fixed numerical expectations are
unchanged.

This resolves the identified declaration-boundary defect against the exact
pinned Mathlib provider inspected in round 1, SHA-256
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`:
<https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/Real/Basic.lean>.
Its noncomputable inverse/division paths are unchanged; its separately
computable additive/ring paths still support keeping the counter observer's
declaration unchanged. The generic mathematical model allows noncomputable
Real specifications, as recorded in ADR 0001.

No actual compiler diagnostic or successful compilation is attributed to this
source review. Any further elaboration/proof/code-generation problem remains
subject to actual validation and the normal correction loop; closure of this
precise source finding does not close the next finding.

### SIGNED-POT-SPEC-VAL-001 — Still unresolved

**Severity: Blocking. Category: required validation evidence.**

The concrete affected closure, this corrected candidate's own isolated
pinned-Nix full build and exhaustive audit, matching `.lake/verification.json`,
and immediate final stock candidate verification remain unavailable.

The first focused round failed at `6797860`. The historical second round at
`9c47a05` has partial output only: its saved record still lacks a terminal exit
and final input check. The completed core/consumer targets in that historical
log retain their limited evidentiary value, but neither the new example/FIFO
closure nor any whole-run/full-gate result can be inferred. The changed
`Examples/SignedPotential.lean` hash also prevents describing that old run as
validation of the complete newer candidate.

No compiler or formal gate ran during this correction or review. The current
environment blocker and rejected installation request remain recorded in
`environment/recovery-040.md` and
`environment/recovery-040-approval.json`. A clean Git checkout, matching file
hashes and a successful source-diff check do not substitute for Lean
elaboration, the project build or the exhaustive axiom audit.

**Required resolution remains:** run the unchanged eleven-target focused
scope against the corrected immutable candidate in a permitted pinned
environment, retain its actual terminal and source-identity evidence, and
obtain that candidate's own `./check.sh --candidate HEAD` build/audit success
and matching verification record. Return the results to this retained review
loop, preserving all previous findings and evidence. Immediately before
accepting identical bytes, after both axes have the necessary evidence, run
`./check.sh --verify-candidate HEAD`. Actual failures require normal
fixed-base corrections and renewed full-scope review.

## Final outcome

Base `5e048f781aa04be9ce993f1e7455bdc82df22bff` and candidate
`d24c443ba22019613b1ce646d6eed7279c791ad6` cover the full six-file task.
One prior static finding is fixed with source-review evidence; there are no
remaining static findings and one unresolved Blocking validation finding.
**Spec remains Blocked, not Passed.** No predecessor foundation, chapter,
forward contract or whole-union acceptance advances.
