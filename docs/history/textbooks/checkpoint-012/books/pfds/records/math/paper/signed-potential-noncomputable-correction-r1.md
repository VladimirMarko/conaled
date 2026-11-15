# Local 10023 — recovered Real-example correction

This is an implementation report in the existing signed-potential review loop.
It is not an independent review outcome or a compiler-success claim.

## Fixed scope and finding

Requirements remain `requirements/signed-potential.md` version 1, SHA256
`bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`.
Both fixed bases remain `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
The first complete independent reviews cover predecessor
`9c47a052ef96b528a85660d4c632704ca03144fe`; both reports and the coordinator
reconciliation were preserved and read fully before the source was unfrozen.

Standards finding `SIGNED-POT-STD-CODE-001` and Spec finding
`SIGNED-POT-SPEC-001` identify the same source issue: ordinary definitions
`Examples.SignedPotential.FractionalSavings.step` and
`Examples.SignedPotential.DebtSign.step` use noncomputable Real division.
The root implementer inspected the exact pinned provider recorded by both
reviewers, including its noncomputable inverse/division instances and separate
computable additive/ring paths. Provider SHA256:
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`.
Source URL:
https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/Real/Basic.lean

## Correction and statement review

Corrected candidate: `d24c443ba22019613b1ce646d6eed7279c791ad6`.
Commit: `fix(resources): mark fractional real examples noncomputable (#10023)`.
Only the two named `def` declarations receive the `noncomputable` qualifier.
The change records their intended mathematical-specification role instead of
requesting executable code through the Real inverse operation.

Their types, bodies, quantifier scope, all theorem statements, all proof terms
and every independently fixed numerical expectation are unchanged. In
particular:

- Fractional savings still costs 1/2 at each step, visits potentials 0, 3/2, 0,
  has charges 2 and -1, and total cost/charge 1. The budget result still invokes
  `run_potentialCharge_exact`; the cost-only bound still proves actual final
  nonnegativity before invoking `run_cost_le_of_nonneg_final`.
- Debt still uses complete cost 1/2 and debt 0 to 1/4 to distinguish savings
  charge 3/4 from debt charge 1/4. Its one-step and paid-pair identities still
  invoke `run_debtCharge_exact`, retaining the terminal-debt qualification.
- The existing measured binary-counter program and its Nat-to-Real additive
  observation map remain unchanged. Its computable additive path does not
  justify changing its declaration or the generic resource library.

This is the existing example-driven-development loop applied to a declaration
boundary correction. No expected value was changed to obtain a proof, and no
new claim, axiom, admission, tactic-budget setting or audit exception was added.

## Actual verification and limits

The exact two-line source diff was inspected, `git diff --check` exited zero,
the correction was committed on `pfds/signed-potential`, and the resulting
isolated checkout is clean. The complete six-file comparison against the fixed
base and its hashes are recorded in
`validation/signed-potential-recovery-review-r2.json`.

No Lean compiler, focused build, full candidate check, proof audit or final
candidate verifier ran. The Nix environment is unavailable and the standard
installation request was rejected, as recorded in
`environment/recovery-040-approval.json`. The old corrected focused round 2
still has an unknown terminal result; it cannot validate this newer candidate.

The two source findings are proposed for closure by the same independent
reviewers on this immutable corrected candidate. Their validation findings
`SIGNED-POT-STD-VAL-001` and `SIGNED-POT-SPEC-VAL-001` remain unresolved. Full
acceptance still requires the eleven-target focused scope, this candidate's
own stock full check/audit and verification record, both review axes, and
immediate final verification. No predecessor or chapter acceptance advances.
