# Local 10023 — independent Spec review, round 1

**Outcome: Blocked, with findings present. Static code findings: 1, High
(`SIGNED-POT-SPEC-001`). Unresolved validation findings: 1, Blocking
(`SIGNED-POT-SPEC-VAL-001`). No mathematical-contract discrepancy found.**

Reviewer: `/root/signed_potential_review/spec`, 2026-11-03. This is the Spec
axis of the existing signed-potential review loop. It is not chapter acceptance
or a successful Lean validation result.

## Immutable scope and requirements

- Fixed base and merge base:
  `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Candidate: `9c47a052ef96b528a85660d4c632704ca03144fe`.
- Scope: `git diff 5e048f781aa04be9ce993f1e7455bdc82df22bff...9c47a052ef96b528a85660d4c632704ca03144fe`;
  all six changed files, both commits `6797860` and `9c47a05`, no exclusions.
- Requirements: `requirements/signed-potential.md`, version 1, SHA-256
  `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`,
  together with `requirements/REQUEST.md` and `REQUEST-union-v2.md`.
- Source reviewed in the clean isolated checkout
  `/workspace/scratch/b566cace4ed6/pfds/signed-potential`. All six changed
  files were compared byte-for-byte with `git show` at the candidate. The
  checkout remained clean. The existing review record had no prior independent
  Spec findings to resolve.

Read the full changed core, both new examples, the public-import change and
the stable API document. Relevant unchanged definitions and consumers were
inspected in `Resources.Measured`, `Resources.Workload`, `Resources.BinaryCounter`,
`Resources.SymmetricCosts`, `Resources.RandomAccess.End`,
`Resources.FIFOContracts`, and the retained PotentialAccounting, FIFOContracts
and RandomAccessEndCosts examples. Applied the AGENTS/README proof boundary,
architectural and domain guidance, ADR 0001, and the example-driven-development
statement-review procedure. The review did not use an unavailable manuscript
as if newly inspected: the bounded algebraic requirements and retained source
preparation define this task, and no whole-chapter source claim is made here.

Author handoff evidence was read in `research/signed-potential-implementation.md`,
`research/potential-transport-client.md`, and
`research/signed-potential-root-integration.md`. The original core report is
preserved as `research/signed-potential-implementation-draft-r1.md`; its bytes
are an exact prefix of the current report, which appends the genuine first-round
failure and correction. This supports the correction history without turning
the author's statement review into an independent approval.

## Mathematical statement review

### Actual state trajectory and separate charge observations

`budget` retains its empty and cons recursion and explicit argument order.
At a cons, it first charges `charge i s`, then recurses at `(step i s).1`.
The step observation has type `C`, and the charge has the independent type
`D`; only the latter needs `Zero` and `Add` for the definition. Thus it neither
chooses a different trajectory nor silently charges every operation at the
initial state.

`budget_append` starts the second budget at the first measured run's final
state. Its `Zero C` and `Add C` constraints come from the existing `run` in
the statement; `AddMonoid D` supplies the identities and reassociation of
charge sums. It does not unnecessarily demand an additive monoid on the step
observation. `budget_map` is the ordinary additive-homomorphism law for this
same recursion. `budget_congr_state` uses equality of next-state projections
at each instruction and state; it assumes no algebraic relation between the
two observation types. These are bounded transport facts, not a second
executor or a new potential hierarchy.

### Exact and ordered telescopes

The exact theorem assumes a local balance for every instruction and state,
then concludes

    runCost + finalPotential = initialPotential + trajectoryBudget.

Its `AddMonoid` assumptions are sufficient. In the induction, the tail's
balance is prefixed by the current cost, the current local balance is then
suffixed by the tail budget, and terms are reassociated. No terms commute.
There is no cancellation, order, positivity or global result hidden in the
premise. Empty executions retain the same state and use the additive identity.

The inequality theorem has the same boundary ordering, with `AddMonoid`,
`Preorder`, and monotonicity of addition on both sides. Those assumptions
support the two inequality transports and transitivity; a linear order,
antisymmetry, nonnegative costs or nonnegative individual charges are not
silently imposed. The three proof-side substitutions in the second commit
do not change these statements or assumptions. The current proof structure
prefixes the tail inequality and suffixes the one-step inequality in the
mathematically required positions. Exact interpretation of the pinned
monotonicity lemmas is still subject to the validation qualification below.

`run_cost_le_of_nonneg_final` requires nonnegativity of the potential at the
actual final state. It derives `cost <= cost + finalPotential` and composes
with the ordered telescope. It does not replace that terminal hypothesis
with an unjustified global premise or omit the initial potential. The
retained Nat wrapper discharges precisely this hypothesis with `Nat.zero_le`.

### Signed savings and debt

The savings definition is `cost + potential(after) - potential(before)`.
The definitions themselves need only the stated operations, while every
balance, sign-conversion and run identity uses `AddCommGroup`. Consequently
the laws make no claim that truncated natural subtraction obeys signed
accounting. `potentialCharge_balance` supplies the local equation to
`run_potentialCharge_exact`, which invokes the shared exact telescope.

The debt definition is `completeCost + debt(before) - debt(after)`.
`debtCharge_eq_potentialCharge_neg` identifies it with savings at negative
debt, and the run theorem reuses the savings theorem instead of inducting
again over a new executor. Its resulting identity is correctly oriented:

    completeRunCost + initialDebt = finalDebt + debtBudget.

Both boundary terms remain. The supplied complete-cost observation is not
identified with runtime or suspended work. The module documentation and
stable API guide explicitly leave allocation/payment coupling, argument and
result incidence, query charges, sharing, and payment before forcing to the
remaining operational developments. No splay inequality, logarithmic bound,
chapter algorithm or persistent global spending theorem is claimed.

## Connected cases and independent expectations

The following source-level connections cover the fixed required cases.
They are reviewed derivations, not newly compiled examples.

| Required case | Candidate evidence and independent mathematical check |
| --- | --- |
| Int savings, prefix and nonzero initial boundary | `IntSavings.step` costs 1 and moves to 3 or 0. The two chosen steps therefore charge 4 and -2, cost 2 in total and return to 0. `total_charge` uses `run_potentialCharge_exact`; `saved_prefix` retains the final 3; `release_boundary` starts at 3 and uses the same public identity to derive charge -2 despite actual cost 1. |
| Negative final potential | `NegativeFinal.step` costs 1 and ends at -1 from 0. Its signed charge is 0. `exact_balance` uses the generic identity; `cost_not_bounded_by_charge` derives the failure of `1 <= 0` through that identity, and a separate declaration states the failure of final nonnegativity. This is a satisfiable counterexample, not a contradictory premise. |
| Genuine fractional Real values | `FractionalSavings` uses costs 1/2 and potentials 0, 3/2, 0. The charges 2 and -1 total 1. The run result is independently stated and the total budget comes through the generic exact identity. The cost-bound application supplies actual terminal nonnegativity. It is not merely a Nat calculation with Real notation. |
| Debt sign and retained terminal debt | The same increasing state 0 to 1/4 with cost 1/2 has savings charge 3/4 and debt charge 1/4. `growing_debt_balance` invokes `run_debtCharge_exact`, retains outstanding debt, and leads to the explicit complete-cost-versus-new-charge distinction. The paid pair charges total 1 through the public debt theorem. |
| Original measured BinaryCounter lifted to Real | `Counter.realStep` calls `incWithCost` and changes only the second projection through `Nat.castAddMonoidHom`. `realRun_transport` uses the existing `reweight_run` and preserves both the original final bits and cast cost. `realStep_potential` lifts the original local write law; `realRun_potential` and `realRun_bound` apply the new generic laws. `realBudget` uses the shared state congruence, additive budget map, and retained Nat constant-budget theorem. |
| Discriminating actual counter observation | Four increments from empty take write counts 1, 2, 1, 3, totaling 7, and end at `[false, false, true]` with one set bit. `realRun_four` connects the original measured pair through run transport; `realRun_four_balance` connects the generic telescope to `7 + 1 = 8`. |
| Noncommutative exact accounting | `OrderedWords` emits the head token into `FreeAddMonoid Nat`. Two steps from `[1,2,3]` emit `[1,2]` and retain `[3]`; `two_steps_conserve` applies the exact telescope with emitted tokens before remaining tokens. The concrete case distinguishes accidental reordering. |
| Independent observation/charge types | `IndependentCharge` has a Nat observation and a free-additive-monoid charge. `two_step_budget` uses `budget_append` at the actual intermediate state to obtain `[0,1]`, rather than charging initial state 0 twice. |

There is no assumed whole-run desired value in these new cases. Local
hypotheses are proved from the actual step definitions or the existing
counter's local law. General counter statements quantify over every initial
bit list and every `n`, including empty runs; no unintended canonicality
restriction is added.

## Existing Nat contracts and public coverage

The fixed Nat signatures and explicit argument orders of `charge_iff_signed`,
`run_cost_le`, `run_zero_potential`, `budget_constant`, `budget_le_constant`,
`run_constant_charge`, and the initial-potential counterexample retain their
mathematical meaning. `Resources.run` and measured sequencing are unchanged.
Existing BinaryCounter, SymmetricCosts, RandomAccess.End and FIFOContracts
source clients are unchanged; their calls continue to ask for the same Nat
balances, bounds and trajectory budgets at source level.

The potentially underconstrained dummy zero in `FIFOContracts.abstractBudget`
has not been edited without a compiler diagnostic. I found no mathematical
contract change there; actual elaboration and all affected examples remain
part of the missing validation evidence. Source inspection alone cannot certify
that Lean infers every unchanged caller exactly as intended.

The two added public imports reach the new examples, and those imports in
turn reach the signed core and generic potential core. No changed file adds
an admission, axiom, native proof shortcut, weakened expectation or proof-budget
override. This source observation does not replace the exhaustive axiom audit.

## Unresolved findings

### SIGNED-POT-SPEC-001 — Fractional Real step definitions need noncomputable status

**Severity: High. Status: unresolved. Category: source/code-generation boundary.**

The required fractional savings and debt-sign applications define ordinary
`Examples.SignedPotential.FractionalSavings.step` and
`Examples.SignedPotential.DebtSign.step` declarations at
`Examples/SignedPotential.lean:109` and `:139`, respectively.
Their bodies use Real divisions `3 / 2`, `1 / 2` and `1 / 4`. The exact pinned
Mathlib provider implements Real inverse and division noncomputably:
`Real.inv'` at lines 86–87, its `Inv` instance at 113–114, and
`Real.instDivInvMonoid` at line 476 of `Mathlib/Basic/Real/Basic.lean`.
These mathematical step specifications therefore need to be declared
`noncomputable def`; the current ordinary definitions request executable code
through noncomputable operations.

The coordinator surfaced the Standards axis's concern; I then independently
inspected the provider and compared its SHA-256
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`.
Its exact pinned source is
<https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/Real/Basic.lean>.
The temporary local provider is
`session/tools/signed-potential-standards-040/RealBasic.lean` and is excluded
from checkpoints by the established reproducible-input policy. The provider's
lines 209–212 explicitly distinguish computable additive/ring instance paths
from the noncomputable field path; this evidence does not justify blanket
noncomputability changes to the separate Nat-to-Real counter observer.

This is a concrete source/provider finding, **not an observed compiler
diagnostic**. The saved partial second round had not completed either new
example module. The consequence is that the required fractional connected
cases cannot yet be treated as usable compiled modules. Annotate only these
two mathematical step definitions as noncomputable, preserving their bodies,
proofs and independently fixed expectations; then return the corrected
candidate and genuine validation evidence through this retained loop.
Such annotations change code-generation intent, not the algebraic statements,
kernel proof standard, or modeled numerical observations.

### SIGNED-POT-SPEC-VAL-001 — Required candidate validation is incomplete

**Severity: Blocking. Status: unresolved. Category: validation evidence.**

The requirements' connected-case item 6 and completion section require the
concrete affected closure, the candidate's own isolated pinned-Nix full build
and exhaustive audit, its matching `.lake/verification.json`, and final stock
verification immediately before acceptance. That evidence is unavailable.

The terminal first focused round at the previous commit `6797860` failed.
The corrected candidate's preserved second-round JSON in
`validation/checkpoint039-progress/signed-potential-r2.json` still says
`running` and has neither an exit code nor an end time. All 44 recorded inputs
match the immutable candidate, and the partial log records completed builds
of Potential, SignedPotential, BinaryCounter, SymmetricCosts,
BinaryCounter.Decrement, RandomAccess.End and SymmetricWorkload. These are
useful historical partial outputs. They do not establish a terminal result,
the wrapper's final input check, FIFOContracts/new-example completion, an
exhaustive audit, or exact-candidate acceptance.

`environment/recovery-040.md` records the unavailable Nix/Lean environment;
the parent additionally reports that the standard `/nix` creation request
was automatically rejected. No compiler or gate was run by this reviewer.

**Required resolution:** in a permitted pinned environment, preserve the
interrupted records, repeat the same focused scope and retain its genuine
terminal/source-identity evidence, then obtain this candidate's own unchanged
`./check.sh --candidate HEAD` success and exhaustive audit with matching
verification record. Return that evidence to the retained review loop. Run
`./check.sh --verify-candidate HEAD` immediately before accepting the identical
candidate, after both independent axes have completed. Actual compiler findings
must follow the ordinary fixed-base correction loop. The concrete annotation
repair requested above comes from inspected provider semantics; no other
source repair is requested merely from the absence of validation.

## Disposition

The full static Spec review found one High code-generation-boundary correction
and no mathematical-contract discrepancy. There is also one unresolved Blocking
validation finding. The base remains
`5e048f781aa04be9ce993f1e7455bdc82df22bff`; the reviewed candidate remains
`9c47a052ef96b528a85660d4c632704ca03144fe`. **Spec is Blocked, not Passed.**
No predecessor foundation, chapter or whole-union acceptance is advanced.
