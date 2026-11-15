# Local 10023 — potential algebra implementation and statement review

Implementation assignment: `/root/potential_generalization_inventory`, within
the root coordinator's existing implement/review loop. No separate loop was
created. This report covers the assigned core, not candidate acceptance.

## Requirements and starting state

Read requirements version 1 from `session/requirements/signed-potential.md`.
Its SHA-256 is
`bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`.
Read the supplied baseline and materialization-reuse records. They identify
the isolated `signed-potential` checkout, branch `pfds/signed-potential`, and
fixed base `5e048f781aa04be9ce993f1e7455bdc82df22bff`. The baseline is clean,
with no pre-existing task changes or exclusions. The coordinator preserved the
prior materialization's source and references while moving its ordinary build
outputs; the record explicitly says that no verification approval was reused.

The source starting hash recorded for `Applications/Resources/Potential.lean`
is `680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe`.
No Git, compiler, cache, process-management, resource-management or remote
operation was performed by this implementation assignment. The coordinator
owns those operations and the frozen focused validation wrapper.

Read and applied the repository's AGENTS, architectural and domain guidance,
language direction, glossary and relevant ADRs, implement skill, shared review
procedure, and example-driven-development skill/worked example. Earlier
source-only investigation is retained in
`session/research/potential-generalization-inventory.md`.

## Implemented scope

Changed `Applications/Resources/Potential.lean` in place, retaining the same
budget recursion and all existing explicit argument orders. Added
`Applications/Resources/SignedPotential.lean`. The possible FIFOContracts
dummy-zero annotation has not been made: it should be justified only by an
actual compiler ambiguity. No other source was edited by this assignment.

The new public interface is:

| Declaration | Explicit arguments after implicit types and instances |
| --- | --- |
| `budget` | `step charge is s` |
| `budget_append` | `step charge is js s` |
| `budget_map` | `h step charge is s` |
| `budget_congr_state` | `step other charge same is s` |
| `run_potential` | `step charge potential hstep is s` |
| `run_potential_exact` | `step charge potential hstep is s` |
| `run_cost_le_of_nonneg_final` | `step charge potential hstep is s hfinal` |
| `potentialCharge` | `step potential i s` |
| `potentialCharge_balance` | `step potential i s` |
| `run_potentialCharge_exact` | `step potential is s` |
| `debtCharge` | `step debt i s` |
| `debtCharge_eq_potentialCharge_neg` | `step debt i s` |
| `run_debtCharge_exact` | `step debt is s` |

The exact signatures were sent to the coordinator and transport-client author
before they developed their connected uses. There is no generic constant/nsmul
layer, invariant hierarchy, parallel budget or second executor.

## Statement review

### Trajectory and codomains

`budget` takes a step observation in C and a charge in D, with independent
universes for both types. Only D requires `Zero` and `Add`. Each cons adds the
charge at the current state before following that actual step's first
projection. It does not charge every operation at the initial state, omit
intermediate states or commute the sequence of charges.

`budget_append` requires `Zero C` and `Add C` because its statement refers to
the existing `run`. It requires `AddMonoid D` to reassociate the two charge
sums. It does not require associativity of C merely to use the run's state.
The second budget starts at the first run's final state. The empty case uses
the additive identities; the cons case only reassociates D.

`budget_map h step charge is s` says that h of the original budget equals the
budget of the mapped charge, for an additive monoid homomorphism D to E. C
requires no algebra. `budget_congr_state` compares possibly different step
observation types under pointwise equality of their first projections. Its
proof uses that equality at each visited state. It requires only Zero/Add on
the charge, with no constraint on the observation transformation. Together
with the existing `reweight_run`, these facts suffice for the actual counter's
Nat-to-Real observation map; no new execution transport is introduced.

### Exact and ordered telescoping

`run_potential_exact` assumes one additive monoid C shared by actual costs,
charges and potential. The hypothesis is local, quantified over every command
and state, and does not assume the whole-run conclusion. Its conclusion is
the existing ordered expression

    totalCost + finalPotential = initialPotential + totalCharge.

The induction takes the tail equality, prefixes it with the current cost,
and applies the current local equality before adding the tail budget. It uses
associativity without exchanging any two terms. No commutativity, inverse,
cancellation, order or positivity assumption is present. The noncommutative
word-consumption client is intended to expose accidental strengthening or
reordering, rather than treating commutative numerical examples as sufficient.

`run_potential` has the same local and global expression with `≤`. Its
requirements are AddMonoid, Preorder, AddLeftMono and AddRightMono. The proof
prefixes the tail inequality using left-monotone addition, suffixes the local
inequality using right-monotone addition, and composes inequalities. Neither
antisymmetry nor a linear order nor nonnegative costs/charges is used.

`run_cost_le_of_nonneg_final` adds only
`0 ≤ potential (run step is s).1`. This is nonnegativity of the actual final
state, not of all states and not of every amortized charge. It first proves
cost ≤ cost + finalPotential and then uses `run_potential`. Keeping this
premise is necessary for the planned cost1, potential0→−1 example: charge0
satisfies exact telescoping but does not bound cost1.

### Natural specialization

The explicit statements and argument order of `charge_iff_signed`,
`run_cost_le`, `run_zero_potential`, `budget_constant`, `budget_le_constant`,
`run_constant_charge` and `initial_potential_matters` are unchanged.
`run_cost_le` now specializes the generic cost corollary, discharging its
terminal premise with `Nat.zero_le`. The remaining Nat convenience proofs
and the RHS convention `k * is.length` are retained. No existing local-law
hypothesis, expected numerical value or algorithm implementation was weakened.

Existing uses to validate include BinaryCounter, SymmetricCosts,
Resources.RandomAccess.End and FIFOContracts, plus their example consumers.
The inventory found no explicit `@budget`/`@run_potential` use that exposes
the old implicit type-parameter list. The possible type-inference risk is
FIFOContracts.abstractBudget's unused `0` observation: after decoupling C/D,
the charge's Nat type no longer forces that observation to Nat. If Lean does
not default it, the sole permitted correction is `(0 : Nat)`.

### Signed savings and debt

The definitions require only the operations Add/Sub. All stated balance,
sign-conversion and telescope laws require AddCommGroup; no theorem asserts
that a natural truncated subtraction obeys these laws. There is no order
or positivity constraint on the signed identities.

The savings formula is exactly

    cost + potential(after) - potential(before).

`potentialCharge_balance` proves the required local equality by group
cancellation. `run_potentialCharge_exact` uses that equality in the shared
`run_potential_exact`; it has no separate trajectory induction.

The debt formula is exactly

    completeCost + debt(before) - debt(after).

`debtCharge_eq_potentialCharge_neg` identifies it with savings at negative
debt. `run_debtCharge_exact` applies the savings theorem at that negative
potential and rearranges the boundary terms, giving

    totalCost + initialDebt = finalDebt + totalDebtCharge.

Thus the sign differs from savings on the same increasing state potential.
The terminal debt remains explicit. API documentation says this is an identity
on the supplied observations and trajectory, not an actual persistent work
bound. It does not prove that persistent aliases share consumable credit,
identify complete cost with runtime, or establish payment before forcing.
Those source obligations remain owned by their algorithm/logical-work tasks.

## Connected-case development

The coordinator owns the signed numerical cases and the transport-client
author owns the lifted actual counter and noncommutative cases. The agreed
independent expectations were fixed before this core draft:

- Int: two cost1 steps, potentials0→3→0, charges4 then−2, total cost and
  charge2; also a prefix and nonzero initial-potential application.
- Negative terminal potential: cost1 and potential0→−1, charge0; exact
  telescope holds while the proposed cost-only inequality is false.
- Real: two cost1/2 steps, potentials0→3/2→0, charges2 then−1, total1.
- Debt: the same increasing debt produces complete+before−after, distinguished
  from the savings charge and connected through the public debt theorem.
- The actual BinaryCounter.incWithCost computation lifted through
  `Nat.castAddMonoidHom Real` retains the actual state and cost via
  `reweight_run`; its original local law supplies the generalized exact
  theorem. Four increments from empty retain cost7, final potential1 and
  budget8. `budget_map` and state congruence connect its budget to the old
  natural constant-budget law.
- FreeAddMonoid word consumption retains order through exact telescoping;
  an independent Nat-observation/word-charge budget exercises the decoupled
  codomains and actual intermediate states.

The missing connection at baseline is the polymorphic public API, rather
than an inability to prove the small numerical calculations by reduction.
No artificial failing numerical test or changed expected value was used.
These are agreed development cases, not a claim here that the final example
files have already passed their checks.

## Imports and validation status

Potential now directly imports `Mathlib.Algebra.Order.Group.Nat`, whose pinned
source supplies Nat's ordered-additive instance for the generic inequality's
old Nat clients. This retains the Nat additive definitions that the former
direct import supplied. Measured already imports the unbundled order basic
provider used by the generic monotonicity proof.

SignedPotential directly imports `Mathlib.Algebra.Group.Basic` for the group
identities used by its algebraic proofs. Neither core module imports Real,
logarithms, an arithmetic tactic umbrella or an optional cancellation/order
hierarchy. Generic telescoping is proved by association/monotonicity, with
the old Nat arithmetic proofs retained only in their existing wrappers.

At draft freeze, review is source-level only. This assignment has run no Lean
compiler, build, proof audit or candidate verifier. The coordinator must record
actual focused findings, their corrections, immutable-candidate validation,
and independent Standards/Spec outcomes in its retained loop. Full acceptance
and Chapter2/whole-book progress remain pending; this foundation alone accepts
no Chapter5 or Chapter6 algorithm or exercise.
