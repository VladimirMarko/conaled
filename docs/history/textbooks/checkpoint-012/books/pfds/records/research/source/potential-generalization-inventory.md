# Potential accounting: bounded generalization inventory

Prepared 2026-11-03 by `/root/potential_generalization_inventory` for root.
This is read-only architectural/mathematical preparation. No Lean theorem was
added or compiled; no implementation/review loop, ticket, candidate or chapter
was activated by this agent. Chapter 2 remains the earliest unaccepted chapter.
Only this report was written.

## Recommendation

Generalize the existing `Resources.budget`, `budget_append`, `run_potential`
and `run_potential_exact` in place, preserving their names, explicit argument
order, recursion/state trajectory and natural-number specializations. Keep the
existing Nat cost-only and constant-charge interfaces. Add signed charge
formulas in a small module importing that foundation, without a second executor
or a separate real-number potential framework.

The change is justified by the prepared book Chapter5 real logarithmic
potentials and Chapter6 opposite-sign debt potential, but this algebra alone
cannot prove either algorithm's local inequality or a persistent work bound.
An exact signed telescope and a source cost correspondence are different
mathematical obligations.

## Inspected source and standards

Main checkout was clean at
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. The relevant current interfaces and
call sites were also located in frozen body-counts candidate
`5e048f781aa04be9ce993f1e7455bdc82df22bff`; their source equality is recorded
below. Pinned Mathlib source was read at actual Git revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Read AGENTS; architecture, domain and glossary guidance; ADR0001/0010; shared
language direction; example-driven-development; README environment/acceptance
rules; and the existing adwh-potential-accounting implementation record.
The design preserves ordinary clients, separates operations/observations/laws,
and exposes only the algebra needed by each argument. No Felix parity claim
or new compiler/interpretation framework is proposed.

## Actual minimal algebra

The following are proposed signatures/requirements, not checked Lean text.
Use ordinary Mathlib structures rather than custom classes.

| Construction | Sufficient standard assumptions | Reason |
| --- | --- | --- |
| `budget step charge` | Step observation type C arbitrary; charge type D with `Zero D`, `Add D` | Recursion observes only `(step i s).1`, and combines charges in execution order. It never reads or adds the step's second field. |
| `budget_append` with `(run step is s).1` | `Zero C`, `Add C`, `AddMonoid D` | `run` needs zero/add on C; only its state projection is used. Associativity/zero for D rebrackets the charge word. C does not need associativity for this state-only theorem. |
| `run_potential_exact` | `AddMonoid C` | Exact telescoping needs association and identities only. No commutativity, cancellation, subtraction, positivity or order is used. |
| `run_potential` | `AddMonoid C`, `Preorder C`, `AddLeftMono C`, `AddRightMono C` | The inductive tail inequality is prefixed by the current cost; the current local inequality is suffixed by the tail budget. Transitivity joins them. |
| Generic cost-only corollary | Previous ordered assumptions plus `0 ≤ potential(finalState)` | The final potential may be dropped only under this additional premise. Nonnegativity at every possible state is stronger than necessary. |
| Conventional signed charge | `AddCommGroup C` | The intended formula `cost + after - before` places the inverse at the right; commutativity justifies its equality with the balance form. The telescope itself does not acquire this stronger assumption. |

For exact telescoping, let c be current cost, t the current next state, R the
rest's cost and B its charge budget. The induction is just

    (c + R) + Phi(final)
      = c + (R + Phi(final))
      = c + (Phi(t) + B)
      = (c + Phi(t)) + B
      = (Phi(start) + currentCharge) + B
      = Phi(start) + (currentCharge + B).

No terms are commuted. The inequality proof uses the same associations and
two monotonicity steps in the same positions. This explains why requiring an
ordered commutative ring or even an additive group in the generic foundation
would be unnecessarily restrictive.

`IsOrderedAddMonoid` is a convenient stronger Mathlib interface but its current
pinned definition requires `AddCommMonoid`. The granular `AddLeftMono` and
`AddRightMono` assumptions retain the valid noncommutative generality already
present in `Measured` and `Workload`. Standard Nat, Int and Real instances can
supply them; their concrete instance providers must be imported explicitly.
Do not replace the algebra with untyped Boolean comparisons or a new bespoke
order record.

## Preserve the natural-number API

Keep the existing Nat statements of:

- `charge_iff_signed` (the current explicit Nat inequality/Int subtraction bridge);
- `run_cost_le` and `run_zero_potential`;
- `budget_constant`, `budget_le_constant`, `run_constant_charge`;
- `initial_potential_matters`.

Their proofs may consume the generalized core. In particular, keep the old
constant-budget right-hand side `k * is.length`; changing it to
`is.length • k` without a Nat facade would break the existing simp uses.
If a generic nsmul constant law is useful for the new Real client, expose it
separately and recover the old Nat theorem through `Nat.nsmul_eq_mul` and the
necessary multiplication orientation. Do not add generic constant lemmas merely
for a declaration quota when the actual new cases do not need them.

The intended compatibility is unchanged Nat specializations and ordinary call
sites, not the claim that a newly polymorphic declaration has the identical
fully explicit Pi type as the old monomorphic declaration. Source inspection
found no `@budget`, `@run_potential` or analogous explicit-implicit applications
in the current callers. External uninspected clients are not certified by this
inventory. Keep all newly generalized type/universe parameters implicit so
existing positional arguments continue to mean the same things.

A concrete inference boundary is `FIFOContracts.abstractBudget`:

    budget (fun c xs => (step (lists alpha) c xs, 0)) profile

Previously `budget` forced the dummy cost to Nat. With independent C and D,
that zero's cost type has no connection to the already-Nat profile. Lean may
resolve its numeral default, but this has not been compiled here. If necessary,
annotating only that zero as `(0 : Nat)` preserves the exact existing public
API and semantics. Do not constrain every generic caller's charge and cost
codomains to be equal just to resolve this local dummy observation.

The later `abstractBudget_append` constructs an explicitly typed
`Instrumentation`, whose cost is already Nat, so its type source is stronger.
Counter and random-access clients also use explicitly Nat measured operations;
symmetric operations return Nat in their signatures. All their public results
and independently justified expected values should remain unchanged.

## Existing affected clients and meaningful validation scope

| Existing client | Connection that must survive |
| --- | --- |
| `Applications/Resources/BinaryCounter.lean` | `totalCost` remains the same trajectory budget; zero/successor equations reduce as before; `counter_potential` applies `run_potential_exact` then `budget_constant`. |
| `Applications/Resources/SymmetricCosts.lean` | `run_charge_potential` and `run_work_potential` retain constants2/8 and distinct source-charge/structural-work observations. |
| `Applications/Resources/RandomAccess/End.lean` | `pushManyRun_potential` applies the exact telescope to `consRARun`; it retains both boundary one-bit potentials. |
| `Applications/Resources/FIFOContracts.lean` | Existential accounting witness, same abstract budget, append composition and public client bound; no potential exposed to ordinary FIFO callers. |
| `Examples/PotentialAccounting.lean` | Binary4-increment cost7, ordered resource word, initial-potential counterexample, bounded Fin3 profile, symmetric exact costs and mixed workload. |
| `Examples/FIFOContracts.lean` | Public ordinary/sequential/rescaled bounds and the retained persistent-branch counterexample. |
| `Examples/RandomAccessEndCosts.lean` | Constructs4 elements with measured cost7 through the public potential result; retains drain/setup/end-operation contracts. |

These are source-inspected validation targets, not new successful checks.
A focused run can cover the new client plus these principal old clients and
any directly affected declaration modules. The ordinary exact-candidate full
build/audit remains the required final integration check. No gate or optional
runtime test was run by this investigation.

`Resources.run`, `Measured.bind`, `run_append`, `run_state`, `reweight_run`,
`run_invariant` and `run_value_fusion` should remain unchanged. Their existing
value/state and ordered observation laws already provide the execution layer.
A new `RealRun`, `SignedRun` or independent recursive state executor would
repeat that layer without justification.

## Signed and debt formulas

For a step whose modeled cost is c and a potential Phi, define the conventional
signed charge by

    q = c + Phi(after) - Phi(before).

Its local balance and the generic exact telescope yield

    totalCost + Phi(final) = Phi(initial) + trajectoryBudget(q).

Individual charges may be negative. This does not make the actual step's
modeled work negative. Neither nonnegative actual costs nor nonnegative charges
is needed for the equality; cost-model interpretation is supplied by the client.

For a debt potential Psi, the opposite-sign charge is

    a = c + Psi(before) - Psi(after).

It is the same conventional construction at potential `-Psi`. The resulting
exact identity can be written

    totalCost + Psi(initial) = Psi(final) + trajectoryBudget(a).

This is a complete-cost/debt algebra identity when the caller gives c that
meaning. It is NOT a bound on the actual time of an arbitrary persistent
computation. Dropping the standard final potential at `-Psi` would require
`0 ≤ -Psi(final)`, which usually fails for a positive outstanding debt. The
source's logical histories, work allocation, unrealized work, query payments,
sharing, inheritance and pay-before-force obligations remain separate.

Use a small `SignedPotential` module importing the generic foundation for
these formulas and exact identities. A generic final-nonnegative cost corollary
belongs with the ordered foundation because it needs no subtraction/group.
There is no need to make the generic telescope import Real analysis or logs.
The future splay access lemma still has to establish its own logarithmic local
bound; the signed identity by itself merely accounts for a chosen potential.

## Transport through the same run

The existing `Resources.reweight_run` already proves that an additive
observation map commutes with execution. Use it for Nat→Int or Nat→Real
modeled-cost transport. Retain the full state/result equality, not just a
numerical cast asserted after the fact.

Two small budget consequences are useful if required by the selected client:

1. An additive charge map h commutes with `budget`:
   mapping every charge yields h of the original trajectory budget.
2. Changing only the step's cost observation leaves its budget trajectory
   unchanged. This can be expressed by equality of step state projections or
   by a direct reweighting specialization.

The second fact does not require h to be additive: the budget ignores the cost
field. By contrast, transporting the cost accumulation with `reweight_run`
does require additivity. Keep these two requirements distinct. Monotonicity is
also separate when transporting an inequality; an additive map alone need not
preserve order. No new global additive structure on supports/sets is relevant.

A single general state-projection congruence for budget may cover all needed
reweighting cases. Do not introduce multiple parallel recursors to prove the
same invariance. An invariant-restricted telescope can be added if a real
client requires it; the currently inspected Nat callers have their needed
local laws on all stated states or use the existing valid-state subtype.
Nothing in this investigation requires adding that optional interface now.

## Source-inspected Mathlib providers

| Provider at the pinned revision | Relevant content |
| --- | --- |
| `Mathlib.Algebra.Order.Monoid.Unbundled.Defs` | `AddLeftMono` and `AddRightMono` are covariance abbreviations for monotone addition on the corresponding side. |
| `Mathlib.Algebra.Order.Monoid.Unbundled.Basic` | Generic monotonic-addition lemmas (generated by to_additive); already explicitly imported by local `Measured.lean`. |
| `Mathlib.Algebra.Order.Monoid.Defs` | `IsOrderedAddMonoid` requires AddCommMonoid and supplies the granular covariance instances. |
| `Mathlib.Algebra.Order.Group.Nat` | `Nat.instIsOrderedAddMonoid` and `Nat.instIsOrderedCancelAddMonoid`; use the actual ordered provider when instantiating new generic inequalities at Nat. |
| `Mathlib.Algebra.Group.Nat.Defs` | Existing additive monoid/cancellation instances and `Nat.nsmul_eq_mul`; this file alone is not the ordered instance provider. |
| `Mathlib.Algebra.Group.Basic` | Ordinary group arithmetic and additive forms of cancellation/negation identities; appropriate proof support for conventional signed balances. |
| `Mathlib.Data.Nat.Cast.Basic` | `Nat.castAddMonoidHom (alpha)` for AddMonoidWithOne alpha. |
| `Mathlib.Data.Int.Cast.Lemmas` | `Int.castAddHom (alpha)` for AddGroupWithOne alpha. |
| `Mathlib.Data.Nat.Cast.Order.Basic` / `.Ring` | Order compatibility and nonnegativity of Nat casts under their actual ordered target assumptions; `.Ring` supplies the familiar `Nat.cast_nonneg`. |
| `Mathlib.Data.Real.Basic` | Real specialization input; retain it in the Real client rather than making the generic potential foundation import analysis. |

This is a declaration/provider inventory, not a newly validated minimal import
closure. A preliminary regex traversal was rejected: import statements inside
tactic documentation examples falsely appeared as actual imports. No conclusion
about available instances was drawn from that traversal. Current module-system
visibility and all required instance synthesis must be checked by the real
focused build. Add direct providers for used instances; do not rely on a broad
incidental tactic import or silently remove an old import's effects.

## Proposed connected cases

These expected calculations are mathematical design inputs, not Lean checks.
Connect them to the public generalized statements with their premises proved.

| Case | Independent expected result and point of the connection |
| --- | --- |
| Int potential0→3→0; each step cost1 | Signed charges4 and-2; total actual modeled cost2 equals total charge2 with zero endpoint potentials. Retains a negative amortized step without truncation. |
| Int potential0→-1; cost1 | Signed charge0, exact balance still true, but actual cost1 is not bounded by charge0. This rejects dropping a negative final potential. |
| Real fractional costs/potentials | For example costs1/2, potential0→3/2→0, charges2 and-1, total1. Demonstrates the same group theorem beyond integer token counts. |
| Actual BinaryCounter.incWithCost cast to Real | Apply the new generic telescope to the same cost-erased state transition with `Nat.castAddMonoidHom`; four zero-start increments retain7 writes and final one-bit potential1, so7+1=8. Prove local law/cast transport from the existing counter theorem; do not use a disconnected arithmetic equality as the whole client. |
| Noncommutative charge word with independent Nat step cost | Two charges observed at successive states produce an ordered word such as[0,1]. Use budget append/state-trajectory laws; this protects order and the separation between C and D. |
| Ordered exact potential consumption, if exposing noncommutative exact scope | A step emits the first symbol of a remaining word and retains its tail, with zero new charge. Two steps from[1,2,3] emit[1,2] and leave potential[3]; emitted word plus remaining word is the initial word. This can exercise the AddMonoid-only telescope without commutativity. |
| Existing Nat initial-credit and persistent-branch cases | Preserve both exactly. Generalizing scalar algebra does not authorize spending one saved potential once on each branch while charging it once globally. |

Only add cases needed to establish the chosen scope and expose consequential
premises. They do not replace the universal algebra proofs, source claim review,
or whole-candidate gates. The existing Mathlib/project proof policies remain
unchanged: no admissions, extra axioms, native proof shortcuts, increased proof
budgets, linter suppressions or gate changes are suggested.

## Remaining root decisions

Root must choose the bounded requirement/version and real starting candidate
before edits, preserve all outstanding predecessor acceptance work, and decide
whether a generic nsmul or invariant-restricted corollary is actually needed by
the selected clients. The source Book5/6 algorithms and full persistent source
cost bridge remain outside this algebra foundation. No current chapter or
coverage row is closed by this inventory.

## Current input identities

All following source bytes were equal between main76d77a1 and body-counts5e048f7
at inspection; this comparison is not compiler validation.

| Relative source | SHA256 |
| --- | --- |
| Applications/Resources/Potential.lean | `680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe` |
| Applications/Resources/Workload.lean | `5db2ef8f7a504b33b4dfbb26ed39de1a194fa59568ba16702f3ba2359b46b4f5` |
| Applications/Resources/Measured.lean | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| Applications/Resources/BinaryCounter.lean | `d990e0e8d9b09fff3f774180fa2396558f2d1abcf7e6231be648f5bd66f6f9c0` |
| Applications/Resources/SymmetricCosts.lean | `2e78ce2ac33ec06e9144988a6541a01bee276ba4035b16d4633b0e870daab6d5` |
| Applications/Resources/RandomAccess/End.lean | `ded4129df132c7fd87a40899cea6f483db02f3f95332bd9ec7c8c57dd868f099` |
| Applications/Resources/FIFOContracts.lean | `dff2940bacabe6b759b4ff1f6ebe361282fb0777192bafbb05911f9c13b6ecbb` |
| Examples/PotentialAccounting.lean | `ee3fbee1b7e8be75226ac912e3cbb2b82c322d843b3231bdb6ac94908c7b1871` |
| Examples/FIFOContracts.lean | `de9e455109ecb5cca0f5e30b7dc993f81149ab7a6145750cc2b62bcb9f83831b` |
| Examples/RandomAccessEndCosts.lean | `ea68d8773ae7fea32d43e9b0eb01d3ca9111a0d41eac28079adafa5a719fa600` |
