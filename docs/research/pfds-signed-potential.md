# Potential accounting over signed and ordered observations

The resource executor and trajectory budget support both the natural-number
accounting used by existing applications and the signed/real potentials needed
by Okasaki's classical and lazy analyses. `Resources.run` remains the executor;
`budget` follows its same sequence of states while accumulating independently
typed charges.

## Shared algebra

`run_potential_exact` keeps the balance

    runCost + potential(final) = potential(initial) + budget.

Its local premise has the corresponding one-step equality. An additive monoid
suffices: the proof re-associates terms without commuting them. The ordered
`run_potential` uses a preorder and monotone addition on both sides. These laws
require neither a total order nor subtraction.

`run_cost_le_of_nonneg_final` discards the final potential only under its stated
nonnegativity premise. In Nat this premise is automatic, and the established
Nat cost-only, zero-initial and constant-charge interfaces keep their existing
meaning. For Int or Real, a negative final potential cannot be dropped.

The budget observes the state projection of a step. `budget_congr_state`
therefore transports it through any state-preserving change of observation;
no additivity assumption is needed merely to retain the trajectory.
`budget_map` transports accumulated charges through an additive homomorphism.
The existing `reweight_run` separately transports a run's accumulated work and
retains its state. Additivity does not by itself establish order preservation.

## Signed formulas

`potentialCharge` in an additive commutative group is

    cost + potential(after) - potential(before).

`potentialCharge_balance` connects this signed expression to the local balance,
and `run_potentialCharge_exact` applies the shared telescope. Individual charges
can be negative even when the modeled actual costs and state potentials are
nonnegative. No truncated natural subtraction is substituted for the change.

`debtCharge` reverses the potential change:

    completeCost + debt(before) - debt(after).

It agrees with the savings expression at negative debt potential. Its public
exact identity is

    completeRunCost + debt(initial) = debt(final) + debtBudget.

This equality alone establishes no bound on actual realized work in a
persistent computation. A positive remaining debt corresponds to a negative
savings potential, whose final term cannot simply be discarded. Source debt
analyses additionally need logical work allocation, valid potential/payment
coupling, query charges, sharing and payment before forcing. The remaining
operational connection is described in [persistent accounting](pfds-persistent-accounting.md).

The generic core imports neither Real analysis nor logarithms. Real clients
instantiate ordinary algebraic structures; the later splay access inequality
and algorithm-specific amortized bounds remain separate obligations.

## Connected applications and boundaries

`Examples.SignedPotential` uses a two-step Int computation with costs 1, 1 and
potentials 0, 3, 0. Its charges 4, -2 total 2, and its release-only suffix exposes
the initial-potential boundary. A separate cost 1 step ending at potential -1
has charge 0 and refutes discarding a negative final term. The Real
specialization uses costs 1/2 and potentials 0, 3/2, 0, producing charges 2, -1
and total 1.

The debt example increases potential from 0 to 1/4 with complete cost 1/2. Its
savings charge is 3/4 and its debt charge 1/4. The exact debt identity retains
the outstanding 1/4; it does not assert that all complete work has already occurred
or that a persistent client can spend a retained alias's potential once globally.

`Examples.PotentialTransport` applies the generic laws to the existing measured
binary increment through the ordinary Nat-to-Real additive map. It retains the
same final bits and cast write count, including the four-increment balance
7 + 1 = 8. An ordered-word application exercises the exact noncommutative telescope
and a charge word with an independently typed Nat step observation.

The original binary-counter, symmetric-deque, random-access end and FIFO
contract clients remain the natural-number applications. Their retained
initial-potential and persistent-branch examples still delimit the same
mathematics. This extension is common algebra for book Chapters 5/6 and thesis
Chapter 3, not completion of any algorithm, exercise or source runtime proof.
