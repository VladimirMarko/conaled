# Local 10023 — shared potential accounting with signed and real charges

Version 1, 2026-11-03. Governing requests: REQUEST.md and REQUEST-union-v2.md.
This bounded algebraic foundation uses the user's permission for necessary
cross-cutting work. Chapter2 remains earliest unaccepted; Chapter3 algorithms
have not begun. No Chapter5/6 algorithm, exercise or complexity contract is
accepted by this task.

## Motivation and baseline

The existing Resources.Potential API uses Nat for measured cost, potential and
amortized charge. Book Chapter5 uses real potentials, including logarithmic
splay potential, and a signed change in potential. Book Chapter6 and thesis
Chapter3 use the opposite sign for accumulated debt. Natural truncation is not
the stated mathematics. A signed amortized step may be negative even when its
actual cost and the state potential are nonnegative.

Source preparation is in research/chapter05-readiness.md and the three
chapter06-*-readiness.md reports. Exact manuscript identities are retained in
research/union-source-identities.json. Relevant book pages are39–41,49–51,
68–70; thesis13–15,28–29. The generic algebra is a common prerequisite; source
algorithm work/debit correspondence remains with10017 and its chapter owners.

Starting bounded and original integration base:
5e048f781aa04be9ce993f1e7455bdc82df22bff. This includes the unaccepted prior
foundation candidates; it does not confer their approval. Record the clean
isolated development branch/materialization and all inclusions before editing.
No pre-existing task change or unrelated exclusion is intended. Retain this
base through ordinary fixes, carrying all findings if later integration changes
it under the repository's shared procedure. Main and all active compiler input
closures remain unchanged. Root owns Git, compiler and candidate operations.

## Existing API and minimal generalization

Reuse Resources.Measured, Resources.run and the existing budget function.
Do not create a second executor, parallel potential hierarchy or a record whose
fields simply assume the intended whole-run inequality. Generalize existing
lemmas where their current Nat uses specialize without changing meaning.

The budget must sum the chosen charge along the same actual sequence of states.
Its charge codomain may differ from the step's observation codomain because
only the first projection chooses the next state. Keep empty, cons and append
behavior and existing explicit argument order compatible. Use only the zero,
addition and associativity/order assumptions needed for each claim.

Generalize exact local telescoping so that

    cost(step i s) + Phi(next) = Phi(s) + charge(i,s)

implies the same exact identity over run and its trajectory-dependent budget.
Associativity and an additive identity suffice for this exact algebra; neither
commutativity nor cancellation nor an order should be imposed without need.

Generalize the inequality telescope over an additive monoid with a preorder
and left/right monotone addition. Preserve both initial and final potential.
In a domain admitting negative values, dropping the final potential requires
its actual nonnegativity at the final state. State that premise explicitly;
do not add unnecessary global positivity or linearity requirements to the
local/exact claims. Existing Nat run_cost_le, run_zero_potential, constant-charge
corollaries and charge_iff_signed must retain their meanings and usable call
interfaces. Small explicit type annotations in otherwise ambiguous old clients
are permitted if needed; no claim or algorithm behavior may be changed.

Provide the small transport/composition facts needed to apply the same laws
after an ordinary additive observation map. Reuse reweight_run for execution.
If budget map or state-preserving-step facts are needed, prove them for this
same budget rather than reconstructing the trajectory. Do not introduce a
broad transport framework solely for this task.

## Signed savings and debt formulas

Over an additive commutative group, define or expose the actual signed charge

    savingsCharge = cost + Phi(after) - Phi(before).

Connect it through the generalized exact telescope, obtaining the exact
whole-run accounting identity. Also expose the opposite-sign debt expression

    debtCharge = completeCost + Psi(before) - Psi(after).

Its exact identity has the corresponding sign and boundary terms. Reuse the
shared algebra (for example through negative potential) rather than duplicating
another run proof. No truncated natural subtraction is substituted for either
formula. Int and Real must both be supported by the same general construction.

The debt identity is only an algebraic identity along an actual given state
trajectory. It is NOT a proof that arbitrary persistent aliases share one
consumable potential, that a complete-cost observation equals runtime, that
payment precedes forcing, or that potential bounds actual suspended debt.
The full source method still needs valid logical work allocation, potential/
payment coupling, argument/result incidence, query charges and work/forcing
correspondence. Make that limitation explicit in API documentation.

Likewise this task proves no splay access lemma, logarithmic data-structure
bound or Chapter5/6 algorithm. Real values are needed to state those later
arguments faithfully; their algorithm-specific inequalities remain open.

## Connected cases with independent expectations

Develop the general claims and checked uses together. Preserve the following
mathematical expectations through proof repairs, connect them through public
lemmas, and prove their actual hypotheses. The same case may exercise several
helpers; no theorem-count quota applies.

1. Int savings with cost1 at each of two steps and potentials0→3→0. The signed
   charges are4 then−2; actual total and total amortized charge are both2.
   Retain a prefix/nonzero-initial-potential use, so the boundary is visible.
2. A final-potential counterexample: one step has cost1 and potential0→−1,
   giving signed charge0. The exact telescope holds, but the claimed cost≤budget
   conclusion fails. This establishes why the nonnegative-terminal premise
   cannot silently disappear outside Nat.
3. A Real specialization with genuine fractional cost or potential, including
   an exact run/budget connection. It must not just restate an integer example
   with Real notation. Check the negative-change/sign convention as relevant.
4. A debt-sign case distinguishing complete+before−after from the savings
   expression on the same state change. Exercise the public debt identity;
   retain the distinction from an unproved persistent actual-cost bound.
5. Lift the existing actual BinaryCounter.incWithCost program to Real (or a
   similarly discriminating existing cost client) using an additive observation
   map. Apply the generalized public theorem and preserve its final state and
   cost observation through reweight_run. This must reuse the original measured
   algorithm, not define an unrelated pair with the desired total.
6. Retain the existing Nat clients: BinaryCounter, SymmetricCosts,
   RandomAccess.End and FIFOContracts, with their relevant existing example
   consumers. Validate the concrete affected closure. Any necessary annotation
   must only resolve a type, with no change of mathematics or runtime behavior.

Use ordinary kernel-checked proofs. A numerical reduction that bypasses the
new public theorem does not by itself exercise that theorem. Preserve an
independent expected value or inequality and the bridge to the public API.

## Statement review and completion

Review quantifier order, universe/typeclass requirements, order directions,
noncommutative exact addition order, initial/final terms, signed subtraction,
state-trajectory identity, natural specialization and observation transport.
Check satisfiable cases and the explicit counterexample to dropping negative
final potential. Keep operations, observations and laws separate. Imports
should name necessary providers without broad tactic imports or suppression.

Integrate new core source and connected clients in normal public/audit coverage.
Keep stable API guidance in the repository and workflow/validation records in
session. No new axiom, admission, native/unsafe proof shortcut, proof-budget
increase, linter suppression or weakened gate is permitted.

Root runs at most one full gate plus one focused wrapper with frozen inputs.
Preserve each failed focused round, exact source/input identity and genuine
correction. Focused evidence alone is not acceptance. Capture a clean isolated
immutable candidate, run its own pinned-Nix stock full check and exhaustive
audit, retain its matching verification record, obtain independent Standards
and Spec outcomes on the complete fixed-base scope in one retained loop, and
run final stock verify-candidate immediately before accepting identical bytes.
Preserve all work, local tickets and evidence in immediately uploaded/exposed
recovery checkpoints. Earlier candidate gates and chapter order remain binding.
