# Cohesive Potential API reconciliation

Read-only design, 2026-11-13. No source changes or compiler claims. Governing
master: `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`; PFDS candidate:
`3cf3de4fbc24c1a144353ae64b13b72f5ead54a5`; FDSA-XP01 donor:
`12cb14fc98b8617b3b625620da8e60936daba340`, retained at
`refs/checkpoint/fdsa/heads/work/fdsa-potential-development`.

The user's current clarification permits a native environment while keeping the
master's Lean/dependency pins. Implementation still waits for the coordinator's
actual review baseline. This plan changes no acceptance or source identity.

## Decision

Use one `Applications/Resources/Potential.lean` owner. Neither incoming branch
subsumes the other. Retain the union of their mathematical contracts and derive
convenient specializations from the most general mapped, invariant-aware core.
Keep `Applications/Resources/SignedPotential.lean` as the named savings/debt layer.
No new executor, observation type, syntax or global cost class is needed.

FDSA XP01 is based on an older FDSA source tree. Its diff against the latest FDSA
candidate contains many apparent deletions that are merely absent later work.
Integrate its selected Potential/example/provenance changes; do not copy that
whole tree over the current FDSA candidate.

## Public contract union

| Declaration | Chosen contract and owner of evidence |
|---|---|
| `budget` | Both donors agree: raw observation `C` is unconstrained; independent charge carrier `D` needs only `Zero` and `Add`. Preserve four explicit arguments and actual-state recursion. |
| `budget_append` | Both donors agree: `Zero C`, `Add C` only to name the state projection of `run`; `AddMonoid D` for charges. Preserve explicit arguments. |
| `budget_map` | Use XP01's strictly weaker requirements: `AddZero D`, `AddZero E`, homomorphism `D →+ E`; no algebra on raw `C`. Preserve name and argument order shared by both versions. |
| `budget_congr_state` | Retain PFDS verbatim: `Zero D`, `Add D`; raw carriers `C` and `E` have no algebra. Equality of every local next state gives budget equality. |
| `run_potential_map_exact_of_invariant` | XP01 core: `AddZero C`, `AddMonoid D`; explicit hom `C →+ D`, validity predicate, closure, local equality on valid states, valid initial state. |
| `run_potential_map_of_invariant` | XP01 core: previous structure plus `Preorder D`, `AddLeftMono D`, `AddRightMono D`; explicit valid-state local inequality. |
| `run_potential_map_exact`, `run_potential_map` | Preserve XP01 wrappers using the invariant `True`. |
| `run_cost_le_map_of_invariant` | Preserve XP01 wrapper with nonnegativity on the preserved valid domain. It retains the initial potential. |
| `run_potential_exact` | Preserve PFDS generic public statement over `AddMonoid C`; derive from `run_potential_map_exact` with `AddMonoidHom.id C`. Nat becomes its checked specialization. |
| `run_potential` | Preserve PFDS generic public statement over `AddMonoid C`, `Preorder C`, `AddLeftMono C`, `AddRightMono C`; derive from mapped inequality with identity hom. |
| `run_cost_le_of_nonneg_final` | Preserve PFDS contract requiring nonnegativity only at the actual final state. This is weaker than demanding nonnegativity everywhere, and is not replaced by XP01's invariant-domain convenience theorem. |
| `budget_amortized` | Retain XP01 signed formula over raw `AddZero C` and accounting `AddCommGroup D`; derive from the mapped exact boundary theorem as in donor. |
| Existing Nat APIs | Retain `charge_iff_signed`, `run_cost_le`, `run_zero_potential`, `budget_constant`, `budget_le_constant`, `run_constant_charge`, `initial_potential_matters` and their existing explicit arguments. |
| Named signed APIs | Retain PFDS `potentialCharge`, `potentialCharge_balance`, `run_potentialCharge_exact`, `debtCharge`, `debtCharge_eq_potentialCharge_neg`, `run_debtCharge_exact`. Their generic same-carrier use now reaches the same mapped core through the identity-hom wrapper. |

The core must not assume commutativity, cancellation or linear order for an exact
boundary theorem. The inequality theorem needs monotone addition on both sides.
Raw work needs no associativity: `run` has its actual right-associated result,
and the additive hom maps that result. The hom need not be monotone because the
local premise already compares mapped work. Signed subtraction belongs only to
the commutative-group layer.

## Exact proof organization

Keep the XP01 mapped invariant proof pair as the fundamental inductions, using
`run_cons`, `map_add`, invariant closure and target associativity. Its explicit
`AddLeftMono.elim` and `AddRightMono.elim` avoid ambiguity about which side of
addition is monotone.

Derive the global mapped pair by `P := fun _ => True`. Then replace the duplicate
PFDS same-carrier inductions with identity-hom applications. This retains public
generality while making the two developments literally share one proof.

Retain PFDS's final-state-only bound using the generic same-carrier telescope;
derive the Nat cost-only bound by `Nat.zero_le`. XP01's invariant-domain bound
uses `run_invariant` to discharge final nonnegativity. These are related useful
views, not redundant assumptions to collapse.

The two signed presentations already factor through the exact telescope.
If an explicit public presentation bridge proves useful, add in SignedPotential
a theorem identifying `budget step (potentialCharge step potential)` with
`run-cost + final-potential - initial-potential`, as the identity-hom instance
of `budget_amortized`. Do not introduce a dependency from Potential back into
SignedPotential or duplicate the generic mapped signed theorem. Existing named
signed clients need no rewrite to consume the shared core.

## Required compatibility annotation

XP01 changes `Applications/Resources/FIFOContracts.lean`:

```lean
def abstractBudget (profile : Command α → List α → Nat) :=
  budget (fun c xs => (step (lists α) c xs, (0 : Nat))) profile
```

The charge carrier no longer determines the step's unused raw observation type.
The annotation fixes that formerly implicit Nat. This is an elaboration bridge,
not a new cost model, trajectory or stronger hypothesis.

## Files and validation consumers

Source edits expected:

1. `Applications/Resources/Potential.lean`: union and proof factoring above.
2. `Applications/Resources/FIFOContracts.lean`: explicit Nat annotation.
3. `Applications/Resources/SignedPotential.lean`: retain incoming code; optional
   named presentation bridge only if it supports a useful connected client.
4. `Examples/MappedPotentialAccounting.lean`: preserve XP01 donor.
5. `Examples/PotentialTransport.lean` and `Examples/SignedPotential.lean`:
   preserve PFDS donors.
6. Public `SquareApplications.lean`: coordinator adds the three example imports
   alongside all other retained integration imports.
7. `docs/research/fdsa-potential-accounting.md`: retain source correspondence;
   update its description of the formerly Nat-only public wrappers to explain
   generic wrappers with unchanged Nat specialization. Preserve original draft
   status until the exact integrated gates pass. A short shared integration note
   can link both sources without duplicating their evidence.

Current master Nat consumers found by exact-pin source search:
`Resources/BinaryCounter`, `DynamicFrontArrayCosts`, `FIFOContracts`,
`FoldedPrune`, `GuardedBuild`, `PricedPrune`, `RandomAccess/End`,
`SymmetricCosts`; `Examples/FIFOContracts`, `Examples/PotentialAccounting`.
These must continue to compile and remain in the normal public audit closure.
No planned edits to these consumers other than FIFO's type annotation.

The donor examples already provide discriminating mathematics:

- XP01: mapped real counter for arbitrary initial bits; negative initial-credit
  charges; actual-state-dependent budgets; fractional accounting valid only on
  states 0/1 with an explicit invalid-state counterexample; ordered noncommutative
  observations.
- PFDS PotentialTransport: reweighted real execution connected to the original
  counter, explicit state/budget mapping, ordered-word balance and independent
  charge carrier.
- PFDS SignedPotential: negative intermediate charges, a negative-final-potential
  counterexample, real fractional savings, and opposite-sign debt with outstanding
  terminal debt retained.

Use those existing public clients first. A cross-route counter agreement theorem
may compare the XP01 mapped observation with PFDS's `realRun_transport`, including
both the actual final counter state and mapped work. Do not replace a missing
arbitrary-input proof by the four-increment example.

Focused compilation covers the changed owner and these client families before
the required full candidate build/audit, independent Standards/Spec review, and
immediate candidate verification. Preserve original findings and unaccepted
source scopes; successful arithmetic examples do not close whole-book coverage,
persistent sharing costs, suspension forcing correspondence, or binary-input
potential accounting.
