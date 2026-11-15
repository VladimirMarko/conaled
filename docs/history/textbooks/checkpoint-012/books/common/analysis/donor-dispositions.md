# Exact donor choices for the first cohesive union

Read-only follow-up to `preservation.md`, against pinned master
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. The complete bounded merge evidence
is in `donor-dispositions.json`:65 new FDSA Lean paths,36 existing-path variant
dispositions, five VFA drafts, observed imports, exact blob/commit identities,
and16 new companion research notes. No source files were edited.

## Receive the missing files once

Every one of the65 selected paths is absent from FDSA's candidate. The JSON
chooses an exact donor for every path and records whether any other candidate
or master already has that path. Keep existing domain placement for these
files; their carriers and namespaces are already domain-specific. The13 selected
donor refs cover the required leaf developments without copying entire old trees.
All observed project imports resolve in master + three candidates + selected
donors. This is source-text planning evidence; external imports and elaboration
still require the pinned compiler.

There are exactly two multiple-version decisions among the missing paths:

| Path | Choose | Why |
|---|---|---|
| `Applications/Probability/PermutationExpectation.lean` | `49d6d470`, blob `9124def903537fd47b71ccb23155eca8eb2fc403` | Earlier file's declarations are unchanged; the new version adds `beforeCount_relabel` and its explanatory scope. No alternate implementation is needed. |
| `Examples/MappedPotentialAccounting.lean` | `12cb14fc`, blob `1fb26b51e9f298bd1ba1d1a5fa2a425142f8d8d7` | Same intended claims with later focused-check elaboration corrections. Preserve earlier proof history in Git, not as another active module. |

## Existing paths that need capability merges

These four files cannot be resolved by taking one complete historical file:

1. **`Applications/Resources/Potential.lean`:** start from the PFDS generic
   same-carrier interface; receive FDSA XP01's mapped/invariant-aware interface
   from `12cb14fc`. Retain `budget_congr_state`, generalized `run_potential` and
   `run_potential_exact`, explicit final nonnegativity, and all SignedPotential
   clients. Add the mapped exact/bounded laws, invariant closure laws and
   `budget_amortized`; preserve separate raw/accounting carriers, noncommutative
   ordered observations and FDSA's weaker AddZero assumptions where valid.
   Keep old natural contracts as usable specializations. The mapped examples
   exercise real/fractional accounting, initial credit and ordered words.
2. **`Applications/Probability/PermutationOrder.lean`:** retain receiving-main
   `e61bb6f` prefix and its proof repairs. From `49d6d470`, add the joint-order
   and intersection-fiber suffix, its four private helpers and extra imports.
   Public additions: `uniformOn_restrictedOrder_pair_eq`,
   `map_restrictedOrder_pair_uniformOn`, `hasLaw_filter_pair`,
   `uniformOn_inter_restrictedOrder_eq`. This last donor contains the earlier
   joint-order extension. Its examples and PermutationPlacement depend on these
   additions. Check the draft's external import spelling with actual Mathlib.
3. **`Applications/Trees/Shape.lean`:** keep receiving-main prefix; append the
   `156ba817` node-balance extension and its two private helpers. Public additions:
   `height_node_eq_clog_of_numNodes_succ`,
   `minHeight_node_eq_log_of_numNodes_succ`,
   `almostComplete_node_of_numNodes_balance`. Braun relies on this bridge.
4. **`Applications/Trees/ShapeLog.lean`:** retain the receiving-main corrected
   Real/Nat casting proofs; append the `156ba817` intermediate source corollaries
   `height_node_eq_ceil_logb_of_numNodes_succ` and
   `minHeight_node_eq_floor_logb_of_numNodes_succ`. Their proof casts may need the
   same receiving corrections; keep the stated claims.

Two other existing paths require explicit treatment. In `FIFOContracts.lean`,
use XP01's `(0 : Nat)` annotation in `abstractBudget` when budget becomes generic.
In `Examples/FunctionalNotation.lean`, retain the receiving `Preorder` signature
of `all_interval_memberships`; the earlier bare LE/LT draft was not compiler
accepted. This difference is a declared signature repair, not described as a
proof-only change. Any future weaker interface must be checked against actual
Mathlib definitions and the intended source contract.

For the other29 paths, the inspected variants are superseded receiving proof,
import, notation or documentation corrections and stronger connected examples;
keep the receiving candidate. `SquareApplications.lean` is the36th path:
rebuild the union from pinned-master coverage plus every received theory/example,
instead of adopting one of39 historical import lists. This classification does
not replace exact candidate compilation or statement review.

## Integrate all five VFA drafts

The JSON records exact staged bytes, SHA256, imports, suggested theory/example
paths, namespace routing and semantic boundaries. The proposed destinations are:

| Draft | Theory owner | Connected cases |
|---|---|---|
| Sorting specifications | `Applications/Sorting/Specification.lean` | `Examples/SortingSpecification.lean` |
| Table observations | `Applications/Collections/TableObservations.lean` | `Examples/TableObservations.lean` |
| Positive keys | `Applications/Arithmetic/PositiveKeys.lean` | `Examples/PositiveKeys.lean` |
| Unary comparison | `Applications/Resources/UnaryComparison.lean` | `Examples/UnaryComparison.lean` |
| Queue peek | `Applications/Resources/QueuePeek.lean` | `Examples/QueuePeek.lean` |

These are routing suggestions, subordinate to the pinned architecture and root's
cohesive design. Replace staging namespaces consistently while preserving all
claims and cases. Tables need a checked connection with FDSA Collections and
PFDS ordered maps; sorting needs the direct existing KeySorted/StableSort seam.
Do not equate default lookup with presence, sorting correctness with stability,
or value equivalence with resource equivalence. The two cost models retain
their counterexamples, explicit tariffs and actual executor connections.

Native setup is now authorized by the user, but this report makes no compiler
claim. Root must establish the pre-edit snapshot before receiving source, then
perform focused checks, statement review, full applicable candidate/audit checks,
both independent review axes and durable saving at the required milestones.
