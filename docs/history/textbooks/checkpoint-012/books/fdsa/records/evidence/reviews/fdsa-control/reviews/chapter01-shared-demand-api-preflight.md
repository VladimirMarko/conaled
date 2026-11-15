# Chapter 1 SharedDemand: bounded API preflight

Recorded 2026-11-02. This is a read-only elaboration-risk preflight, not an
additional Standards/Spec review, compiler result or acceptance result.
The separate contributor `/root/tail_examples_preflight` inspected the
coordinator-provided repair candidate
`a14977b9e316cc484ffad8a470d26b15615956c0` in
`conaled-ch01-cost-models` without changing any file or ref.

## Scope and result

After reading the applicable AGENTS, README environment/build instructions,
implementation-loop guidance and example-driven guidance, the contributor
read `Applications/Resources/SharedDemand.lean` and
`Examples/SharedDemand.lean` against their existing resource dependencies and
pinned library sources. It identified no concrete likely elaboration mismatch
or uncovered dependency in this bounded scope.

The coordinator records the unchanged source identities from the immutable
candidate handoff:

| File | SHA-256 |
| --- | --- |
| `Applications/Resources/SharedDemand.lean` | `c9740655b7afb51b28b044f1a72006d7a393b74a3e60e2f26464dc7eca7ee996` |
| `Examples/SharedDemand.lean` | `73f4cfc1c3a8ee5bddd37ec4bc1937d66dd08f6eae4e35a25849e860b42a10d2` |

These identities are coordinator provenance; the contributor did not run a
Git command or independently certify the worktree identity.

## Interfaces inspected

- `Measured α C` is the ordinary product `α × C`. The cache, request result,
  projected step and arbitrary-payload example fit its universe parameters.
  `run_invariant` and `run_potential_exact` also quantify their identity and
  state types over independent universes; no apparent `Type 0` restriction
  was found.
- `run_invariant` takes the step, state predicate, transition closure proof,
  request list, initial state and initial predicate proof. Both
  `run_preserves_cached` and `run_valid` supply that order. The returned-value
  argument uses `request_valid` with the stored-value fact from
  `request_stores` in the required equality direction.
- `run_potential_exact` requires cost plus final potential to equal initial
  potential plus charge. `step_potential` supplies this with zero charge;
  `Nat.add_zero` reconciles the local statement. The final simplification
  through `budget_constant`, `Nat.zero_mul` and `Nat.add_zero` agrees with
  the existing global theorem.
- `Function.update_of_ne` requires the queried identity to differ from the
  updated identity. The `j ≠ i` arguments in cache preservation, validity
  and remaining-work proofs have that orientation.
- The additive declaration generated from `Finset.mul_prod_erase` has the
  required finite-set, function and membership-proof argument order. Both
  uses of `Finset.add_sum_erase _ _ (Finset.mem_univ i)` agree with the
  displayed sum decomposition.
- `List.replicate_succ` agrees with both repeated-request inductions. The
  shared-layer example's two requests use the same updated cache. Its
  equations use the existing `Measured.bind`, `pure`, `CallCount.tick` and
  `CallCount.primitive_rule` interfaces consistently. No concrete mismatch
  was found in the arbitrary-prefix cache example, empty catalogue, or
  shared/unshared recurrences.

## Validation boundary

No Lean, Lake, `check.sh`, project hash helper, Git operation or validation
command was run. No source, control file, ref, cache or configuration was
modified by the contributor; root transcribed this report afterward.
The frozen old Chapter 1 gate continued unchanged.

Source inspection cannot certify simplifier behavior, metavariable inference,
tactic completion or proof terms. All existing retained findings and gates
remain open. Focused elaboration, whole-candidate validation, exhaustive audit,
both retained independent reviews and immediate candidate verification still
belong to the repaired candidate's acceptance path.
