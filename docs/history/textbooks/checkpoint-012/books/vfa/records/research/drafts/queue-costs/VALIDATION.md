# Queue traversal staging validation

Date: 2026-11-02. Status: focused Lean check passed; integration and chapter
acceptance are pending. This is assigned cross-cutting implementation
preparation within the parent's existing workflow.

## Checked files and toolchain

- Lean source: `QueuePeekCost.lean`
- Source SHA-256:
  `41486ba378124a2d459a74bd8199655e40a4c521e20abb75b9e5580671161df0`
- Explanation: `README.md`
- Explanation SHA-256 at focused-check completion:
  `294235c2ae5454fd513bdce8a3b2e9c6764886d090227dfc36a6520cf670d5fe`
- Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Pinned Batteries revision:
  `66e469188fe07963e5cf666c7d4433f45b8131c5`.
- VFA `ADT.v` SHA-256:
  `87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2`.

The Lean file contains eleven definitions, one abbreviation, one reachability
inductive predicate, and 30 checked theorem declarations, including six
concrete or specialized clients. It sets `autoImplicit` to false and
`warningAsError` to true. Its imports are `Batteries.Data.List.Lemmas` and
the actual project interface `Applications.Resources.Potential`.

## Exact command

Working directory:
`/workspace/scratch/0c54f2db1fdf/conaled`.

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
nix develop --command lake env lean /workspace/scratch/0c54f2db1fdf/work-state/staging/queue-costs/QueuePeekCost.lean
```

The shell was run through approved escalated execution solely because the
sandbox does not expose the installed Nix profile. The final invocation exited
with code **0** and emitted **no diagnostics**. It did not request Lean output
artifacts (`-o` or `-i`), invoke `lake build`, or mutate dependencies. This
preparation made no changes to main project sources or cache configuration.

## Development corrections

The first invocation found one proof error in
`repeated_peeks_exhaust_initial_credit`: an unrestricted multiplication
rewrite expanded the left side through a local `let` before the intended right
side. The fix supplied explicit arguments to `Nat.mul_add`, `Nat.mul_one`,
and `Nat.mul_comm`. No theorem statement, model, or cost definition was
weakened. The second invocation passed without diagnostics.

One explanatory comment was subsequently tightened to state precisely that
a state-only potential cannot reduce the required self-loop charge. The final
invocation for that initial revision rechecked the complete source and also
passed without diagnostics. That historical source hash was
`9266dae6612db42d811f798ca012ae45688fbc438b7cc75113ac01eaf20e078f`;
its independent staging review found no unresolved findings, recorded in
`../../reviews/resource-model-drafts.md`.

## Actual resource-interface follow-up

The parent authorized the environment agent to build the existing main
checkout targets `Applications.Resources.Measured`, `.Workload`, and
`.Potential` with one worker. That build exited 0, with existing module-format
warnings only. Once the artifacts were ready and the shared focused compiler
slot was released, this subtask imported the real resource stack and added
exactly four theorem declarations:

1. `runPeeks_eq_resourcesRun`: equality of the complete state/observation
   pair with actual `Resources.run` on repeated unit inputs.
2. `resources_exact_accounting`: an actual `Resources.run_potential_exact`
   caller whose state-dependent charge is the measured peek observation.
3. `resources_peeks_exhaust_initial_credit`: the original reachable
   arbitrary-initial-credit counterexample expressed with `Resources.run`
   and `Resources.budget`, using `Resources.budget_constant`.
4. `Examples.QueuePeekCostDraft.resource_workload_observation`: a connected
   concrete existing-workload client, reusing the original source enqueue
   example through the executor bridge.

No original algorithm, reachability definition, cost equation, lower-bound
proof, or potential counterexample was changed. The new import and these
adapters are the entire Lean follow-up. The README now records actual checked
interfaces rather than an uncompiled proposed adapter.

The follow-up used the exact command above, once, after artifact readiness.
It exited **0 with no diagnostics** on the current source hash recorded at
the top of this file. Only one staging compiler was running; after completion
the slot was explicitly released to the environment agent. No subsequent
queue compiler launch or source edit occurred before this freeze.

The final source/README/validation files are frozen for the independent
follow-up staging review assigned by the parent. That review is separate from
full chapter acceptance and its results will be recorded separately.

A lexical check of the Lean source found no `sorry`, `admit`, `axiom`,
`native_decide`, or `unsafe` occurrences. The only concrete evaluation proofs
use ordinary kernel-checked `decide`. This lexical check is not presented as
a substitute for conaled's full integrated exhaustive axiom audit.

## Deliberate validation limits

- Project `Applications/Resources` output artifacts were unavailable at the
  beginning of the initial preparation. The authorized follow-up build and
  focused check have now discharged the proposed `Resources.run` adapter;
  it is no longer an outstanding staging obligation.
- No full-project build, proof audit, candidate verification, or chapter
  acceptance was run by this subtask.
- No claim is made about wall-clock cost, compiler preservation of this cost
  interpretation, extracted execution, allocation, garbage collection, or
  external memoization.
- The source and README are frozen at focused-check completion for the
  independent staging review assigned by the parent. Review results will be
  recorded separately rather than silently folded into this record.
