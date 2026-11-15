# Final #417 author handoff

The candidate containing this file incorporates published base `8925b914dc49322d323a1c1475451f3b8d4b81ec`. Resolve its exact commit before final validation; the author handoff supplies that immutable SHA separately. All formal endpoint, consumer and rejection sources are committed. No long validation process is left running by the author.

The complete statement review and focused source-bound records are adjacent to this file. The [current report](../../../docs/research/relative-cached-acceptance.md) gives the artifact, assumptions, controls and portable commands. Earlier checkpoint records are historical scopes, not pending obligations of this candidate.

## Changes affecting validation

The portable runner already discovers all top-level graph modules and their imports. Its only runtime-file edit in this final slice is the opening docstring, changing “#135” to “#135/#417”; executable behavior and `Commands`/`ClosureAudit` interfaces are unchanged. The test adds plan membership/order assertions for `CachedPending10`, `CachedEmittedAcceptance`, `CachedAcceptedEmission`, `CachedRejectionsComposition` and `CachedRejections`. Four tests passed in 8.040 seconds through direnv under the shared build lock. Existing certified-nat-checker clients still import the same shared helper interfaces; their runner controls can check that boundary without repeating their expensive native execution.

The new inference/comparison support modules and all concrete proofs are isolated under `experiments/relative-graph`. The main Lake graph, toolchain, package pins and public imports are unchanged. Historical scratch sources are `.lean.txt` files outside discovery. The unused expression-comparison diagnostic is likewise archived.

## Final validation to perform

Use the README candidate protocol in a clean checkout. Serialize commands with the coordinating build lock. Run:

```sh
direnv exec "$checkout" python3 "$checkout/experiments/relative-graph/test-reproduce-acceptance.py"
direnv exec "$checkout" python3 "$checkout/experiments/certified-nat-checker/test-reproduce.py"
direnv exec "$checkout" python3 "$checkout/experiments/relative-graph/reproduce-acceptance.py" --run-dir "$new_run_directory"
```

Then run `direnv exec "$checkout" ./check.sh --candidate HEAD` and `direnv exec "$checkout" ./check.sh --verify-candidate HEAD` from that checkout. The portable output directory must not exist beforehand. Retain its complete `provenance.json`, command logs and exhaustive closure audit, plus the separate main candidate receipt. These are required acceptance results, not claims already made by the focused measurements.

Independent Standards and Spec reviews must reconcile the full source against the incorporated base and matching final validation. The supervising originator review remains required. The concrete scope supplies no binary-driver correctness, runtime bound, arbitrary-declaration completeness or general cached/pure equivalence. #107/#108 ownership gates are untouched.
