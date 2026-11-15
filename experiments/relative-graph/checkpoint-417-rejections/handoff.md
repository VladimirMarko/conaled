# Cached malformed-family controls

**Final control status:** the seven-module source checkpoint `5c5c0dc` proves all three unconditional exported rejection equations. All seven modules compiled and audited in the recorded final cohort. The earlier conditional checkpoint descriptions below are history, not remaining proof obligations.

The initial checked source checkpoint is `ea574ef`, based on `5f69973bff7697e90e077f392c2102e4ba38f385`. It adds only five CachedRejections modules. Whole exported-checker errors are not established by this checkpoint: record 7 success and the final pending-list composition remain separate obligations.

`measurements.json` retains compiler identity, exact module source hashes, phase timings, and successful module audits. `failed-attempts.json` retains construction failures and bounded timeouts. The local checks used the Nix shell, the shared orchestration build lock, one sequential Lean subprocess, `Elab.async=false`, private control outputs, and read-only author/upstream compiled dependencies. Module limits were 30 seconds, with one recorded 90-second trial. Timeout wall times include subprocess termination. Proof generation and normal kernel declaration checking are separate measurements; none is a cached driver runtime claim.

Reproduce the final integrated closure with the repository acceptance runner once these modules are included in its manifest. The temporary run-module.py harness is not a portable acceptance receipt. Root owns the fresh audit and independent reviews for the final complete #417 candidate.

The source-binding theorems identify replacement of declaration 12's body or type, or deletion of declaration 11. The missing-helper control retains the exact unresolvedConstsErrorL result because the pinned formatter's partial scanner is opaque to kernel reduction. It proves rejection and supplies the actual position; it does not claim a normalized textual category.

The next checkpoint adds `CachedRejectionsComposition.lean`. All three complete exported error equations are checked conditional on exactly `CachedPending7.accepted`'s local success proposition. This exposes the remaining dependency without admitting it. The separate final wrapper module must discharge it before claiming unconditional controls.

## Final integration handoff

Source base is `5f69973bff7697e90e077f392c2102e4ba38f385`. Control commit chain: `ea574ef`, `149e63b`, `f637e90`, `5c5c0dc`, followed by this evidence-only update. Changes are confined to CachedRejections*.lean and checkpoint-417-rejections. No author support module was edited.

`CachedRejections.lean` imports the author's new `CachedPending7`, whose accepted local certificate was checked in attempt `1794220693956990564-CachedPending7`. Its exact source and compiled hashes are retained. Integrate that author source/dependency chain before reproducing the final module. No success of pending10 is needed to reject these forward records; the actual backward header is installed, then its pending body remains unreachable after the earlier error.

Include all seven new modules in the existing portable acceptance build/audit closure: Body, Type, Missing, Prefix, Families, Composition, then CachedRejections. The supplied upstream/source pin and compiler remain unchanged. The final full-candidate fresh audit and review belong to root and the main author; this focused leaf run neither replaces them nor claims binary execution correctness.
