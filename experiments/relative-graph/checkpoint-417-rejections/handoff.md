# Cached malformed-family controls

The initial checked source checkpoint is `ea574ef`, based on `5f69973bff7697e90e077f392c2102e4ba38f385`. It adds only five CachedRejections modules. Whole exported-checker errors are not established by this checkpoint: record 7 success and the final pending-list composition remain separate obligations.

`measurements.json` retains compiler identity, exact module source hashes, phase timings, and successful module audits. `failed-attempts.json` retains construction failures and bounded timeouts. The local checks used the Nix shell, the shared orchestration build lock, one sequential Lean subprocess, `Elab.async=false`, private control outputs, and read-only author/upstream compiled dependencies. Module limits were 30 seconds, with one recorded 90-second trial. Timeout wall times include subprocess termination. Proof generation and normal kernel declaration checking are separate measurements; none is a cached driver runtime claim.

Reproduce the final integrated closure with the repository acceptance runner once these modules are included in its manifest. The temporary run-module.py harness is not a portable acceptance receipt. Root owns the fresh audit and independent reviews for the final complete #417 candidate.

The source-binding theorems identify replacement of declaration 12's body or type, or deletion of declaration 11. The missing-helper control retains the exact unresolvedConstsErrorL result because the pinned formatter's partial scanner is opaque to kernel reduction. It proves rejection and supplies the actual position; it does not claim a normalized textual category.
