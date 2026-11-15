# Optional project-cache recovery companion — #1027

This amendment is **pending** until the accepted candidate and both independent
review outcomes are recorded in `work-state/validation/1027-acceptance.json`.
Its historical original requirements are preserved unchanged at
`work-state/REQUIREMENTS.md` (SHA256
`85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84`) and
`work-state/specs/1002-full-requirements.md` (SHA256
`43dbf2c1104ec2503a0dc89206001fd541daaf7f677ad7e89c7fcbda61f5939a`).

The user authorized recovery of work after workspace or chat loss and the
immediate exposure/upload of checkpoints. Saving completed compilation can
avoid repeating expensive work. The earlier cache exclusion was our local
interpretation, not a restriction in the user's words.

Complete source/history/ticket/review checkpoints remain mandatory,
self-contained and cache-free. As an explicit exception to the original cache
exclusion **and** standalone-completeness requirement, a separate optional
project-cache companion may accompany a named, successfully uploaded complete
source checkpoint. It must record that checkpoint's filename, complete SHA256,
byte size, Library file ID and source commit. It cannot replace that checkpoint.

Only complete, stable module output families with supported unchanged traces
and matching pinned Lake hashes may be saved. Capture uses independent private
copies and does not write to the running build. External dependency caches,
credentials, downloaded research copies, setup files, hash sidecars, unrelated
outputs and verification success records remain excluded. Retained old entries
are not claimed to have been compiled from the captured candidate.

Each finalized companion must pass the documented archive/extraction checks,
be exposed and uploaded immediately, and have its exact receipt retained in
the next complete source checkpoint. Its integrity metadata is not proof of
source provenance or hostile-data authentication. The saved cache is optional
and safe to discard if unavailable, inconsistent or incompatible.

Recovery restores the named complete source checkpoint and pinned environment
first. Install the companion only into an explicitly idle isolated checkout
with absent or empty project outputs, after all identity and archive checks.
Do not merge it into an active or nonempty build cache. Never restore a success
record. Reuse across different root paths is not guaranteed.

Every original acceptance gate remains: exact-candidate guarded build and
exhaustive proof audit, the required ProofAudit/regression steps, separate
Standards and Spec reviews, and final candidate verification immediately before
acceptance. This amendment grants no chapter credit and changes neither the
chapter order nor the nonblocking disposition of #1025. No GitHub writes are
authorized. The operational specification is
`work-state/specs/1027-cache-companion.md`.
