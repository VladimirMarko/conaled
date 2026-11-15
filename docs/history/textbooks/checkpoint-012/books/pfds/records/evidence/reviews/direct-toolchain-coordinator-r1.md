# Direct-toolchain review coordination — round 1

## Result

**Correction required.** Both independent axes completed review of candidate
`f010b5d0fdbef9c9f007c56531c326e738557f9d` against fixed base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c` and returned
**Findings-present**. Neither axis is skipped or blocked. No approval applies
to this candidate or a later tip.

| Axis | Complete report | Unresolved findings | Worst severity |
|---|---|---:|---|
| Standards | [direct-toolchain-standards-r1.md](direct-toolchain-standards-r1.md) | 2 | Medium |
| Spec | [direct-toolchain-spec-r1.md](direct-toolchain-spec-r1.md) | 2 | High |

The full requirement, candidate and validation identities, scope exclusions,
reviewer provenance and finding history are retained in
[direct-toolchain.md](direct-toolchain.md). The two complete axis reports are
preserved without changing their severities or findings.

## Standards findings

- **DTS-001, Medium, unresolved:** The incremental-only full route and record
  validation omit the repository's required fresh validation after this
  tooling/runtime transition. Add the fresh route and preserve the actual
  successful mode through retained evidence and final verification.
- **DTS-002, Medium, unresolved:** Both public smoke tests assume the excluded
  temporary parent `session/tools` exists. Ensure the workspace-local parent
  is created so a recovered workspace can reach the Lean/Lake probes.

Complete Standards report SHA256:
`a286dc7fdb24d2b2fdbd85fcd5d9aa5c6000d51e976f6ae9c46c99bfc14542d4`.

## Spec findings

- **DTP-001, High, unresolved:** The full/verify workflow cannot record the
  required fresh full check. Provide an explicit route, bind retained
  evidence to its actual mode, and invoke stock final verification without
  `--fresh` or `--jobs` flags.
- **DTP-002, Medium, unresolved:** The smoke-test fixture precondition is not
  guaranteed after checkpoint recovery; both tests need to establish their
  workspace-local temporary parent before allocating projects.

Complete Spec report SHA256:
`c1a00422ebe8cd8bbbbf8e75d98dc9251ab8dad9b07dfd4b6691b3ed5508d051`.

## Reconciliation and implementer response

The independent axes agree on the two underlying corrections. Their IDs,
severities and standard/spec reasoning remain separate. The coordinator has
not performed a third source review or discarded any finding.

When asked about the fresh rule, the implementer confirmed that no saved
exemption exists. The correction will expose a full fresh route and preserve
its actual stock mode; the first full run under this runtime will use fresh
mode with the established one-job policy. Stock verify will retain its
ordinary flag contract. No formal full gate had started.

The implementer also identified the omitted temporary directory in cold
recovery. Each reviewer independently checked the immutable test setup and
confirmed the consequence. Creating that parent is the accepted correction.
An accepted remedy is not a verified fix: every ID remains unresolved on the
round 1 snapshot.

## Validation status and scope

The candidate-matched public CLI, Lake executable build/run, and three public
runner-refusal checks passed. The coordinator checked evidence identity and
recomputed all eight frozen/delivered source hashes against the manifest.
Dependency bootstrap/retrieval and clean exact dependency pins are retained
as adjacent operational evidence. No completed mechanical check was repeated.

Those successes remain valid within their recorded coverage. They do not
cover the cold-recovery fixture omission or missing fresh orchestration, and
they do not accept any formal candidate, proof, chapter or book/thesis claim.
The reviewers did not demand a full formal build as a prerequisite to this
tooling-only artifact review. Future formal acceptance keeps all stock gates.

## Handoff for correction round 2

Keep the base fixed and preserve all eight authored files in the next
candidate. The parent reports candidate
`822cb7adeed4943acaf10454e9facfc2e3ee8ceb` in
`pfds/review-direct-toolchain-041-r2`; its isolated validation was still
running when this report was finalized. Await genuine terminal evidence,
then reuse both independent reviewers for full-scope review, reassessing
DTS-001, DTS-002, DTP-001 and DTP-002. Reuse only unaffected validation whose
relevant inputs still match. Later delivery must match the eventually
approved immutable snapshot.

**Round 1 final record:** base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`; candidate
`f010b5d0fdbef9c9f007c56531c326e738557f9d`; Standards Findings-present,
2 unresolved/Medium worst; Spec Findings-present, 2 unresolved/High worst.
