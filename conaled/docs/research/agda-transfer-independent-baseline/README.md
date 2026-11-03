# Independent Agda transfer baseline

This preserves the unassisted experiment for [#106](https://github.com/VladimirMarko/conaled/issues/106), following the first transfer in #105. A new author selected agda-unimath's path-concatenation associativity theorem and stopped at its prospective 40-cycle limit without completing the general source derivation. The checked partial work and failed attempts remain evidence; they are not production library modules.

## Records

- [Frozen protocol](protocol.md): declaration, dependencies, intended applications, budget and allowed inputs.
- [Independent scope review](scope-review.md): approval before proof construction, protocol digest and exposure disclosure.
- [Author report](report.md): partial results, unresolved obligation, statement review and limitations.
- [Independent evaluation](evaluation.md): integrity checks, effort assessment and recommendation.
- [Direct-Lean comparison](comparison-record.md): separately checked after archival, with its preliminary failures preserved.
- [Attempt ledger](attempt-log.md) and [cycle summary](cycle-summary.json): actual investigations, commands, failures and categories.
- [Immutable baseline archive](unassisted-baseline.tar.gz) and [manifest](MANIFEST.sha256): all attempt snapshots, diagnostics, upstream source/license evidence and accounting files.

Paths such as `work/` and `cycles/` in the author report refer to files inside the archive. The readable report, protocol, ledger and summary here are unchanged copies. The manifest describes the archived baseline, not this directory's later evaluation documents. Extract the archive outside the production source tree when replaying failed attempts.

Archive SHA-256: `27c81261b1ff1452acfdb2d999eaab6cd9c8293100fdbae057a9c9308d9f129f`.
Manifest SHA-256: `502e3e3d1128ae34f38739861c92504871c236bfc0369aa035014fc13e8280ab`.

## Independence and frozen interface

Author task `01a15f76-ecf1-7da1-bc56-717ed6849978` was newly created with only the task and public handoff instructions, without inherited turns. It had no framework implementation or review role. The author chose the theorem, recorded its protocol, received a solution-free scope PASS, and archived its attempt before evaluation or a direct-Lean comparison. The orchestrator supplied no theorem-specific preparation or coaching. Launch provenance is recorded by the orchestrator; the author and evaluator could not independently inspect the platform's launch configuration.

The frozen checkout was `8b1ed308f29cbe9d00e03c8b6b7780ffeb4b7c17`, the accepted local #105 review snapshot. Production commit `8267b71c1c275c44b21bacfe878749d0b99dce1c` has the identical tree. The checkout reused pinned external dependency caches and rebuilt project imports from frozen sources. Its tracked source/API files remained unchanged throughout the baseline.

The scope reviewer accidentally displayed adjacent upstream proof text while checking declarations, as disclosed in its report. It supplied no proof guidance to the author. The author's own declared upstream-source inspection was an allowed input. This reviewer exposure did not introduce assistance into the baseline.

The final partial artifact passed a targeted Lean check and selected-root axiom inspection. It did not receive the repository's full fresh build or exhaustive generated/private-root audit. Some exploratory checks raised a local heartbeat limit; none of that scratch work is integrated into the production closure. No completed transfer, semantic applications, or production proof-quality approval is claimed for these partial results.

The [first-port design record](../first-transfer-design.md) and [#104 design experiments](../contextual-j-design.md) record the earlier framework work. This archive adds independent author evidence and must remain separate from later repairs or assisted retries.

## Recommendation and next decision

The independent evaluator recommends improving the interface and retesting within a separately approved scope. The author repeatedly encountered dependent substitution and annotation comparisons; the ordinary direct-Lean result and its action applications checked without completing that source machinery. The source route's additional reuse across interpretations remains prospective for this second theorem. This one bounded attempt does not establish that the route is unviable.

The originating session agrees that the evidence warrants an interface experiment before more ports. A follow-up should target reusable substitution and congruence operations, preserve this baseline, and use another unexposed author to test any claimed savings. No repair, assisted retry or further port is included in this delivery. Under [#103's entry gate](https://github.com/VladimirMarko/conaled/issues/103), the repair/retest decision must be resolved before smooth-model implementation proceeds. The first port's technical result remains valid.
