# #462 independent replay outcome

**Passed.** All 16 original budget-check snapshots reproduce their recorded outcomes in fresh isolated replay repositories. Fifteen successful snapshots pass the exhaustive project/setup/local/generated-root audit. The sole expected failure, direct H2 round 2, reproduces the same rewrite mismatch. It was preserved unchanged and not repaired.

The two final submissions per arm all pass their complete mathematical checklists; see `statement-review.md` for declarations, actual assisted use and separate scoring. This is trial/replay evidence, not final issue acceptance.

## Isolation and exact inputs

Each replay repository was provisioned from its arm's frozen one-commit source snapshot, with its own newly built project outputs and only pinned external dependency packages linked. No original author or other replay project build outputs were copied. Builds and checks ran through direnv on CPU0 under the shared build lock. All frozen artifact hashes were rechecked after replay and remain unchanged.

Every budget source snapshot was compiled byte-for-byte, including generated request, certificate and result snapshots. Replay filenames were placed under `Examples.ReplayroundNNN` so module-origin audit ownership includes the complete submission, without editing its content. Snapshot hashes match original control receipts. Embedded support and generated declarations are therefore audited along with final author additions. All failed/successful original artifacts remain frozen.

## Audit coverage

The auditor is the accepted ProofAudit implementation with three explicit adaptations: import Lean instead of the full public entrypoint, add the common `TaskSetup462` module to the module-origin root list, and move invocation to a driver importing the one exact replay module. The audit algorithm is unchanged. The adaptation diff is retained for each arm.

Each successful snapshot audit covers its entire module, imported project modules and every common setup declaration, not just the final theorem's dependencies. The explicit root lists retain private/generated roots. Final submission coverage is:

| Arm/task | Snapshot logical roots | Snapshot theorem declarations | All audited project roots |
|---|---:|---:|---:|
| Direct H1 | 14 | 11 | 1111 |
| Direct H2 | 32 | 22 | 1129 |
| Assisted H1 | 20 | 13 | 1123 |
| Assisted H2 | 48 | 28 | 1151 |

Each audit includes all 14 common setup roots. The transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`. No unsafe runtime roots are excluded in these final snapshots. All passing intermediate generated request/certificate snapshots also receive separate complete audits, so later-added author helpers cannot hide behind an earlier CLI audit marker.

## Replay setup failures, separated from author results

Initial replay provisioning lacked a Git repository root for Nix's flake resolution; the resulting environment failure occurred before Lean ran. Initial audit-helper compilation then lacked the Lean command import formerly supplied transitively by the full entrypoint. Both setup failures and their logs are retained. The replay environments and auditor import were corrected before the affected checks; frozen author sources were never edited. Neither setup failure is counted as an author attempt or reproduction failure.

## Evidence

`evidence.json` binds every replay snapshot to its original hash and records outcomes, audit counts/root lists and log hashes. `receipts.json` retains commands, cwd, exits and elapsed durations. `run.log` records successful completion. `statement-review.md` provides the task/scoring review. The two replay repository directories contain private source/output environments; archive the named evidence and source snapshots without their `.lake` caches.

No source or mathematical findings remain. Both routes completed H1/H2, and the assisted route used actual checked generated applications. The sample does not establish net author-effort savings, a productivity ranking or permission for broader architectural adoption.
