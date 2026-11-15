# Operational toolchain — coordinator reconciliation, r9-043

## Outcome and correction handoff

**Findings-present on candidate `ff3f709723e5c49e5ba40798abbed7d36141a6fb`.**
Both independent full-scope reviews are complete. Standards retains one new
unresolved Medium finding, DTS-003; Spec separately retains one new unresolved
Medium finding, DTP-003. Both concern the Elan recovery appendix's actual child
command selection. No other new finding or evidence-access blocker was reported.
The four older findings remain fixed with their original severities and evidence.

The document appends its verified Elan directory after ambient PATH, whereas the
unchanged stock checker test invokes bare `elan`. An earlier installed executable
can therefore win. The actual cold setup used absolute Elan paths and does not
resolve this later selection interface. Root has accepted the narrow correction:
prepend the real package directory and retain evidence of effective bare-command
selection, genuine version and native Lean selection under the same child launch
environment, including an earlier ambient executable with that basename.

Neither finding is closed by that plan. Root will capture the correction as a new
immutable candidate in this same loop; both axes must assess the whole task,
retaining matching analysis and validating the changed interface. Full stock-suite
execution is a separate formal-validation obligation, not required solely to
establish this narrow selector correction.

Coordinator: `/root/direct_toolchain_validation_plan`. I read both complete
independent reports, reconciled their evidence and separate findings, and checked
candidate identity. I authored an earlier original runner and therefore supplied
no third Standards or Spec review. I performed no compiler/build/test/network or
protected-path operation and changed only coordinator/review records.

## Exact scope and independence

| Item | Identity |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `ff3f709723e5c49e5ba40798abbed7d36141a6fb` |
| Retained ref | `refs/pfds-review/native-toolchain-r9-043` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r9` |
| Full task diff | 19 files, 3,456 insertions; one synthetic snapshot commit |
| Manifest SHA256 | `af74d3d1ab35c9a26dd1034bf223d2479232d6e82732c05ac72b701c7f0e09ec` |
| Artifact aggregate SHA256 | `a86be8c447403d0947e7542461471e47570b69e484e4464522c3a12661221ddc` |

The exact comparison is the three-dot diff from the fixed base above to the
candidate. The manifest and complete dispatch
`session/reviews/direct-toolchain-dispatch-r9-043.md` enumerate all 19 source
paths, six saved requirements, applicable guidance, prior evidence and exclusions.
All original 18 files match approved r7 in both bytes and modes. The only r7-to-r9
change is the added `session/environment/RECOVER-ELAN-REGRESSIONS.md`.

Standards `/root/lean_native_path_options` confirmed it authored none of the 19
source files; its earlier investigation and review records are outside scope.
Spec `/root/chapter02_continuation_plan` confirmed it authored neither the new
appendix nor its Elan recipe. The r7 Standards reviewer `/root/recovery_audit`
supplied that recipe and was not assigned independent review of this addition.

Both axes assessed the full task. Standards read the full 19 source files and
related stock interface. Spec retained its complete r7 analysis only after
independently matching original18 bytes/modes, guidance and relevant evidence,
and directly inspected the appendix and affected interfaces. This follows the
existing review-loop reuse rule; it does not reduce the acceptance scope.

## Complete independent outcomes

| Axis | Outcome | Prior findings retained | New / unresolved | Worst unresolved |
| --- | --- | --- | ---: | --- |
| Standards | Findings-present | DTS-001 Medium fixed; DTS-002 Medium fixed; no regressions | 1 / 1 | Medium, DTS-003 |
| Spec | Findings-present | DTP-001 High fixed; DTP-002 Medium fixed; no regressions | 1 / 1 | Medium, DTP-003 |

| Frozen complete report | Bytes | SHA256 |
| --- | ---: | --- |
| `session/reviews/direct-toolchain-standards-r9-043.md` | 22,456 | `b40654b0be536883a61ef62c1dd9dde10868ffd4b3fa9a9297f38212b7fb2a7b` |
| `session/reviews/direct-toolchain-spec-r9-043.md` | 23,878 | `1651fad484a6c01c68e3038a980e2edce9cbe309f9fef84b1a8167731fd60526` |

The complete reports remain authoritative for each axis. Their shared concrete
mechanism is at appendix line 114 (`PATH="$PATH:$PFDS_ELAN_PACKAGE"`), native
launcher line 138 (prepend only native Lean bin), and stock `scripts/test-check.py`
line 372 (bare `elan which lean`). Standards identifies an operational robustness
and coverage judgment tied to artifact-appropriate validation and reproducible
public interfaces. Spec identifies a reproducible-handoff requirement gap. The
two findings are not merged or reranked, and no claim is made that an ambient
Elan failure occurred outside the later owned fixture.

The reviewers accepted existing setup and original18 artifact evidence within
its stated coverage. There is no access blocker or unperformed source-review
portion. The outstanding issue is the uncovered real selection behavior, so the
outcomes are Findings-present rather than approval or a wait for unrelated jobs.

## Evidence reuse and historical preservation

The r9 aggregate reuses actual r8 appendix syntax/cold-setup results on identical
19 source blobs and unchanged relevant runtime inputs. Round 8 was superseded
before review because two controller executable modes were normalized. Round 9
restores the r7 modes; those controllers do not participate in the cold Elan
recipe. The r8 discrepancy and original successful commands remain preserved,
without inventing r8 approval or calling them newly executed r9 tests.

The original18 r7 evidence remains applicable after full identity matching.
Its actual exact-version, valid/false proof, native/Lake, 18-case metadata,
controller-refusal and recovery checks retain their previously reviewed limits
and their explicit r6/r2 reuse provenance. Earlier failed/partial rounds remain
failed/partial. The new appendix has genuine official acquisition/link/version
evidence; its three shell blocks were syntax checked, but its stock-suite calls
were not executed. Absolute setup checks do not establish the later bare lookup.

After the source findings were surfaced, root supplied a separate public selector
red case: `session/validation/elan-path-selection-red-r9-043.json`, SHA256
`08a5bcf224750c9dfd154c571be36e1f2ae5fdb2fdb55d0712636c84df7682c3`.
I read that complete record without executing it. It preserves the r9 child
environment/native launcher and substitutes only a selector probe for the suite
entrypoint. An owned earlier PATH entry named `elan`, symlinked to `/usr/bin/false`,
is selected. The probe exits 7 before invoking the wrong executable. The record
contains the actual selected path and reports no stock-suite run or formal
acceptance. It corroborates the selection issue; it does not rewrite the frozen
axis reports or supply correction evidence. No version or proof output is faked.

The six requirements remain unchanged: original request, book/thesis union,
direct-toolchain request and scope, environment handoff, and native-toolchain
steering. The explicit Nix exception waives the Nix launcher requirement only.
Exact compiler/dependency identity, genuine results, source policy, isolated
formal checks, audits, both reviews, final verification and durability persist.

## Final read-only identity and remaining boundaries

At `2026-11-03T18:01:15.741892+00:00`, I rechecked exact HEAD/ref/merge base,
empty isolated porcelain, all 19 committed/isolated/delivered source hashes and
modes, all six requirement hashes, and eight manifest/validation/dispatch/report
record identities. All matched with no failure. The durable receipt is
`session/validation/native-toolchain-coordinator-identity-r9-043.json`, SHA256
`9d762ec88725ccc74db261d811e333aabe0ebd45d5979a9d4bdafd6244001ea6`.
This is identity verification for a findings handoff, not a passing review,
stock verifier invocation, or acceptance receipt.

Both r9 axes and this reconciliation are frozen. Root may now implement the
narrow correction, retain its public red/green evidence, and capture r10 while
preserving the same base and correct modes. Original18 and cold-setup evidence
may be reused only with matching inputs. Both axes must independently resolve
their own stable003 finding against the exact corrected candidate.

The active full901 run, three stock regression suites, prerequisite10013/10018
closure and signed-potential10023 own full/audit/record/final verification remain
separate. The standalone module-header investigations are not operational or
formal acceptance. No chapter or whole-union status is advanced by this round.
