# Preface/Perm — independent source review continuation

Recorded: 2026-11-03T23:40:29.546548+00:00

This supplements the existing `1002-Perm.md` loop and the pinned
`1002-unified-continuation-brief.md`. It does not alter the historical record,
start another formal implementation loop, or accept a chapter.

## Scope shared by both axes

- Base and independently verified merge-base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Exact candidate: `c988f183887896c00b09aaff9077a6ea7fb8d68f`.
- Full scope: 25 files, 496 insertions and 17 deletions, no exclusions.
- Isolated checkout: `vfa-native-kit-validation`, source clean at review.
- Previous source-reviewed candidate:
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.

Both reviewers independently verified that the previous 23 changed files are
byte-identical. The only further changes replace the first-line `import Lean`
with `import Init` in Squares and Dependent; all other bytes are unchanged.

| File | Independently verified SHA-256 |
| --- | --- |
| `Squares.lean` | `d535da719c3d7b3db4f536b5b791611d07c6dd6dd8bdae59572a8b375040dc41` |
| `Dependent.lean` | `1a770edc3353192e1f82315353e52d4a3e6bec511659a6ccfbed42316be29e90` |

The preserved full requirements, amendments, #1002 chapter specification and
#1034 import-footprint supplement define this round. Their hashes and exact
comparison command are retained in the continuation brief.

## Standards — source complete, validation Blocked

Reviewer: `/root/formal_review/standards`.

The reviewer explicitly reuses independent Standards analysis from rounds 1–8:
chapter architecture, connected examples, statement review, provenance,
coverage and earlier import corrections. Full-diff `git diff --check` passed.
No new unresolved Standards source finding was identified.

The unchanged foundation bodies use ordinary type/function, equality,
product/sum/subtype, dependent-family and finite-index constructions. No new
abstraction, mathematical claim, admission, axiom, execution shortcut or
performance theorem was introduced. Retained Verification and direct consumers
were inspected; the existing connected cases are sufficient for an import-only
change. Complete downstream elaboration remains a full-build obligation.

All seven exact foundation fixture inputs (six sources plus checker) were
matched to the candidate. The saved recorder reports normal child/recorder
exit 0, the six checks, selected axiom reports, and outputs `(43, false)`, `8`,
and `(8, 8)`. This supports only the focused foundation obligation.

The reviewer checked the successful post-relocation doctor and ten expected
smoke outcomes, including rejection of the false proof. The user-authorized
pinned native environment is permitted without Nix. The kit's one-thread
setting and fresh jobs setting do not establish explicit CLI `-j1` or an
OS-thread/RSS bound.

- ST-001 remains fixed by the previously reviewed composition relocation.
- ST-002 remains open, medium: the historical four-family artifact mismatches
  require the incident assessment and successful recovery evidence. Empty new
  project outputs do not explain or reconstruct historical mismatches.
- New Standards source findings: zero.
- **Outcome: Blocked.**

The historical cause can remain explicitly unknown if completed evidence
supports a bounded mitigation and acceptance disposition. Unsupported causes
or reconstructed originals must not be invented.

## Spec — source complete, validation Blocked

Reviewer: `/root/formal_review/spec`.

The reviewer explicitly reuses independent rounds 1–8 Spec analysis: Preface
and Perm correspondence, all 30 inventory records and four exercises, faithful
comparison/swap recurrence, reflection and Forall adaptations, connected
examples, composition placement, and the prior import corrections. No new
Spec source finding was identified.

Both complete foundation modules and the retained Verification boundary were
read. Squares retains distinct runtime/specification arrows, arbitrary decode
functions, and its product/coproduct/exponential/currying compatibility laws.
The forgotten-Boolean obstruction and nonvacuous constant-square cases remain.
Dependent retains the concrete split-family model, substitutions, indexed maps,
transport, Pi/Sigma contracts, proof-valued relatedness and quantified
assumptions, without a stronger arbitrary-setting claim. The dependent examples
still obtain lambda/application/pair certificates through the public combinators.
Their value-dependent output types and deliberate Boolean-tag erasure remain.

The delta introduces no new premise, weakened conclusion, circular assumption,
algorithm change, admission, axiom, unsafe declaration or runtime claim. The
actual metaprogramming imports in graph modules remain present. Successful
elaboration of the full downstream closure is still required.

The reviewer independently matched every foundation fixture input, checked the
normal focused completion and expected results, verified all 17 recovered
chapter hashes, compared all nine doctor dependency revisions to the candidate
manifest, and checked all ten smoke outcomes. These scoped results do not
constitute the exhaustive integrated audit.

- SP-VAL-001 remains open: the exact completed full candidate evidence is absent.
- ST-002 is corroborated and remains open; empty current outputs do not explain
  historical inconsistencies.
- ST-001 remains fixed and unchanged.
- New Spec source findings: zero.
- **Outcome: Blocked.**

## Remaining evidence and limitations

At each reviewer's last observation, the fresh recorder was running with null
child return and no completed candidate success record. Partial module progress
is not full validation. Root continues to own all compiler/process/cache actions.

The remaining sequence is full fresh build/audit and saved record; stable idle
inputs and unchanged non-repairing assessment; classification/preservation before
repair; separate guarded build, integrity check and exhaustive audit/record;
managed no-cache/rehashed ProofAudit prerequisite; all four audit regressions;
both independent completed-evidence assessments; and root's immediate
`--verify-candidate HEAD` before acceptance. Unexpected prerequisite rebuilding
requires the established investigation and corresponding guard evidence.

Both axes retain `1002-fresh2-record-protocol-clarification.md` for supported
native-record attribution when an original parent wait status is unavailable.
It never permits inventing an observed exit. Neither reviewer ran a compiler,
guard, process-control operation, cache/source mutation, or GitHub operation.
The coordinator recorded these returned reports without conducting a third axis.
