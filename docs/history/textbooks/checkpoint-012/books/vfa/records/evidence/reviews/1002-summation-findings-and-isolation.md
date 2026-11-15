# Summation import findings and bounded isolated continuation

This is a continuation of the same Preface/Perm review, coordinated by
`/root/formal_review` with the original Standards and Spec axes. Fixed base is
7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd. No new review loop or gate waiver.

## Confirmed findings on4adc

Standards independently confirmed ST-004 (medium): FiniteMH's
Finset.sum_le_sum and Finset.sum_pos come from
Mathlib.Algebra.Order.BigOperators.Group.Finset, absent from its2604-module
source import closure. Pinned source generates both through to_additive and
installed v5 metadata confirms their ownership. Root then checked the entire
actual source via direct Lean: both unknown-constant errors occurred, actual
exit1, complete kit result with no timeout/recorder error. See
validation/1039-finite-mh-before/.

Standards independently confirmed ST-005 (medium): StructuredCosts's
List.sum_replicate comes from Mathlib.Algebra.BigOperators.Group.List.Defs and
global nsmul_eq_mul comes from Mathlib.Algebra.Ring.Defs. Both are absent from
its2317-module closure; adding either module alone still omits the other.
Protected Nat.nsmul_eq_mul is a different name. Root checked all five actual
local source modules in private outputs: four prerequisites passed and the
target returned1 with both unknown names plus the repeated-list summation goals.
Before/after source and clean candidate identities matched. Complete evidence:
validation/1039-structured-before/ and1039-focused-structured.py.

Both files already belonged to this task diff because earlier task changes
narrowed Mathlib.Tactic imports. Attribute these failures to that incomplete
narrowing, not to unchanged baseline files. All three required artifact families
already exist; no dependency acquisition is needed for these corrections.

## Corrected candidate

cf0a687265c1929ffd3ff6f15fa18febe0fb61b5 adds exactly the three defining imports.
The existing body bytes of both files, including all statements, assumptions,
witnesses, cases and proofs, are unchanged. Full enclosing scope remains26files,
now+500/-17, no exclusions. See validation/1039-candidate.json and
specs/1039-summation-imports.md. Both original axes must assess this concrete
candidate and its actual positive checks; no approval is asserted by this note.

## Interruption and input separation

Root sent Ctrl-C through the then-live owned58093 session to investigate the
newly confirmed gaps early. The execution API returned1; the kit wrote no
result.json and the raw log ends at61 completed ordinary modules. This does not
establish the checker's own terminal result or descendant quiescence. /proc is
absent; no escalation, guessed/historical PID signal, or cleanup was attempted.
The exact status is validation/1039-interruption-assessment.json.

The old vfa-unified-pty-validation checkout remains clean and frozen at4adc,
including its sources, detached HEAD, package links, outputs and records. The
new vfa-summation-validation checkout has independent source files, private
proof/diagnostic and managed output paths, and a distinct verification record.
No old project output or verification record was copied. Both use only the
unchanged real dependency directories under the frozen provisioning checkout.
Its root source HEAD remains4adc; those root project files are not imported by
the new candidate. Read-only Git observations disable optional index locking.

The operational agent and retained Standards independently inspected the
unchanged kit/checker write paths. Standards found this new-worktree continuation
adequate under these conditions; unknown old-descendant status alone is not a
material ownership blocker. The old fresh command binds ROOT to its own source,
invokes direct Lean into its own temporary outputs, reads dependencies through
LEAN_PATH and can write only its own final verification record. It does not call
Lake build, dependency/cache acquisition or the repairing guard. The known old
command has no configured output path into the new checkout. The kit's general
TMPDIR remains state-wide: only the proof/diagnostic outputs are described as
private. Its per-project lock is not a cross-worktree liveness certificate.

Keep shared compiler/profile/source/artifact inputs stable, with no competing
setup, cache, dependency edit or profile replacement during new validation.
Focused checks use direct Lean and an explicit LEAN_PATH containing only the
new private outputs and stable dependency libraries, established inside run.
The collector still needs stable current inputs after the new full fresh run;
later guarded operations retain sole-writer discipline and incident triggers.
Evidence of a writer reaching new/assessed inputs requires reassessment.

No interpretation here supplies quiescence, proof, build, preservation or review
credit. Standards remains Blocked. ST-001 remains fixed; ST-002, ST-003's actual
complete-module obligation, ST-004/ST-005 and SP-VAL-001 remain open pending the
required actual evidence and reviewer disposition.

## Returned correction assessment on cf0

The complete corrected FiniteMH file and all five actual StructuredCosts local
modules returned 0, with complete matching kit and execution-API records.
Both retained independent axes assessed these results and the exact three-line
source delta: ST-004 and ST-005 are fixed; no new source finding was raised.
The earlier open-finding statement above records the pre-assessment state.
ST-001 remains fixed; ST-002, ST-003 complete-module elaboration and SP-VAL-001
remain open. Both formal outcomes remain Blocked pending all integrated gates.
See 1002-summation-correction-source-review.md for the durable returned report.
