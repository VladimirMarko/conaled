# XQ01 shared partition draft handoff

## Identity and authority

- Local ticket FDSA-XQ01, parent FDSA-000; original whole-book scope unchanged.
- Frozen requirements `three-way-partition-requirements.md`, version 1,
  SHA-256 `b1f55911c44a11def3498484787fcb04972398ec040bf1bd65c75796c116d541`.
- Original and immediate parent base:
  `07e480f6ec9958d4975bb90151005b84f2907614` (unaccepted Chapter 1 repair).
- Candidate: `de5410286bbefd841dff50bef55c2e52d2ebbd2a`.
- Branch `work/fdsa-three-way-partition`; checkout `conaled-three-way-partition`.
- Commit `feat(sequences): share three-way partition and source costs (#174)`.
- Seven paths, 618 insertions and 31 deletions; clean after pinned-shell commit.
- Checkpoint 0044 saved the frozen clean pre-code state before authoring;
  checkpoint 0045 will preserve the committed draft, assessments and tracking.

Accepted repaired Chapter 1 remains the integration/acceptance prerequisite.
The initial Chapter 2 foundation prefix c80eec9 is unchanged and does not depend
on this unit. This branch depends on no other pending shared unit. Preserve
this original base/ref and all earlier histories, requirements and findings;
incorporate accepted predecessor corrections through history-preserving merges.
No chapter, appendix or shared unit is accepted by this source handoff.

## Source and semantic boundary

The shared `Sequences.Partition` module owns the original partition3 operation
and seven independent semantic facts. Its eight-declaration fragment is
byte-identical to the original: two stable List.partition operations, exact
three-filter correspondence, concatenated permutation, membership, total
length and pivot-membership-qualified strict sizes. It retains standard
nested tuples and the universe-polymorphic LinearOrder interface.

Selection retains its old same-signature def and all seven theorem adapters.
The entire suffix from sorted_partition is byte-identical, as are Rank,
Consumers and RankSelection. Root independently verified those boundaries;
the exact evidence is in `three-way-partition-compatibility-reading.json`.
The shared core/resource dependency graph does not import the selector.

New nil/cons value equations match the companion's y<p then p=y branch order.
They are theorems about the existing operation, not another pure algorithm.
The actual `Resources.Partition.partitionRun` executes one tail recursion,
binds its actual triple and reconstructs one selected bucket under an entry
tick. Its value proof targets the shared operation. Its independent nil/cons
cost recurrence proves length+one, including the empty call. No output equality
assigns that count to the existing two-stage implementation or replaces the
separately charged two-filter quicksort metric.

The manuscript supplies the three-filter specification and time recurrence;
the pinned companion supplies the explicit one-pass code equation. The note
retains that provenance and the applicable source notice. Domains include
arbitrary pivots, duplicates and empty lists, with no added inhabitance,
distinctness, finite-payload or general pivot-member premise. Strict shrinking
is a sufficient qualified implication, not an equivalence. No bucketwise
noninjective monotone-map or physical-runtime claim is introduced.

## Connected cases

| Case | Public connection and independent expectation |
| --- | --- |
| Generic equal-block family | Shared nil/cons gives the exact replicate triple; separate measured value/cost laws give n+one. Empty/singleton cost one/two. Positive length supplies actual membership before strict shrinking. |
| Mixed duplicates | Pivot two on [4,1,2,0,3,2,1,4] gives ([1,0,1],[2,2],[4,3,4]), work nine, public permutation/length consequences and qualified strict sizes. |
| Absent outside pivot | Pivot four on [3,1,3] gives the unchanged lower side and work four; unconditional shrinking is false. |
| Absent interior pivot | Pivot two on [3,1,3,1] gives ([1,1],[],[3,3]), work five; both sides shrink without membership, so membership is not necessary. |
| Actual returned-bucket bind | The second invocation partitions the first actual lower list [1,0,1] around one, returning ([0],[1,1],[]) with combined work thirteen. Ordinary bind adds nine/four without an extra tick. |
| Existing interface | Old/shared and measured/old value connections are explicit; existing selector examples remain unchanged and in the public root. |

These are complete uncompiled proof scripts. They do not implement full
quicksort3, selection's middle-index bridge, selector recursion, median-of-medians,
random policies or whole-algorithm costs. Those original obligations remain.

## Assessments and validation limits

All authors stopped writes. Root read all three new Lean modules, the complete
Selection diff, source note and import/map changes; it matched every stopped
author identity before commit. Author, root and separate documentation readings
are retained in `three-way-partition-source-assessments.md`. No concrete
mathematical contract deviation remained. Narrow-import sufficiency and new
proof simplification/elaboration remain expressly untested.

`three-way-partition-source-identities.json` records the final seven-path
identities. Passed: original-base/changed-path checks, stopped identity matches,
source compatibility comparisons, unstaged and complete staged whitespace
checks, explicit seven-path staging, commit and clean post-commit status.
The new example import provides intended public closure; this is not a checker
coverage or exhaustive audit result.

No compilation, focused compatibility run, full candidate gate, exhaustive
audit, final Standards/Spec review or immediate verification has run for XQ01.
Root's sole full Chapter 1 gate continues at 07e480f (session 83124); no second
compiler/checker/project hash helper ran. Save/upload checkpoint 0045 promptly.

After accepted prerequisites and the initial Chapter 2-first sequence permit,
form a clean immutable history-preserving integration candidate. Retain the
union of accepted root imports and source records, and all accepted predecessor
corrections. Run the specified focused compatibility targets, full applicable
guarded build/audit and both independent final axes on the complete frozen
scope, preserving findings through corrections. Immediately verify the approved
candidate record before acceptance, then save/upload its evidence. Source-only
readings and this commit do not close any acceptance gate.

## Recovered development checks and corrections — 4 November 2026

The historical prerequisite above is now satisfied by accepted Chapter1 at
exact R07e480f. The first outstanding acceptance remains isolated shared
foundationf17cc6b; this XQ01 continuation is development only. Exact original
de54102 was merged into cumulativeccaee9422 after bottom-up cost draft7f17c441.
Only SquareApplications and reconstruction-map appended sections conflicted.
Root retained every existing import/paragraph and added the exact XQ01 import
and complete section. The five other XQ01 files matchedde54102 byte-for-byte;
Selection's entire suffix from sorted_partition still matched accepted R.
Resolution stages/diff/identities are preserved in
chapter02-bottom-up-xq01-development-20261104/.

First eight-target attempt closed actual exit1 at unchanged cleanccaee9422.
XQ01 shared core reported three redundant List.filter_cons simp arguments.
Root made only those proof deletions in a temporary-index successorb3bdc12b
of exactde54102, preserved on work/fdsa-partition-proof-fixes. A later
focused attempt at clean1ffb61fc built the shared core and all three existing
Selection.ThreeWay/Consumers/RankSelection compatibility targets; its actual
overall exit remains1 because the measured partition value proof left a
definitional pure first-projection goal. Root added only rfl in successor
0612e80a0c297a38fa1add6e837dc7781e1bbd9c afterb3bdc12b. This latest repair is
not yet merged into the compiler checkout or checked. No source equation,
interface, expected case, restriction or dependency pin changed.

| Stable finding | Status | Evidence |
| --- | --- | --- |
| XQ-ELAB-001 | Three redundant arguments removed; focused core confirmed | partition-correction1 provenance; closed list-builder-partition attempt1 |
| XQ-ELAB-002 | Definitional value-proof repair implemented; matching check pending | partition-correction2 provenance; same actual failed attempt |

All complete logs and native records are preserved. The measured/example
focused targets, elaborated statement inspection, full integrated candidate
check/audit, both independent final axes and immediate candidate verification
remain pending. Original base/requirements/source assessments and all earlier
records are retained. This new record accepts no component or chapter.

## Checked elaborated statements — 4 November 2026

All40 shared/example declarations and eight preserved Selection wrappers passed explicit-universe type inspection at clean4ac0e7e, inside the successful84-declaration command. Root read every corresponding source/type and recorded no concrete mismatch. Complete report and exact output identities: provenance/chapter02-three-way-partition-types-20261104/partition-root-readback.md. This is coordinator statement assessment, not final independent review or acceptance; full XQ01 scope and all gates remain.
