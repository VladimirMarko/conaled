# Natural-sort compiler correction 1

This continues the existing full natural-sort implementation/review scope.
The first central focused attempt was at immutable
`e2db54211dfe3b2efd76904f1797a9460567ebbc` and closed with actual exit 1 in
27.319240105000063 seconds, with unchanged clean HEAD. Its complete 11,989-byte
log has SHA-256 `057996ba9c497d0821e21cb47efad8b7eda3a2a8db26b7f112259adf77e0983f`.
Both full.log and result.json were read; start.json retains the exact result
and its hash. Applications.Sorting.Natural built successfully in that failed
combined command. The other natural modules have no successful result from
that attempt; dependent examples were not established. XD01 errors in that
same log remain root-owned and are not edited here.

## Findings and exact bounded fixes

| Finding | Actual diagnostic | Correction and preserved contract |
| --- | --- | --- |
| C02-NAT-ELAB-001 | Examples/NaturalSorting.lean:36: simplification retained the keyed sortNaturalOn lhs while the goal used sortNaturalBy. | Expose the definitionally equal keyed goal with change, then keep the existing strict-descending specialization and reverse simplification. The same [2,1,0] -> [0,1,2] case and public theorem remain. |
| C02-NAT-ELAB-002 | Examples/NaturalSorting.lean:131: simplification leaves arbitrary List.Pairwise True. | Apply the existing List.pairwise_of_forall with the actual reflexive Nat key relation. The theorem still quantifies over every List α without payload instances or extra assumptions. |
| C02-NAT-ELAB-003 | Examples/NaturalSorting.lean:138: explicit lambda binders do not match Pairwise.imp's implicit element arguments. | Supply only the relation proof binder to Nat.le_of_lt. The range family, argument n and exact fixed-point assertion remain unchanged. |
| C02-NAT-ELAB-004 | Applications/Resources/NaturalSorting.lean:235: unannotated first Big-O function inferred a Real index, conflicting with inputs : Nat -> List α. | Annotate only that first function index as Nat, as required by the frozen length-indexed family. The lower bound, assumptions, atTop filter and inverse Big-O conclusion are unchanged in intent. |

The line-253 uses-sorry message is downstream compiler recovery from the
malformed declaration, not an admission added to source. It is retained in
the failed log and must disappear in actual recompilation; no successful
resolution is claimed now. No admission, new axiom, unsafe/partial definition,
compiler bypass, linter suppression or option change was introduced.

## Complete source/diff readback

Both corrected files were read from beginning to end (22 example declarations
and 37 resource declarations). The complete four-hunk source.diff was read.
All 105 declarations in the original four-file static assessment were compared:
104 source statements are byte-identical; the sole header change explicitly
annotates the intended natural index. The three other edits affect only proof
bodies. The two other assigned source files remain byte-identical, including
all expected comparison totals and dependent cost examples. The complete
per-declaration comparison is declaration-readback.json, with full old/new
statements and retained intended assessments for the four affected claims.

The pinned Lean 4.35.0 Init/Data/List/Pairwise.lean source was inspected directly:
Pairwise.imp accepts implicit elements followed by one relation proof;
pairwise_of_forall accepts the all-elements relation. These are existing laws,
not a new helper framework. This assessment is source-level; explicit compiled
statement inspection and all candidate gates remain pending.

Only Applications/Resources/NaturalSorting.lean and Examples/NaturalSorting.lean
are changed. No algorithms, domains, hypotheses, numeric expectations,
comparison tariff, imports, options, public integration files or dependencies
are changed. The new operational preparation remains a plan and is not
implemented. No compiler/cache operation ran in the author worktree.

## Next gate

Commit the bounded source correction after parent
`9c5858d0feb56b42701ab1f84e5d9265b953cfea`, preserve exact source identities,
then HOLD for root's qualified immutable candidate build. Do not infer success
from this static readback or from the previously built pure core. Full audit,
independent Standards/Spec review and immediate verification remain mandatory.
