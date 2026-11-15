# Top-down comparison implementation draft

Active Chapter 2 implementation, 4 November 2026; focused checks passed,
full chapter validation and acceptance pending.
The development worktree is conaled-ch02-top-down on work/fdsa-ch02-top-down-costs.
It retains the checked value prefix b167717 and focused-checked ordinary merge
72a0951 in c00558e6d69cdba24475e73c027ce7a003b2dc2a. Those components are not
represented as finally accepted dependencies. The original accepted chapter
review base remains 07e480f, and isolated foundation f17cc6b is unchanged.

Readiness uses the frozen Chapter2 requirements and complete source/cost plan,
the exact pinned book §2.4, accepted Measured/Growth/Sort APIs, newly checked
ListMerge run/projections, and the actual pinned Nat.clog/Real.logb/ceiling/
asymptotics interfaces. The source-style all-length induction uses actual child
lengths and the standard ceiling-halving recurrence. No new logarithm, resource
carrier, recurrence framework or payload typeclass is introduced.

The actual run binds recursively measured floor-left and right halves before
calling the existing measured merge on their returned lists. Projection keeps
only head comparisons; no second scalar sorter is executed. Independent
mathematical obligations are value erasure, exact source scalar equations,
comparison-step bound, all-length n*clog2(n), printed k*2^k and unrounded real-log
specializations, and general real O(n log n). The generic numeric bridge extends
the existing Growth interface for reuse by bottom-up/natural comparison bounds.
The printed unrounded real bound keeps its power-of-two premise; the general
constant-two bound keeps its n>=2 threshold.

Independently expected cases from the prior readiness notes are retained:
empty/singleton cost zero; floor-left ascending/descending three-element counts
2/3; the reference's concrete ceiling-left logical execution counts3/2; equal
returned values with unequal work; arbitrary payload ties in source order;
arbitrary-comparator occurrence/budget claims; empty payload type; k=0; and an
actual descending range family witnessing the asymptotic interface. The
three-element reference run is expressly bounded to that recursion tree and
proved to erase to List.mergeSort there; it is not a compiler-runtime model.

Source statement readback found no intended mathematical premise change or
admission. The initial draft identities and intended counts remain in
chapter02-top-down-costs-draft-20261104.json under provenance. The completed
focused continuation is recorded below; the existing full Chapter 2 acceptance
workflow remains mandatory. Public root, coverage,
all other source obligations and the complete cost/probability/natural operational
scope remain pending and unchanged.

## Closed focused continuation

The initial candidate 497ecb9 failed attempt 1 because the natural numeral 2
inside the real logarithm was not normalized before the ceiling proof's
linear arithmetic. C02-TOP-ELAB-001 adds only Nat.cast_ofNat normalization
in fc54ed5dc9514a7f8b04f4f3a00670b0ecc21f9d. Attempt 2 compiled both libraries,
then failed in the examples: decide rejected length propositions with free
payload variables, and one simp argument was unused. C02-TOP-ELAB-002 changes
those proof steps to simp and removes that unused argument. Both source-preserving
patches, failed exits and complete closed logs remain in provenance. No algorithm,
theorem type, premise, metric or independently expected observation changed.

Exact clean candidate 7fb7c3ed47b5b1ae6c378227928f7da7d67f1cb0 passed all three
focused targets in attempt 3 (exit 0, 51.551 seconds). The required elaborated
statement inspection of 32 declarations passed (exit 0, 59.084 seconds). Root
read the complete resulting types: raw erasure, permutation and bounds retain
arbitrary payloads/comparators; key stability carries only its explicit key
instances; the printed unrounded real bound retains the power-of-two premise;
the general constant-two bound retains n >= 2; and the asymptotic theorem
quantifies over actual exact-length input families. The independent 2/3 versus
3/2 source/reference cases, tagged payloads, empty carrier and k = 0 remain exact.

The complete recorder and native command results/logs are preserved under
chapter02-top-down-costs-focused-20261104-attempt{1,2,3}/ and
chapter02-top-down-costs-types-20261104/. Source/pin identities and all actual
results are in chapter02-top-down-costs-focused-summary.json. The unchanged
qualified native environment used one Lean thread and a private dependency tree;
no proof guard, linter, pin or profile was relaxed. Visible module-import
advisories are retained. Full Chapter 2 coverage, independent final axes,
complete candidate checking/audit and immediate verification remain pending.
