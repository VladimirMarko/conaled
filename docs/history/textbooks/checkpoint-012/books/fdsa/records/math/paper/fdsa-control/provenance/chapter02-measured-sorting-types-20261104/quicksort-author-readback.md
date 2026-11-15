# Deterministic quicksort: author elaborated-statement readback

Received 4 November 2026 from retained author /root/chapter02_quicksort.
This is per-claim author statement assessment, not an independent Standards or
Spec review, full candidate audit or acceptance. Root read the complete returned
assessment. The author made no source/ref/control writes and ran no compiler.

All83 assigned declarations were read in full and compared with exact source,
original preimplementation contracts, the pinned source recurrence and Exercises
2.2/2.4, and independently fixed cases. Outcome: zero concrete findings.

## Exact evidence

Inspection candidate:1ffb61fceaf7c893e25a35339f6e1fce8531021d. Actual exit0,
45.32261590999951s, unchanged clean final HEAD. Complete log SHA256:
607eba97643a8361295857fb0777248e018534e0a7a78ed7d49760834f3ae325.

| Read file | Complete readback | SHA256 |
| --- | --- | --- |
| QuickSort-core-types.log |53/53 declarations,584/584 lines|8365c4bbcc04463466d927ace4c764d55b80798abc669509d5a0e3a987820ae2|
| QuickSortCosts-examples-types.log |30/30 declarations,406/406 lines|99ecb6fb2cd1f0591868ea93bc418801c2f2870b0646df920cb4a4f64887067a|
| Applications/Resources/QuickSort.lean |474/474 lines|e98024f6b741e1aba1fb1e38b419eee2e1acad76a8a40e669752f54775783263|
| Examples/QuickSortCosts.lean |193/193 lines|9d61ea34342e2f5d961c3d2962630f2ed853939802057dbfc2aca65ee1e9f999|

The author recomputed matching whole-log/section/source hashes. Both source
files and imported Sorting/QuickSort, Examples/QuickSort, Resources/ListCalls
and Resources/ListReversal have identical bytes at focused841413dc and1ff.

## Assumptions and actual source execution

Generic payload universe and arbitrary Boolean comparator remain. Keyed
statements retain a separate key universe. Generic laws acquire no Nodup,
payload order/equality, inhabitance, positive-length or probability premise.
Sorted exact costs allow duplicate keys; strict-descent costs retain their
explicit pairwise strict premise and decidable strict relation.

Both measured tail filters provide actual child inputs. Actual recursive child
values feed both right-associated appends. appendPivotRun costs left.length+3.
The erasure/length/exact-value laws refer to the checked first-pivot quickSortBy.
For tail size m and left-partition size l, the exact equations remain
T=T_L+T_R+4m+3, A=A_L+A_R+l+3, F=F_L+F_R+4m+l+6, and F=T+A.
Strict-left and complementary nonstrict-right source filtering is preserved.

The accumulator executes its actual right recursive result as part of the left
suffix. Its arbitrary-suffix exact law returns quickSortBy lt xs ++ suffix with
cost pair(T(lt,xs),0). There is no sorted/disjoint/length premise on the suffix.
Its cost-independence compares complete cost pairs. Only strict improvement
requires a nonempty first input; saving directions are correct.

Universal coefficients/domains remain T≤2n²+2n+1,3n≤A,2A≤n²+5n,A≤T,
T≤F≤2T,2F≤5n²+9n+2,F≤(5n²+9n+2)/2. The last quotient is Nat division,
derived from its division-free bound. All-right/all-left hypotheses have the
correct pivot orientation. Nondecreasing-with-ties and strictly descending
families remain distinct. Reversed List.range attains the full upper bound for
every n, including0. partitionMass follows the same pivot/partition recursion
with one tail-length charge; T=4*partitionMass+4*length+1 allows duplicates and
is not identified with literal two-filter predicate work or a probability law.

## Connected expectations retained

| Input | T | A | F |
| --- | ---: | ---: | ---: |
| Empty |1|0|1|
| Singleton |5|3|8|
| [0,1,2] |25|9|34|
| [2,1,0] |25|12|37|
| [2,2,2] |25|9|34|
| [1,0,2] |21|10|31|
| [2,1,2,3,0] |45|18|63|

The overlapping unsorted suffix[4,0,2] remains verbatim with pair(45,0).
Right-associated append costs5 versus7 for left association; the elaborated
operation is Resources.bind. Mixed root children[1,0] and[2,3] retain tariff19.
All-size duplicate families, structure-free tagged payloads, mixed/balanced
partition masses6/2 and generic public suffix/bound/cost-bridge uses are intact.

No concrete statement/model correspondence issue was found across all83
claims. Probability obligations, full candidate validation/audit, independent
final axes and acceptance remain pending. This post0086 receipt is preserved
in the next checkpoint;0086 truthfully recorded readback as pending.
