# Chapter 2 three-way quicksort — implementation record

## Scope, identity and current status

2026-11-04: **two closed central failures retained; explicit attached-list
decrease correction committed, awaiting recheck; unaccepted.**
Immutable author candidate: `d4208023c1c30f5f15773b1f50a4d11db0a29e2c`.
This continues C02-102 / Exercise 2.3 in the existing complete
Chapter 2 implementation/review loop. It does not create another shared unit
or acceptance workflow. All 112 current chapter obligations, the original
frozen requirements and their explicit clarification remain unchanged.

Root assigned a genuinely new source-only worktree:
`/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch02-three-way`,
on new branch `work/fdsa-ch02-three-way`, at exact XQ01 draft
`de5410286bbefd841dff50bef55c2e52d2ebbd2a`. Its direct parent and the complete
chapter review base are accepted Chapter 1
`07e480f6ec9958d4975bb90151005b84f2907614`.

The destination and branch were absent before creation. The resulting HEAD,
branch and clean status were verified, with no dependency cache or project
outputs. The old quicksort author worktree remained clean at
`df67f1cc9c0f4fb51d317ff4a2957ab047c179b9`. The complete transition is recorded
in `provenance/chapter02-three-way-start-20261104/`.

The exact XQ01 dependency at the author base is an original uncompiled draft
and remains **unaccepted**. Its presence does not supersede the exact original
foundation prefix or its acceptance gates. While this sorter was authored,
root reported a central shared-core focused pass after proof-only correction
`b3bdc12b304499bf6675a58bc1eb0992e19e3e75`, with unchanged APIs and passing
existing Selection consumers. Root expressly retained this sorter's original
base and will merge those preserved histories before its focused check. That
reported dependency progress does not compile or accept this sorter candidate.
Root owns central compilation, shared dependency corrections, public imports,
coverage/tickets, complete checks, independent reviews and acceptance. The
author may write only `Applications/Sorting/ThreeWayQuickSort.lean`,
`Examples/ThreeWayQuickSort.lean`, this handoff and dedicated provenance.
**No build or cache writes are authorized.**

## Source and readback

The pinned July 27, 2026 FDSA PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Chapter 2 is by Tobias Nipkow and Christian Sternagel. Exercise 2.3 is on
printed p. 28 / PDF p. 34; the linear-order domain is stated on p. 13.
The source PDF and current text extraction are external reading copies, not
files to add to the repository or checkpoint payload.

The complete source, API and independent case readiness reports were read,
together with `reviews/quicksort-three-way-readiness-assessment.md`, full
Chapter 2 requirements and scope clarification, the frozen XQ01 requirements
and its current 87-line shared core. The applicable repository instructions,
architectural guidance, glossary, ADR 0001/0010 and existing implementation,
review and example-driven-development instructions were read.

The actual exercise prints three filters of the **tail**: strict less,
equal and strict greater. It recursively sorts only the strict buckets and
places one held pivot before the entire equal block. The actual definition
will retain these three filters and right-associated assembly. The shared
`Sequences.Partition.partition3` instead executes two stable partition calls;
its exact filter-value theorem is a proof interface, not a cost equivalence.
The complete selector and the measured partition realization are unnecessary
dependencies and will not be imported.

## Concrete plan recorded before source

1. Define `Applications.Sorting.threeWayQuickSort` directly by the literal
   nil/cons source recurrence, on arbitrary `α : Type u` with `[LinearOrder α]`.
   Only strict-filter lists occur as recursive arguments. The equal filter is
   emitted directly after the one held pivot.
2. Prove the two recursive decreases by the ordinary filter-length bound on
   the tail, followed by the strict successor step to the whole cons input.
   Do not use `partition_strict_sizes` without its pivot-membership premise,
   and do not add that premise to the sorter.
3. Expose nil, singleton and literal source cons equations, plus a value
   equation through the existing shared partition triple. This connects the
   source execution to XQ01's existing occurrence and membership laws without
   duplicating its partition theory.
4. Prove permutation of every input using the actual two recursive outputs,
   the whole equal block and exactly one pivot. Derive multiset, length and
   support observations through ordinary existing interfaces.
5. Prove nondecreasing order separately. Recursive output membership transfers
   through permutation to the strict buckets; every middle member equals the
   pivot. Assemble the existing pairwise cons/append observations. Expose the
   existing ordinary `KeySorted id` plus permutation correctness contract,
   without a new sorting record or a stability assertion.
6. Prove the all-equal family directly through the source equation and connect
   the fixed independent examples to the public equations and correctness
   theorems. Inspect the actual body for absence of equal-bucket recursion;
   final output equality alone cannot certify that execution property.

No `Nodup`, positive-length, pivot-in-tail, finite-carrier or `Inhabited`
premise is justified for universal correctness. No arbitrary-comparator,
keyed-stability, numerical cost, probability, stack or tail-recursion claim is
part of this pure source exercise.

## Independently fixed cases and connection gap

The missing connection is the actual three-way sorter and its universal
correctness laws. No compiler failure is claimed while compilation is held.

| Input | Tail buckets, when nonempty | Expected output |
|---|---|---|
| `[]` | No pivot required | `[]` |
| `[2]` | `([],[],[])` | `[2]` |
| `[2,2,2]` | `([],[2,2],[])` | `[2,2,2]` |
| `[2,3,1,2,0,3,2,1]` | `([1,0,1],[2,2],[3,3])` | `[0,1,1,2,2,2,3,3]` |
| `[0,2,1]` | `([],[],[2,1])` | `[0,1,2]` |

The mixed strict child outputs are `[0,1,1]` and `[3,3]`; its output
multiplicities are 1, 2, 3 and 2 for values 0, 1, 2 and 3. The absent pivot
`0` is not a member of its tail `[2,1]`, whose greater bucket has length 2,
equal to the tail length but strictly below the parent length 3.

The prepared altered-root cases keep the correct strict child outputs fixed.
Dropping the pivot or equal block, or inserting a second pivot, can preserve
sortedness while losing occurrence correctness. Moving the pivot ahead of
the sorted left child preserves occurrences but violates order. If retained
as Lean witnesses, these will be labelled altered root assemblies, never
executions of a globally modified recursive sorter.

## Authored claims and static statement review

The new source module has 148 lines; its example module has 142 lines. The
complete files were read back before the candidate commit. No existing source
file was edited. The exact source reading identities remain in the start
provenance; candidate identities and the post-authoring readback are recorded
under `provenance/chapter02-three-way-draft-20261104/`.

The scoped commit is `a338b540ada6d1aa85e5c7c3adfe1edd4cea4a8c`, directly after
`de5410286bbefd841dff50bef55c2e52d2ebbd2a`. The new worktree is clean and has no
compiler/dependency output directory. The old quicksort author HEAD and clean
status were reverified unchanged. Source SHA-256 identities are:

- `Applications/Sorting/ThreeWayQuickSort.lean`:
  `36388954d5478761cb0176f947face60b5c681ceb6c19fce1d1f21c4c2445d3f`.
- `Examples/ThreeWayQuickSort.lean`:
  `0951a0f474638250912d4b6ee3084bbbf129c67c0f1527785778003ee1331d86`.

`candidate.json`, `source.diff`, `commit.log` and `diff-check.log` retain the
exact source transition; staged whitespace validation and commit both exited
0. These are source-only results. `Statements.lean` contains 36 explicit public
definition/theorem readbacks for later central execution. No compiler was run.

The actual `threeWayQuickSort` body contains exactly the three printed tail
filters, one held pivot, the entire equality-filter result and two recursive
calls, on the strict less/greater filters only. Both appends are explicitly
right-associated. The shared `partition3` is used only through its exact
value equation in the correctness proofs; the definition does not replace
the three filters with that operation or import its measured realization.

| Claim family | Statement and derivation assessment | Connected cases |
|---|---|---|
| `threeWayQuickSort_nil`, `_singleton`, `_cons`, `_cons_partition` | Actual all-input source recurrence and exact bridge to the shared triple. Tail filters, predicate directions, one pivot and untouched equal bucket match the exercise. | Generic nil/singleton, all-equal source equation, mixed root equation, absent-pivot shared equation. |
| `threeWayQuickSort_perm` | Actual recursive strict outputs are appended around the complete equal block; the shared tail permutation plus one pivot proves full occurrence preservation. Termination uses filter bounds below the whole cons length. | Mixed correctness, independent output multiplicities 1/2/3/2, all four altered-root witnesses. |
| `threeWayQuickSort_length`, `mem_threeWayQuickSort`, `_multiset`, `_support` | Derived from permutation; no switch to a weaker set-only claim. Quantification covers every finite source-domain list. | Mixed length 8, full multiset equality, present value 0 and absent value 4. |
| `threeWayQuickSort_sorted`, `_correct` | Source membership is transferred from each actual recursive output through permutation. Middle members equal the pivot; pairwise append laws assemble nondecreasing order. The ordinary contract is `KeySorted id` and permutation. | Independently sorted mixed output consumes both correctness fields through standard uniqueness; the misplaced-pivot root preserves occurrences but fails order. |
| `threeWayQuickSort_replicate` | One source unfold after the empty/successor split makes both strict children empty and returns the equality block directly. This needs no induction over an equal recursive child and makes no numerical time claim. | The fixed `[2,2,2]` example, generic `replicate n x`, right child `[3,3]`. |
| Absent-pivot example | Pivot 0 is absent from `[2,1]`; its greater bucket is length 2, below parent length 3 and not below tail length 2. The actual source equation sends that bucket to recursion. | `[0,2,1]` returns `[0,1,2]` without a pivot-in-tail premise. |

All general source declarations retain arbitrary `Type u` and `[LinearOrder α]`
only. There is no extra `Nodup`, positive length, global inhabitance, finite
carrier or pivot-membership hypothesis. The nil theorem does not manufacture
an element. The all-equal theorem's explicit element parameter is not a global
inhabitation instance. Numeric fixtures are explicitly natural-valued.

Static API inspection caught that Lean's `++` notation is left-associative,
whereas the literal source definition is explicitly right-associated. The
permutation proof now rewrites the existing shared tail-permutation grouping
with `List.append_assoc` before moving the held pivot. This preserves all
source operations and expected values and asserts no cost equality. No failed
compiler attempt is claimed for this source-level adjustment.

The independent expectations were preserved without modification. The altered
root witnesses use the proved correct child values and are explicitly labelled
local assembly variants, not executions of different recursive algorithms.
Final values alone are not used as evidence that the equality block avoids
recursion; that conclusion also relies on the complete defining-body review.

The static scan found no forbidden proof placeholders, trailing whitespace,
extra namespace terminators or imports of Selection/Resources. This is not
Lean elaboration, proof audit or independent review evidence. Explicit public
statement readback input is supplied for root's later coordinated check.

## Emitted central diagnostics and narrow decrease repair

After checkpoint 0086, root released only a correction of the defining
termination proof. Its central twelve-target attempt at immutable candidate
`5d7a479549f5acd64a9e5adb418ab48780c238ef` had emitted exactly two errors in
this module, both:

```text
error: Applications/Sorting/ThreeWayQuickSort.lean:29:12: `simp` made no progress
```

The source and examples at that central candidate exactly match original
author candidate `a338b540ada6d1aa85e5c7c3adfe1edd4cea4a8c`. The emitted log
does not display a separate generated termination-goal context. The defining
recursion supplies the strict tail filters, whose lengths are bounded by the
tail length and thus strictly below the whole cons input.

Successor `2b632a610bf15b7c248250abe9d55e0bfb710e4c`, directly after the
preserved original author candidate, deletes exactly the preliminary
`all_goals simp only [List.unattach_filter, List.unattach_attach]` line. It
retains the direct existing proof
`all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)`.
The actual algorithm, all theorem statements and hypotheses, the other
termination proofs, and all expected examples remain unchanged. No proof
restriction or validation gate changed.

The core now has 147 lines and SHA-256
`7b1d0269b645453635cf4324b5064f24609ef61621615968d047977f3d2b0e91`.
The entire 142-line example file retains SHA-256
`0951a0f474638250912d4b6ee3084bbbf129c67c0f1527785778003ee1331d86`.
The commit and staged whitespace check exited 0, and the author worktree is
clean with no dependency or compiler output directory. No local compiler ran.

`provenance/chapter02-three-way-decrease-repair-20261104/` preserves the
actual emitted excerpt in `diagnostics.partial.log`, its hash and source
identity comparisons, the one-line `source.diff`, commit/check logs and the
successor identity. Root described the attempt as live when assigning this
repair and retains responsibility for its terminal record. This repair receipt
therefore records the diagnostics as **partial** and asserts no overall exit
for that central attempt. It also does not claim the corrected successor has
compiled. The 36-statement readback input and all original case expectations
remain unchanged.

## Closed check and attached-list length normalization

Root subsequently supplied the secured terminal result for the next focused
attempt at `a113c14ec4aa02f84309087c3e080407f5f6808e`. The complete result and
log in `provenance/chapter02-three-way-focused-20261104-attempt2/` were read.
The actual exit is **1**, with elapsed time **12.898998964001294 seconds**,
unchanged final HEAD and clean final status. Its 4,198-byte closed log has
verified SHA-256
`6eba89d92d4e90675f979af1f4542136b20c9787e5f452314af114778476889d`.
Both source files at that central candidate exactly match author predecessor
`2b632a610bf15b7c248250abe9d55e0bfb710e4c`.

Removing the redundant simplification exposed the actual generated decrease
premises. The left premise printed by Lean is:

```lean
(List.filter (fun x => decide (↑x < pivot)) xs.attach).unattach.length ≤ xs.length
```

The right premise has `decide (pivot < ↑x)` in the same position. Applying
`List.length_filter_le` directly cannot match these goals because it bounds
the filtered attached list before the final `unattach` projection.

The exact pinned Lean 4.35.0 sources were inspected. `Init/Data/List/Attach.lean`
supplies `List.length_unattach` and `List.length_attach`, with implicit list
parameter `l`; `Init/Data/List/Lemmas.lean` supplies
`List.length_filter_le (p : α → Bool) (l : List α)`.
Successor `d4208023c1c30f5f15773b1f50a4d11db0a29e2c`, directly after the
preserved `2b632a610bf15b7c248250abe9d55e0bfb710e4c`, changes only the
defining `decreasing_by` block to:

```lean
  all_goals
    apply Nat.lt_succ_of_le
    rw [List.length_unattach, ← List.length_attach (l := xs)]
    exact List.length_filter_le _ _
```

Thus the existing filter bound applies to the actual attached list after
explicit length normalization. The algorithm, all public statements and
hypotheses, every other proof and the entire example file remain unchanged.
No pivot-in-tail, distinctness or positivity premise was introduced.

The core now has 150 lines and SHA-256
`7ef1adb48a9211c010c84c20c64bd01690eba11683002d8a16cc820eefaf1f0e`.
The example SHA-256 remains
`0951a0f474638250912d4b6ee3084bbbf129c67c0f1527785778003ee1331d86`.
The author worktree is clean; commit and staged whitespace validation exited
0. No local compilation or cache activity occurred. The successor is not yet
claimed to compile, and the original 36-statement readback input is unchanged.

The first twelve-target attempt's now-closed terminal result was also read and
verified, without overwriting the earlier partial diagnostic receipt. It
records exit **1**, elapsed time **290.0513030030015 seconds**, unchanged
candidate `5d7a479549f5acd64a9e5adb418ab48780c238ef` and clean status. Its
17,330-byte complete log has SHA-256
`6ff459c43eade60da3fc4a15edd26da81c71ae5767be9b1a73253f0a29faad76`.
Both failed attempts and both original source candidates remain preserved.

`provenance/chapter02-three-way-attach-decrease-repair-20261104/` records the
clean starting identity, both closed terminal/log identities, the pinned lemma
source identities, exact source diff, source readback and actual commit/check
logs. This is a narrow proof repair awaiting the next central validation.

## Validation and remaining gates

Static source and assumption review and the actual emitted compiler diagnostics
are recorded above. No successful focused or full check, proof audit or
independent review result is claimed for this sorter. Root will validate the
corrected immutable development candidate centrally. The
exact elaborated public statements and connected cases require readback before
the applicable complete check/audit, independent Standards and Spec reviews
and immediate candidate verification. Focused success will not accept XQ01,
C02-102 or the entire chapter by itself.


## Completed focused modules and full author statement readback

Latest status, 2026-11-04: **both three-way modules built successfully and all
36 authored declarations received complete elaborated statement assessment;
no concrete author findings; still unaccepted.** This later record supersedes
the earlier pending-recheck status without changing the retained failure
history or either source correction.

Root's closed six-target attempt at exact central candidate
`4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9` separately records the three-way
core built in 5.8 seconds and its examples built in 1.0 second. The enclosing
attempt exited **1**, because `Applications.Resources.DifferenceListCosts`
and `Examples.RandomQuickSort` failed. It is not an aggregate success. Its
complete log/result and native record remain in
`provenance/chapter02-variants-xd01-focused-20261104-attempt1/`; the closed
log is 19,446 bytes with SHA-256
`bd000490148fe78ad1f67dfd0f1eb38c05aa9ecd3212ea58ac038e15622947fa`.
The terminal HEAD was unchanged and the final status clean.

The subsequent combined 84-declaration explicit/universe-visible inspection
at that same central candidate exited **0** in **14.876180347000627 seconds**,
with unchanged HEAD and clean final status. Its complete 91,292-byte log has
SHA-256 `c05a5e5a0098492721b81c689383d421a24ec3d6bf2b00a7629ae18be5ad8d99`.
Both native terminal records were read. The author started no compiler.

The author read all **36 of 36** assigned declarations: **13 core** and
**23 examples**, occupying all **534 lines** of the 41,779-byte
`three-way-types.txt`. Its verified SHA-256 is
`0cfc0cbc9452e2b1dfd7eef5fe4f7022732d43cb41c1d84c308d9a145c99f70c`.
The complete 150-line core and 142-line example source were also reread and
verified byte-identical between clean author candidate
`d4208023c1c30f5f15773b1f50a4d11db0a29e2c` and the central candidate.
Their hashes remain respectively
`7ef1adb48a9211c010c84c20c64bd01690eba11683002d8a16cc820eefaf1f0e` and
`0951a0f474638250912d4b6ee3084bbbf129c67c0f1527785778003ee1331d86`.

The complete per-declaration assessment is
`provenance/chapter02-three-way-partition-types-20261104/three-way-author-readback.md`,
SHA-256 `d0e2da8af2e438391d2cfc5e6cc16346fccca6c0e672b8303631b999e602f318`.
It finds no altered universe/domain, hidden inhabitance/distinctness/positivity
or pivot-membership premise, weakened occurrence claim, changed order relation,
or changed expected case. The defining body and explicit cons equation retain
three tail filters, exactly two strict recursive calls, one held pivot, the
entire equal block and right-associated append. Termination bounds attached
filter lengths below the whole parent, with the pivot-absent case independently
showing child length 2 below parent length 3 but not below tail length 2.

The mixed output and multiplicities remain exactly
`[0,1,1,2,2,2,3,3]` and `1,2,3,2`. Generic nil/singleton/replicate cases retain
their intended quantifiers. The four concrete altered-root witnesses consume
the correct child results and distinguish occurrence preservation from order;
they are not presented as globally modified recursive algorithms. No claim
about absence of equal-bucket recursion relies only on output equality.

This is **author statement assessment**, not an independent Standards/Spec
review, full candidate check, audit or acceptance. Root separately assesses
the other 48 shared partition/legacy declarations. No numerical cost,
probability, stability, stack or tail-recursion assertion was introduced, and
all existing full-scope acceptance gates remain mandatory. Only the report and
this appended handoff section were written; source, references, builds and
caches remain untouched and held.
