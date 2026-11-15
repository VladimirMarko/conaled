# Chapter 2 ordinary sorter uniqueness — implementation handoff

Recorded 4 November 2026. This continues the existing full Chapter 2 implementation/review loop. It does not start another review hierarchy or confer acceptance.

## Authorization and frozen scope before source edits

Root assigned the concrete C02-090 gap identified by the complete 112-row reconciliation at dfaf68114d1dda4e15628c94c3d988c3f5457c49. The assignment authorizes alignment of the held clean source-only worktree to the exact incorporated/checked development base, followed by two new modules, their source/per-claim assessment, a scoped local commit and a hold. Compilation, public-root integration, final coverage mapping, independent review and all acceptance gates remain root-owned.

The required result is pointwise and function equality for arbitrary ordinary correct sorters, using only the actually sufficient antisymmetry assumption. Reuse List.Perm.eq_of_pairwise' and the existing Pairwise/Perm/multiset interfaces. Preserve the source multiset correspondence. Do not add stability, totality, decidable equality, a default payload, a new sorting carrier, an alternate sorting algorithm or a cost claim. Include a small connected case set demonstrating actual sorters and the relevant weak-order/keyed boundaries. Keep C02-089/091 dispositions in this handoff for later source-map integration.

Only the following source paths are owned:

- Applications/Sorting/Uniqueness.lean
- Examples/SortUniqueness.lean

Dedicated evidence is confined to this handoff and provenance/chapter02-uniqueness-author-draft-20261104/. No public imports, reconstruction map, global controls, tickets, other worktrees, dependencies or caches may be changed. No compiler, child agents, GitHub mutations or push are authorized here.

### Source and requirements identity

| Input | Frozen identity |
| --- | --- |
| Whole chapter accepted/review base | 07e480f6ec9958d4975bb90151005b84f2907614 |
| This component's incorporated development base | 0ec9954479b081664bd4504c90fb66fba5fd22c8 |
| Previous preserved three-way author HEAD | d4208023c1c30f5f15773b1f50a4d11db0a29e2c |
| Book | July 27, 2026 edition, §2.7 printed pp.25–26; PDF SHA-256 9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645 |
| Chapter extraction | SHA-256 6ce61b4bd1af76ec56bf4007be27f41c4c2bda12853292cc8d48cf3f1bd22cd4 |
| Full frozen chapter requirements | reviews/chapter02-requirements.md; SHA-256 f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36 |
| Current 112-obligation inventory | research/chapter02-obligations.md; SHA-256 a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2 |
| Frozen reuse plan | research/chapter02-reuse-plan.md; SHA-256 ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a |
| Concrete gap record | provenance/chapter02-completeness-reconciliation-20261104/report.md; SHA-256 dba195724f672c38f4fc178d754ce9401878640e5fd2e1145645ecd4a824dc8b |

The source Corollary 2.10 gives two universal sortedness-and-multiset specifications and concludes equality at every input, equivalently function equality. Theorem 2.9 is the underlying ordinary list uniqueness theorem. The order-prose correction is preserved: totality is not needed once both outputs are pairwise sorted and the relation is antisymmetric.

AGENTS.md, implement and example-driven-development skills, the shared review loop, architecture/domain instructions, glossary, ADR 0001/0010 and README environment/build/audit rules were read. The user's existing Nix waiver remains in force; exact Lean/Lake/dependency pins and proof restrictions are unchanged. This task launches no environment command or builder.

## Exact development alignment

The starting worktree conaled-ch02-three-way was clean at the expected d4208023 HEAD on work/fdsa-ch02-three-way. A read-only ancestor check confirmed that this HEAD is an ancestor of 0ec9954. The authorized git merge --ff-only used per-command ChatGPT / chatgpt@openai.com identity and exited 0. The resulting HEAD is exactly 0ec9954479b081664bd4504c90fb66fba5fd22c8, with clean index/worktree and no conflict.

The complete command, before/after identities and actual output are in provenance/chapter02-uniqueness-author-draft-20261104/alignment.json, SHA-256 a9d852ee015d9d0c18748c925b1206638e586de8511e38dd067f4e0ec218adaa. All earlier author commits remain in history. This development alignment does not change the full Chapter 2 review base or accept the pending foundation dependency.

## Planned API and independent expectations

The new library module is the assigned canonical destination: the existing Stable module has keyed stable uniqueness, while this corollary concerns arbitrary ordinary functions. Import the canonical List.Sort and Multiset.Defs APIs directly. Use the existing conjunction of Pairwise and Perm, without another specification structure.

| Planned declaration | Intended contract and proof connection |
| --- | --- |
| Applications.Sorting.sorters_eq_at | For arbitrary f, g and a single input xs, pairwise order and permutation to xs for each result imply f xs = g xs. Only Std.Antisymm r. This local form permits genuinely partially ordered admissible input domains; it does not assume that a sorter exists for every input. Apply List.Perm.eq_of_pairwise' directly to the two result observations. |
| Applications.Sorting.sorters_eq | Universal ordinary correctness of arbitrary f and g gives f = g. Apply sorters_eq_at at every input, then funext. No equality of algorithms, costs or execution traces is claimed. |
| Applications.Sorting.sorters_eq_of_multiset | The literal source universal Pairwise-plus-multiset specifications imply f = g. Convert each input's multiset equality with Multiset.coe_eq_coe, then use sorters_eq. Pointwise source equality follows by congrFun. |

| Planned case | Independent mathematical expectation and connection |
| --- | --- |
| First-pivot versus floor-left source sorting | Both are independently correct ordinary sorters for a LinearOrder element type, so the new universal theorem identifies their output functions. The algorithms and costs remain different. |
| Three-way versus floor-left source sorting | Use the three-way public multiset theorem and the floor sorter's public occurrence contract with the new literal multiset interface, preserving duplicates. |
| Existing mixed duplicate fixture | Transfer the already independently checked three-way output for [2,3,1,2,0,3,2,1] to floor-left sorting via the new function equality. Expected output remains [0,1,1,2,2,2,3,3]. No new independent concrete sorting computation is needed. |
| Non-total equality relation | A list pairwise related by equality consists of equal elements, so reversal equals the original list. Apply the new local theorem to identity/reverse, with actual sortedness and permutation proofs. The generic payload type needs no instances. Equality on Bool is antisymmetric and not total, guarding the book's incorrect totality prose without claiming that every Bool list can be sorted by equality. |
| Constant-key ordinary correctness without payload antisymmetry | Identity and reversal on List Bool both preserve every occurrence and have constant sorted keys for every input, yet differ on [false,true]; reversal is not stable on that input. This gives satisfiable universal ordinary keyed contracts while exposing why element-level antisymmetry cannot be inferred from key antisymmetry. |

These expectations were recorded before source writing. The gap is the missing general theorem/client connection, not a manufactured compiler failure. Existing standard lemmas and checked component cases already suffice for its underlying mathematics.

## C02-089 and C02-091 dispositions for later root integration

- C02-089 reuses List.Perm.eq_of_pairwise' in the pinned Mathlib/Data/List/Sort.lean. It assumes Std.Antisymm of the observed element relation. Multiset.coe_eq_coe in Mathlib/Data/Multiset/Defs.lean gives the source multiset conversion. Do not duplicate that list theorem or replace it with the stronger keyed StableSort.unique contract.
- C02-091's (2.33)/(2.34) are proof premises in the source induction establishing list uniqueness. They are accounted for by that reused proof, not by new independent algorithm hypotheses or redundant public declarations.
- The existing sorted_permutation_not_stable distinction is preserved. The new constant-key case will connect the boundary directly to universal function specifications.
- No part of C02-024, C02-088/C02-111/C02-112, probability, cost accounting, public coverage or whole-chapter acceptance is weakened or closed by this bounded addition.

## Validation state before authoring

No new Lean/Lake invocation, checker, proof audit, type inspection or dependency/cache operation has run. Source writing and static statement assessment are authorized; root will compile the exact committed candidate centrally. Until that result, all new proof scripts are uncompiled development.

## Completed source and per-claim assessment

Both new files were read from beginning to end, including every proof. The source contains exactly three library theorems and six example theorems. The actual declaration headers, exact source identities and per-claim assessments are retained in provenance/chapter02-uniqueness-author-draft-20261104/source-assessment.json (SHA-256 6d27309d1b1e4f505f7a982261c681d0b59f3102fcac9e5a5a7307dcea9b7e55).

| Actual declaration | Statement review and consequential connection |
| --- | --- |
| Applications.Sorting.sorters_eq_at | Type u and arbitrary Prop relation/functions/input; only Std.Antisymm. Both observations concern actual outputs, and the composed permutation has the right direction. Standard uniqueness is called directly. The theorem is usable on a locally admissible input even if no global sorter exists for that relation. |
| Applications.Sorting.sorters_eq | Universal contracts precede function equality; funext consumes the preceding pointwise theorem. No stability, totality, transitivity, decidability, payload equality/default, cost or trace premise/conclusion is added. |
| Applications.Sorting.sorters_eq_of_multiset | Full source multiset equality converts with Multiset.coe_eq_coe. Permutation and multiplicities are preserved; this is not set or length equality. The exact source pointwise form is obtained by congrFun. |
| Examples.SortUniqueness.first_pivot_eq_floor | The actual first-pivot and floor-left algorithms independently discharge all-input correctness under LinearOrder elements. The generic new function theorem is used, not an existing selected-algorithm equality. |
| Examples.SortUniqueness.three_way_eq_floor | The literal multiset interface compares the actual three-filter sorter and floor-left sorter, retaining duplicates without Nodup. Their public occurrence facts supply the source hypotheses. |
| Examples.SortUniqueness.floor_mixed_duplicates | Applies the new function equality and the preserved ThreeWayQuickSort.mixed_value to the eight-element fixture. The fixed expected output and multiplicities are unchanged. |
| Examples.SortUniqueness.reverse_eq_of_equal | Arbitrary payload type without instances; equality is used as the relation. Actual reversal sortedness and reverse_perm discharge the local public theorem. Local antisymmetry uses ordinary let, respecting root's pinned haveILetI linter finding without suppressing it. |
| Examples.SortUniqueness.equality_order_boundary | Bool equality is antisymmetric/non-total. A nonempty repeated-value input establishes the pointwise theorem's premise and consumes it. This exposes the source prose correction without implying that equality sorts every mixed Bool input. |
| Examples.SortUniqueness.constant_key_boundary | Both identity and reverse have satisfiable universal ordinary constant-key contracts. They differ on [false,true], and reversal fails the exact key-zero stability observation. Key antisymmetry is not smuggled into the record relation. |

Static source findings: none identified. This assessment does not claim elaboration success. No compiler failure has been invented, and no compiler run has occurred. There are no admissions, application axioms, unsafe/partial definitions, native-evaluation shortcuts, linter suppressions or option relaxations in the new source. The core imports the canonical Mathlib sorting/multiset interfaces; the examples import the already retained source algorithms and mixed-value fixture. No existing algorithm or proof is edited.

## Committed uncompiled candidate and hold

The scoped local commit is **3b727e83fcf9f00ad7d0c95d07305b036ebecbca**, directly after the fixed component base **0ec9954479b081664bd4504c90fb66fba5fd22c8**. Subject: feat(sorting): prove ordinary sorter extensionality (#174). The command used per-command ChatGPT / chatgpt@openai.com identity and exited 0. Only the two owned new source files are included; the diff has 131 inserted lines. The index and working tree are clean.

| Committed source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| Applications/Sorting/Uniqueness.lean | 44 | 1,999 | e0df544f59be358a3e40ad48f25115ae2ba3b4507a30cdeb3425907bf94c8744 |
| Examples/SortUniqueness.lean | 87 | 3,903 | ce63cd0d8a953f9441b9b6b1597f9a3604ef736131290cba8c0430c36cd177b7 |

The exact source.diff has SHA-256 18e5d73b16032b0a7936c01c68bd4c8572e9b2584d99ca5193602dd9e511b843. The result.json in the dedicated provenance retains the commit command, terminal output, parent, source inventory, static assessment digest and clean status. The staged whitespace check exited 0. No compiler result, elaborated-type success or audit result exists for these new modules yet.

Root requested checkpoint 0089 while this small candidate was being completed. All source/ref/control writes are now held after this coherent commit and handoff. No Lean/Lake process was started by this assignment, and no dependency/cache operation ran. The intended next central targets are Applications.Sorting.Uniqueness and Examples.SortUniqueness, followed by the nine-declaration elaborated readback and the existing whole-chapter review/validation process. This does not close C02-090 or any acceptance gate before those checks.
