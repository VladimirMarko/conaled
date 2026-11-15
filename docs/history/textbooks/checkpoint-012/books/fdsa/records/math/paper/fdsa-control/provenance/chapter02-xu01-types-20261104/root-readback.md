# XU01 complete source and elaborated-statement assessment

Recorded 2026-11-04T06:55:28.188619+00:00. Root implementation assessment; not an independent final review axis.

Exact central candidate `3fa2b59d6dcab007627af98a2f05c3a016a4c4c4`; minimal corrected source candidate `f00078bb2dbf1b8dc8d186d9728c9678f46a96b0`. Allthree Lean files match the checked source. All public statements and expected cases are unchanged from the original draft. Corrections XU01-ELAB-001–005 affect proof bodies only and all actual failures remain retained.

Thethree-target focused check exited0 in139.781127974s, complete log SHA256 `13a97628489251f92bcd75a7deb5a1d047b57fbbf2fe4744bfeb376aa3f8caf6`. The37-name inspection exited0 in166.823910829s, complete46,850-byte log SHA256 `79a9faa38a7647046be84cdd475416793e56bb2fef1f802cad1d3306413be94b`. Both native records are secured and both final HEAD/status identities match the clean requested candidate.

Root read the complete frozen scope, original three sources/private proofs, original source note/root-map delta, every correction diff, complete corrected examples and all37 actual types. The one initially truncated overlap type was separately reread in full. The mechanically checked ordered type headings match7 core,16 main-example and14 boundary declarations. No source or type mismatch was found. These are named declaration counts, not exhaustive audit counts.

| Declaration | Actual statement and source connection |
| --- | --- |
| `Applications.Probability.PermutationMinimum.minimumEvent` | Arbitrary independent index/priority universes, LE only; event retains member a and every comparison under the same sampled permutation. |
| `Applications.Probability.PermutationMinimum.mem_minimumEvent` | Exact membership iff; no measurability, finiteness, order-law or default-index premise. |
| `Applications.Probability.PermutationMinimum.minimumEvent_empty` | Empty subset event is empty for any LE priority operation. |
| `Applications.Probability.PermutationMinimum.minimumEvent_of_not_mem` | Outside-member premise makes the event empty; no comparison-only substitution. |
| `Applications.Probability.PermutationMinimum.minimumEvent_singleton` | Preorder reflexivity makes the sole singleton member a minimum on every sample. |
| `Applications.Probability.PermutationMinimum.minimumEvent_inter` | Intersection of the same member minimum in two subsets equals its minimum on their union; both membership hypotheses and DecidableEq for union remain. |
| `Applications.Probability.PermutationMinimum.uniformOn_minimumEvent` | Finite I and independently universe-polymorphic LinearOrder P; explicit permutation measurability/singletons, injective priority and a in S yield ENNReal inverse cardinality. No order/measurable structure on I, finite target, Nonempty I or public Fintype premise. |
| `Examples.PermutationMinimum.law` | One uniform measure on permutations of Fin3 with the local example measurable structure. |
| `Examples.PermutationMinimum.firstSubset` | Concrete fixed first subset {0,1}. |
| `Examples.PermutationMinimum.secondSubset` | Concrete fixed second subset {1,2}. |
| `Examples.PermutationMinimum.first_minimum_mass` | Actual same-law minimum event for shared member1 has mass1/2 in first subset. |
| `Examples.PermutationMinimum.second_minimum_mass` | Actual same-law minimum event for member1 has mass1/2 in second subset. |
| `Examples.PermutationMinimum.overlap_event` | Actual intersection under the same permutation equals the full-universe minimum event. |
| `Examples.PermutationMinimum.full_minimum_mass` | Every Fin3 candidate has full-universe minimum mass1/3. |
| `Examples.PermutationMinimum.overlap_mass` | Overlap has mass1/3 through the exact event-union bridge and public minimum law. |
| `Examples.PermutationMinimum.marginal_product` | Product of the two actual marginal masses is1/4; valid ENNReal multiplication side conditions are proved. |
| `Examples.PermutationMinimum.overlap_mass_ne_product` | Actual intersection mass differs from the actual product; no independence assumption or conclusion is introduced. |
| `Examples.PermutationMinimum.singleton_minimum_mass` | Every singleton has minimum mass1 through the public minimum theorem, retained by restricted normalization. |
| `Examples.PermutationMinimum.spacedPriority` | Concrete Fin3-to-Int priority function, with infinite target allowed. |
| `Examples.PermutationMinimum.spacedPriority_values` | Exact priority values -7,100,4 remain unchanged. |
| `Examples.PermutationMinimum.spacedPriority_injective` | Actual concrete priority function is injective; kernel-checked decide supplies the finite proof. |
| `Examples.PermutationMinimum.spacedPriority_not_monotone` | That priority function is not monotone in ordinary Fin3 index order. |
| `Examples.PermutationMinimum.spaced_minimum_mass` | Its actual second-subset member2 minimum still has mass1/2; injectivity and target order suffice. |
| `Examples.PermutationMinimumBoundary.empty_index_normalized` | Uniform measure of the empty-index permutation universe is1 because the identity sample exists. |
| `Examples.PermutationMinimumBoundary.empty_subset_event` | Concrete empty-subset minimum event is empty. |
| `Examples.PermutationMinimumBoundary.empty_subset_mass` | That event has mass0 through its exact empty-event identity. |
| `Examples.PermutationMinimumBoundary.outsider_event_empty` | Candidate0 is outside singleton{1}, so its member-minimum event is empty. |
| `Examples.PermutationMinimumBoundary.outsider_mass` | The outsider event has mass0; no reciprocal singleton law is asserted. |
| `Examples.PermutationMinimumBoundary.outsiderComparison` | Raw comparison event pi0<=pi1 is defined separately from member minimum. |
| `Examples.PermutationMinimumBoundary.outsiderComparison_eq_full_minimum` | Raw outsider comparison equals the full two-index minimum event, retaining pointwise meaning. |
| `Examples.PermutationMinimumBoundary.outsiderComparison_mass` | Its actual mass is2 inverse through the public full-subset theorem. |
| `Examples.PermutationMinimumBoundary.outsiderComparison_ne_singleton_inverse` | That mass differs from the singleton reciprocal1; the missing-member boundary is consequential. |
| `Examples.PermutationMinimumBoundary.tiedPriority` | Both indices receive constant Nat priority0. |
| `Examples.PermutationMinimumBoundary.tiedPriority_not_injective` | The tied priority assignment is not injective. |
| `Examples.PermutationMinimumBoundary.tied_event_univ` | Every candidate is a non-strict minimum on every sample under tied priorities. |
| `Examples.PermutationMinimumBoundary.tied_mass` | Both tied-member events have actual mass1. |
| `Examples.PermutationMinimumBoundary.tied_mass_ne_half` | The tied mass differs from2 inverse, exposing necessity of injectivity. |

The generic law retains independent universes, Finite indices, an arbitrary LinearOrder priority target, explicit measurability only on the sampled permutation space, injectivity and member status. Neither priority-target finiteness nor an index order/default or measurability instance appears. The empty, outsider, tied and correlated-subset cases preserve the hypotheses and same-sample boundary. The proof source still uses finite minimum coverage, pairwise disjointness and permutation-bijection invariance; it does not assume the desired mass.

Outcome: complete37-declaration implementation source/type assessment, zero new findings. Full independent Standards/Spec reviews, coherent integrated full validation/audit, immediate verification and acceptance remain pending. Source-draft prose remains historical until accurately reconciled in the final integration candidate. No chapter or shared unit is accepted by this report.
