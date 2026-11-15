# FDSA-XU05 independent Spec source preparation

## Current disposition

**Blocked for approval.** This is the completed independent Spec source assessment of original candidate `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`, with fixed base and sole parent `11923e9ffd17246b6f22c5594002a1ba0434e43c`. The complete original six-path scope and all frozen requirements are retained. **No new concrete mathematical Spec finding was identified. Zero actual printed types, compiler results, full checks or audits are credited to this candidate.** The source assessment does not establish elaboration or acceptance.

Reviewer: `/root/chapter02_spec`, independent nonauthor. This continues the existing whole-book review loop and its already recorded cross-cutting exception. It does not activate a later chapter, replace another review loop or alter the accepted Chapter 1 state. Foundation terminal review remains first priority when its actual secured evidence is supplied. Checkpoint 0105 released only this new review/provenance write scope; all earlier Spec reports, XU04's separate two-header correction and the 314-name preparation assessment remain unchanged.

## Exact scope and complete reads

The immutable parent and changed-path list were checked directly. The complete diff has six paths, 1,007 insertions and four deletions in the older module description. All six complete files were read in bounded outputs, with no truncated source output credited. Exact hashes and read ranges are in the accompanying source assessment.

| Immutable candidate path | Lines | Bytes | Read scope |
|---|---:|---:|---|
| `Applications/Probability/PermutationOrder.lean` | 590 | 29,717 | Complete core, including all retained old declarations and new joint proof |
| `Examples/PermutationJoint.lean` | 290 | 13,379 | All ordinary and actual conditional examples, declarations and instances |
| `Examples/PermutationJointBoundary.lean` | 232 | 11,107 | All unequal/proper, empty and overlap cases |
| `SquareApplications.lean` | 257 | 8,464 | Complete root; sole new import is `Examples.PermutationJoint` |
| `docs/research/fdsa-permutation-joint.md` | 185 | 10,069 | Complete public mathematical and source-correspondence note |
| `docs/research/fdsa-reconstruction-map.md` | 356 | 21,507 | Complete map, including all historical scope/status text |

The complete local ticket, frozen requirements, start and candidate handoffs, draft/source/API preflights and independent calculation record were read. The frozen requirements are 277 lines, 14,845 bytes, SHA-256 `a80952af26c830231070feb9305f7c678277349c95861b39826edc9297486325`. The eight control records' exact identities and complete read boundaries are retained in the receipt. The Nov. 2 start/handoff's former workspace and acceptance state are historical records; the user's Nix waiver and accepted Chapter 1 at `07e480f6ec9958d4975bb90151005b84f2907614` remain authoritative.

All 15 governing blobs match the previously fully assessed identities: `AGENTS.md`, implementation/review-loop/code-review/heuristics, example-driven development and its worked example, architecture/domain/glossary, ADR index/0001/0010, language direction and README. The complete earlier README read is retained, together with the normal-versus-fresh acceptance reread at lines 161–248. These rules do not make a focused build into a complete candidate check, require an unnecessary fresh baseline, or revoke recorded accepted Chapter 1 evidence after workspace loss.

The old `PermutationOrder` formal body, from both option declarations through its last earlier proof, is **exactly byte-preserved**: 13,575 bytes. All 17 old public names and four private helpers remain. Outside that body, the core adds only the two relevant imports, accurate joint-law documentation, three private helpers and the three required public results. No Tail import is introduced into the core. The new Main imports Boundary; Boundary imports existing lower-level fixtures and does not import Main. The root imports Main, so the connected boundary file remains reachable through the public entrypoint.

## Frozen requirements and mathematical assessment

| Frozen requirement range | Source assessment |
|---|---|
| Lines 9–53: placement and preserved interfaces | Existing core/private helpers extended; no replacement sampler, carrier, independence wrapper, framework or new core Tail dependency; all old formal source retained |
| Lines 55–105: scalar paired source fibers | Actual pair from one permutation; fixed disjoint subsets; complete Nodup positions; exact supported factorial-product inverse and off-support zero |
| Lines 107–173: mapped product and generic HasLaw | Existing uniform order factors, canonical product measure and required normalization; generic paired filtering under the current source measure and only existing HasLaw strength |
| Lines 175–241: connected examples and boundaries | All ordinary/unsupported/unequal/proper/empty/conditional/overlap requirements represented by actual observations and public theorem applications |
| Lines 243–277: source correspondence and exclusions | Distribution versus expectation distinction, occurrences, pivot/rank/execution/tariff bridges and later conditional/algorithm obligations retained; all final gates remain pending |

### One simultaneous relabeling and the actual source fibers

The new private `exists_relabel_order_pair` uses support membership to identify the exact members of each component list. Disjointness makes both concatenations `xs ++ ys` and `xs' ++ ys'` Nodup. Their equal lengths allow the existing finite-embedding permutation extension to produce **one ambient permutation** mapping the concatenations. `List.append_inj` then yields both coordinate maps, and injective membership gives preservation of A and B separately. The proof does not choose two unrelated relabelings or require that A and B cover the ambient population.

`pair_fiber_mass_eq` applies that same relabeling to the actual global sample via right multiplication by its inverse. The existing restriction/relabeling lemma establishes both coordinates. A bijection preserves the cardinality of the actual pair event; the existing finite uniform-source formula then gives equal fiber masses. There is no assumed independence of coordinates, constructed independent redraw or unattached product sample.

`uniformOn_restrictedOrder_pair_eq` partitions the actual sample by `(orders positions A).product (orders positions B)`. Every actual observation lies in this support. The finite sum of source-fiber measures is one, all supported fibers are equal, and the product support has `A.card! * B.card!` members. This proves the advertised reciprocal product factorial. If either proposed list is unsupported, actual component support makes its paired source fiber empty. Both empty subsets and an empty index universe remain valid: the order support is a singleton, not an empty probability support.

The scalar source signature adds no public `Finite`/`Fintype`, ordered/inhabited/nonempty index assumption, nonempty subset premise, population-cover premise or measurable structure on lists. Completeness of `positions` supplies the finite index instance locally. Its actual printed signature still requires inspection after compilation; source binders are not substituted for that gate.

### Product map and generic observed-order transport

`map_restrictedOrder_pair_uniformOn` proves an equality for the **actual paired pushforward**. It installs probability measures on each existing finite nonempty order support and explicitly supplies the factors' `SFinite` instances before product evaluation. This matters because the pinned `Measure.prod` uses a fallback value when the second factor is not s-finite. The proof therefore does not obtain a spurious product conclusion through that fallback.

Completeness gives finite indices and hence countable list outputs. The proof uses countable singleton extensionality on pairs of lists; it does not assume that all lists over a finite index type form a finite type. It uses the canonical product measurable space and the existing product singleton class. The scalar formula, old marginal pushforward and the finite factorial casts give the singleton equality. The `ENNReal.mul_inv` side conditions are discharged from the first factorial's positivity and finite Nat cast. Unsupported pairs evaluate to zero on both sides.

The private canonical filter-pair law first composes the old whole-order map with actual filtering. The existing subset-filter equations reduce both components to the corresponding restrictions of the same permutation. The temporary discrete permutation measurable space is entirely local to that canonical proof.

The final `hasLaw_filter_pair` quantifies over an arbitrary measurable source Ω and arbitrary current measure μ, given an observation Y with the stated whole-order `HasLaw`. It requires only fixed A and B contained in S and disjoint. Composition uses the pinned `HasLaw.fun_comp`, retaining μ and the original almost-everywhere measurability strength. It adds no finite/discrete/singleton-measurable Ω, stronger `Measurable Y`, explicitly uniform μ, public permutation measurable structure or independent-coordinate premise. The target's probability law can imply source normalization through HasLaw, but this is not inserted as an unnecessary extra public premise.

## Connected examples and consequential boundaries

| Case | Actual observation and public connection | Exact expected result |
|---|---|---|
| Fin 4, A={0,2}, B={1,3} | Two restrictions of the same permutation; new scalar/map/HasLaw results plus actual marginal laws and Mathlib's existing `IndepFun` characterization | Joint mass 1/4, each marginal 1/2, independence under the same law |
| Malformed left or right output | Repeated output in one coordinate is outside that actual order support | Joint mass 0 for either malformed coordinate |
| Fin 5, A={0}, B={1,2,3} | Unequal subsets with key 4 outside their union, instantiated in the generic scalar theorem | Supported pair mass 1/6; explicit disjointness and proper-union facts |
| Empty/full on Fin 4 | Actual pair `([], positions.map π.symm)` | Specified full-order pair mass 1/24 |
| Empty index universe | Identity permutation remains an actual sample; actual pair is `([],[])`; generic whole-order and filter-pair HasLaw instantiated | Source normalization and pair mass both 1 |
| Fin 5 after the actual first-key-2 event | Existing conditional-tail theorem feeds the new generic pair law on the actual tail; disjoint remaining subsets {0,1} and {3,4} | Original event mass 1/5, conditional event mass 1, actual conditional pair mass 1/4 |
| Original projections on that conditional event | Existing Tail value bridge identifies both tail filters with restrictions of the original same permutation on the event; `ae_cond_of_forall_mem` and `HasLaw.congr` transfer that observation | Original projection pair has the same conditional product law and mass 1/4 |
| Overlap on Fin 3 | Actual pair `[1,0]` on {0,1} and `[1,2]` on {1,2} equals the actual full-order first-key-1 event | Joint mass 1/3 versus marginal product 1/4, with explicit inequality |

The exact finite expectations agree with the preserved independent calculation record. For the four-key disjoint pair, each of four supported pairs has six interleavings among 24 whole orders. The unequal five-key case has 20 samples per supported pair among 120. In the conditional example, 24 of 120 samples have first key 2, and each supported pair has six of those 24 samples. The original event-and-pair mass 1/20 is a retained calculation; the source's explicit output theorems claim the conditional mass 1/4. The overlapping event has precisely the two full orders `[1,0,2]` and `[1,2,0]`, giving two of six samples; each marginal has three of six.

These are connected probability claims, not isolated arithmetic values. The conditional environment changes: its mass on the actual conditioning event is one rather than one fifth. Equality to the original projection pair is asserted on that event and then almost everywhere under the conditioned measure, not globally under the old source. The overlap example disproves an unrestricted product-law conclusion; it does not assert that every overlapping pair must be dependent.

The full immutable Main, Boundary and inherited fixture source was read, including all private proofs and anonymous instances. The recorded small-sample calculation campaign was not rerun, and no compiler was called. Direct `decide` reductions involving `orders`/permutations, ENNReal coercions, local-instance elaboration and tactics remain actual compilation obligations, not observed new failures of this uncompiled XU05 candidate.

## Exact APIs and inherited inputs

The candidate pins `leanprover/lean4:v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; all three project pin/configuration files match the earlier retained identities. The supplied official native kit pairs Lean 4.35.0 with its matching Lake; this source review executes neither binary. The new API reads used immutable Mathlib blobs at that exact commit. The specific source ranges and full-file hashes are in the receipt; no unviewed gap is described as read.

The assessed pinned inputs include `List.Nodup.append`, `Equiv.Perm.exists_extending_pair`, Finset product membership/cardinality, finite preimage-fiber summation, countable singleton measure extensionality, product definition/evaluation/normalization, `Measure.map_apply` and `map_map`, `HasLaw`'s actual structure/composition/congruence/measure/independence interfaces, list countability, local `Fintype.ofList`, canonical product measurable structures, `ENNReal.mul_inv` and conditional self-mass. Earlier exact source reads of UniformOn, conditional probability, measurable-of-countable/finite, inverse/cancellation and set cardinality APIs are retained after full-file hash matching.

The installed official Lean 4.35.0 source for `Init/Data/List/Lemmas.lean` was read at lines 1–45 and 1658–1701. Its SHA-256 is `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb`. The actual `append_inj` signature takes concatenation equality and equality of the first component lengths and returns both equalities, matching the new proof. This was a source read only, not execution or qualification of generated outputs.

The three formal roots have nine exact local source inputs and 20 direct external imports. All local inputs were completely assessed, with exact retained complete reads for the old Minimum and Tail cores and complete new reads of the four inherited example files. The six inherited input files remain byte-identical to the XU05 base, which is the original XU04 candidate. Each differs from its later Chapter 2 version. The old Order formal body also preserves the earlier correction debt. Thus no later C2 compiler pass or actual-type result is transferred here.

The retained corrections include the old core's explicit Sublist spelling, local finite/instance and filter/map proof repairs; old examples' corresponding Sublist spelling, theorem-backed support/permutation reasoning, conditional rewrite and inverse/cast/numerical simplifications; and Minimum examples' injection/normalization proof repairs. The complete old-versus-C2 example diffs were read. The original old Order/Minimum/Tail diffs are retained only through their exact earlier read identities. The older unelaborated Sublist notation is not claimed to have a verified equivalent elaborated type. Any incorporated successor must account explicitly for the corrected dependencies and preserve this whole original XU05 scope.

## Public, private and anonymous declaration inventory

| Source | Public theorems | Public definitions | Named local instances | Explicit public total | Private theorems | Anonymous local instances |
|---|---:|---:|---:|---:|---:|---:|
| Complete Order core | 18 | 2 | 0 | 20 | 7 | 0 |
| Main examples | 24 | 12 | 3 | 39 | 2 | 8 |
| Boundary examples | 20 | 15 | 0 | 35 | 4 | 10 |
| **Complete three-file total** | **62** | **29** | **3** | **94** | **13** | **18** |

Seventeen core public names are retained old declarations: 15 theorems and two definitions. The **new unit surface is 77 explicit public names**: the three new public core theorems plus 74 new example names, comprising 47 theorems, 27 definitions and three named local instances. There are three new private core helpers and six private example theorems, together with four retained old private helpers. There are no anonymous `example` commands, new structures/inductives or generated-constructor surface in these three files.

The named local instances are `Examples.PermutationJoint.law_isProbabilityMeasure`, `law5_isProbabilityMeasure` and `afterTwo_isProbabilityMeasure`. Their probability claims matter for the independence and conditional examples. All 125 authored declaration/instance rows carry exact path, line, visibility, namespace/name, header and source identities in the receipt. All five HasLaw declarations using `where` end their recorded header before that delimiter; no first proof-field prefix is included. This incorporates the lesson from XU04's separately preserved metadata correction without changing that prior report.

These are source inventories, not printed-type or kernel declaration counts. All 94 public names of the complete changed files must be accounted for by actual inspection or explicitly qualified exact reuse at the eventual candidate; the 77-name added surface is not permission to drop the 17 retained names, old cases, private proofs or anonymous instances from compilation/audit/review scope. No current name or count is added to Chapter 2's 1,763-name account, Foundation's pending 145, or potential 110-name reuse.

## Book correspondence and historical status

The pinned book text was read at literal-newline lines 734–774, §2.3 on printed page 16, with file SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The PDF identity is retained as `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. The actual source uses the first pivot and two filters with equal payloads in the second branch. It states both average-input and fresh randomized-pivot mean claims and refers their probabilistic analyses elsewhere. This source preparation changes neither model and does not mark either chapter obligation discharged.

The complete frozen source preflight and the 28-line pinned AFP retrieval record were read. Their attributed bounded primary-source assessment identifies the actual joint partition step in `Quick_Sort_Average_Case.thy`, its uniform-head/remaining-order decomposition and distribution correspondence, plus the separate occurrence-index randomized sorter and cost law. The original AFP theories were not available as an exact supplied seed for a fresh read in this continuation. This report therefore retains the attributed inspection and immutable archive/theory hashes; it does **not** claim a new full theory read, retrieval or Isabelle rebuild. No AFP proof is a Lean dependency, and no concrete unresolved correspondence claim was found that requires inventing a general new external-proof review gate.

The new pair law supplies a fixed-disjoint-partition ingredient for that distribution route. For sums of expected costs, correct conditional marginals and linearity suffice; independence is not added as a mathematical requirement of the book's mean result. Algorithm clients still need actual occurrence-to-payload, pivot-index/rank/deletion, strict versus reflexive partition, recursive execution/coupling and source cost-tariff bridges. Repeated payloads can collapse occurrence observations, and the source two-way repeated-key behavior remains distinct from a three-way variant. The theorem does not make adaptive sets independent, turn pivot mixtures into product laws, prove independence of global ranks/raw priorities, settle selection work, or justify treap conditional depth/Jensen/correlated weighted charging.

The public note's final line 185 says repaired Chapter 1 and the earlier shared base keep pending gates. This is historical Nov. 2 draft status, as explicitly dated in the original handoff. The sentence should be dated or updated when incorporated into a current development note so readers cannot interpret it as reopening accepted Chapter 1. It is retained here as documentary incorporation debt, not a mathematical finding, a new Chapter 1 gate or a mutation of the frozen candidate. The pending gates applicable to XU05 and its unaccepted predecessor inputs remain intact.

## Findings and remaining approval conditions

**New concrete mathematical Spec findings: none in the completed full original scope.** Inherited corrections and historical documentary state are explicitly accounted for above. No missing type, compile or audit evidence is treated as a mathematical proof, and no current source assessment closes an acceptance gate.

Approval remains Blocked until the exact incorporated candidate has qualified successful compilation; complete actual public-type inspection and independent full-scope assessment; the applicable full normal/fresh candidate check and exhaustive audit with secured terminal log, actual exit and matching immutable verification evidence; and both complete independent final review axes with findings resolved. The unchanged proof restrictions and allowed axiom policy apply. Immediate qualified `./check.sh --verify-candidate HEAD` remains mandatory immediately before any accepted local fast-forward.

The accepted Chapter 1 state and all earlier Foundation/C2/XP01/XR01/XW01/XU04 review dispositions remain unchanged. Foundation's exact 145-name inspection and potential 110-name reuse remain separate and uncredited in this report. No terminal result is inferred from its still-live execution. This reviewer performed no compiler, process poll, source/ref/cache/output change, chapter activation or external communication.
