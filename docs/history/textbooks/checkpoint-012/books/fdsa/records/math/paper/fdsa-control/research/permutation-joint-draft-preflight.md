# XU05 stopped draft: bounded source assessment

Prepared 2026-11-02 by the retained `tail_examples_preflight` assessment agent.
This is one bounded source assessment inside the existing implementation
loop. It is **not a final Standards/Spec review**, a Maintainability review,
compilation evidence, a proof audit, or acceptance of any shared unit or
chapter. No XU05-SP defect finding was identified in the inspected scope.
That conclusion means only that this reading found no concrete source-level
mathematical, statement, connection, documentation, or checked-API defect.
It does not establish that the Lean source elaborates.

## 1. Candidate, scope and evidence identity

The coordinator supplied candidate commit
`a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`, with parent
`11923e9ffd17246b6f22c5594002a1ba0434e43c`, in
`conaled-permutation-joint`. The coordinator reports six changed files,
1007 insertions and four header deletions, a clean worktree, a passed staged
whitespace check, and no forbidden markers in its bounded inspection of the
three Lean files. The coordinator also reports that comparison against the
parent confirmed the entire prior formal body of `PermutationOrder.lean`
is byte-identical; only its imports/header and new joint section changed.
These are **coordinator-provided Git/check results**, not Git commands or
independent acceptance checks performed by this assessor.

All six source files were stopped during this assessment. Their ordinary
SHA-256 fingerprints were taken directly from their bytes and rechecked
after the reading; the identities remained unchanged:

| File under `conaled-permutation-joint/` | Bytes | SHA-256 |
| --- | ---: | --- |
| `Applications/Probability/PermutationOrder.lean` | 29717 | `8a427831a044b3c2aac2b7272648ec702d8b04da2e11a1db57521dde28a0e50c` |
| `Examples/PermutationJoint.lean` | 13379 | `51e712d2b69ea8abb930597452988d4fb02ec57b48503f30a18cb97287de3c28` |
| `Examples/PermutationJointBoundary.lean` | 11107 | `2ed11acdb8615ae5fd9696ce9c843bf93cb59821a580229753d5b45396a7526f` |
| `docs/research/fdsa-permutation-joint.md` | 10069 | `cf80730065f60325297835548c98790b14778d7db61bde84da9429c0192b4b64` |
| `docs/research/fdsa-reconstruction-map.md` | 21507 | `8583097adf4bb97611ddda8b276cd5d85d7d7c1dab5bfb31685f427daa3ac408` |
| `SquareApplications.lean` | 8464 | `556524fdf37e4237c0e086af06c97d43561b19c35886913688568ad228bdb700` |

The full core, including its existing private extension and relabeling
helpers, both full example modules, and the full new joint note were read.
Assessment of the reconstruction map is limited to its new section
“Shared joint orders on disjoint subsets (draft)”; assessment of the public
entry point is limited to its new `import Examples.PermutationJoint` and
immediate import context. Full-file hashes identify those files, not a new
assessment of their preceding content. Existing `PermutationTail` signatures
and the called value bridge were consulted for the new clients; that does
not turn this into a new review of the entire XU03 module.

The full frozen requirements and start record were read:

| Control input | Bytes | SHA-256 |
| --- | ---: | --- |
| `reviews/permutation-joint-requirements.md` | 14845 | `a80952af26c830231070feb9305f7c678277349c95861b39826edc9297486325` |
| `reviews/permutation-joint-start.md` | 4026 | `dfb23cda6e96a20b381380f49ad3e1225ff50030ae3885a3a4de0bbaf50d88df` |

Saved preparation and independent calculations were read and reused:

| Research input | Bytes | SHA-256 |
| --- | ---: | --- |
| `permutation-joint-api-preflight.md` | 21815 | `1de920cbde00e253d18bcdb98786559ea39005be05ba3a99d12e20b2c731feb4` |
| `permutation-joint-source-preflight.md` | 17807 | `83bbceb6a6f74434b80e3eec13d3bc59a8f21025ae3a93b1f387b3a8ccf86f64` |
| `permutation-joint-calculations.json` | 7281 | `a7c8be932999da48c13c7291dbd68ee013d3ab1d7da65a978a2d7c8f9463bad4` |

The already-read repository AGENTS and architectural-quality,
example-driven and domain guidance remain the applicable constraints. No
new review credit is claimed from that earlier reading. Primary Mathlib
declarations were read locally only to resolve specific source uses. The
saved API preflight identifies Mathlib pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The saved Lean list source is
identified by the preflight as commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. This assessment did not run Git
to independently re-establish either dependency identity.

## 2. Public statements and mathematical scope

The new core exposes the three required results, in the agreed argument
orders: `uniformOn_restrictedOrder_pair_eq`,
`map_restrictedOrder_pair_uniformOn`, and `hasLaw_filter_pair`. The extra
joint-specific construction and canonical law remain private. It adds no
independence predicate, new sampler, order carrier, generic action
framework, or public conditional wrapper. The unconditional core does not
import `PermutationTail`.

The scalar theorem observes
`(restrictedOrder positions A π, restrictedOrder positions B π)` for one
and the same π. It assumes fixed disjoint A and B, and gives the reciprocal
of the cast natural factorial product for supported pairs and zero for
every unsupported pair. It does not assume A or B nonempty, or that their
union covers the universe. Its public premises require the existing
DecidableEq interface, a complete Nodup positions list, and measurable
singletons on the permutation sample. It does not require a measurable
space on lists, a public Fintype/Finite instance, an order on keys, or an
inhabited key type. The complete positions list supplies local finiteness
inside the proofs.

The map theorem uses the actual paired observation and the ordinary product
of the two existing uniform order measures. It adds the caller's list
measurable-space and measurable-singleton instances, and uses the canonical
product measurable space. Separate marginal equalities are not treated as
proof of the joint product equation.

The generic theorem starts from the whole-order premise
`HasLaw Y (uniformOn (orders positions S)) μ`, for arbitrary measurable Ω
and arbitrary current μ. It has both containment premises A⊆S and B⊆S,
as well as disjointness. It concludes the law of the actual two filters of
Y under that same μ. It adds no finiteness, countability, discreteness, or
measurable-singleton premise on Ω, no uniformity premise on μ, no stronger
`Measurable Y`, and no public permutation-sample measurable structure.
Those choices retain the a.e. measurability and support boundary of HasLaw.
They do not make valid support a pointwise property of an arbitrary Y.

Containment remains mathematically necessary: a filter of a whole S-order
cannot produce a target order containing a label outside S. Fixedness also
remains substantive: the quantified A and B are not functions of the sample
or of unrevealed information. No statement widens them to adaptive subsets.

## 3. Simultaneous support transport and normalization

The proof adds an actual joint argument. From membership in the old order
supports, `exists_relabel_order_pair` obtains each component's support,
Nodup property and equal length. Disjoint A and B make both concatenated
lists Nodup. The existing finite-list extension helper then gives **one**
ambient σ mapping the two concatenations. `List.map_append` and
`List.append_inj` split that equality using the established first-component
length. This supplies both component maps and, by injective map membership,
preservation of A and B separately. No pointwise fixation of the unused
complement is asserted or needed.

`pair_fiber_mass_eq` applies the existing orientation law twice, with the
same σ and the same source transformation π ↦ π * σ.symm. The two
coordinate equalities are transported together. Injectivity of list map
and bijectivity of right multiplication identify the actual joint fibers'
encards, then their uniform source masses. The proof does not choose
independent transformations for the coordinates or introduce a product
sample at this stage.

For the supported branch of the scalar formula, the product finset of old
order supports contains every actual paired output. The existing finite
singleton-preimage sum therefore has total mass one. Equal joint fiber
masses turn that sum into the support cardinality times the selected mass.
The product cardinality and the two existing factorial cardinality results
give exactly A.card!·B.card!. Unsupported outputs have empty source fibers
by the old support theorem in one or both coordinates. No hidden
reachability or factorial sample-cardinality premise is substituted for
that normalization.

The map proof explicitly establishes probability instances for **both**
finite nonempty target order measures, and explicitly installs SFinite
instances before the product rectangle formula. This avoids relying on an
unproved product-normalization assumption. Countable singleton
extensionality is appropriate: finite I makes `List I` and its ordinary pair
countable, not generally finite. The factor singleton equations come from
the earlier actual marginal map/scalar results. The four supported versus
unsupported cases then match the new joint formula.

The ENNReal factorial calculation uses `Nat.cast_mul` and `ENNReal.mul_inv`.
Its first disjuncts respectively use positivity and finiteness of the first
factorial cast, which suffice for the two displayed side conditions. There
is no missing requirement that both factors be supplied in each disjunction.

The private canonical filter-pair law rewrites the whole-S law backward
through the old actual global projection, composes maps, and uses the two
existing nested-filter identities under A⊆S and B⊆S. The public theorem is
then the existing `HasLaw.fun_comp` applied to this canonical law and hY.
That assembly preserves the current environment and needs only its supplied
whole-observation law. It does not infer independence from old marginals.

## 4. Connected clients and consequential boundaries

All required cases appear as statements about the actual observations.
The saved small-population calculations were read without rerunning them;
their values agree with the following source statements.

| Case | Connection visible in the Lean source |
| --- | --- |
| Fin4, A={0,2}, B={1,3} | `joint_mass` uses the new universal pair formula for mass 1/4. The two 1/2 marginal statements use the old scalar formula. `joint_map` uses the new map theorem; `joint_hasLaw` is its actual HasLaw. |
| Existing IndepFun client | `orders_independent` uses `indepFun_iff_hasLaw_prodMk_prod` with the two actual old marginal HasLaws and the actual new joint HasLaw. Its source finite-measure instance follows from the explicitly established probability instance. |
| Unsupported coordinates | `[0,0]` paired with the supported right order, and `[1,1]` paired with the supported left order, each get zero through the new all-output formula. |
| Fin5 unequal proper union | A={0}, B={1,2,3} give mass 1/6 by the new scalar theorem. Separate statements show key 4 excluded and the union unequal to univ. |
| Fin4 empty/full | The empty coordinate is explicitly [] and the full coordinate is the inverse order. The selected paired output has mass 1/24 through the new formula. |
| Empty index type | The actual pair is ([],[]) with normalized mass one. The old actual whole-order map supplies `empty_whole_hasLaw`; the new generic pair-filter theorem is instantiated at S=A=B=∅ and transferred to the actual empty pair. No default key or nonempty key premise is introduced. |
| Fin3 overlap | Actual nested filters and a finite supported-full-order table identify the selected pair event with full-order first key 1. The old head law gives 1/3, while two old marginal laws give 1/2 each and their product 1/4. |

The overlap example proves the particular violation needed to prevent
dropping disjointness from the general result. It does not claim every
overlapping pair is dependent. The supported-order table is connected to
the actual full-order observation through `restrictedOrder_mem_orders` and
the nested-filter identities; it is not an unrelated arithmetic table.

The Fin5 conditional example follows the required chain:

1. `globalOrder5` is the original full restriction of the actual π.
   `global_hasLaw` comes from the old global map law.
2. `firstTwo` is its actual first-key-2 event. The old head theorem gives
   original mass 1/5, which discharges the nonzero premise for the
   conditional source probability instance.
3. `tail_hasLaw` is the old conditional-tail theorem under
   `afterTwo = law5[|firstTwo]`, with support `univ.erase 2`.
4. `conditional_pair_hasLaw` passes that exact law to the new generic
   theorem for fixed disjoint {0,1} and {3,4}, both contained in the
   remaining support. The old conditional marginal laws and this actual
   joint law also support the conditional IndepFun statement.
5. `tail_pair_eq_projection_on_event` uses the old actual value bridge
   twice for the same π. Equality is asserted on `firstTwo`, not everywhere
   under the original measure.
6. `ae_cond_of_forall_mem` lifts that equality to an a.e. equality under
   `afterTwo`. The reversed equality passed to `HasLaw.congr` has its
   required direction: the desired new observation equals the already
   known one almost everywhere. `conditional_projection_hasLaw` therefore
   concerns the original paired projections under this changed measure.
7. Both actual paired masses are obtained from their HasLaws and the
   explicitly normalized product singleton computation, giving 1/4.
   Finally `afterTwo_first_event_mass` gives mass one for the head event,
   and `environment_changed` contrasts it with the original 1/5.

The complete original positions list is retained at every call. No partial
tail is passed as a complete enumeration. There is no zero-event
conditioning escape: the selected head event's positive mass is exhibited.
The product-output helper normalizes both factors locally before using the
product rectangle identity; it does not use only a target expression with
unestablished SFinite instances.

## 5. Bounded pinned-API checks

The following concrete uncertainties were resolved by reading the local
primary declarations, in addition to the saved preflight:

| API | Assessment of the displayed use |
| --- | --- |
| `List.Nodup.append` | Takes the two Nodup proofs and List.Disjoint, matching the concatenation construction. |
| `List.append_inj` | Takes concatenation equality followed by equal first-component lengths, matching the split after `List.map_append`. |
| `Measure.prod_prod` | Has the SFinite premise on the second measure; the source has supplied probability/SFinite instances for both measures before use. Singleton products use the ordinary set-product equality. |
| `HasLaw.fun_comp` | Outer/canonical law is the receiver, inner/current law the argument, matching the generic theorem. |
| `HasLaw.congr` | Requires the desired observation equal a.e. to the known observation; the conditional projection client explicitly uses the symmetric on-event value equality. |
| `indepFun_iff_hasLaw_prodMk_prod` | Requires a finite source and the two actual marginal HasLaws; both clients have source probability instances and supply their actual joint law in the reverse implication. |
| `cond_isProbabilityMeasure`, `cond_apply_self` | Their positive/finite event premises match the explicit 1/5 head-mass arguments. |
| `ae_cond_of_forall_mem` | Accepts event measurability and equality on its members; the concrete top measurable structure supplies the former. |
| Existing XU03 head/tail/filter signatures | Their arguments, erased support, current conditional measure and pointwise bridge match the new examples' calls. |

These checks support the stated source-level connections. They do not
decide coercion elaboration, instance synthesis in the complete import
graph, tactic execution, generated proof terms, or the status of the earlier
uncompiled core on which these clients depend.

## 6. Documentation fidelity and retained limits

The new note and new reconstruction-map section describe the three actual
laws, their simultaneous relabeling mechanism, normalization, the changed
environment client, and the consequential examples accurately at source
level. Both mark the unit uncompiled and unaccepted. The new public import
reaches the main module, which imports the boundary module, so the written
example entry points are connected to the project entry point in source.

The source discussion is consistent with the saved source preflight's
identified `partition_random_permutations`/`pair_pmf` use in the AFP full
quicksort cost-distribution correspondence. It correctly distinguishes that
use of a joint law from expectation linearity, which requires no
independence. This assessor did not newly retrieve the book or AFP archive
or independently recertify all their source statements.

The docs retain the substantive future correspondences: actual partitions
and recursive execution, occurrence identity and pivot rank, strict versus
non-strict partition agreement on distinct pivot-deleted keys, further
history laws or fresh-choice coupling, and the source cost tariff. They do
not turn the book's repeated-key two-way sorter into a three-way sorter, or
identify equal payloads with distinct occurrences. They do not assert
independent global ordinal positions or raw priorities, arbitrary adaptive
subset laws, automatic product laws after mixing pivots, or independence
for overlapping treap operands. Selection's one retained branch and the
open conditional depth/Jensen/actual-work/correlated charging obligations
remain accurately limited; the note does not factor E[dZ] from E[d].

## 7. Findings and limits of this work

**Findings: none identified in this bounded source assessment.** No
XU05-SP01 or other defect ID is opened without a concrete defect. No source
change was made or silently incorporated. This is not an assertion that
there are no compilation failures or no issues discoverable by the required
independent final review axes.

Only this report was written. No compiler, Git operation, project hash
helper, gate, cache, configuration, repository source, requirements or
tracker change was performed. Ordinary SHA-256 file fingerprints were used
only to identify the inspected bytes. No new enumeration, repeated
calculation campaign, web research, or broader test campaign was run.

The candidate remains **uncompiled and unaccepted**. Focused compilation,
the required full guarded build and exhaustive audit, both independent
final review axes, and the immediate matching-candidate verification remain
the coordinator's pending gates. The underlying shared drafts and repaired
Chapter 1 retain their own pending gates. This report closes none of them,
does not activate or complete a chapter, and supplies no acceptance credit.

