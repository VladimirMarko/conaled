# Shared binary-tree rotations: bounded source preflight

Prepared 2026-11-02 by the source-assessment agent for the existing whole-FDSA
implementation effort. This is source preparation under the user's cross-cutting
exception, not chapter activation, implementation, compilation, independent final
review or acceptance. Chapter 1 remains the active sequential chapter; its sole
full guarded check is owned by root at candidate
`07e480f6ec9958d4975bb90151005b84f2907614`.

The assessment was completed read-only, then preserved in this one new file under
root's explicit authorization. No existing report, requirement, inventory, source,
Git ref, cache or validation state was changed. No compiler, checker or project
hash helper ran. Ordinary SHA-256 was used only to verify source identities.

## Recommendation

A small shared root-rotation component is justified by the pinned source.
Chapters 5, 9 and 21 use the same two ordinary binary-tree rearrangements. The
useful shared content is exact inorder preservation, legal-domain inverse laws,
label-map compatibility, and consequent node/leaf-count observations. A cache-aware
specialization can reuse XT01's smart constructors while recomputing the changed
nodes.

This can remain a bounded cross-cutting unit. It need not implement positioned
schedules, listification, AVL rebalancing, splaying, a search-tree interface, or a
new tree carrier. It is not a prerequisite to the existing minimal Chapter 2
foundation integration.

The applicable AGENTS, domain, architectural-quality, glossary and ADR 0001/0010
guidance were read. Operations, semantic laws, representation/cache validity and
resource observations must remain distinct.

## Exact primary-source connections

The notation below uses the book's constructor order N(l,a,r). Lean's existing
BinaryTree.node takes the label first.

| Source | Exact connection to a shared unit | Boundary to preserve |
| --- | --- | --- |
| Chapter 5, p.67; definitions p.70 | Right rotation sends N(N(A,a,B),b,C) to N(A,a,N(B,b,C)); left rotation reverses this rearrangement. The p.67 introduction identifies preservation of inorder as the common balancing mechanism. | These are partial shape patterns in the HOL source. Neither definition gives a meaningful unmatched-case result. Use explicit failure or an explicit legal domain. |
| Chapter 5, pp.69–70 | apply_at and apply_ats lift a transformation to positions and sequential schedules. They give future consumers of the root laws. | Schedule legality depends on the current tree after each preceding operation. A small root unit need not implement this later machinery now. |
| Chapter 9, pp.105,108–110 | Height-cached AVL nodes use ht and the smart constructor node. The single-rotation branches of balL and balR are exactly the two shared rearrangements with two smart reconstructions. | Correct cache values and AVL balance are separate from inorder preservation. The source's balance/height theorems require actual AVL hypotheses. |
| Chapter 9, p.114 | The balance-factor variant performs the same underlying rearrangements but assigns specific new tags; rot2 handles the middle-node cases of a double rotation. | Do not inherit the height-cache variant's unconditional raw-domain guarantees: malformed tags can demand a missing child. |
| Chapter 21, pp.245–246 | Zig-zig composes two root right rotations. Zig-zag performs a left rotation in the left child followed by a right root rotation; mirrored forms handle the other side. | The p.246 question distinguishes root-only composition from composition at positions. Both diagrams use ordinary rotations once positions are allowed. The shared unit does not prove splay termination or access bounds. |
| Chapter 10's advertised AVL join instance; pinned AFP support | joinR and joinL in StronglyJoinableAVL.thy reuse balR and balL. This supplies another concrete consumer through the Chapter 9 specialization. | The supporting AFP snapshot postdates the book. Its generated time model gives these nonrecursive helpers zero cost; it is not a machine-cost or XT01-tariff theorem. |

### Exact companion locations

All file paths below are relative to the task workspace's book-source directory.
Line numbers identify the unchanged local pinned copies inspected in this pass.

- Tree_Rotations.thy: rotR at line78, rotL at81, apply_at at84, apply_ats at89,
  apply_ats_append at93, and apply_ats_map_R at100. Later schedule results are
  inorder_rotRs_poss at103, rot_id at133 and tree_to_tree_rotations at138.
- AVL_Set_Code.thy: cached node at line25, balL at28, balR at39, and the
  unconditional inorder_balL / inorder_balR at80/84.
- AVL_Set.thy: ht_height at line21; height_balL, height_balR, their fallback
  laws, and avl_balL / avl_balR at lines26–53.
- AVL_Bal_Set.thy: rot2 at line37; the constrained semantic laws inorder_balR
  and inorder_balL at120/125.
- Splay_Tree.thy: actual single/double rotation branches occur in splay and
  splay_code; inorder_splay is at line148 and size_splay at213.
- StronglyJoinableAVL.thy: joinR / joinL use the AVL balancers near lines22–37.
  T_ht_0, T_node_0, T_balL_0 and T_balR_0 occur at239–249; size laws for the
  balancers occur at313–317.
- Interval_Tree.thy: max_hi at line72, max3 at76, inv_max_hi at79, and the
  cached-maximum smart constructor node at121.
- Splay_Tree_Analysis_Base.thy: T_splay_simps at line23 records the actual
  guarded recursive-call cost equations.

### Original inventory obligations retained

The existing inventories already retain the immediate common obligations as
C05-042/043, C09-018–026/038, and C21-005–008. No inventory change is needed to
justify the shared work.

The following scopes remain later chapter obligations:

- C05-044–065: legal positions/schedules, list form, listification and its
  termination, exact rotation counts, inverse schedule, tree-to-tree
  transformation, and Exercises5.5–5.7. A root law supplies reusable facts but
  does not complete these constructions or their source-specific proof demands.
- C05-074/078/085 and the remaining interval-tree obligations: actual interval
  smart reconstruction, invariant preservation, balanced augmentation and
  overlap/search correctness. A generic cache-aware rotation is not that
  concrete balanced interval-tree solution.
- C09-018–040: actual cached AVL balancer decisions, all cases, invariant and
  precise height effects, update algorithms and operation-cost bounds.
- C09-075–079/092: balance-factor rot2/tag cases, exact raw-domain hypotheses,
  balance-factor algorithm and its independently observed resource bounds.
- C10-107: the concrete AVL join instance and its invariant/rank/work contracts.
- C21-009 onward: actual splay recursion, nonempty recursive-result domains,
  functional correctness, measured execution, logarithmic potential/access
  lemmas, sequence bounds and the remaining chapter/exercise obligations.

No treap-specific theorem is needed to justify this shared component. The
existing treap history/distribution/work obligations remain separate.

## What is genuinely common

### Ordinary structural laws

The smallest common semantic contract is:

1. The exact two matching-shape equations.
2. Preservation of the complete inorder list, with no order, equality-decision
   or inhabitance requirement on payloads.
3. Opposite rotations undo a successful legal rotation.
4. Node count and leaf count are preserved.
5. Applying any label map commutes with a successful rotation, including
   annotation erasure.

Items1–4 are directly present or supported by the book's rotation discussion and
later consumers. Item5 is a straightforward parametric consequence of the
displayed equations and an appropriate conaled compatibility law; it should be
described as a useful derived law, not an additional explicitly printed book
theorem.

Exact inorder equality also transports any already established predicate or
observation of that list. Strict BST preservation therefore belongs in a later
specialization, without adding a BST premise to the raw rotation theorem.

### Cache-aware reconstruction

The source supports rebuilding the changed nodes through a smart constructor:

- AVL uses node l a r = N(l,(a,max(ht l)(ht r)+1),r) on p.105.
- Interval trees use the analogous cached-maximum constructor on p.73;
  Interval_Tree.thy defines it at line121.
- The balanced interval-tree augmentation on p.75 is a future concrete consumer
  of correct cache rebuilding.

XT01 already supplies the relevant ingredients in Applications.Trees.Cached and
Applications.Resources.TreeCache: ordinary erasure, smartNode, recursive cache
validity, read_eq_fold, and measured nodeRun laws. This scoped read found no
rotation operation in those files at saved XT01 candidate
64c6b777d828ecfe83234fc2aed94600a1f24297. The architecture assessment's broader
reuse search remains the evidence for whether a matching operation exists
elsewhere; this source pass does not claim a repository-wide absence by itself.

A generic cache-validity theorem may apply to an arbitrary fold algebra, but
equality of the old and new root cache does not. A correctly cached height may
change under rotation. Recomputing the two changed nodes preserves validity when
their retained children are valid; it does not repair invalid descendant caches.

For an inorder-derived monoidal summary, old/new root-summary equality can follow
from inorder preservation. Noncommutative summaries remain meaningful because
the full label order is preserved.

## Important source boundaries

### Height is not a rotation invariant

The three-node left chain N(N(N(E,x,E),a,E),b,E) has height3. One right rotation
at its root produces N(N(E,x,E),a,N(E,b,E)), which has height2. Labels and inorder
are unchanged. This is an independent mathematical boundary calculation, not a
Lean-checked example in this preflight.

The source's AVL-specific height statements are correspondingly conditional.
For example, height_balL assumes valid AVL children and h(l)=h(r)+2, then gives
output height in {h(r)+2,h(r)+3}. These should remain with the later AVL
implementation, rather than becoming unconditional shared rotation claims.

### The two AVL representations have different raw domains

For the height-cache implementation, the test ht AB=ht C+2 forces AB to be
nonempty even if its stored height is incorrect, because ht E=0. The
double-rotation branch similarly forces the middle tree to be nonempty. This
explains the source's unconditional inorder lemmas.

For balance-factor trees, a malformed Lh or Rh tag can instead demand a
nonexistent heavy child. The actual source semantic lemmas retain nonempty/AVL
hypotheses on the relevant side. A shared ordinary legal-rotation law can support
both implementations without silently collapsing this distinction.

### Rotation count is separate from other work

Chapter5, pp.67–71, counts legal rotations. It does not establish that executing
a list of k positions in immutable trees costs k total steps.

Chapter21's printed/AFP observation counts recursive splay entries: nonrecursive
comparisons and rearrangements receive no additional tick.
Splay_Tree_Analysis_Base.thy, T_splay_simps at line23, records the actual guarded
recurrence. An empty grandchild guard avoids a recursive call; an implementation
must not silently insert an additional call to splay E.

If the shared unit includes a measured cache client, its result should use
XT01's separately named observation. Two actual nodeRun calls give the two
callback costs at their reached arguments plus the two local constructor
overheads. Under the existing nodeRun tariff this is the actual callback sum
plus6. This is a proposed composition of the existing XT01 model, not the book's
rotation count, its generated zero-cost convention, or an already proved
rotation theorem.

## Verified source identities and provenance

The following locally recomputed SHA-256 values match the saved provenance.
The book is the July27,2026 version, official URL
https://fdsa-book.net/functional_data_structures_algorithms.pdf . Its downloaded
PDF and extracted reading text remain research inputs, excluded from normal
source/history/control checkpoint payloads.

| Local source | Bytes | SHA-256 |
| --- | ---: | --- |
| functional_data_structures_algorithms.pdf | 1742029 | 9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645 |
| Tree_Rotations.thy | 4870 | 745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea |
| AVL_Set_Code.thy | 3403 | 423ea6e7e5d415a9d279ca24c48ce45b2d1bd60f591fae50a00ffa6e852cb2e3 |
| AVL_Set.thy | 12033 | 282cf829b7efc3421428cbe7ee3e590492d45ed0b8c7b80eff1ae3c57630f3b9 |
| AVL_Bal_Set.thy | 7109 | f347f9d6f788e1a057e82c4e5fd0a274cfb95593d1a0fc6094e00ceef83bdcae |
| Interval_Tree.thy | 10778 | 0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2 |
| Splay_Tree.thy | 16544 | 1f922b404850d90b4fee6345577c945e297948dde7efe03e58886ed3df24beab |
| StronglyJoinableAVL.thy | 18830 | 1855a887f6a7c7c0bcd5f5ed280688d5a8ad954f4c3f6dd16a0b4b806a6e2461 |

The Isabelle mirror files use revision
f86f290225eebcc52c1ae7dba2e098f405f51c21 and paths under
src/HOL/Data_Structures/ . Raw source URLs have prefix
https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/ .
The inspected revision is not asserted to be the one that generated the book.
The Isabelle source is BSD-3-Clause; the retained COPYRIGHT file has SHA-256
44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d.

Splay_Tree.thy uses the retained AFP archive
https://isa-afp.org/release/afp-Splay_Tree-2026-10-26.tar.gz , SHA-256
4c9b4a9fd24a63ba40eb5a357e2d8469d32eb437173018213bff2232f6dfd2f6.
Its companion analysis uses
https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz , SHA-256
d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a.
Splay_Tree_Analysis_Base.thy is pinned by the retained Chapter21 inventory at
3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17;
this pass read its relevant initial cost equations, without rerunning an Isabelle
build or claiming complete analysis re-review.

StronglyJoinableAVL.thy comes from the retained archive
https://isa-afp.org/release/afp-Joinable_BST_Work_Bounds-2026-10-26.tar.gz , SHA-256
5bf4d3bfc7f9106748163e8c7d4940d7756bcfe5a7ae197ce98dc520fb0b4911.
That AFP entry was published September24,2026 and explicitly postdates the
manuscript. AFP license provenance remains the BSD-3-Clause license at
https://isa-afp.org/LICENSE , SHA-256
9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd.

Existing exact inventories/provenance remain the governing broader records:
research/chapter05-obligations.md, research/chapter09-obligations.md,
research/chapter10-obligations.md, research/chapter21-obligations.md, and
provenance/source-inventory.json. No existing requirement or source inventory
was rewritten by this preflight.

## Suggested scope disposition

Proceed only with ordinary legal root rotations and a small XT01-based
reconstruction client. Leave positioned schedules/counts, rebalancing decisions,
tag maintenance, balance proofs, splay analysis and later chapter acceptance with
their existing tickets. The source facts justify this bounded reuse direction;
they supply neither Lean validation nor acceptance of XT01, the proposed unit,
any chapter, or the whole book.
