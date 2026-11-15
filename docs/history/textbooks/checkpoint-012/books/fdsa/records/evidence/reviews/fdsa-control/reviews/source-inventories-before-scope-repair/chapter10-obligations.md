# Chapter 10 source obligations: Beyond Insert and Delete

Status: **queued; source preparation only**. This inventory preserves the
generic union/intersection/difference construction, the printed red-black
pivot join, all three exercises, and the advertised work bounds. It also
records a substantial implementation boundary: the newly available AFP
work analysis uses a red-black join that deliberately changes the book's
root-color policy. No complexity theorem is transferred merely because
the algorithms implement the same sets.

Read with `../DECISIONS.md` and Chapters 4–9 inventories. No Lean
implementation, build result, acceptance, or completed coverage is asserted.

## Pins and source scope

- Book: July 27, 2026 version, Chapter 10 by Tobias Nipkow, printed
  pp.117–125; printed p.126 is blank (PDF pp.123–132).
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  Printed pp.118 and 123 were rendered and visually checked for the
  mistaken exercise reference and reversed split arguments.
- Isabelle mirror:
  <https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21>.
  BSD-3-Clause; `COPYRIGHT` SHA-256
  `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  This is an inspected companion revision, not a claim about the PDF's
  generating revision.
- Raw source prefix:
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.
- Reuse baseline: conaled
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries
  `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean v4.35.0
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Shared sources `Set_Specs`, `Tree2`, `Isin2`, `RBT`, `RBT_Set`,
  `Tree23`, `Tree23_Set`, `AVL_Set`, and `AVL_Set_Code` have their pins
  and hashes in Chapters 5–9 inventories.

| Companion path | SHA-256 | Inspected content |
|---|---|---|
| `src/HOL/Data_Structures/Set2_Join.thy` | `15edbd8a0b1b00633a15d9d1ccffb92d60ca9b313ba3b2f3bf4313af79f57d1b` | Five join/invariant assumptions, helpers, point updates, union/intersection/difference, all semantic/BST/invariant proofs, Set2 interpretation, unbalanced instance |
| `src/HOL/Data_Structures/Set2_Join_RBT.thy` | `cdd90cd62897ea5a8882d88266f33ce5fff8693294ccf0fe275866a716dbaf4e` | Printed red-black pivot join, raw/color/height/list/set/BST laws, generic instance |

### Cited paper and newly available formal cost source

The book cites Blelloch, Ferizovic, and Sun, *Joinable Parallel Balanced
Binary Trees*, ACM TOPC 9(2), article 7, 2022:
<https://doi.org/10.1145/3512769>.
The inspected author-hosted PDF is
<https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>, SHA-256
`c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`.
It is 41 pages and explicitly licensed CC-BY-4.0. Its primary role here
is provenance for the book's asymptotic claim and rank-based framework;
the book does not require all of that paper's other algorithms or
parallel-machine results.

Marco Haucke's AFP entry *Work Bounds for Strongly Joinable Balanced
Binary Search Trees*, published September 24, 2026, postdates the pinned
book but supplies relevant formal proofs:
<https://isa-afp.org/entries/Joinable_BST_Work_Bounds.html>.
Use the dated release
<https://isa-afp.org/release/afp-Joinable_BST_Work_Bounds-2026-10-26.tar.gz>,
SHA-256 `5bf4d3bfc7f9106748163e8c7d4940d7756bcfe5a7ae197ce98dc520fb0b4911`.
The inspected entry HTML has SHA-256
`e93d6463cb60970a8b669bb0b56aefb9e5d155aa89811662f41ae0295db040df`.
Its BSD-3-Clause license is <https://isa-afp.org/LICENSE>, SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`.
The entry discloses AI assistance for the RBT instantiation and part of
the submodularity appendix. This is provenance, not a substitute for
source/statement review or local Lean checking.

| AFP source | SHA-256 | Inspection scope |
|---|---|---|
| `Analytical.thy` | `f1760f87303f8d29285928977ddeacf76a030ada13b476f9a0cb4b1a49a198cd` | Pinned analysis dependency; not reviewed line by line |
| `BalancedBinary.thy` | `2633b3d0f24e544bc14b1d23dc567de5c2b81deb50a8eb6c124c1376fc0a9dda` | Rank/balance locale and height/size framework |
| `StronglyJoinable.thy` | `da113a8cbdadeb27b7c6689b9e9b929dfb654870484238d4a29e515868b7185f` | Exact locale premises, generated-time bridge structure, final uniform and asymptotic bounds; lengthy intermediate summation proofs not independently reproduced |
| `StronglyJoinableAVL.thy` | `1855a887f6a7c7c0bcd5f5ed280688d5a8ad954f4c3f6dd16a0b4b806a6e2461` | Concrete cached AVL join, invariant/rank/cost instance, numerical bounds |
| `StronglyJoinableRBT.thy` | `9cc1c0462b939507ab7b13b44019324b03e94ebebaec9850e19227d27ea48edc` | Concrete cached RBT join, changes from the book, rank/cost instance, numerical bounds |
| `Submodularity.thy` | `efa718027c7f7f9005b8ce6619c88457ca2fce551b45c8ce82f57b550aeb830a` | Formal singleton obstruction to a flag-free paper-rule reading and the alternative rule used by the AFP development |

No `sorry`, `oops`, `axiomatization`, or `admit` token was found in these
six downloaded AFP theories by the scoped source scan. No Isabelle build
was run here; this scan is not an independent validation or Lean port.

## Observations and domain boundaries

For generic augmented binary trees write E, N(l,(a,b),r), S(t) for the
finite set of payloads with annotation b erased, I(t) for erased inorder,
and BST for the strict search-tree invariant. The generic structural
predicate V=`inv` is separate from BST. The public Set2 invariant is
`V t ∧ BST t`.

The chapter's **three-argument pivot join** J(l,a,r) differs from Chapter
8's two-argument deletion join. Chapter 10's derived `join2` first
extracts a right minimum and then calls J; it is not definitionally the
earlier equal-black-height merging helper.

The generic specification constrains **sets**, not arbitrary inorder
lists or node counts. Under BST separation, strict sortedness and equal
sets can recover a unique inorder list; outside that domain, the five
assumptions do not prohibit extra copies of an existing key. Additional
inorder/size laws in a concrete family must be proved, not inferred from
the generic set equation alone.

The annotation type need not have a chosen default. Express the BST
premise for join as the equivalent annotation-independent conditions:
BST l, BST r, all left labels<a, and all right labels>a. This avoids
inventing an annotation solely to write `BST(N(l,(a,_),r))`. If the
source-shaped formula is exposed too, prove the equivalence on the
available annotation domain. A join satisfying its set law already
provides a nonempty result for any actual pivot; do not add a global
`Inhabited` assumption just to mimic HOL's type convention.

split_min E is unspecified in HOL; use a nonempty domain or an explicit
failure return and prove all public calls are valid. Other empty tests
are shape tests and do not require equality on payloads or annotations.

Reuse labels: **R** existing infrastructure, **P** checked bridge needed,
**G** gap, **X** cross-chapter dependency. They never mean accepted coverage.

## Set2 and the generic join contract: pp.118–119, Figures 10.1–10.2

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-001 | Extend the shared Set interface with union, inter, and diff, all binary operations on the same representation type (p.118; `Set_Specs.Set2`). | R/P/X Chapter 6. Difference has the usual first-minus-second order. |
| C10-002 | Preserve all six Figure 10.1 laws: under both public invariants, each operation implements the corresponding set union/intersection/difference and preserves the public invariant. | P/G. These are six distinct value/preservation statements. |
| C10-003 | Retain all seven inherited Set laws as well, giving thirteen obligations in the generic Set2 interpretation (`Set2_Join` sublocale proof). | X Chapter 6. Binary-operation correctness does not replace point-update/search laws. |
| C10-004 | Generic representation is the shared binary tree labelled by `(element,annotation)` (p.118). | R/P Chapter 4. Annotation is ignored by generic comparison/value functions, but may matter to J and V. |
| C10-005 | Use S(t)=set_tree and the strict recursive BST predicate, with their bridge to erased inorder and finite set cardinality under BST. | R/P Chapters 4–5. |
| C10-006 | Parameterize the entire construction by J and V, retaining five distinct assumptions from Figure 10.2. | G/P reusable domain contract. The interface is semantic; it does not yet impose rank or cost rules. |
| C10-007 | Equation (10.1): unconditionally `S(J l a r)=S l∪{a}∪S r`. | G/contract. No BST/V premise. |
| C10-008 | Equation (10.2): if l/r are BSTs separated by a, then J l a r is BST. | G/contract. Keep the separation premise; joining arbitrary overlapping BSTs need not produce a BST. |
| C10-009 | V E holds (the unnumbered empty assumption in Figure 10.2). | G/contract. |
| C10-010 | Equation (10.3): V l and V r imply V(J l a r), independent of search ordering. | G/contract. |
| C10-011 | Equation (10.4): V of a nonempty raw node implies V of each child. | G/contract. This hereditary property excludes Chapter 8's black-root requirement from the generic V. |
| C10-012 | Provide the annotation-independent BST-premise formulation described above and any checked source-shaped adapter; do not require an arbitrary annotation merely to express a constructor's ordering condition. | P/Lean domain adaptation. |
| C10-013 | Keep generic value correctness, structural invariant preservation, and optional resource hypotheses separated, with exact valid-domain correspondence for partial helpers. | X project abstractions/resources and `DECISIONS.md`. A Set2 instance alone is not a balanced/fast implementation. |

## Generic helpers and point operations: pp.119–122

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-014 | split_min of N(l,(a,_),r): if l=E return (a,r); otherwise obtain (m,l') recursively from l and return `(m,J l' a r)` (p.119). | G/P. Reassemble with the supplied J, not the ordinary node constructor. |
| C10-015 | If split_min t=(m,t') and t≠E, then m∈S t and `S t={m}∪S t'` (p.122; `split_min_set`). | G/P. Neither BST nor V is needed; without BST, m can still occur in t'. |
| C10-016 | With the same nonempty/extraction hypotheses plus BST t, prove BST t' and every x∈S t' satisfies m<x (`split_min_bst`). | G/P. This implies m is absent from the residual set. |
| C10-017 | With nonempty/extraction hypotheses plus V t, prove V t' (`split_min_inv`). | G/P. No BST premise. |
| C10-018 | `join2 l r=l` when r=E; otherwise extract `(m,r')=split_min r` and return J l m r' (p.119). | G. This is right-minimum pivot extraction, distinct from Chapter 8's two-tree join. |
| C10-019 | Equation (10.5): unconditionally `S(join2 l r)=S l∪S r` (`set_join2`). | G/P C10-015. |
| C10-020 | BST l, BST r, and every left key strictly below every right key imply BST(join2 l r) (p.122; `bst_join2`). | G/P. Keep cross-tree strict separation. |
| C10-021 | V l and V r imply V(join2 l r) (`inv_join2`). | G/P. |
| C10-022 | split x E=(E,false,E); at N(l,(a,_),r), LT recursively splits l and joins its upper part with a/r; EQ returns (l,true,r); GT recursively splits r and joins l/a with its lower part (p.120; exact recurrence below). | G. The Boolean records presence, while both returned trees exclude x under BST. |
| C10-023 | Equation (10.6): if split x t=(l,b,r) and BST t, then `S l={a∈S t : a<x}`, `S r={a∈S t : x<a}`, b iff x∈S t, and BST l/BST r (p.122; `split`). | G/P. All five clauses are needed; set partition alone does not certify returned search trees. |
| C10-024 | If split x t=(l,b,r) and V t, then V l and V r (`split_inv`). | G/P, no BST premise. |
| C10-025 | Preserve the p.120 split diagram's path/order claim: under a<b<c<d<e, splitting at c follows the compared spine a,e,b,d and rebuilds separated outputs with J; the shown concrete shapes assume J is raw construction. | G/evaluation witness or concrete specialization. Do not demand those exact output shapes from an arbitrary balancing J. |
| C10-026 | Source insert x t obtains (l,b,r)=split x t and returns J l x r, ignoring b (p.120). | G. No implicit reuse of the older point-insertion recurrence. |
| C10-027 | Under BST t, source insert implements `{x}∪S t` and preserves BST (`set_tree_insert`, `bst_insert`). | G/P split/J laws. |
| C10-028 | Under V t, source insert preserves V (`inv_insert`). | G/P, independent of BST. |
| C10-029 | Source delete x t obtains (l,b,r)=split x t and returns join2 l r, ignoring b (p.120). | G. |
| C10-030 | Under BST t, source delete implements `S t\{x}` and preserves BST (`set_tree_delete`, `bst_delete`). | G/P split/join2 laws. |
| C10-031 | Under V t, source delete preserves V (`inv_delete`). | G/P. |
| C10-032 | Answer the p.120 optimization question: after splitting, insertion can return original t if b=true; deletion can return original t if b=false. Prove the same semantic/BST/V contracts and the avoided final J/join2 work in an explicit nonnegative cost model. | G. The split has still been performed; do not claim its search/reconstruction work vanished in a strict evaluator. |

### Exact split recurrence

| Compared branch | Output after the one recursive call |
|---|---|
| E | (E,false,E) |
| x<a; split x l=(l1,b,l2) | (l1,b,J l2 a r) |
| x=a | (l,true,r) |
| a<x; split x r=(r1,b,r2) | (J l a r1,b,r2) |

## Generic binary operations: pp.120–123, Figure 10.3

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-033 | union E t=t; union t E=t. For nonempty first input N(l1,(a,_),r1), split a t2=(l2,b,r2), recursively union corresponding children, and J the results with pivot a (p.121). | G/P. b is intentionally ignored because a is in the first input. |
| C10-034 | Terminate union structurally on the first input's subtrees; the second argument's split outputs need not be structural subtrees. Preserve the source computation-induction principle. | G/P. |
| C10-035 | **Only BST t2** is required for `S(union t1 t2)=S t1∪S t2` (p.122; `set_tree_union`). | G. Do not silently require BST t1 or V merely for this value theorem. |
| C10-036 | BST of both inputs implies BST of union (`bst_union`). | G/P. |
| C10-037 | V of both inputs implies V of union (`inv_union`), without BST hypotheses. | G/P. |
| C10-038 | inter E t=E and inter t E=E. Decompose the first input, split the second at its pivot a, recursively intersect corresponding children, then use J with a iff b=true, otherwise join2 (p.121). | G. The pivot-inclusion Boolean is essential. |
| C10-039 | Terminate inter on first-input subtrees, retaining its actual conditional join/J2 recurrence. | G/P. |
| C10-040 | BST of both inputs implies `S(inter t1 t2)=S t1∩S t2` (p.123; `set_tree_inter`). | G/P. Unlike union, the source theorem uses both BST hypotheses. |
| C10-041 | Preserve the displayed intersection argument: a is absent from L1∪R1 and L2∪R2; L2∩R2, L1∩R2, L2∩R1 are empty; with A={a} if b else ∅, intersection of the two decomposed unions is `(L1∩L2)∪(R1∩R2)∪A` (p.123). | R/P set algebra and G separation bridge. The prose's `split t2 a` is a type/order typo; use `split a t2`. |
| C10-042 | BST of both inputs implies BST of inter (`bst_inter`). | G/P. |
| C10-043 | V of both inputs implies V of inter (`inv_inter`), without BST hypotheses. | G/P. |
| C10-044 | diff E t=E and diff t E=t. In the third equation decompose the **second** input N(l2,(a,_),r2), split first input at a, recursively subtract corresponding parts, and always join2 the results (p.121). | G. The removed-set pivot must never be reinserted. |
| C10-045 | Terminate this diff on second-input subtrees; preserve the argument direction and source computation induction. | G/P. Do not assume a structural decrease of the first split outputs without proof. |
| C10-046 | BST of both inputs implies `S(diff t1 t2)=S t1\S t2` (`set_tree_diff`; p.123's stated analogous correctness). | G/P. |
| C10-047 | BST of both inputs implies BST of diff (`bst_diff`). | G/P. |
| C10-048 | V of both inputs implies V of diff (`inv_diff`), without BST hypotheses. | G/P. |
| C10-049 | Instantiate all thirteen Set2 laws using S and public invariant `V∧BST` (`Set2_Join` sublocale). | X Chapter 6/project interface. Generic functions should be actual reusable consumers. |
| C10-050 | Retain the companion's concrete unbalanced witness: annotation Unit, J=raw node, V=true satisfy all five generic assumptions (`unbal`). | G/P specialization. It is a useful negative boundary for any claim that the semantic interface alone guarantees balancing or optimal work. |

## Printed red-black pivot join: pp.123–124, Figure 10.4

Use Chapter 8 notation C=`invc`, H=`invh`, C2=`invc2`, bh for the
left-spine black-height function, and R/B for colored node constructors.

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-051 | Choose V t=`C t∧H t` (p.124), allowing a red root; prove it has logarithmic height using Exercise 8.1. | X Chapter 8. This is weaker than its black-root rbt but sufficient for the required hereditary invariant. |
| C10-052 | Prove V is inherited by children, and preserve a checked counterexample showing black-root rbt is not: `B(R(E,0,E),1,E)` is rbt but its left child is red-rooted. | G/P. This explains the exact failure of (10.4) for the stronger predicate. |
| C10-053 | joinL l x r: if bh r≤bh l return R(l,x,r); otherwise descend into r's left child, rebuilding R at a red parent and using Chapter 8 baliL at a black parent (p.124). | G/P Chapter 8 balancers. The stopping test is ≤, not equality. |
| C10-054 | joinR l x r: if bh l≤bh r return R(l,x,r); otherwise descend into l's right child, rebuilding R at a red parent and using baliR at a black parent (p.124). | G/P. This is not the earlier two-tree deletion join. |
| C10-055 | Prove termination on the traversed input tree and that an omitted E case is impossible when the stopping test is false, since bh E=0 and bh is natural. | G/P. No default payload is needed. |
| C10-056 | Public J: if bh r<bh l, paint Black(joinR l x r); if bh l<bh r, paint Black(joinL l x r); at equality return B(l,x,r) (p.124). | G. Retain the book's unconditional blackening and black equal-height node exactly in this implementation. |
| C10-057 | Source color-only joinL law: C l, C r, and bh l≤bh r imply C2 of joinL; strict height inequality and old right root Black additionally imply C (`invc2_joinL`). | G/P. H is not a premise of this particular companion lemma. |
| C10-058 | H l, H r, and bh l≤bh r imply H(joinL) and `bh(joinL)=bh r` (`invh_joinL`, `bheight_joinL`). | G/P. No color premise. |
| C10-059 | Preserve the actual companion joinR hypotheses: its `invc2_joinR` includes C and H of both inputs and bh r≤bh l; its separate H/black-height laws require H of both and that height order. | G/P. The inspected weaker-premise lemmas are not perfectly symmetric; do not report a color-only joinR theorem as already supplied. |
| C10-060 | Prove both full displayed/symmetric laws (`inv_joinL/R`): C/H of both inputs plus the appropriate bh ordering imply C2, the strict-inequality/old-black-root C conditional, H, and bh equal to the higher input (p.124). | G/P Chapter 8 balancer laws. |
| C10-061 | Companion `inorder_joinL`: bh l≤bh r implies `I(joinL l x r)=I l++[x]++I r`. | G/P. Record this source premise even if a later direct proof removes it. |
| C10-062 | Companion `inorder_joinR` gives the same inorder equation unconditionally. | G/P. |
| C10-063 | Retain the set laws: joinL with bh l≤bh r, joinR unconditionally, and painting unconditionally preserve the pivot-set equation (`set_joinL/R`, `set_paint`). | G/P. |
| C10-064 | Retain strict-order preservation: separated BST inputs plus bh l≤bh r for joinL; separated BST inputs suffice for joinR (`bst_joinL/R`). | G/P. No structural V premise is needed for these source order laws. |
| C10-065 | Public J has unconditional inorder and set equations and preserves BST under separation (`set_join`, `bst_join`, unnamed inorder theorem). | G/P. Its stronger inorder observation is extra concrete structure beyond the generic contract. |
| C10-066 | C/H of both inputs imply C/H of J and, in fact, black-root rbt of J (`inv_join`, `rbt_join`). | G/P. The strong result for J does not make rbt hereditary for arbitrary input subtrees or generic base cases. |
| C10-067 | Preserve the companion black-height bound: if both inputs satisfy black-root rbt, `bh(J l x r)<=max(bh l)(bh r)+1`; also `bh(paint Black t)<=bh t+1` unconditionally. | G/P. Any strengthening to merely C/H inputs must be proved explicitly. |
| C10-068 | Instantiate the generic locale with this J and V=C∧H, yielding source insert_rbt, delete_rbt, split_rbt, join2_rbt, split_min_rbt, inter_rbt, union_rbt, and diff_rbt (`global_interpretation RBT`). | G/P/X. Keep it distinct from Chapter 8's point-update implementations and from the later optimized join. |
| C10-069 | To realize p.123's **conditional** efficient join, augment each node with an exact cached black height, maintain it through every constructor/recoloring/rotation, and prove erasure to the printed recurrence. Cached access is bounded local work under the named model. | G/X Chapter 4 augmentation. Recomputing bh or annotating the entire input on every join does not meet the condition. |
| C10-070 | Count the literal uncached implementation separately: joining E with a complete all-black height-h tree descends a spine while repeatedly recomputing remaining black heights, producing a quadratic-in-h sum under charged bh traversal. Preserve this family as a cost-boundary witness. | G. The book explicitly assumes caches for its linear-in-black-height statement; this is not a counterexample to that conditional claim. |

## Exercises: p.125

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-071 | Exercise 10.1: define singleton x=`J E x E`, then a concrete alternative insertion such as `insert' x t=union(singleton x)t`. | G/P. Use only the permitted union/J/E ingredients. |
| C10-072 | Exercise 10.1: `delete' x t=diff t (singleton x)`. | G/P. Reversing the diff arguments is incorrect. |
| C10-073 | Prove both alternatives have the correct set observation and preserve BST on BST inputs; retain V preservation for their concrete Set integration. | G/P generic laws. They need not return the identical tree as split-based insert/delete. |
| C10-074 | Exercise 10.2 diff1: keep empty equations; decompose the **first** input at a, split the second at a, recursively compute u/v, then use join2 u v if b=true and J u a v if b=false. | G. This is the actual exercise, not the abstract-tree exercise incorrectly referenced on p.118. |
| C10-075 | Under BST inputs, prove `S(diff1 t1 t2)=S t1\S t2` and BST of the result (Exercise 10.2). | G/P. The Boolean polarity differs from intersection. |
| C10-076 | Prove diff1 terminates on first-input subtrees and preserves V from V of both inputs. | G/P support and project integration. |
| C10-077 | Relate diff and diff1 by their set observation under BST, with checked boundary cases such as equal singletons→empty and a first-only singleton retained. | G/P. Do not assert concrete output or resource equality. |
| C10-078 | Exercise 10.3 uses the existing 2-3 carrier and insertion result UpI=Eqi tree or Of left pivot right, with projection treei; use complete 2-3 inputs (p.125). | X Chapter 7. The helper result is a height-change/overflow representation. |
| C10-079 | Define a concrete joinL23 of the required type, descending the leftmost child of the taller right tree; at equal heights return Of l x r; absorb/propagate overflow exactly as in the table below. | G/design solution. Calls require h23 l≤h23 r; invalid inputs need an explicit domain/failure or totalization policy. |
| C10-080 | Define the mirrored joinR23, descending the rightmost child of the taller left tree and using the exact right-overflow cases below. | G. Preserve the pivot's inorder position during every promotion. |
| C10-081 | Under completeness and the helper's height ordering, prove `I23(treei(helper l x r))=I23 l++[x]++I23 r`. | G/P Chapter 7 overflow/list lemmas. |
| C10-082 | Prove helper completeness/height contracts: treei of the result is complete, and its UpI level observation hi equals `max(h23 l)(h23 r)`; for Of, both components are complete at that level. | G/P. These precise helper properties are the exercise's stated missing inductive support. |
| C10-083 | Define overall join23 by choosing the helper matching the height order and applying treei; retain the exact equal-height behavior. | G. No ordering on payloads is needed to build the complete tree. |
| C10-084 | Exercise 10.3 first conclusion: complete l and complete r imply complete(join23 l x r). | G/P C10-082. |
| C10-085 | Exercise 10.3 second conclusion: under completeness, exact inorder concatenation with pivot x; derive the strict search-tree specialization when l<x<r. | G/P. Do not weaken the exercise to equality of sets. |
| C10-086 | Account for the representation boundary: generic binary Set2_Join cannot directly instantiate with an N3 constructor. Any shared abstract decomposition framework or 2-3-specific bulk extension needs an explicit representation/recursion bridge. | P/X architectural integration. The exercise itself specifies the join and its two laws, not a new whole 2-3 Set2 implementation or a hidden cached-height cost theorem. |

### A concrete 2-3 join solution to recover later

Below C is completeness and h23 is the source 2-3 height. These are
prospective executable equations and proof targets, not checked Lean.
Equality of input heights returns Of(l,x,r). A strict height difference
justifies destructuring the taller tree and recursing on its outermost
child. In each row z is the one recursively computed UpI result.

| Helper / taller node | z=Eqi t | z=Of u b v |
|---|---|---|
| joinL23 l x N2(A,a,B), z=joinL23 l x A | Eqi N2(t,a,B) | Eqi N3(u,b,v,a,B) |
| joinL23 l x N3(A,a,B,c,C), z=joinL23 l x A | Eqi N3(t,a,B,c,C) | Of N2(u,b,v) a N2(B,c,C) |
| joinR23 N2(A,a,B) x r, z=joinR23 B x r | Eqi N2(A,a,t) | Eqi N3(A,a,u,b,v) |
| joinR23 N3(A,a,B,c,C) x r, z=joinR23 C x r | Eqi N3(A,a,B,c,t) | Of N2(A,a,B) c N2(u,b,v) |

Overall output height is max input height or one greater. This is a
useful strengthened theorem, but a logarithmic implementation cost cannot
be inferred by treating the source h23 (which recursively traverses all
children) as a free oracle. The printed exercise's required conclusions
are structural completeness and exact inorder.

## Introductory algorithms, comparisons, and work target: pp.117–118

Let 1≤m≤n denote nonempty **set cardinalities** for the book's asymptotic
formula, and define `F(m,n)=m*log₂(n/m+1)` with real division. Empty-input
operations must have explicit constant base cases; the expression with
m=0 is not a uniform positive runtime bound.

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C10-087 | Preserve the introductory insertion-fold union algorithm and prove its set result using the existing Set interface (p.117). | R/P finite folds and Set laws. This gives a concrete comparator for the new algorithm. |
| C10-088 | Formalize the two displayed logarithmic growth sums and their log-product identity. Exact size growth n,n+1,… occurs when inserted keys are all new; overlapping sets instead give a bounded size schedule. | R/P finite sum/product logarithms. Distinguish the assumed per-insertion tariff from actual path-sensitive costs. |
| C10-089 | For 1≤m≤n and n≥2, prove `m*log₂ n <= Σ(i<m) log₂(n+i) <= 2*m*log₂ n`, hence the stated Θ(m log n) growth in this model (p.117). | G/P arithmetic. The upper bound uses n+i<2n and log₂ n≥1. The n=1 boundary must not be used as an exact zero-time insertion claim. |
| C10-090 | Prove the smaller-into-larger sum is no greater than the larger-into-smaller sum under positive m≤n; their common high-end terms cancel, leaving nonnegative logs (p.117). | G/P. This is an inequality of the displayed tariff sums, not an exact implementation runtime comparison for every overlapping input. |
| C10-091 | Preserve the explicit assumption that insertion cost is proportional to logarithmic set size, or state the appropriate worst-case contract. A present root key can be found in constant path work, so no per-input Θ(log n) fact follows from balance alone. | G/qualified cost contract. A singleton batch containing the existing root is a useful boundary example. |
| C10-092 | Preserve the flatten/merge/rebuild alternative: use linear inorder2, merge the strictly sorted lists while suppressing equal keys, and use a verified balanced list conversion (p.117). Prove union contents and strict ordering. | X Chapters 4,7–9; G deduplicating merge adapter. |
| C10-093 | Prove its three actual stages take O(m+n) in the chosen model, including the balanced conversion's algorithm, rather than an arbitrary semantically equal builder. | G/X existing traversal/conversion cost targets. |
| C10-094 | Keep the duplicate boundary explicit: ordinary sorting merge of [1] and [1] gives [1,1], which cannot be a strict BST inorder. A set merge must advance both sides on equality or apply a proved linear adjacent deduplication. | G/P value witness. “Merge” in the introductory set algorithm cannot silently mean the multiplicity-preserving Chapter 2 routine without this adapter. |
| C10-095 | Retain the central advertised bound: each of union, inter, diff has O(F(m,n)) work for suitable balanced join implementations, with m=min cardinalities, n=max cardinalities and explicit empty cases (p.117 and Chapter Notes p.125). | G. Neither semantic laws nor a height bound alone discharge this target. |
| C10-096 | Prove the p.118 comparisons of growth expressions with their stated domains: for m,n≥2, `n/m+1<=n`, hence F≤m log₂ n; for m≥1 use `m+n=m*(n/m+1)` and an appropriate logarithm bound to show F=O(m+n). | G/P. “At least as fast” here concerns asymptotic work, not measured constants or all implementation times. |
| C10-097 | Preserve the illustrative regimes: F(n,n)=n and F(1,n)=log₂(n+1), and use these or suitable asymptotic specializations to explain similar-size versus highly unequal-size inputs (pp.117–118). | G/P. Keep real division and positive arguments. |
| C10-098 | Introduce and prove the additional rank/size/cost hypotheses actually used by a work analysis, such as the inspected AFP StronglyJoinable contract below. | G/P external formal proof route. Its rank assumptions are additional to Figure 10.2 and must be validated for a concrete J. |
| C10-099 | Prove the supplied T_join corresponds to the actual executable J under the declared primitive tariff, then transport generated helper/union/inter/diff counts through the analysis. | G/X resource layer. The abstract AFP locale explicitly does not establish this correspondence by itself. |
| C10-100 | Retain a uniform pointwise work bound, not only an asymptotic theorem: the AFP generic `T_union_bound`, `T_inter_bound`, `T_diff_bound` have the form `K0+K1*M+K2*M*log₂(N/M+1)` under structural invariants. | G/P. Exact constants and cost model belong to the chosen instance. |
| C10-101 | Bridge AFP M/N (minimum/maximum **external-leaf counts**) to book m/n (set cardinalities): under BST, M=m+1 and N=n+1; for 1≤m≤n, `M*log₂(N/M+1)<=2*F(m,n)`. Absorb constant/linear terms using F≥m≥1. | G/P. A direct substitution of m for size1 would be off by one. Empty input behavior is handled separately. |
| C10-102 | Preserve the quantifier strength: AFP's `tree_pair_filter` makes both valid input sizes tend to infinity. Use its uniform finite bounds to cover a fixed small m, including m=1 while n grows. | G/P. A product-filter Big-O theorem alone does not cover those families. |
| C10-103 | If using the AFP fast red-black instance, implement its distinct cached-height join: only blacken a red root with a red child; at equal bh use a red pivot node when both inputs have black roots, otherwise black. | G/P explicit optimized variant. Do not rename the book's always-black J to obtain this cost proof. |
| C10-104 | Retain a checked obstruction to applying that rank rule directly to the book: with `rk=2*bh+redRootIndicator`, J E x E is a black singleton of rank 2, while the valid old red singleton has rank 1. The framework's zero-shift rebuilding/submodularity inequality would require 2≤1. | G/negative correspondence witness. This refutes the proposed rule/transport, not by itself the book variant's complete asymptotic work bound. |
| C10-105 | Prove both red-black variants' semantic/BST/V contracts and document their actual representation/algorithm relationship; they already differ concretely on E,x,E. | G/P. Equal set or inorder observations are enough for common clients, but not for equal ranks, trees, or costs. |
| C10-106 | For the matching cached AFP RBT variant, the pinned source offers concrete uniform bounds and Big-O corollaries listed below; port or independently prove them with the cost bridge. | G/P. These are available Isabelle results, not existing Lean coverage. |
| C10-107 | Preserve the advertised AVL applicability by a concrete join instance; the pinned AFP AVL join uses Chapter 9 cached heights/rotations and supplies its own invariant/rank/work proofs. | G/P/X Chapter 9; exact algorithms and constants below. No new full copy of the generic set algorithms is needed. |
| C10-108 | Preserve the introductory claim that the class also includes weight-balanced trees by identifying a suitable concrete J and checking its semantic plus rank/cost contracts if that advertised family is claimed covered. | G external-source witness. The inspected AFP archive instantiates AVL and RBT, not weight-balanced trees. Std.TreeMap's existence or set laws alone do not fill this gap. |
| C10-109 | Resolve the book-specific fast-bound gap explicitly: either prove an appropriate work theorem for its cached always-black J, or retain that implementation's correctness while presenting a documented corrected/optimized variant with its checked bound and exact differences. | G/source disposition. The current inventory has not proved the book variant's bound false; failure of one proof framework is insufficient to assert that. A future chapter closure must not silently mark it covered through unrelated costs. |
| C10-110 | Preserve a concrete counterexample to deriving optimal work from the generic semantic contract: use the unbalanced J/V instance, a right chain of n increasing keys, and union with a singleton pivot above them; split traverses the chain although the target F(1,n) is logarithmic. | G/negative specialization. The missing balance/rank assumptions are substantive. |
| C10-111 | Classify the p.118 parallelism sentence accurately: the two recursive branches are independent pure subcomputations, so their functional results can be combined in either evaluation order. The chapter explicitly does not develop a parallel runtime model or numerical span theorem. | Formal independence/value statement where used; broader efficiency discussion remains identified analysis. Do not import all cited-paper parallel claims as if printed here. |

## Exact external work contracts and reuse limits

### StronglyJoinable is stronger than the five functional assumptions

The pinned AFP adds a real rank ρ, constants 0<c_l≤1 and c_u≥1, and
ρ(E)=0. On invariant nodes, the child ranks satisfy

`max(ρ l,ρ r)+c_l <= ρ(node) <= min(ρ l,ρ r)+c_u`,

recursively. It additionally requires:

- monotonicity: invariant l/r imply `max(ρ l,ρ r)<=ρ(J l a r)`;
- its one-sided rebuilding rule: if `ρ l'<=ρ l+x` and `ρ r'<=ρ r+x`,
  l'/r' are invariant, and the old raw node N(l,(a,b),r) is invariant,
  then `ρ(J l' a r')<=ρ(oldNode)+x`, for arbitrary real x;
- exact size: invariant l/r imply
  `nodes(J l a r)=nodes l+nodes r+1`;
- cost: invariant l/r imply
  `T_join l a r<=k0+k1*abs(ρ l-ρ r)`, with nonnegative k0/k1.

The size law is a genuine additional condition when no BST separation is
assumed. Set equality alone permits deduplication or extra occurrences
outside the valid search domain. The locale's proof explicitly keeps it
so the work analysis does not need BST at every intermediate lemma.

It defines idealized W_join as the absolute rank difference, with
`K_T=1+2*k0+k1`, and proves bridges such as `T_split_bridge`,
`T_split_min_bridge_strong`, `T_join2_bridge`, `T_union_bridge`,
`T_inter_bridge`, and `T_diff_bridge`. The generic operation recurrences
are imported from `Set2_Join`; they are not replaced with different
value-equivalent bulk algorithms.

The exact cost interpretation matters: the concrete instances inline
nonrecursive accessors/constructors/rotations, giving them generated cost
zero. Recursive helper entries are counted. In particular, a constant
equal-height join has generated T_join=0, not a claim of physically zero
runtime. Conaled may use another named observation, but must provide a
checked tariff/recurrence bridge instead of copying these numbers.

### Cached RBT instance differs from the book

The AFP RBT carrier stores `(payload,(color,blackHeight))`. Its invariant
contains exact cache correctness, C, and H, and permits a red root. Its
joinL/R recursions and rotations follow the book after cache erasure;
the **public root policy** changes as recorded in C10-103. On invariant
inputs it proves `max(rk l,rk r)<=rk(join)<=max(rk l,rk r)+1`, using
`rk=2*bh+redRootIndicator`, and has c_l=1, c_u=2, k0=2, k1=1.

Let M=min(leaves t1,leaves t2), N=max(leaves t1,leaves t2), and
G=M*log₂(N/M+1). The source's finite bounds, requiring only its structural
invariants, are:

| Operation | Source theorem | Generated-count bound |
|---|---|---|
| Union | `rbt_T_union_linlog` | `T<=6+1856*M+943*G` |
| Intersection | `rbt_T_inter_linlog` | `T<=6+3333*M+1696*G` |
| Difference | `rbt_T_diff_linlog` | `T<=6+3333*M+1696*G` |

The corresponding `rbt_T_union_bigo`, `rbt_T_inter_bigo`, and
`rbt_T_diff_bigo` use natural logarithms and the product filter of valid
trees whose node counts both tend to infinity. Base change and C10-101
connect them to the book, while the uniform bounds handle fixed small
inputs. Source theorem existence does not constitute a Lean proof or
cost correspondence for a different root policy.

The AFP's introductory prose correctly warns about missing cached black
heights. Its description of the uncached cost as linear in input ranks
is not a substitute for a recurrence count: the literal book joinL on a
complete all-black tree repeats left-spine bh computations at descending
heights. C10-070 retains the explicit quadratic sum for that family.

### AVL instance and other reuse

The AFP AVL carrier/invariant are the Chapter 9 cached implementation.
Public J returns `node l a r` when child heights differ by at most one.
If l is taller, joinR destructures l=N(l',k,r'); when ht r'≤ht r+1 it
returns `balR l' k (node r' a r)`, otherwise it recursively joins r'
with a/r and balances with balR. joinL is the mirror using balL.
These helpers require the appropriate strict height gap to enter their
nonempty cases. The source proves set/BST/AVL correctness, exact size,
rank rules with ρ=h, c_l=1, c_u=2, and generated cost at most
`1+abs(h l-h r)`, so k0=k1=1.

| Operation | Source theorem | Generated-count bound |
|---|---|---|
| Union | `avl_T_union_linlog` | `T<=4+1238*M+629*G` |
| Intersection | `avl_T_inter_linlog` | `T<=4+2222*M+1131*G` |
| Difference | `avl_T_diff_linlog` | `T<=4+2222*M+1131*G` |

The generic code, strict comparator/set laws, Chapter 8 balancers, and
Chapter 9 AVL helpers are substantive reuse opportunities. Existing
conaled representation/refinement and resource composition should express
their distinct value and work observations. No exact integrated
join-based Set2 domain was established by the scoped project inspection.

Batteries `RBSet.union` is **an insertion fold** (`t2.foldl insert t1`),
not the chapter's split-and-join recurrence. Its intersectWith and sdiff
also use lookup/filter/fold operations. Reusing those functions would
cover the introductory alternative or abstract semantics, not the new
algorithm or O(F) work bound. Batteries' two-tree `append` also lacks
this arbitrary-rank pivot-join contract. Std.TreeMap uses a different
size-balanced carrier; any join/rank theorem reuse needs its own checked
algorithm and invariant correspondence.

## Source corrections and handoff

1. **p.118 exercise reference:** the text calls Exercise 10.2 a more
   generic abstract-tree approach. Printed Exercise 10.2 is actually
   first-argument difference. Preserve that exercise as printed; the
   abstract-carrier idea is mentioned in the companion introduction
   but no such exercise appears in this chapter. Do not replace the
   real diff1 task or invent missing exercise text.
2. **p.123 split arguments:** the intersection explanation writes
   `split t2 a`; the definition, Figure 10.3, and companion proof use
   `split a t2`. This is a type/order typo, not a second splitting API.
3. **Introductory costs:** exact increasing-size sums assume new keys;
   the asymptotic insertion tariff is an explicit model assumption.
   Overlap, existing-root queries, n=1, and m=0 require the qualifications
   above. The flatten/merge route needs duplicate suppression to preserve
   strict search ordering.
4. **Book versus fast RBT join:** caching alone does not make the
   book's root policy satisfy the inspected stronger rank framework.
   The singleton witness refutes that framework instance. It does not
   prove the complete book-algorithm asymptotic claim false. Retain the
   precise unresolved disposition C10-109 and the separately named
   optimized implementation if used.
5. **Paper/AFP rank-rule distinction:** `Submodularity.thy` proves
   `no_join_satisfies_paper_inc_rule` and `no_PaperJoinable_rbt` for a
   flag-free join and the stated RBT rank. With unchanged empty children,
   an old red singleton would force the joined rank to be 1, while an
   old black singleton would force the same call's rank to be 2. The
   paper's extra flag resolves that ambiguity; the AFP instead uses a
   different one-sided rule and proves the work bound with it. This is
   not evidence that the paper's flagged algorithm is inconsistent.
6. **Costs/quantifiers:** keep actual T_join correspondence, leaf versus
   key size, uniform finite bounds, and asymptotic filter domains explicit.
   The newer proof source is valuable precisely because these details can
   be inspected; importing only its headline formula would lose them.
7. **Acceptance:** all 111 numbered entries remain obligations or
   explicitly identified support/disposition work. A later chapter closure
   needs exact Lean mappings, actual recurrence/observation correspondence,
   matching validation, and both independent review axes on the same
   immutable candidate. This source inventory and the external proof
   archives do not themselves complete any Lean coverage.

This original reconstruction preserves mathematical scope without copying
the whole manuscript. The mutable official PDF URL and exact hash remain
explicit; no immutable official URL for this PDF edition has been found.
