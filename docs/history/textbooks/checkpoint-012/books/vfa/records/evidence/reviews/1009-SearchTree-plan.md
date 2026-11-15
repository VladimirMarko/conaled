# Local #1009 SearchTree — independent planning review

2026-11-02. Root independently reviewed the plan authored by `searchtree_plan`.
This bounded source/reuse assessment supplies no compiler result, implementation
review-axis approval, or chapter acceptance.

Plan: `../specs/1009-SearchTree.md`, SHA-256
`7bd10a9e771d38364bc806d28b38e6cca8f042a7701e3b852fe331d4cd0819e3`.
Complete pinned source: `SearchTree.v`, SHA-256
`44b9464a10e8c9e3222530f6f26be45bd44d1c0568deb1710417618706fae61d`.
Inventory SHA-256:
`23dad4eb956d2e6acddf5a845e4ac32b10156da02069defb6a202c914af3331f`.
Inspected candidate context:
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, still under full validation.

## Outcome and coverage

No actionable omission or incorrect proposed contract was found. I read all
1,325 source lines and the complete plan. Its 90-record table matches the
inventory in exact order; all 35 exercise names and line ranges match,
including 24 optional, 12 advanced, and their eight overlaps. The 11 commands,
the grading stub's substantive bound exercise, and the deliberately aborted
false completeness specification have explicit dispositions.

The plan preserves unconditional raw-tree search/update laws, all-node
predicate preservation, enumeration completeness, bound-value quantifier order,
and inverse correctness. It retains BST precisely for enumeration soundness,
inverse completeness, ordering, projected-key uniqueness, and the source
abstraction correspondences. The two structural counterexamples coexist with
the valid structural shadowing theorem; default-valued observation is not
mistaken for presence or representation equality.

All source recurrences remain recognizable: short-circuit strict comparisons,
same-key replacement, inorder append, arbitrary-accumulator traversal,
kvs_insert, head-wins list decoding, collision-to-none union, and direct tree
decoding. The kvs_insert separator theorem keeps its original premises without
an added sortedness restriction. The union update premises are local absence;
the append decoder theorem requires disjoint projected domains but no added
within-list nodup premise. Primed abstraction proofs retain the independent
structural route before the final enumeration-coherence theorem. Proposed
canonical enumeration uses equal partial bindings, with valid trees, rather
than one default-valued observation.

## Reuse and resource boundaries

I inspected the actual BinaryTree constructors, map/shape facts, and the entire
Get module. The plan accurately distinguishes raw key/value storage from
indexOf's complete-label/path interface. The inspected Function.update APIs,
staged table observation laws, List.Nodup append interfaces, and
List.Pairwise.eq_of_mem_iff (including its surrounding Antisymm assumption)
support the proposed uses. Strict projected-key order and actual pair
membership can support canonical enumeration without imposing an order on
payloads; ordinary non-strict projected-key order alone does not supply that
antisymmetry.

The actual appendWithCost_exact, measured erasure/sequence interfaces, and
isBigO_of_nat_bound types agree with the plan. Its traversal is not silently
identified with the existing leaf-labelled Bracketing traversal. The source
append association gives the stated future copy recurrence. I checked its
left-chain, right-chain and perfect-tree formulas mathematically; these remain
unproved implementation obligations, not new Lean evidence. The accumulator
counts distinguish cons requests from visits and do not claim constant stack
space, pointer identity, or native allocation behavior. The unary comparison
draft's exact min-plus-one result and difference-only counterexample were
inspected, with its separate strict-comparison/native-runtime limitations kept.

All 14 listed provider/input hashes, source and inventory hashes, and the plan
digest match. The existing erasureSquare universe limitation is stated rather than
silently restricting all payloads. The plan provides meaningful malformed-tree,
default-binding, duplicate-key, union-collision, structural, and measured cases.

Implementation remains blocked by accepted Maps. Actual elaboration, connected
proofs and statement review, full isolated build/audit, applicable regression,
both independent implementation review axes, final candidate verification, and
an immediately uploaded recovery checkpoint remain mandatory. No compiler,
source/dependency/cache/configuration change or checkout mutation occurred in
this review. Only this review record was written.
