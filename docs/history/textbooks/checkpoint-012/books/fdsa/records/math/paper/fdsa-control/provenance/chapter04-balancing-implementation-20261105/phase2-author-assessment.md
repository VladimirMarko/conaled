# Phase 2 author source and mathematical assessment

Status: UNCOMPILED. No compiler, Lake, candidate check, audit, or independent
review was run by this author. The source readback is complete; source names
and signatures are not substitutes for actual elaborated statement inspection.
This continues the same whole-Chapter4 loop and the frozen 76 obligations.

## Actual execution and tariff

Resources.TreeBalance.balRun has its own recursive execution. Its recursion
sizes, left-before-root-before-right control, Option failure branches, suffix
selection and node construction agree with Trees.Balance.bal. Observations
come from Resources.bind applied to the actual children; CallCount.tick charges
one entry after each selected body, including the size-zero case. No result is
produced by assigning a synthetic cost to an independent call of pure bal.
The declared primitives are arithmetic, variables, constructors and head/tail
pattern matching. They add zero in this conditional source call-count model.

## Public statement meanings

balRun_zero and balRun_succ expose that execution. balRun_value compares the
first projection with the ordinary core for every size and input, including
all failing paths; it assumes neither sufficient input nor inhabited labels.

balRun_cost retains n <= xs.length. Its induction uses the pure left result's
exact decomposition and size to establish a nonempty root suffix and the right
call's domain. It then adds the two actual recursive costs and the parent's
entry. With m = (k+1)/2, the recurrence is
(2*m+1) + (2*(k-m)+1) + 1 = 2*(k+1)+1.
The arithmetic also uses m <= k, so truncated subtraction does not obscure
the source split. Zero contributes one even though it produces no internal node.

balRun_eq packages separately proved value and cost. balRun_of_some derives
the domain from successful execution; it does not replace the input premise
with an assumed cost or observation. balRun_prefix exposes the exact retained
suffix, inorder prefix and node count together with the measured result.

## Independently expected connected clients

Examples.TreeBalanceCost.valid_execution consumes the public success-domain,
value/result refinement, decomposition, node-count and suffix laws for an
arbitrary label type. prefix_execution is a universal sequential client.
The generic zero call costs one. The previously frozen three-node unsorted
prefix and full ten-node Figure 4.3 consume the ordinary public execution
results and measured correspondence, obtaining costs seven and twenty-one.
The count-only observations also invoke the public balRun_cost theorem.

The failed one-node request on [] is an actual execution: its zero-size left
child returns an empty suffix, so no root and no right recursion are available.
Its cost is two. A separate example proves that this differs from 2*1+1, and
another invokes the unconditional value refinement on that failed input.
Consequently no result or documentation implies the count law on failure.

The cost does not account for the direct inorder performed by balanceTree,
physical sharing, allocation, bit-cost arithmetic, Lean execution or wall time.
No linear full-tree balancing theorem is claimed here.

## Scope and completion boundary

Together the two author phases supply source implementations for C04-047..053,
the full concrete Figure 4.3 portion of C04-058, and C04-061. General height,
minimum height, almost-completeness, their wrapper corollaries and the strict
BST connection remain mandatory later phases. No absent/unaccepted Shape
module is imported. The original 76-obligation chapter and its final independent
Standards/Spec reviews, complete check/audit and immediate verification remain
unchanged. The four new modules require the root's serial compiler checks,
actual statement review and acceptance gates. No acceptance is recorded here.
