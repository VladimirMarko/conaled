# FDSA-XT08 implementation-side source assessments

This record belongs to the existing authoring workflow. It is not independent
Standards or Spec acceptance, compiler evidence, or a chapter completion.
Chapter 1 remains active and its attempt3 is the sole running project gate.

The original base is `66eae34815a177c6b4bf5120e05202ebb8876c91`.
The frozen 22,861-byte /385-line requirements have SHA-256
`22fcd74bdfdc71085b690041f6dddc10407f188d11be83fe7ffdc084c31a5535`.
The complete source/API/case preflights, author readiness, saved checkpoint0057
receipt and exact release record remain separate retained evidence.

## Core: complete stopped source and root readback

Architecture reported all writes stopped after reading the complete final
`Applications/Resources/TreeLeftmost.lean` and checking its statements and
pinned interfaces. Root independently read all 388 lines of the exact stopped
file: 16,112 bytes, SHA-256
`c8a2cd47ce515330d36f16810add1af2401ff39f36bd7e74a83610d27e5c7cd0`.

The actual recursive run uses the original BinaryTree and measured bind/pure
with CallCount.tick. The nil extension and left-empty base both charge one;
the nonempty recursive branch consumes only the actual left-child execution.
No terminal nil is called in a successful descent. The result and entry count
are projections of that execution, and the successful-child rule retains both
the actual residual and the untouched right fringe.

The domain laws cover every raw nonempty tree, with no inhabitance or decision
premise. The inorder theorem is one-way from the actual successful result.
Membership, head/tail and occurrence decrement derive from that equation.
Residual height nonincrease instead follows the actual splice structurally.
Whole measured map transport includes both the removed entry and residual
across independent universes without injectivity or order assumptions.

Generic Ordered preservation uses residual membership to retain ancestor
bounds and requires no transitivity. The separate all-tail relation retains
Transitive R. Its strict-key specialization needs only Preorder: leastness,
removed-key absence and exact residual-key membership retain strict input
order and the actual successful result. Specializing the generic preservation
theorem supplies strict-key residual order without a duplicate wrapper.
There is no comparator or global key-injectivity premise. Entry positivity,
nonempty/successful height bounds, the existing height-to-node bound and the
all-input height-plus-one bound preserve the selected empty-domain distinction.

Relative to the first published 391-line source, the author changed only the
proof of the successful-child rule and the two head/tail proofs. The final
root readback includes all three proof bodies. Root found no concrete
mathematical/domain discrepancy in the complete stopped source. This does
not establish elaboration, termination acceptance, warnings or kernel validity.

## Intermediate example and documentation readback

Root read the entire initial 351-line /13,417-byte example snapshot, SHA-256
`293c9b35931db9150a683832a439815ed5379e939ed35139047c3f2375c48a2c`.
It is an intermediate source, not the completed example suite. The actual
base/splice executions, semantic observers and successor body, and all-length
shifted chain equations in that snapshot matched the fixed expected behavior.
The final cases and public-law connections still require complete readback.

Root also read all 375 lines of the initial source note, 23,806 bytes, SHA-256
`10f02a0daec4895a5351e16d3240ac9b261b59448ea14962f9b1a8541eeafb48`.
That version explicitly left its declaration maps pending the actual source.
Its source identities, empty-domain extension, one-way raw results, separate
order/cost claims, p.82 correction, ordinary-versus-join timing distinction,
full Isabelle notice and retained chapter obligations had no concrete
correspondence discrepancy in root's readback. Final declaration maps and the
append-only reconstruction-map section remain to be read and checked.

## Completed examples and documentation

The case author completed the full final read and stopped at 26,744 bytes /
609 lines, SHA-256
`35df93b81d199b91fadcea90597409b154132cb161552f92d084f741f499b1e6`.
Root read the complete initial source, all 250 added client/boundary lines and
the added import in the 602-line snapshot, then every final proof-only delta.
The line comparisons found no other source changes. The only statement-text
adjustment explicitly supplies the already intended Nat type for one duplicate
node-count expression. The author also read the stable core and pinned range
and lookup interfaces. Both source assessments found no concrete mathematical
or domain discrepancy; elaboration and warning behavior remain unvalidated.

The general branch and opaque-fringe clients consume actual full-run laws.
The promoted and printed cases connect actual outputs to the public inorder,
node, height, order, minimum, exact key removal and count theorems. The complete
semantic entries flow through bind/pure observers and primitive_rule; some
false stays distinct from absence. The successor body consumes the actual
right-child result and retains its false payload, with only extraction subcost
one. Lookup assumptions remain local to the observers: BEq, ReflBEq, and then
LawfulBEq plus strict key order for absence. Noninjective semantic mapping and
outer-annotation erasure have their distinct meanings and preserve the actual
residual/count through run_map.

Duplicate-key and projected-label cases refute unconditional key/set removal
without weakening the one-occurrence law. The malformed example returns a
nonminimum first label despite an ordered residual. The next relation exhibits
arbitrary-relation preservation while refuting an all-tail conclusion without
transitivity. The exact sizeSample execution starts cache-valid and leaves
three nodes with stale root cache four; the actual Cached.Valid predicate
fails, while erasure correspondence is separately connected. General shifted
left/right chains specify the complete returned trees for every nonempty
length, their range inorders/order/size/height, exact counts n versus one,
residual-shape difference for n at least three, and sharpness/tall-tree clients.
The empty extension remains a separate count-bound boundary.

The documentation author completed and stopped both files, then inspected the
last two proof-only case changes and confirmed that no documentation rewrite
was needed. Root read the entire initial note and every final delta, including
the complete actual core/example declaration maps. The final note is 31,269
bytes /434 lines, SHA-256
`b8f2ca0448a960a409aca5e02281723b8dd4585db2cee67e78f835a7f57d1ba8`.
Root read the entire final appended map section. The final map is 28,971 bytes /
423 lines, SHA-256
`1c9bc81e8c55e34d31149245470e21fb61a2c3f550fc7884eeef35ba4c6cb2a7`.
No source/cost/domain correspondence discrepancy was found. All original
chapter obligations and the later algorithm/representation boundaries remain.

The precommit check accounts for all 23 original baselines: 21 are unchanged,
the entire original 23,287-byte map prefix is identical, and the root change
is exactly one import. The complete 1,673-byte Isabelle notice is present
byte-identically once. Requirements, main, the immutable C1 source checkout,
pins and tooling are unchanged. There is no project build in the source
checkout. The exact checks and file identities are retained in
tree-leftmost-source-precommit.json and tree-leftmost-source-final.json.

The five-path source is committed cleanly as
`7b8ab2bee299c937256bf9ce7e82977333d07134`, parent/original review base
`66eae34815a177c6b4bf5120e05202ebb8876c91`, on work/fdsa-tree-leftmost.
The diff is five files and 1,500 insertions. Checkpoint0058 is the next action.
This commit and source assessment do not accept the unit or any chapter.

## Acceptance boundary

All XT08 source is uncompiled and unaccepted. No compiler, Lake invocation,
checker, project hash helper, cache operation or final review loop has been
started for this unit during C1 attempt3. Applicable prerequisite integration,
matching immutable-candidate focused/full checks, both integrity phases, the
complete integrated build, exhaustive transitive axiom audit, both retained
independent review axes and immediate candidate verification remain mandatory.
