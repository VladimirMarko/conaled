# XT07 source and statement assessments

Candidate: `66eae34815a177c6b4bf5120e05202ebb8876c91`.
Original base: `28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2`.
Frozen requirements SHA-256:
`309bd487fbe1a49ddd1348af0e517327ebf22614b9e5adcf92d1254a9aeca7a1`.

These are author/coordinator source assessments, not independent final
Standards or Spec review, compilation, integrated audit or acceptance.
All three source authors stopped writes before the root's local commit.
Exact six-path identities are in `tree-order-source-identities.json`.

## Core author: /root/tree_order_api

The author read the complete frozen requirements and all three preflights,
the applicable project/implementation/example-driven guidance and actual
inherited observation interfaces. Its pinned-shell baseline check observed
the clean exact base and branch, absent owned file/build directory, and
matching frozen requirement identity before editing. It edited only
`Applications/Trees/Ordered.lean`.

The complete 126-line core was read back per claim. Its one recursive
`Ordered` predicate has whole-subtree bounds and no typeclass/inhabitance/
equality assumptions. Pairwise-to-structural ordering is arbitrary in R;
the reverse supplies actual cross-subtree comparisons through explicit
`Transitive R`. The iff and inorder congruence retain that premise. Direct
relation weakening and exact arbitrary-map pullback require no relation laws.
Forward mapping consumes those two public laws. Key-preserving mapping is
an iff with only LT on the key type, not global injectivity.

The strict key bridge consumes the generic theorem plus `pairwise_map`,
then standard SortedLT equivalence and Nodup. It uses a key Preorder with
independent payload/target/key universes. Weak order plus key distinctness
uses the actual standard theorem in the PartialOrder domain, preserving
antisymmetry. No extra carrier, comparator, executor, recursive invariant or
sorting-algorithm dependency was introduced.

The actual settled signatures were supplied to the adapter and example
authors, who read the real file. No mathematical contract deviation was
found in the author's complete source readback. Ordinary elaboration,
implicit arguments, map simplification, import sufficiency and linter
behavior remain unverified. Stopped identity: 5,817 bytes / 126 lines,
SHA-256 `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66`.

## Adapter author: /root/tree_order_source

This author likewise verified the clean original base, frozen/preflight
identities, absent owned file and absent project build directory. It read
the complete freeze, preflights, applicable guidance and actual inherited
rotation/cache modules, then read the settled actual core before writing
only `Applications/Trees/OrderedRotations.lean`.

The two ordinary iff theorems take R, explicit transitivity, input/result
trees and the actual corresponding Option-success equation. Both consume
`ordered_congr_inorder` with the actual successful inorder equality, putting
the result first. Failure remains none. The cached iff consumes
`inorder_erase_rebuildLeft_eq_rebuildRight` and has no cache-validity,
balance, summary-reassociation or callback-cost premise. Payload and summary
universes remain independent. No operation or resource theorem was added.

Complete statement/proof readback found no source-level contract deviation.
The three proof terms directly apply the intended public interfaces.
Stopped identity: 1,814 bytes / 43 lines, SHA-256
`c610556b727e7ddd35187c9302649948a203c0d0076e8bf3758fcfc95da50c89`.

The author also read the complete root-owned provenance note and found no
concrete source/frozen-scope mismatch. The reproduced notice matches the
pinned Isabelle notice after trailing-whitespace normalization. Read note:
14,273 bytes / 239 lines, SHA-256
`3bff161862811b03a8f58978bb71a1f3a4ad275c284275f078001cc7cc1af798`.
At that read, example connections were prospective; root later checked them
against the completed actual example file.

## Example author: /root/tree_order_cases

This author read the complete freeze, all preflights, start record, project
instructions, EDD guidance, inherited examples and actual settled core and
adapter. It verified the exact base/branch, absent owned file and no project
build directory before authoring; peers owned other paths. The first
requirement-hash read used an incorrect worktree-relative control path and
reported missing-file; it was corrected to the absolute shared control path,
whose ordinary byte hash matched. This caused no source or requirement change.

Only `Examples/OrderedTrees.lean` was edited. Complete final source readback
included the final explicit mapped-key observation and its rejection client.
Stopped identity: 17,154 bytes / 386 lines, SHA-256
`e7715af3106bfa32983d424abc87ee75c70c8e362bb6d9e27de3ee7a253793d1`.
The author's earlier adapter size of 1,812 was a transcription error, not a
different source version; its final read_bytes identity matches 1,814 bytes
and the stopped adapter hash above.

| Connected family | Public connection and intended observation |
| --- | --- |
| Empty and singleton | Public nil equation and inherited empty/failure laws; no label/default or reflexive comparison is supplied. |
| Generic three labels | Under a<b and b<c over a Preorder, exact inorder [a,b,c] feeds the public pairwise-to-structural law; actual root rotation supplies its result and transported inorder. |
| Printed six-label tree | Exact [2,3,5,6,8,9], strict ordering, key Nodup, actual left/inverse success, and both new ordinary adapters. |
| Successor relation | Root1/children0,2 has recursive bounds but lacks pairwise relation; actual legal rotation keeps inorder yet fails the new root bound. The negative proof extracts next 0 2 through ordered_node. |
| Repeated labels | Existing balancedThree/leftThree retain [1,1,1], weak order, and failed strict order via key Nodup; the left-tree rejection consumes the rotation iff. |
| Distinct records / repeated keys | Explicit lex relation, unequal full pairs (1,10)/(1,20), exact keys [1,1], and failed strict key order through the public distinctness consequence. |
| Missing antisymmetry | A theorem-local Preorder.lift of Bool through constant Nat0 gives weak ordering and Nodup of [false,true], but not SortedLT. No global order instance changes. |
| Adjacency and weak converse | Generic composition with standard SortedLT/IsChain; actual PartialOrder weak-plus-Nodup theorem exercised by ordered sample. |
| Local uniqueness | Payload Nodup and key injectivity on actual support consume standard List results after ordered_key_nodup; no global key injectivity. |
| Relation/mapping laws | Strict-to-weak uses ordered_mono; StrictMono forward mapping uses ordered_map without an iff claim. |
| Noninjective key preservation | discardTag maps Nat×Bool to Nat×Unit, preserves keys, is not globally injective, and has exact mapped inorder [(0,()),(1,()),(2,())]; ordering uses the public iff. |
| Constant key collapse | Existing ordered sample maps to four zeroes and fails strict order through mapped-key distinctness. |
| Cache independence | Existing corrupt is ordered after erasure but invalid; existing valid sizeBefore erases to repeated labels and fails strict order. |
| Actual invalid-fringe rebuilding | Both erased inorders are [0,1,2,3,4,5]; actual left success is retained. Right ordering uses the public observation bridge, left ordering uses the new cached adapter, and each invalidity conclusion consumes the corresponding inherited validity iff. |

The author found no mathematical or inspected-signature mismatch. Remaining
uncompiled risks include generic triple simplification, local letI order
elaboration, Prod.fst/implicit arguments, definitional reductions through
named fixtures, ordinary finite decide proofs, linter behavior and inherited
uncompiled dependencies. These are not claims that the scripts pass.

## Root's complete readback and commit scope

Root read all three completed Lean files, including the final example
version, the provenance note and the complete root/map diff. It inspected
the actual pinned List membership/map/Nodup/support-injectivity and lifted
preorder signatures where relevant, along with the actual inherited
same-inorder, rotation, sizeBefore and invalid-cache theorem statements.
No concrete mathematical or actual-signature deviation was found. The
generic relation bridge, strict/weak domains, exact Option result, local key
uniqueness, semantic-pair distinction and cache-independence claims match
the frozen scope. This readback is not elaboration evidence.

Pinned-shell checks before commit confirmed exactly the six frozen paths,
all stopped identities, no project build directory, and no inherited tracked
source change. The public root adds only its one example import; the
reconstruction map retains its entire original prefix and appends 36 lines.
Staged and unstaged whitespace checks passed. After commit the worktree was
clean and every committed blob equalled the read source bytes.

No XT07 compiler, Lean/Lake invocation, project checker/hash helper, cache
experiment, remote mutation or independent final review ran. Root's local
Git commit is the sole source-history mutation for the draft. The active
Chapter 1 run remains unchanged; all acceptance gates and original scopes
remain open.
