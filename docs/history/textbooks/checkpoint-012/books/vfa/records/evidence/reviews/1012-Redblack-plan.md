# Independent bounded review — #1012 Redblack plan

**Outcome: clear for planning; no actionable findings.**
This is an independent source and reuse-plan assessment within the existing
whole-book workflow. It is not an implementation review axis, a compiler
result, or chapter acceptance. All proposed operations, adapters, proofs,
instrumentation and executed comparisons remain implementation obligations.

## Reviewed identities and scope

- Frozen author plan: `../specs/1012-Redblack.md`, SHA-256
  `cf11fe2794f8c40814ab19228eb92f39c86cb9ee957065c8d54e3e6e59dfba10`,
  58,809 bytes, 710 lines. The author announced the freeze before this review;
  the full plan was read and its identity checked during reconciliation.
- Complete VFA 2.1 `Redblack.v`: SHA-256
  `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2`,
  27,066 bytes, 838 lines. Root independently read the entire chapter before
  assessing the frozen plan, including the abandoned proofs, tactic hole,
  advanced exercise, enumeration prose and execution discussion.
- Inventory: `../source/Redblack.inventory.json`, SHA-256
  `c801f47c6922fca2dd72b29f3a59c1f650461bc5bb834ed70cbd8f9389e58c34`.
- The complete auxiliary `test_searchtree.ml` and Extract chapter had already
  been independently read for the preceding source review. The accepted
  Extract implementation does not yet exist; its reuse remains conditional.
- Inspected project candidate:
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.
  The running Preface/Perm gate is separate from this planning assessment.

Repository AGENTS, implementation/review rules, README build/audit guidance,
architecture/domain guidance, GLOSSARY, ADRs 0001/0010 and the user's local
ticket/checkpoint requirements were applied. Planning does not open another
implementation loop or authorize bypassing the chapter sequence.

## Coverage reconciliation

The exact 45 declaration IDs occur once each and in inventory order. All
13 exercise names and exact source ranges match, including the advanced
`redblack_bound` exercise and both of its executable definition holes. All
six pedagogical commands have the correct kind and line: the five Checks
at 576, 580, 584, 588 and 592, and Extraction at 799. There are no source
module records. All 22 source/provider identity rows match actual file bytes.

The source admissions are future proof obligations, not trusted facts. The
admitted tactic is explicitly replaced by kernel-checked reasoning in the
two-part insertion invariant proof. The four abandoned proofs retain their
statements and methodological dispositions without becoming false claims or
requirements to reproduce incidental Coq goal counts. The grading constant
does not replace the advanced mathematical work.

The full source read also confirms coverage beyond lexical declarations:
insert nonemptiness, the relevant complete enumeration contract, the
performance argument, root convention, minimum-depth hint, runnable exports,
and an actual bounded ordinary/red-black comparison.

## Exact algorithms and reusable carrier

Actual pinned `RBTree/Basic.lean` definitions confirm the raw carrier match:
nil and a colored node with two children and one key/value entry. `All` has
the stated root/left/right conjunction. Its implication lemma has the needed
direction. `foldr` is the source's right-accumulator-then-left recurrence;
`foldr_cons` and `toList_node` supply the claimed all-accumulator and inorder
equations. `setBlack` agrees on both nil and nonempty nodes.

The source's full balance has left-left, left-right, right-left, right-right
priority. The pinned library's right balancing helper tries right-right
first, and its insertion calls only the helper for the changed side. Its
final insertion blackens only for an originally red root. The plan preserves
all three differences and does not misapply a library insertion theorem to
the source operation.

The ordered overlap fixture is sound by direct constructor reasoning: root
0 with red right child 2 and red grandchildren 1 and 3 promotes 1 under the
source priority and 2 under library balance2. The final blackening difference
is already visible at empty input. No compiler or test execution is claimed
for these planning observations. The future connected checks require
propositional constructor/root facts, correctly avoiding the library's
inorder-stream BEq as evidence of structural equality.

The supplied two Boolean comparisons remain in executable branches. A
proof-only decoded order does not silently replace them with Int comparisons.
Key replacement includes both the key and value in the equality case. No
payload equality/order or globally fixed default is invented.

## Ordering and semantic hypotheses

Source BST uses complete subtree bounds, rather than only child-root tests.
`balance_BST`, arbitrary-predicate preservation and lookup preservation retain
their distinct hypotheses. RB is not added to the source's BST-only results.
The exact balance lookup equation preserves the comparison orientations and
the arbitrary default/query quantifiers.

The malformed-tree counterexample explains why the source same-key law needs
BST: a black root 2 with left red root 5 and red left grandchild 4 can rotate
that pre-existing violation after insertion of 3 into the right subtree.
The resulting lookup for 3 follows 5 then 4 and misses. Conversely the
ordered overlap example need not satisfy RB, and a shape-valid duplicate-key
tree need not satisfy BST. These are useful independent boundary checks.

Strict-comparison reflection suffices for the same decoded key and ordering
arguments; decoder injectivity is retained where distinct original keys or
original-key identification require it. The plan does not impose an inverse
or surjectivity on finite signed carriers. Default BitVec ordering remains
distinguished from the required signed comparison.

Direct inspection of `cmpLT`, `cmpLT_iff`, `ordered_iff`, `Ordered.unique`,
`find?_some_eq_eq`, `find?_some_mem`, `Ordered.memP_iff_find?` and
`Ordered.find?_some` confirms the proposed premises. The comparator relation
contains a conditional TransCmp binder; the plan requires the actual lawful
instance before identifying it with decoded strict order. Finding a binding
implies membership without ordering, while the converse needs the stated
ordering/cut assumptions. Comparator equality of arbitrary key/value records
is not treated as record equality; the uniqueness theorem needs membership
of both records in the same ordered tree.

## Balance predicates and depth

The actual constructors of `Balanced` index root color. The source indexes
parent color. The proposed bridges are correct: source RB under a red parent
corresponds to a black library root, and source RB under a black parent allows
either library root color. Empty contributes black height zero.

The actual `RedRed` constructors include a balanced empty tree. Consequently
the planned NearlyRB equivalence correctly adds nonemptiness. Both source
ins_RB conclusions are preserved at the same black height, with shape
reasoning independent of BST or comparison laws. Parent-index weakening does
not recolor a tree; root blackening can change black height and retains its
existential result. The singleton and empty cases expose that distinction.

The complete pinned `Depth.lean` was inspected. Its exact size/depth
recurrences, root-sensitive depth bounds, exponential size bound and
`depth_bound` theorem agree with the plan. The mistaken depthLB docstring is
not relied upon. The source's separate minimum-depth exercise still needs
the actual lower path induction; a logarithmic-size theorem alone would not
discharge it. The Nat-log bound uses size+1 and handles empty/singleton
inputs. BST is unnecessary for shape bounds and remains necessary for their
unique-key map interpretation.

## Enumeration, costs and execution

Color erasure retains original keys and payloads. The plan requires raw
lookup, all-node, BST, height, size and all-accumulator traversal adapters.
It correctly rejects structural commutation between balanced insertion and
ordinary unbalanced insertion. Inorder update uses the accepted
replacement-aware list operation and actual source rotation preservation.

The proposed enumeration reuse retains the raw/valid asymmetry, a value
independent of every default, projected-key nodup, both abstraction routes,
and canonical enumeration from partial binding equality. Presence is not
inferred from total lookup at one default. The existing WF closure
constructors are not used as an unexplained proof: the plan points to the
proved WF equivalence and keeps ordering and balance contracts separate.

The resource recurrences are consistent with the source branches: one
comparison on a left branch, two on right/equality, zero at nil; no balance
call at nil/equality; one balance after a recursive return; one syntactic
node for fallback/terminal/replacement and three for a rotation. The proposed
height bounds include the terminal insertion node and final root blackening.
The sequential full-pattern model charges root selection plus attempted
patterns, with a separate bounded-depth observation refinement. These are
explicit source models, not claims about generated match code or heap
allocation. Traversal invocation count 2*size+1 and cons count size keep the
nested right call and do not imply constant stack use.

Lookup/insertion growth retains terminal work, comparison weights, actual
current size and both invariants on insertion histories. Finite signed width
and unbounded integer comparison costs are not hidden in an unconditional
machine-time claim. Erasure proves values only; cost bounds need their own
recurrences and inequalities.

The benchmark adaptation matches the independently inspected ML program:
construction precedes the timer; random queries are fresh random draws;
the printed insertion/lookup label is inaccurate; the returned hit count is
discarded. The plan requires reproducible identical stored workloads for
controlled comparisons, distinguishes RNG-in-loop source-shaped timing,
checks results against an independent reference, and labels direct/compiled
modes and clocks honestly. Historical timings are not local measurements.
The original named large configurations remain recorded, while bounded
actual execution is required and cannot be presented as a completed larger
run. Signed correctness cases remain distinct from positive-only workloads.

## Findings and disposition

| ID | Status | Finding |
| --- | --- | --- |
| — | None | No actionable omission, false provider claim, weakened source contract, unjustified hypothesis or unsupported completion claim found. |

The frozen plan is clear as preparation. Implementation remains blocked on
accepted #1011 Extract, then requires actual checked adapters/algorithms,
connected applications, full source coverage, execution evidence, the
required candidate build/audit, both independent implementation review axes
and final candidate verification. Only root may record acceptance and create
the corresponding durability checkpoint.

This assessment ran read-only file, digest and inventory comparisons. It
started no compiler or benchmark and modified no project source, dependency,
cache, configuration or GitHub state. Its only direct write is this review.
