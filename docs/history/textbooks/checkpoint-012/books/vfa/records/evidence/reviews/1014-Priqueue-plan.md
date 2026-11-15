# Independent bounded review — #1014 Priqueue plan

**Outcome: clear for planning after one verified provider-precision correction.**
No unresolved actionable finding remains. This is preparation review, not an
implementation review axis, compiler result or chapter acceptance. The initial
finding, corrected identity and actual verification remain recorded below.

## Exact inputs and independent scope

- Initial frozen plan: `../specs/1014-Priqueue.md`, SHA-256
  `c872b3d57800af62d49bfedec32c9256e50d09da3012cd6742776af6cb04d88c`,
  45,202 bytes, 534 lines. Root read the complete frozen plan.
- Complete source: VFA 2.1 `Priqueue.v`, SHA-256
  `e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d`,
  9,029 bytes, 273 lines. Root independently read every source line before
  assessing the plan, including all signature laws, exercises and prose.
- Inventory: `../source/Priqueue.inventory.json`, SHA-256
  `ed1d31505ff5a96128f3cfe6ed8fe7e033ce95d058b76196abbecfd3931168fb`.
- Inspected project: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.
  Actual accepted predecessor APIs remain future inputs.

AGENTS and its architecture/domain, implementation/example-driven,
build/audit and review guidance, the applicable ADRs and the user's local
ticket/checkpoint requirements apply. This planning review opens no separate
implementation loop and does not authorize later chapter implementation.

All 43 exact source IDs occur once and in inventory order. Both exercise
names/ranges match: select_perm_and_friends at 137–165 and simple_priq_proofs
at 241–269. Both modules and their real endings have dispositions. The
zero-command inventory is accurate; the commented premature End remains
covered as a teaching experiment, not a fabricated Fail command. The inner
admit in select_biggest is explicitly counted as a logical gap to discharge.
All 27 recorded source/provider hashes match the actual files, including the
two pinned core list providers read through the native filesystem.

## Source contract and actual operation boundaries

The source is a mergeable maximum queue over Nat with repeated occurrences.
All eleven laws retain their exact validity and abstraction premises. The
None theorem is an iff about empty abstraction on valid states. Successful
removal preserves validity and relates the original list to the returned key
consed onto every actual residual witness, with the maximum bound on that
residual. Merge quantifies over every actual result witness and concludes a
permutation of the two input witnesses appended.

The specification assessment correctly uses can_relate and validity closure
to avoid vacuous residual/result witness premises. It derives selected-key
membership, a bound on all original keys and one-element length loss from
permutation plus the source residual bound and reflexivity. Empty validity
and empty abstraction provide a nonvacuous realization. None need not imply
raw equality to the distinguished empty state for a generic representation.

The concrete Abs relation is identity, exactly as its single constructor
requires. It is not permutation closure. The interface allows different
witness orders but does not require that every permutation be a witness.
The plan retains this distinction while separately using the accepted
finite-multiset observation. Repeated insertion increases counts and merge
adds multiplicities; a set or keyed replacement queue would lose this contract.

The exact selector compares before recursing, retains the current candidate
on a tie, and reconstructs the displaced/nonselected value on unwind. The
source max branch is h≤i. The accepted minimum selector can be reused only
through that actual reversed-order recurrence, with no runtime list-map
preprocessing hidden in an alleged identity.

Direct inspection of Selection's source confirms that the reusable result
is select_fst_leq, not the stale name select_smallest_aux mentioned in
Priqueue's comment. Its dual supplies a stronger result than the source
auxiliary wrapper, whose redundant residual-bound premise is still retained.
Permutation and length proofs do not need order laws; maximum claims need
their actual total-preorder/reflection assumptions.

## Independently inspected provider contracts

The complete PriorityInterface and ExactPriority files were read, along with
the relevant PrioritySearchQueue selector/replacement definitions and actual
leftist, Huffman, order-dual, list/multiset, extremum and resource declarations.

ExactLaws adds exact occurrence insertion to the weaker keyed interface.
Its add_exact and remove_none fields quantify over every carrier state;
the source only constrains valid states. The proposed all-valid list instance
is appropriate, while future raw forest implementations need a valid-state
subtype or additional all-raw proofs. The proposed subtype adapter preserves
the operations using closure proofs and needs an actual observation witness.
The source's relational abstraction is not simply assumed to be a function.

Unit with OrderDual Nat gives the precise list specialization. Every batch
entry has the intended encoding, so there is no extra payload/priority
invariant. The observation map is distinct from stored state and does not
add runtime traversal to source insertion/removal. Native source append
stays separate because Operations has no merge field.

The actual existing exactList appends on batch addition and sorts at deletion.
The actual takeMin first selects from the tail and then compares the current
candidate. Both are lawful observational ingredients but differ from the
source's raw recurrence and remainder. The concrete fixtures in the plan are
correct by direct source inspection: selectMax 2 [1,3] leaves [1,2], while
the tail-first dual leaves [2,1]; source deletion of [3,1,2] leaves [1,2],
while sort-at-deletion in descending priority leaves [2,1]. These observations
are not claimed as compiled tests during planning.

OrderDual's actual comparison equation reverses the operands. The core
Perm.count_eq theorem requires only BEq; the converse permutation/count
equivalence and the ordinary self/unequal cons count facts need lawful
equality. The Nat specialization supplies it. Multiset coercion equates
lists exactly up to permutation, and multiset addition/one-copy erasure
have the expected count semantics. Optional argmax/WithBot maximum observations
do not return the source remainder and cannot replace its selecting operation.

Chosen-occurrence correspondence is correctly retained as an obligation for
a later split scan/removal implementation. A total-preorder extremum bound
alone does not identify two original values. Conversely, actual scan
provenance can identify the literal occurrence without imposing antisymmetry
or injectivity where the algorithm does not need them. This chapter's selector
already returns the literal occurrence it removes.

## Costs, cases and architectural fit

The measured obligations follow the actual source recurrences. A tail of
length n causes n comparisons, n+1 selector calls and n residual cons
constructions. A queue of length N has N−1 deletion comparisons, using Nat
subtraction at empty/singleton; one delete-entry charge plus actual selector
calls is N+1, including the empty case. The inspected appendWithCost helper
really computes the append and charges exactly the first list's length.

Merge's multiset observation commutes while raw append order and copied-cons
cost need not. In particular, an empty first operand does not force work
linear in the total operand size. Primitive comparison weights, key-size
parameters, terminal work and syntactic allocation models remain explicit.
No native timing, sharing, GC, stack or heap-allocation conclusion follows
from the mathematical counts. The source's discussion of heap/BST merge
is correctly treated as a strategy comparison, not an unavoidable lower bound
for every meld algorithm.

The proposed cases exercise zero versus empty, both comparisons and ties,
source remainder order, repeated maxima, overlapping merge multiplicities,
identity versus permutation abstraction, original-occurrence maximum bounds,
and the exact queue consumer. Repeated deletion of the proposed duplicate
fixture removes one maximum at a time. The plan does not add payload
stability or raw-state equality across implementations.

The placement beside existing priority interfaces, separate relational laws,
native merge theorem and Examples consumer is appropriately bounded. The
source's opening application list does not require reimplementing Dijkstra,
Huffman, simulation or computational geometry. Their order/occurrence needs
are not silently identified with this numeric-maximum queue.

## Findings and correction verification

| ID | Status | Finding and required correction |
| --- | --- | --- |
| PQ-PLAN-1 | Fixed and independently verified | The initial LinearOrder provider row referred to a standard linear-order instance used by existing queue laws. The corrected row states the actual weaker signatures: ExactLaws/ExactQueue require only LE; concrete exactList/exactLeftist use LE, DecidableLE and Std.IsLinearPreorder; ExactQueue.keyed adds reflexivity. It explicitly avoids an antisymmetry requirement. Other plan sections already used total preorders correctly. |

The finding was sent to the author before any clear disposition. The author
changed only that provider row and refroze the plan at SHA-256
`0028ed8013db98fb62e365eb31153ab5030d027bc9a3b9d06f7e8fbb43a42c7d`,
45,453 bytes, 534 lines. Root read the complete corrected row against the
actual declarations. Replacing that row with the recorded original text
reconstructs the exact initial plan SHA-256, proving all other bytes unchanged.
Consequently the source map, exercise/module coverage and 27 identity rows
remain the independently verified ones. PQ-PLAN-1 is closed; no second
unresolved finding was identified.

All chapter implementation, proofs, measured erasure/results, connected
checks, full candidate build/audit, independent implementation review axes
and final verification remain outstanding. Only this review record was
written by the assessment; no compiler, benchmark, project source, cache,
configuration, dependency or GitHub change was made.
