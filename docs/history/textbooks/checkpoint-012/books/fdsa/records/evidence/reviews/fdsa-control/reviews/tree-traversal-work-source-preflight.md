# XT05 bounded source assessments

These are independent source-only readings of stopped draft files, not final
Standards/Spec review, elaboration, a build, audit or acceptance. Frozen full
requirements and original base remain unchanged. Root-recorded reading-phase
identities are in `tree-traversal-work-source-preflight-snapshot.json`; readers
are not claimed to have computed or checked those digests. Old Chapter 1 gate
80227 remained unchanged, without a second compiler/checker/project hash helper.

## Pure traversal-work core — book_inventory

**No concrete mathematical defect or likely elaboration/API mismatch arose.
No XT05-SP ID is assigned.** The reader read the complete frozen requirements,
all three retained preflights and stopped `Applications/Trees/TraversalWork.lean`,
plus exact reused fold, tree, binomial-coefficient and list identities. No
declaration was elaborated or checked.

### Pair fold and canonical size

Private `leftSummary` uses the required ordinary pair fold, with algebra
`(nL,AL),a,(nR,AR) -> (nL+nR+1,AL+AR+nL)`. Its first projection is connected
to the existing size algebra by `fold_fusion`, then to canonical `numNodes`
by `fold_numNodes`. The public interface exposes only `leftSizeSum`, without
a second public size carrier/API.

The public node equation consumes the first-projection theorem before replacing
the accumulated size by `l.numNodes`. It states the intended occurrence sum,
not an assumed separate size recurrence. Its external mathematical-observation
description correctly avoids inserting an extra measured traversal.

### Recurrence, map and occurrence semantics

Nil/node equations match XT05-01. `leftSizeSum_map` permits independent source/
target universes and arbitrary label maps. The pair algebra ignores the mapped
label, requiring no injectivity, equality decision, order or inhabitant.
`leftSizeSum_repeated` retains both child occurrences, `2*A(t)+t.numNodes`,
with no deduplication of equal trees or labels.

### Sharp arithmetic and boundary cases

`2*A+n<=n^2` is correct at nil and singleton without positivity. The node
induction leaves nonnegative gap `2*r.numNodes*(l.numNodes+1)`; the supplied
nonnegativity facts match the polynomial argument attempted by `nlinarith`.
`A+n<=n^2` follows from nonnegativity of A. The private Pascal-derived
`2*(n.choose 2)+n=n^2` identity supplies the sharp binomial bound without Nat
subtraction/division conditions. The reader directly confirmed the pinned
signatures/orientation of `Nat.choose_succ_succ'` and `choose_one_right`;
their uses in both arithmetic and left-chain attainment fit those APIs.

### Explicit chain families

Both constructors take a supplied label, introduce no global Inhabited and
make no positive-size claim for Empty. Canonical node-count/height statements
include zero. Left-chain inorder uses `replicate_succ'`, appending its root
label; the right family uses `replicate_succ`, prepending it. Exact identities
were checked in retained Lean 4.35 primary source copies. Both return the same
`List.replicate n a` without label equality.

Attainments `A(leftChain a n)=n.choose 2`, `2*A(leftChain a n)+n=n^2`, and
`A(rightChain a n)=0` are correct. Their proof structures preserve zero/one
boundaries and use the same Pascal recurrence as the arithmetic bridge.

### Limits

This file covers ordinary XT05-01 mathematics. The old Unit-chain bridge belongs
in connected Examples as frozen; its absence from the domain file is not a
finding. The reader did not assess the resource theorem, actual execution
instances, inequalities, asymptotics or developing client in this pass.
Source-level API fits do not establish successful simp/rw/ring/nlinarith
elaboration. No observed Lean failure is claimed. No file, Git/cache/gate state,
compiler/checker/project hash helper changed or ran. No acceptance credit.

## Generic actual fold-cost theorem — architecture

**No XT05-RP finding arose.** `Applications/Resources/TreeTraversalWork.lean`
matches XT05-02 and the inspected existing `TreeFold` contracts. Statement and
proof route are sound at source level; compilation remains outstanding.

### Callback premise and parameter scope

`run_cost_leftSizeSum` has argument order entry, empty, callback, d, c, hcost, t.
Entry, empty summary, callback and coefficients are fixed before the target
tree. The premise ranges over every finite child-tree pair and label and
inspects the callback on the actual two run values using those same parameters.
It neither requires an all-summary law nor restricts the contract to one
selected tree's subtrees. It is local callback work, not an assumed total-run
formula.

No extra value-erasure argument is needed in the generic proof because neither
entry nor callback changes. The concrete clients must still establish the
premise through actual value/read/length bridges.

### Proof and observation grouping

The node proof expands actual `run_node_cost`, applies `hcost l a r` to that
exact callback occurrence, rewrites both child observations, then rewrites
`leftSizeSum_node`/canonical size and normalizes Nat arithmetic. The collected
polynomial is exactly

```text
e*(2*nL+1)+d*AL+c*nL + e*(2*nR+1)+d*AR+c*nR + d*nL+c+e
  = e*(2*(nL+nR+1)+1)+d*(AL+AR+nL)+c*(nL+nR+1).
```

Rearrangement remains Nat-specific. The theorem does not alter raw Add grouping,
generalize collected observations to arbitrary Add or change earlier transport/
constant-callback contracts.

### Assumptions, boundaries and architecture

Payload and summary universes remain independent. No equality, order,
inhabitant, validity class or other payload/summary structure is added. Nil
reduces to its actual entry, through imported nil and canonical size equations.
Zero d removes shape work, zero c removes the constant callback term; d=c=0
leaves only structural work, and entry=d=c=0 yields zero. No unsupported
positivity or asymptotic claim is made.

The new module contains one theorem, no execution/carrier/cost recursion or
reachability abstraction, and imports no Examples. Required pure constructor
statements have the exact names/forms used. Ring is available through the
inspected imports. No concrete rewrite, namespace or type mismatch was found.
Actual elaboration and broader validation/final axes remain required. The
reader did not assess developing clients or duplicate the pure-core reading.
No files, compiler/checker, Git, cache or gate were changed.

## Natural bounds and actual-family growth — architecture

**No XT05-GP finding arose.** Natural bounds, actual-family growth statements
and `materialize_le_square` match XT05-04. Constants and positivity thresholds
are correct, and proofs concern actual execution projections.

### Upper estimates

Private `size_le_square` derives `n<=n^2` from positive n. `entry_le_square`
derives `e*(2*n+1)<=3*e*n^2`, without requiring positive entry. Each
`nlinarith only` has enough explicitly supplied inequalities:

| Theorem | Upper constant times n^2 | Extra facts |
| --- | --- | --- |
| single_cost_le_square | 3*e+1 | A+n<=n^2 |
| right_cost_le_square | 3*e+3 | A+n<=n^2, n<=n^2 |
| left_cost_le_square | 3*e+3 | 2*A+n<=n^2, n<=n^2 |
| cache_cost_le_square | 3*e+4 | A+n<=n^2, n<=n^2 |

These are direct nonnegative combinations of the supplied inequalities and
retain positive node count instead of silently applying the bound at nil.

### Actual chains and lower estimates

Exact chain theorems return full measured pairs with both list values equal to
`List.replicate n a`. Literal-right work is
`e*(2*n+1)+n.choose 2+3*n` on left chains and `(2*e+3)*n+e` on right chains.
The left lower bound uses `2*A+n=n^2`; its excess after doubling work is
`2*e*(2*n+1)+5*n`, nonnegative for every n, including nil and entry zero.
The right lower bound n<=W likewise holds for all n. Its upper bound uses
1<=n to obtain e<=e*n, yielding `(3*e+3)*n`.

### Standard asymptotics and source witnesses

Both IsTheta declarations concern real casts of actual run projections. The
existing Nat-bound bridge uses upper C=3*e+3,N=1 for both; lower C=2,N=0 against
n^2 for left chains and C=1,N=0 against n for right chains. Constructor matches
pinned IsTheta's conjunction of two Big-O directions. Entry and supplied label
are fixed outside the index, and 1<=n is correctly converted to positive
canonical chain size.

`source_upper`, `source_witness` and `source_rightChain` retain the universal
upper/exhibited lower distinction. `nil_not_square_bound` covers positive-entry
nil without a payload inhabitant.

### Materialization and zero cases

`materialize_cost` consumes the existing actual-bind cost and new single-run
formula, giving `4*n+2+A` for every suffix. Its quadratic bound combines
`(A+n)+3*n+2 <= n^2+3*n^2+2*n^2`; the asserted 1<=n^2 follows from positive
size and size_le_square. Nil is correctly excluded.

The generic zero-coefficient boundary is separate: pure_callback_cost actually
instantiates d=c=0, and zero_pure_callback also sets entry zero. Growth belongs
to the concrete positive-work append callback, with no blanket Theta claim
for arbitrary coefficients.

No concrete declaration, coercion, rewrite or proof-shape mismatch was found.
Polynomial normalization and casted Big-O applications remain uncompiled.
No files, Git/cache, compiler/checker or gate changed, and no final-review or
acceptance result is implied.

## Actual client connections and worked cases — tail_examples_preflight

**No XT05-CP finding identified.** The reader read the complete stopped
420-line `Examples/TreeTraversalWork.lean`, frozen requirements and public
shape/resource/XT03/XT04 contracts needed by its uses.

### Actual callback instantiations

The four instances match generic argument order and actual reached-child
premises. Single (d,c=1,1), literal-right (1,3) and comparison-left (2,3)
consume their actual step cost, actual child value and inorder length.
List-cache annotation (1,4) consumes the actual measured smart node, actual
returned cache read and inorder length. It retains the explicitly typed
raw-run hread bridge from XT03-CP01; final `simpa only [annotateRun,Nat.one_mul]`
reconciles the wrapper explicitly. Four already includes three helper charges.
The premise remains over actual summaries from arbitrary finite child trees
at fixed parameters, without silently substituting unrelated summaries.

### Zero parameters and finite cases

`pure_callback_cost` genuinely instantiates d=c=0 using the existing pure size
callback; entry zero then gives zero observation. Removing structural entry
from the actual append/cache sample separately leaves 6/14/16/18. Entry-one
counts 15/23/25/27 are derived through new formulas; nil/singleton retain their
offsets. The asymmetric sample has A=2. `repeated_singleton` consumes the public
repeated-child law and obtains A=1.

### Chains, labels and returned objects

`old_chain` keeps the original Unit family and supplies only its equality
bridge. Both chain execution theorems retain full measured results, including
the replicated list for every n. The arbitrary-label map theorem preserves
actual literal-right work across independent payload types; its constant Nat
case retains all four occurrences and work 23. The three-node countercase
connects canonical size, height, complete returned list, A=3/0 and work19/16
without label equality. Empty uses the existing empty-tree theorem, while
positive-size families have a supplied label. The cached sample treats its
result as an annotation tree and connects reader, erasure and cost, never
identifying that full tree with an inorder list.

### Complete suffix-program comparison

The client independently derives equality of the two values and the exact
cost equation materialize=buildOnce+A. Both quantify over every suffix and
consume existing actual-program contracts. Construction remains included in
buildOnce1,1. The right-chain theorem uses both projections to establish
equality of complete measured results; the left chain retains excess choose(n,2).
Nil/singleton/sample totals are correctly 2/2, 6/6 and 20/18. Invocation-only
sample nine is not substituted for the staged total.

No concrete proof-expression/public-interface mismatch was found. This does
not establish elaboration; bounds/Theta were the separately assigned reading.
No overlap required further coordination. No file, compiler, checker, project
hash helper, Git/ref/cache or gate operation occurred. No final approval or
acceptance credit.

## Documentation reading and correction — book_inventory

The reader read the full reconstruction note and only its appended XT05 map
section against the frozen requirements and complete source preflight. One
narrow finding arose; no discrepancy in work formulas, source-model
qualifications, worst-case argument or retained scope was found.

### XT05-DOC01 — Identify the construction theorem

Classification: low-severity documentation precision, not a mathematical
formula defect. In “Complete suffix programs with construction included,” the
original paragraph said that construction cost is included in the second line
and then used “Its value equality has inner measured-result codomain.” After
the displayed buildOnce cost equation, that referent was ambiguous.

The reader's narrow declaration check confirmed:

```text
build     : Measured (List α -> Measured (List α) Nat) Nat
buildOnce : Measured (List α) Nat.
```

The nested function codomain belongs to build/build_value. The suggested fix
names build_value, says it identifies the returned invocation function while
preserving each application's inner measured result, and attributes application
work to the independent all-suffix invocation theorem.

### Remaining documentation assessment

Literal association is correctly attributed to the book. Exact counts concern
saved measured executions, with the absent generated timing declarations and
postdating companion snapshot qualified. Annotation-ignoring Tree2.inorder is
distinct from full list-cache construction; the latter's returned tree uses
reader/erasure/validity bridges, and a mathematical projection is not a new
charged execution.

Sharp division-free/binomial bounds include nil/singleton. Proportional uppers
require positive size, and the left-chain lower includes zero. Universal upper
plus explicit witnesses supplies the worst-case reading, with right chains
linear. Entry and coefficients are fixed across families; zero entry retains
callback/helper work, and arbitrary zero coefficients receive no unsupported
Theta classification.

Complete suffix comparisons retain arbitrary suffixes, actual binds,
construction in buildOnce1,1 and the independent invocation theorem; invocation
alone remains separate. The formulas 4*n+2+A versus 4*n+2 and small counts are
consistent. Uncompiled status, prerequisite acceptance, pending gates, chapter
order and original scope remain. Exclusions do not invent future requirements.

Apart from the narrow declaration check for DOC01, the reader did not repeat
pure-core assessment or independently review new implementations in this pass.
No file/compiler/checker/hash/Git/cache/gate or final-review action occurred.

### Original bytes, implementation and same-reader recheck

Before correction root retained the original complete note at
`tree-traversal-work-preflight-snapshots/XT05-DOC01-fdsa-tree-traversal-work.md`,
SHA-256 `e8a35e4e1d7e866b64f2b415bf2042476ac509dc5f0d7e50a616cb6420599867`,
14308 bytes / 275 lines, with a separate identity JSON. Frozen requirements,
Lean files and source map were unchanged by the fix.

The corrected paragraph explicitly names build_value, supplies the returned
function type `List α -> Measured (List α) Nat`, preserves both inner components,
attributes application work to the all-suffix theorem, and distinguishes
buildOnce's own ordinary-list value from that construction function.

The same reader then reread only the corrected paragraph and confirmed the
ambiguous referent is removed without changing formulas or scope. Disposition:
**implemented and source-rechecked; final confirmation pending**. The reader
performed no edits, compilation/checking/hashing, Git/cache/gate or final review.
This source recheck neither erases the finding nor replaces the final axes.
