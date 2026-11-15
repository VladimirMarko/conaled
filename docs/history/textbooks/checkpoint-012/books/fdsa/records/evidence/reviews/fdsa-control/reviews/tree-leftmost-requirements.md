# FDSA-XT08 — frozen ordinary leftmost extraction scope

Frozen 2026-11-02 after root read all three complete stopped preflights and
both complete ordinary Isabelle theories. This is a selected cross-cutting
source unit for Chapters 5 and 6, not activation or acceptance of those
chapters. Every original book obligation remains mandatory. Chapter 1 remains
active; its single attempt3 is the sole authorized compiler/checker.

## 1. Exact original base, source and ownership

The original review/source base is
`66eae34815a177c6b4bf5120e05202ebb8876c91`, the retained unaccepted XT07
candidate with its XT01/XT06 ancestry. The clean isolated source checkout is
`/workspace/scratch/845aa1048b05/conaled-tree-leftmost`, branch
`work/fdsa-tree-leftmost`. The start/clean-start JSON records preserve 23
baseline file identities, the absent new paths, unchanged main state and the
dependency-only symlink. There is no project build directory in this checkout.

This base is sufficient for the chosen raw, order and case contracts. XS01,
the shape/fold/traversal units, a new ADT, a balanced carrier, and the later
potential/merge/permutation units are not dependencies selected for this unit.
Inherited source remains uncompiled/unaccepted; the accepted repaired C1 and
applicable tree prerequisites must be reconciled before integration acceptance.

Exactly five source paths are selected:

| Owner | Path and responsibility |
| --- | --- |
| architecture | `Applications/Resources/TreeLeftmost.lean`: one actual measured extractor and its raw, structural, order and count laws. |
| rotation_cases | `Examples/TreeLeftmost.lean`: actual connected executions, general clients, boundary cases and chain families below. |
| book_inventory | `docs/research/fdsa-tree-leftmost.md`: exact source/statement correspondence, model/domain distinctions, full applicable notice and pending scope. |
| book_inventory | `docs/research/fdsa-reconstruction-map.md`: append-only section; preserve the entire original 23,287-byte prefix. |
| root | `SquareApplications.lean`: append only `import Examples.TreeLeftmost`; preserve its original prefix. |

No other source path, existing definition, pin, checker, warning policy or
public contract may be changed under this authoring scope. A concrete issue
requiring a scope change must be reported with the exact statement and evidence;
do not weaken the requirement or silently change another file. Routine proof
scripts and helper names inside the assigned paths are the author's choice.

Primary source: July 27, 2026 FDSA PDF, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`, which
postdates the manuscript and is not claimed as its generation revision.
`Tree_Set.thy` (3,801 bytes /119 lines) has SHA-256
`f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b`;
`Tree_Map.thy` (2,028 bytes /58 lines) has SHA-256
`c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43`.
The map theory imports and literally reuses the ordinary polymorphic split_min
on complete semantic pairs. The retained p.82 reference error points to §5.2,
p.61, not interval-tree §5.6.4. Preserve that existing correction.

Read the complete stopped preflights, not only their proposed API sketches:

| Report under research/ | Bytes / lines | SHA-256 |
| --- | --- | --- |
| tree-leftmost-source-preflight.md | 30,462 /392 | 82fe82030581dc888d2165a0c7a236ec316a83b66906b9d7fcf32f6af18b3185 |
| tree-leftmost-api-preflight.md | 30,485 /485 | 2cc8c6f1f9802a85cbc64ffbbec5285edccf154e7d8bb75807534550e63db038 |
| tree-leftmost-case-preflight.md | 34,807 /311 | 85e375129bf291beec1f9c2d73d183851720fdf1417ca94818f873566ea52cfe |

The inspected ordinary BinaryTree APIs have no matching extractor. Ordnode
splitMin and Std minView use other cached/balanced carriers and rebuilders.
They are not a correspondence proof for this ordinary recurrence. Reuse the
existing BinaryTree, Trees.inorder/Ordered, list laws, Measured and CallCount.

## 2. One actual execution and the explicitly selected extension

Fixed primary namespace/names:

```text
Resources.TreeLeftmost.run :
  BinaryTree α → Resources.Measured (Option (α × BinaryTree α)) Nat
Resources.TreeLeftmost.extract? : BinaryTree α → Option (α × BinaryTree α)
Resources.TreeLeftmost.entries : BinaryTree α → Nat
```

`extract?` and `entries` are transparent projections of that same run. There
must be no separately recursive pure extractor, cost oracle, second visit
metric, generic rebuilder/callback executor or new carrier. Labels may inhabit
an arbitrary universe. The executor requires no order, comparator, equality
decision, finite enumeration or inhabitant on labels or keys.

The actual structural branches are:

| Input | Full result/control | Entry observation E |
| --- | --- | --- |
| nil | `CallCount.tick (Resources.pure none)` | 1, the selected total Lean extension. |
| node a nil r | Tick the pure `some (a,r)`, returning the actual original r. | 1. |
| node a l r, l nonempty | Tick the bind of the actual `run l` with the pure Option-map rebuilding `(m,l')` as `(m,node a l' r)`. | E(l)+1. |

Use constructor matching for the empty-child test. Valid nonempty execution
**does not call run on the terminal nil child** and does not traverse the right
subtree, compute inorder, scan a minimum or rebuild from a list. The recursive
residual must be the actual returned l', and every untouched fringe must remain
the actual input fringe. The unreachable recursive none alternative can be
handled by Option.map; it must not invent a default label or fallback tree.

This freezes `(none,1)` on nil. The HOL source supplies no empty-tree equation;
the selected Option value and its one-entry charge are a named total extension,
not a recovered source timing case. Successful/nonempty source correspondence
retains the guarded recurrence. Constructors, shape inspection, pair/Option
observations and the nonrecursive reconstruction body have charge zero under
the declared Chapter1 primitive/inlining convention. Only extractor entries
are counted here. No allocation, stack, runtime, compiler-sharing, cache-repair
or later-balancer cost claim is made.

Prove direct equations for the full run, its value and E at nil, a left-empty
node and a node with nonempty left child. Include the actual successful-child
rebuilding consequence for any returned pair/count. Do not replace a branch
equation by a statement merely assuming the final desired output. Qualify the
existing Resources.bind/pure where needed; ordinary monadic composition is
the execution model, not a new sequencing abstraction.

## 3. Complete domain and raw structural contracts

All following raw statements require no key/order/payload decision or default.
Use the actual exported result and no second executor.

1. Failure is exactly nil: `extract? t = none ↔ t = nil`. State explicit
   success on every nonempty raw tree, and the corresponding isSome/domain
   consequence. A successful result itself supplies the nonempty domain.
2. If `extract? t = some (m,r)`, prove
   `m :: Trees.inorder r = Trees.inorder t`. This is **one-way** from the
   actual result. An arbitrary residual with the same inorder is not thereby
   the actual output, and the theorem must not be made an equivalence.
3. Derive the returned entry's input membership, residual membership inclusion,
   and input-label membership iff equality to m or membership in the residual.
   These preserve occurrences via the stronger list equation; do not assert
   unconditional set difference or uniqueness.
4. Derive the original inorder head and residual-tail observations from the
   actual result. Prove `r.numNodes + 1 = t.numNodes` using existing
   Trees.inorder_length. This removes one occurrence, not a raw set-cardinality
   decrement. No new size implementation or finite-set traversal is selected.
5. Prove `r.height ≤ t.height` by reasoning about the actual structural
   splice/rebuilding. List equality alone does not establish it. No blanket
   claim of an exact one-height decrease is permitted; the printed case keeps
   height unchanged. This is the helper portion of C05-013, not full deletion.

For arbitrary `f : α → β` across independent universes, prove whole measured
transport:

```text
run (t.map f) =
  ((run t).1.map (fun (m,r) => (f m, r.map f)), (run t).2).
```

Derive the value and E transport laws. No injectivity, order, key preservation
or cache validity is required for this raw label-blind execution. The returned
residual is mapped as well as the removed label. Building `t.map f` in an actual
client has separate work; this equation does not charge that construction for
free. An outer annotation projection must retain an inner semantic key/value
pair. A Bool-to-Unit semantic-payload map intentionally changes that value.

## 4. Structural order, strict minimum and key removal

Select the thin structural preservation theorem for arbitrary `R : α → α → Prop`:
actual successful extraction from `Trees.Ordered R t` leaves `Trees.Ordered R r`.
No transitivity is needed for this preservation claim; use the actual residual
and raw membership inclusion to retain ancestor bounds.

Separately, under `Transitive R` and Ordered R input, prove R m b for every
residual entry b. Reuse the existing ordered-inorder/Pairwise interface or a
direct proof, retaining the transitivity premise. Do not introduce an order
hierarchy or a generic preservation-record framework for these two lemmas.

For `key : α → κ` with `[Preorder κ]`, strict key Ordered input and actual
successful extraction, require all of the following:

- Strict key Ordered residual.
- Every residual key is strictly greater than key m.
- The actual extracted key is a least member of the original key observation,
  packaged with the existing IsLeast on `{q | q ∈ (inorder t).map key}`.
- The removed key is absent from the residual.
- Exact key membership/removal: membership of q in the residual key list iff
  q belongs to the original key list and q is not key m.

These do not require linearity, a comparator, key/payload equality decisions,
or global injectivity of key. Actual strict ordering gives local key uniqueness.
Full-record distinctness, weak ordering or a lexicographic order on complete
pairs is not a substitute. Do not impose the query unit's local Compares premise:
this operation has no query and performs no key comparison.

## 5. Exact invocation laws and bounds

E is the second component of the one actual run, not an independently supplied
trace, count, source axiom or analytical oracle. Require:

- The direct nil/base/nonempty-recursive equations from §2.
- E≥1 on every input under the selected one-charge empty extension.
- E≤height on nonempty inputs, equivalently successful inputs with the actual
  result/domain premise retained.
- E≤numNodes on nonempty inputs, reusing the existing height/node inequality.
- E≤height+1 on all inputs, including the extension at empty height zero.
- Exact E preservation in the full label-map transport above.

The nonempty recurrence counts the nonempty left-spine nodes and stops before
nil. There is no need for a new separately recursive public left-depth statistic
to state these laws. Calling nil and then interpreting failure as the root
would add an invocation to the valid source execution and is not this scope.
The strict chain families below must give general exact actual-run witnesses,
not only a few evaluated arithmetic examples. A per-input height lower bound,
logarithmic bound, complete deletion bound or later rebuilder-work theorem is
not established by these observations.

## 6. Connected example obligations fixed before implementation

Use namespace `TreeLeftmostExamples`, actual core operations/public laws and
the existing OrderedTreeExamples fixtures. Freeze the expected mathematical
results below; helper/declaration names beyond the primary core names remain
author choices. Exact finite runs may use kernel reduction, but the semantic,
order, map and bound clients must actually consume the corresponding public
theorems. No native_decide, admission, axiom, unsafe or partial Lean definition.

### A. Domain and literal promotion

Cover arbitrary nil, arbitrary-label node a nil r (exact r, E1), and the general
one-parent splice with opaque untouched fringes B and R:
`node c (node a nil B) R` returns `(a,node c B R)` with E2. No equality/order
on labels or traversal of those fringes is allowed. Instantiate the strict
numeric example with left node0/right child1, root2/right child3: output entry0,
residual root2 with leaves1/3, E2, node counts4→3, heights3→2. Connect the raw
inorder, node and structural-height laws.

Cover every `BinaryTree Empty` and `BinaryTree (Nat × Empty)` as nil, returning
none/E1 without manufacturing a payload. Extraction has no query argument;
do not introduce an impossible query as a substitute for this domain test.

### B. Printed tree and minimum

Use the existing printedTree rooted at6, left3 with leaves2/5, right9 with left8.
The exact output is entry2 and residual root6, left3 with nil left/singleton5
right, unchanged right subtree9/8. E=3, residual inorder [3,5,6,8,9], five nodes,
and unchanged height3. Through the actual general laws and printed_ordered,
establish leastness, strict tail bounds, ordered residual, removed-key absence,
node decrement and the successful height/count bounds.

### C. Full semantic map entries and actual successor body

Use taggedTree with inorder [(0,false),(1,true),(2,false)]. Extracting the
whole tree returns (0,false), residual root(1,true) with nil left and right
singleton(2,false), E2. Observe the returned semantic value as some false and
presence as true through ordinary bind/pure and CallCount.primitive_rule;
preserve E from that same measured result. The nil observer is none/false with
the selected extension charge. No payload order/default is introduced.

Provide a general actual-result List.lookup cons observation for semantic
labels κ×β with the minimal BEq key interface: an extracted (k,v) makes lookup
on the original inorder test q==k, returning some v on true and the residual
lookup on false. The extracted-key specialization needs only ReflBEq; identifying
tests with equality or proving removed-key lookup none must carry the applicable
lawful/local equality and strict-key premises. Keep all such assumptions on
the observer, not extraction. Use this observation and the actual tagged result
to show residual lookup0 none and unchanged lookup1/2 values.

The source replacement-body client is a different execution: bind extraction
of taggedTree's actual right singleton(2,false) to pure root reconstruction
using its returned full entry/residual and the original left singleton(0,false).
The result is root(2,false), left(0,false), nil right, with extraction subcost1;
inorder [(0,false),(2,false)], key1 absent, key2 still false. Use the actual
measured child result. This is the nonrecursive source body only, with no full
delete implementation or claim that total deletion costs one. The old true
value must not replace the successor's semantic false value.

### D. Noninjective and outer-annotation transport

Use existing discardTag, its noninjectivity and key preservation with the actual
whole-run transport on taggedTree: removed entry(0,()), mapped residual with
keys1/2 and Unit values, E2. Show the required key/order observation at its own
level. This intentionally changes the semantic Bool; it is not preservation
of that Bool value.

Include a general outer-annotation erasure application for
`BinaryTree ((κ × β) × γ)` across independent key/value/tag universes. The actual
returned logical pair and residual tree retain β after erasing only γ, with
the same extraction count and no cache-validity premise or free-preprocessing
claim. Use existing projections/map rather than a new conversion operation.

### E. Independent missing-premise boundaries

- sameKeyRecords returns (1,10), residual singleton(1,20), E1. Reuse its actual
  full-record distinctness/lexicographic versus strict-key facts. Key1 remains.
  Projecting by Prod.fst gives the identical-label case: input and residual sets
  both contain1, so unconditional set difference is false, although exact
  head-inorder and one-node decrement still hold. State the failed key/duplicate
  observation precisely; removal of the distinct full record is not the failure.
- three 2 0 1 returns2 and residual root0/right singleton1, E2. Its raw head
  equation holds but 2 is not a least natural label because0 is present. Show
  the missing strict input order; a successful/ordered residual does not repair it.
- Because arbitrary-relation preservation is selected, reuse next and
  next_ordered on three 0 1 2. The actual residual root1/right2 is Ordered next,
  but next 0 2 is false. This separates preservation from the all-tail theorem
  requiring transitivity; introduce no new relation package.
- Use the actual sizeSample and existing Cached.Valid from XT01. Ordinary
  extraction returns (0,1) and residual root(1,4), nil left, original right
  subtree(3,2)/(2,1), E2. The residual has3 nodes but retained root cache4, so
  it is not size-cache valid although the input is. Apply raw erasure/map
  correspondence separately. No cached extractor or smart-rebuilder executor
  is selected; semantic map payloads remain distinct from derived annotations.

### F. General strict chain families

Select genuine all-length Nat-key families, including a left chain on
[0,...,n-1] rooted at n-1 and a right chain on the same keys rooted at0.
Example-local recursive constructors/shifted versions are permitted; no new
core carrier or independently recursive analytical cost function is needed.
Prove actual family inorders `List.range n`, strict Ordered, node counts and
heights n. On every nonempty length n, prove the complete measured outputs:

- Left input returns0 and the actual left chain on [1,...,n-1], E=n.
- Right input returns0 and the actual original right child/right chain on
  [1,...,n-1], E=1.

Give exact shifted residual constructors/families in the formal statements;
the remaining-key list alone is insufficient. At n=1 both residuals are nil.
At n=3 the residuals are root2/left1 and root1/right2 respectively. Prove their
shape difference for n≥3 and the cost difference for n>1, while their inorders
agree. Connect the first family to height-bound sharpness and the second to
arbitrarily tall strict trees with count1. This does not instantiate AVL's
rightmost operation or prove a logarithmic bound. Length zero uses only the
chosen total nil extension and is not a source-defined successful case.

## 7. Documentation and retained chapter obligations

The source note must map actual exported declarations and actual examples,
after reading their completed source; do not document an imagined API as
implemented. Preserve exact manuscript/companion identities, local assumptions,
the p.82 correction, and the generated-versus-reconstructed timing distinction.
There is no ordinary generated T_split_min in the inspected sources; the later
AFP StronglyJoinable theory does generate timing for its different join-based
algorithm under additional rank/balance/size/join-cost assumptions. Do not make
an unqualified absence claim or transfer its result to this ordinary executor.

Retain the complete 1,673-byte Isabelle BSD notice, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`, in the
source note, with provenance from the stopped report. Do not redistribute the
manuscript or its extracted research text. Existing Lean/Mathlib imports retain
their own Apache-2.0 provenance. No source axiom or trusted-compiler shortcut.

Map only the corresponding helper portions of C05-006/007/008/013 and C06-047/
048/063. C05-021 still needs its direct recursive proof route for the full
exercise. Full insert/delete, both deletion algorithms, list refinement, Set/Map
interpretations, interval algorithms and complete chapter obligations remain.
The raw helper can support future work; its presence does not close those rows.

Keep later variants separate: interval smart-cache rebuilding; 2–3 completeness
and underflow domains; red-black old-child-color tests and invariant conclusions;
rightmost AVL split_max and differing cached/balance-factor premises; arbitrary
join's actual residual, invariant and work contracts. Raw set conservation does
not supply ordinary raw inorder/multiplicity/node decrement. Retain C10-117 and
all later work/logarithmic obligations. No generic rebuilder, mirror algorithm,
balancer, complete deletion or allocation framework is added to this scope.

The reconstruction-map edit is append-only. Preserve the original 23,287 bytes
exactly and clearly label the new section as an uncompiled unaccepted draft.
All implementation-side source assessments must distinguish meaningful public
claims from untested elaboration, and both from final independent acceptance.

## 8. Release, validation and durability

Each of the three retained authors must read this entire scope, report any
concrete obstruction, then report readiness and stop. They may not write source
before the pre-code checkpoint is created, exposed and successfully saved, and
root records the exact clean-base/requirements/receipt recheck and release.
Root owns the sole import. Before a source checkpoint, all non-main source
changes must be committed on their preserved branch so the complete bundle
captures them; checkpointing is not unit acceptance.

During the active C1 attempt3, no XT08 compiler/Lake/checker/project hash helper,
cache deletion/transplant, performance experiment, dependency change or final
review loop is authorized. Source authoring after release is restricted to the
five owned paths. Preserve all earlier failures, unknown outcomes, review
findings, original requirements and refs. No GitHub write is authorized.

Future acceptance requires applicable prerequisite integration, the matching
focused/full guarded immutable-candidate checks, both integrity phases,
complete integrated build, exhaustive transitive axiom audit, both retained
independent Standards and Spec axes on the entire original scope, and immediate
verify-candidate before acceptance. No source read, focused pass, hash, commit
or saved checkpoint substitutes for those gates. Use the existing workflow,
not an additional parallel acceptance loop.

The initial Chapter2 prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this unit does not become an added
prerequisite for that prefix. Main and the active immutable C1 checkout remain
unchanged. The goal remains the entire book and appendices, chapter by chapter.
