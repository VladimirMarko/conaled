# Tree traversal work: API and architecture preflight

Prepared 2026-11-02. **Bounded source-only preparation. XT05 is not frozen.**
The proposed declarations below are not implemented or compiled, and this is
not either final review axis. The report path was checked absent before writing;
this is the sole new file written for the assignment. The stopped inspected
checkout is `conaled-tree-accumulator`, identified by root as draft `b035f11`.
Old Chapter 1 gate 80227, chapter order and all acceptance states are unchanged.

## 1. Smallest useful shared unit

Recommend one ordinary shape observation, `Trees.leftSizeSum`, and one natural
resource theorem for the **existing actual** `Resources.TreeFold.run`.

The shape observation is the sum, over node occurrences, of the number of
nodes in that occurrence's left child. Define it as the second projection of a
private ordinary `Nat × Nat` fold. Prove the first projection is canonical
`BinaryTree.numNodes` using existing fold fusion. Expose only the useful
observation and laws, not a second size API or a new tree/count record.

The resource theorem consumes one exact reached-callback premise:

```text
callback work on the actual summaries of child trees l and r
  = d * l.numNodes + c.
```

It derives, for `n = t.numNodes` and `A = Trees.leftSizeSum t`,

```text
(run e empty combineRun t).cost = e*(2*n+1) + d*A + c*n.
```

There is no new executor, cost-only recursion, arbitrary reachability object,
or generic cost-language framework. Four existing executions instantiate this
one theorem with distinct callback contracts. Their definitions remain where
they already are; no old execution is replaced by its closed-form cost.

Use generic explicit-label left/right chain families, with a checked example
bridge from the left family at `Unit` to the existing
`TreeCacheExamples.chain`. Preserve that old definition and all its clients.
Both chains should have canonical size and height `n`, and inorder
`List.replicate n a`; their work differs because their left-size sums differ.
A universal upper bound plus attained left-chain bound suffices. No maximum
function over labelled trees, shape-extremizer classifier, or new hierarchy
is justified by this scope.

## 2. Guidance, inspected code and placement

Read `AGENTS.md`, `docs/agents/architectural-quality.md`,
`docs/agents/domain.md`, `GLOSSARY.md`, the ADR index, and ADRs 0001/0010.
Their relevant direction is to reuse ordinary carriers and existing
interpretations, retain minimal assumptions, separate semantic observations
from executions, and test cross-domain compositions against actual independent
implementations. This proposal does not change a compiler frontend,
preservation interface or Felix-parity capability.

The pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean 4.35.0.
Inspected sources include:

- `Applications/Trees/Observations.lean` and pinned `Mathlib/Data/Tree/Basic.lean`;
- `Applications/Resources/TreeFold.lean` and the actual XT03/XT04 example
  definitions/contracts in `Examples/TreeFold.lean`, `TreeFoldCache.lean`,
  `TreeAccumulator.lean` and the earlier `TreeCache.lean` chain family;
- `Applications/Resources/Growth.lean` and its existing application in
  `Applications/Resources/TreeFlattening/Growth.lean`;
- `Mathlib/Data/Nat/Choose/Basic.lean`, `Choose/Cast.lean`,
  `Mathlib/Algebra/BigOperators/Intervals.lean`,
  `Mathlib/Analysis/Asymptotics/Defs.lean`, and `Data/Nat/Cast/Basic.lean`;
- pinned Lean `Init/Data/List/Basic.lean` and `Lemmas.lean` for chain observations.

The sibling `tree-traversal-work-source-preflight.md` owns the precise book and
companion-theory scope. The literal direct inorder retains two right-associated
append calls. `Tree2.inorder` on p.56 traverses an annotated input while ignoring
its annotations; it is not the full list-cache construction analyzed here.
The latter is a separate connected use of the generic augmentation API.

A suitable small module split, still only a proposal:

| Placement | Contents and dependency boundary |
| --- | --- |
| `Applications/Trees/TraversalWork.lean` | Ordinary shape statistic, canonical-size bridge, label transport, sharp bound, explicit chain families and their value observations. Depends on existing ordinary trees/fold and natural arithmetic. |
| `Applications/Resources/TreeTraversalWork.lean` | One generic exact theorem about existing `TreeFold.run`, importing the pure statistic and that executor. No new execution definition. |
| `Examples/TreeTraversalWork.lean` | Instantiate actual append/cache executions, preserve the old Unit-chain specialization, compare actual XT04 programs, and prove their natural inequalities and real-cast growth. |

The actual specialized algorithms currently live in `Examples`. Importing
those example modules into a domain library to state specialized formulas
would reverse the intended dependency direction. Keeping the generic theorem
in Resources and its connected specializations in Examples avoids that problem
without moving or duplicating any old algorithm. XT02's separately saved
shape/log branch is unnecessary. XD01 is unnecessary. Existing source and
acceptance prerequisites remain in force independently of this import plan.

## 3. Ordinary left-subtree-size observation

The exact existing fold API is:

```lean
Trees.fold (empty : β) (combine : β → α → β → β) : BinaryTree α → β
Trees.fold_fusion empty combine empty' combine' observe h_empty h_node t
Trees.fold_map empty combine label t
Trees.fold_numNodes t
Trees.numNodes_map label t
```

Use a private ordinary pair fold with algebra

```text
empty = (0,0)
combine (nL,AL) _ (nR,AR) = (nL+nR+1, AL+AR+nL).
```

Projecting the algebra with `Prod.fst` preserves the canonical size algebra;
`fold_fusion` followed by `fold_numNodes` proves its first component equals
`t.numNodes`. The public `leftSizeSum` is its second component. This gives:

```text
leftSizeSum nil = 0
leftSizeSum (node a l r) = leftSizeSum l + leftSizeSum r + l.numNodes
leftSizeSum (t.map f) = leftSizeSum t.
```

All labels are ignored by the statistic. The map theorem requires no
injectivity, decidable equality, order or inhabitant, and allows independent
source and target payload universes. It follows from existing `fold_map` with
the label-ignoring pair algebra. Repeated equal subtrees still contribute once
per occurrence. This is not a set of distinct subtrees or a storage statistic.

The pure statistic's definition is not a second measured execution. Computing
it is not silently added to, or asserted free within, any existing traversal.
It is an external observation used to state and prove those traversals' work.

## 4. One generic exact resource theorem

A proposed signature in the existing `Resources.TreeFold` namespace is:

```lean
-- Proposal only; not implemented or compiled.
theorem run_cost_leftSizeSum
    (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat)
    (d c : Nat)
    (hcost : ∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
      (combineRun (run entry empty combineRun l).1 a
        (run entry empty combineRun r).1).2 = d * l.numNodes + c)
    (t : BinaryTree α) :
    (run entry empty combineRun t).2 =
      entry * (2*t.numNodes+1) + d * Trees.leftSizeSum t + c * t.numNodes
```

Here `α : Type u` and `β : Type v` remain independent. There are no new payload
or summary typeclasses. The premise ranges over **every finite pair of child
trees** at the same fixed entry, empty value and callback. It is not an
arbitrary-summary premise, nor a claim restricted to one supplied input's
subtrees. One fixed pair `d,c` serves the family. An independently varying
coefficient is not a uniform complexity constant.

Proof: induct on the actual tree, rewrite existing `run_node_cost`, apply
`hcost` at those actual child results, use the two induction hypotheses and
the public `leftSizeSum_node`/canonical `numNodes` equations, then normalize
natural polynomial arithmetic. Nil costs `entry`. The algebra is

```text
[e*(2*nL+1)+d*AL+c*nL]
 + [e*(2*nR+1)+d*AR+c*nR]
 + [d*nL+c] + e
 = e*(2*(nL+nR+1)+1) + d*(AL+AR+nL) + c*(nL+nR+1).
```

Reordering is legitimate for this Nat theorem. It is not an ordered-observation
identity, and it does not alter the grouping of the raw generic executor.
The existing `run_cost_const` remains intact; `d=0` is the matching mathematical
specialization, but refactoring the old proof merely to depend on this new
module is unnecessary and could introduce an avoidable import change.

## 5. Exact existing client bridges

The current public declarations already establish the local facts needed for
all four instances:

| Execution | Exact callback bridge to use | `d,c` | Whole work |
| --- | --- | --- | --- |
| `TreeFold.run e [] TreeCacheExamples.appendStepRun t` | `TreeFoldExamples.single_step_cost`, then `single_value` on the actual left run, then `Trees.inorder_length` | `1,1` | `e*(2*n+1)+A+n` |
| `TreeFold.run e [] TreeFoldExamples.rightStepRun t` | `right_step_cost`, `right_value`, `inorder_length` | `1,3` | `e*(2*n+1)+A+3*n` |
| `TreeFold.run e [] TreeFoldExamples.leftStepRun t` | `left_step_cost`, `left_value`, `inorder_length` | `2,3` | `e*(2*n+1)+2*A+3*n` |
| `TreeFoldCacheExamples.annotateRun e [] TreeCacheExamples.appendStepRun t` | `TreeCacheExamples.append_node_cost`, then `TreeFoldCacheExamples.list_read` on the actual returned child annotation, then `inorder_length` | `1,4` | `e*(2*n+1)+A+4*n` |

The existing `single_node_cost`, `right_node_cost`, `left_node_cost`, and
`TreeFoldCacheExamples.list_node_cost` independently record those same actual
recurrences. They remain useful corroborating contracts and need not be
replaced. The full-cache instance uses summary type
`BinaryTree (α × List α)` and the existing actual `TreeCache.nodeRun` callback.
Its read law is supported by annotation value/recursive-validity/erasure
contracts. It does not assume an arbitrary supplied annotation has a correct
cache, nor substitute a structural traversal for a cached read.

The current node theorem for the list cache already includes local callback
work and all three XT01 helper charges. Hence the coefficient is `4*n`, not
`n` or `3*n`. Its returned object is an annotated tree; its root-reader result
is the inorder list. Compare that reader to a traversal list, not the full
returned objects. The size of all mathematical cached lists is not a theorem
about physical allocation or retained sharing.

Each formula gives label-map work invariance by `leftSizeSum_map` and the
existing `Trees.numNodes_map`; this compares given tree values. It does not
pay for computing a separate mapped input.

### Actual XT04 composition

The existing exact theorem is

```text
TreeAccumulatorExamples.materializeAppend_cost t suffix:
  materializeAppend work
    = (TreeFold.run 1 [] appendStepRun t).cost + (t.numNodes+1).
```

It comes from the actual bind of the single-append traversal to measured append,
using its returned list and the inorder-length bridge. The new single-run
formula therefore gives `4*n+2+A`, independent of suffix length.

`TreeAccumulatorExamples.buildOnce_exact 1 1 t suffix` separately gives the
actual staged construction-plus-invocation cost `4*n+2`. Both programs have
value `Trees.inorder t ++ suffix`, via their own existing value theorems. Thus
one useful additional identity is

```text
(materializeAppend t suffix).cost = (buildOnce 1 1 t suffix).cost + A.
```

This is a comparison of actual measured programs, not an inference from their
erased-value equality. Construction is included in `buildOnce`. On the saved
sample the counts are 20 versus 18, while invocation alone remains 9. No
additional construction comparisons are needed for this unit.

## 6. Sharp bound without division or a new triangular definition

Pinned `Mathlib/Data/Nat/Choose/Basic.lean` supplies:

```lean
Nat.choose_succ_succ' (n k : Nat) :
  (n+1).choose (k+1) = n.choose k + n.choose (k+1)
Nat.choose_one_right (n : Nat) : n.choose 1 = n
Nat.choose_two_right (n : Nat) : n.choose 2 = n*(n-1)/2
Nat.add_one_mul_choose_eq (n k : Nat) :
  (n+1) * n.choose k = (n+1).choose (k+1) * (k+1)
Nat.choose_succ_right_eq (n k : Nat) :
  n.choose (k+1) * (k+1) = n.choose k * (n-k)
```

Use existing `Nat.choose` as the sharp public expression. Do not define another
triangle-number operation. A small private arithmetic identity is enough:

```text
2 * n.choose 2 + n = n^2.
```

It follows by Nat induction from `choose_succ_succ' n 1` and
`choose_one_right n`; polynomial normalization avoids both natural subtraction
and division. Alternatively the inspected multiplicative choose identities
supply the same relation. No new field or real-number assumption is needed.

The recommended structural intermediate is

```text
2 * leftSizeSum t + t.numNodes ≤ t.numNodes^2.
```

For a node, put `x=l.numNodes`, `y=r.numNodes`. Its left-hand side is

```text
(2*AL+x) + (2*AR+y) + 2*x + 1.
```

The induction hypotheses bound this by `x^2+y^2+2*x+1`. Its deficit from
`(x+y+1)^2` is exactly `2*y*(x+1)`, a nonnegative Nat term. An explicit polynomial
identity followed by `Nat.le_add_right` proves the final inequality without
nonlinear division automation. Both children of nil and the `n=0,1` cases are
covered by the same argument.

Rewriting the square with the private choose identity and cancelling the
linear terms yields the sharp public bound

```text
leftSizeSum t ≤ t.numNodes.choose 2.
```

The same division-free bound immediately gives `A+n≤n^2`, useful for the tight
whole-work constants below. These are shape facts, not execution observations.
An alternative choose-addition proof would leave surplus `y*(x+1)`; it is
mathematically sound but requires an extra addition identity that the direct
squared bound avoids.

`Finset.sum_range_id_mul_two` and `Finset.sum_range_id` are present in
`Mathlib/Algebra/BigOperators/Intervals.lean`:

```text
(sum i in range n, i)*2 = n*(n-1)
sum i in range n, i = n*(n-1)/2.
```

They are optional for explaining the chain sum. They are not needed for the
minimal fold/Pascal proof and need not become an extra import.

## 7. Explicit chains, canonical values and sharpness

Proposed ordinary families, with an explicitly supplied label `a : α`:

```text
leftChain a 0 = nil
leftChain a (n+1) = node a (leftChain a n) nil
rightChain a 0 = nil
rightChain a (n+1) = node a nil (rightChain a n).
```

These are input families, not new cost executors. Useful contracts are:

```text
(leftChain a n).numNodes = n = (rightChain a n).numNodes
(leftChain a n).height = n = (rightChain a n).height
inorder (leftChain a n) = replicate n a
inorder (rightChain a n) = replicate n a
leftSizeSum (leftChain a n) = n.choose 2
leftSizeSum (rightChain a n) = 0.
```

All follow by ordinary Nat induction and the existing tree/observation laws.
The pinned list identities are exactly:

```lean
List.replicate_zero : List.replicate 0 a = []
List.replicate_succ : List.replicate (n+1) a = a :: List.replicate n a
List.replicate_succ' : List.replicate (n+1) a = List.replicate n a ++ [a]
List.replicate_append_replicate :
  List.replicate n a ++ List.replicate m a = List.replicate (n+m) a
List.length_replicate : (List.replicate n a).length = n
```

Use `replicate_succ'` for left-chain inorder, whose root label is appended to
the subtree list; use `replicate_succ` for right-chain inorder. No payload
equality is needed. The chain triangle recurrence is `A(n+1)=A(n)+n`, which
is precisely the inspected Pascal specialization up to commutativity.
The exact division-free identity `2*A(leftChain a n)+n=n^2` follows as well.

The existing `TreeCacheExamples.chain : Nat → BinaryTree Unit` is already the
left family at `()`, with `chain_numNodes`. Preserve that definition and its
cached-node examples. Add a checked specialization
`leftChain () n = TreeCacheExamples.chain n`, proved by constructor induction;
no replacement or move of the old definition is needed. Existing label-map
facts can also transport its value observations; `List.map_const'` is available
with exact conclusion `l.map (fun _ => a) = replicate l.length a`.

Sharpness means the universal bound is attained at each `n` by this supplied-
label family. It does not require a supremum over all labelled trees or a proof
classifying every equality case. A nonempty family cannot be manufactured at
payload type `Empty`; the universal statistic and execution statements still
cover its unique nil tree without an `Inhabited α` assumption.

Root's independently checked three-node comparison is particularly useful:
left and right chains have equal size 3, equal height 3 and the same list of
three labels, but `A` is 3 versus 0. Their literal-right execution work at
entry one is 19 versus 16. Thus size, height and erased inorder together do not
identify this work observation.

## 8. Natural bounds and existing real-cast asymptotics

Keep explicit Nat inequalities as the primary bounds. For `n≥1`,
`e*(2*n+1)≤3*e*n≤3*e*n^2`; with `A+n≤n^2` and `2*A+n≤n^2` this gives:

| Actual execution | Universal upper bound for `n≥1` | Right-chain exact work |
| --- | --- | --- |
| Single append | `(3*e+1)*n^2` | `(2*e+1)*n+e` |
| Literal right-associated double append | `(3*e+3)*n^2` | `(2*e+3)*n+e` |
| Left-associated comparison | `(3*e+3)*n^2` | `(2*e+3)*n+e` |
| Actual full list-cache annotation | `(3*e+4)*n^2` | `(2*e+4)*n+e` |
| Actual `materializeAppend`, entry fixed at one | `6*n^2` | `4*n+2` |

The selected callback coefficients are positive, so these actual right-chain
programs are linear even when `e=0`. For the left chains, the exact triangular
identity gives, for every `n` including zero,

```text
n^2 ≤ 2 * singleWork(leftChain a n)
n^2 ≤ 2 * literalRightWork(leftChain a n)
n^2 ≤     comparisonLeftWork(leftChain a n)
n^2 ≤ 2 * listAnnotationWork(leftChain a n).
```

The materialize-append program has the same convenient factor-two lower bound.
These lower bounds use the actual formulas; the positive per-node callback
term absorbs the small-size triangular boundary. Nil itself has work `e` for
the first four executions, and two for `materializeAppend`; therefore the
quadratic upper inequality is deliberately stated only when `n≥1`.

### Exact existing project interface

`Applications/Resources/Growth.lean` already provides:

```lean
Resources.isBigO_of_nat_bound
    (f g : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * g n) :
  Asymptotics.IsBigO Filter.atTop
    (fun n => (f n : ℝ)) (fun n => (g n : ℝ))
```

`Asymptotics.IsTheta l f g` in pinned `Analysis/Asymptotics/Defs.lean` is exactly
`IsBigO l f g ∧ IsBigO l g f`. The existing
`TreeFlattening.recursive_flatten_theta` and `stack_flatten_theta` already use
two calls to `isBigO_of_nat_bound` with explicit constants and thresholds.
Follow that local proof style instead of introducing a new growth predicate.

For example, the **actual** single-append left-chain count has a proposed
statement of the following shape:

```lean
Asymptotics.IsTheta Filter.atTop
  (fun n => ((Resources.TreeFold.run e []
    TreeCacheExamples.appendStepRun (leftChain a n)).2 : ℝ))
  (fun n => ((n^2 : Nat) : ℝ))
```

For the upper direction call the existing bridge with `C=3*e+1,N=1`.
For the lower direction reverse the functions and use `C=2,N=0`.
The literal-right and annotation variants use their table constants and the
same lower factor. The left-associated comparison uses lower factor one.
Each statement quantifies `e` as a fixed parameter before the eventual index.
Allowing `e` to grow with `n` would be a different theorem.

For actual single-append right chains, use comparison function `fun n => n`:
upper `C=3*e+1,N=1`, lower `C=1,N=0`. The other right-chain programs use
`3*e+3`, `3*e+3`, `3*e+4`; materialize-append uses `6`, all with the same lower
factor one. These produce genuine actual-family `IsTheta` results, not just
an asymptotic statement about a newly defined polynomial tally.

A universal quadratic upper statement for a specified family
`ts : Nat → BinaryTree α` with `(ts n).numNodes=n` can consume the same pointwise
bound. Such an upper statement does not supply a lower bound for every family;
the right chains are the concrete counterboundary. The universal pointwise
bound plus the explicit attained left family is the required worst-case claim.
There is no need to define a worst-case supremum function.

### Real arithmetic is an optional presentation layer

Pinned `Nat.cast_pow (m : Nat) (n : Nat)` gives
`((m^n : Nat) : R) = (m : R)^n` for a semiring `R`. Thus the target square above
can be restated as `(n : ℝ)^2` by the existing cast lemma.
If an explicit rational polynomial form is useful,
`Nat.cast_choose_two (K : Type*) (a : Nat)` from `Choose/Cast.lean` gives

```text
(a.choose 2 : K) = (a : K) * ((a : K)-1) / 2
```

under `[DivisionRing K] [NeZero (2 : K)]`. The subtraction there is in `K`,
not truncated Nat subtraction, and the identity includes `a=0`.
This heavier import is unnecessary for the natural proof and existing
real-cast Big-O bridge. No limit calculation, real logarithm, field-valued
resource interface or generic polynomial-growth framework is needed.

## 9. Coefficient, semantic and validation boundaries

The generic exact theorem intentionally permits `d=0` and `c=0`:

- `d=0` removes the shape term and recovers the constant-callback form.
- `d=c=0` leaves only structural entry work.
- `entry=d=c=0` gives zero observation for every tree.
- On right chains the `d*A` term is always zero, whatever `d` is.

Consequently, no blanket quadratic or positive linear `IsTheta` result should
be stated for arbitrary coefficients. The growth claims above belong to the
specific positive callback clients. Other coefficient cases can be proved
later with the premises they actually require; they need no new public
classification framework now.

The literal source inorder, the one-append normalized/augmented traversal,
the left-associated comparison, and full cache construction retain their
separate cost models. Equal inorder observations never identify their costs.
Function-valued folds still distinguish construction from invocation.
`TreeFlattening`'s existing leaf-labelled worklist/copy statistic is a different
carrier and algorithm and should not be reused as though it were this
node-labelled `leftSizeSum` recurrence.

The selected sharpness and chain statements do not prove every Chapter 4
exercise, every maximizing-shape characterization, balanced-tree n-log-n
families, memory allocation/sharing bounds, or a source compiler theorem.
All original book obligations remain in their owning scope. The proposed unit
adds no acceptance credit; the earlier shared source drafts are also unaccepted.

No implementation, build/compiler/checker/project hash helper, Git/ref/index,
cache/configuration/gate, remote action or new review loop was performed.
No finite enumeration was run. Only this new report was written. Its source/API
recommendations are ready for ordinary checkpoint capture; writing is stopped.
