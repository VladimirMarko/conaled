# Tree traversal work: independent shape-sensitive cases

## Status and inspected contracts

This is bounded mathematical/case preparation for a possible shared follow-up.
XT05 is not frozen. This note changes no chapter status, source implementation,
prior report, worktree, ref or cache. It supplies no compiler, checker,
final-review or acceptance evidence. Gate 80227 is unchanged. Only this new
note is written. All derivations and finite cases below were checked by hand;
no new shape enumeration, Python run or hash helper was needed.

The actual draft contracts read for this task were:

- `conaled-tree-fold/Examples/TreeFold.lean`: the three real append callbacks,
  their value/work laws, their actual fold node recurrences and finite cases;
- `conaled-tree-fold/Examples/TreeFoldCache.lean`: actual full annotation,
  validity/erasure/read bridges and the corrected list-node cost recurrence;
- the relevant exact-count, repeated-occurrence, `buildOnce_exact` and materialize/append
  contracts in `conaled-tree-accumulator/Applications/Resources/TreeAccumulator.lean`
  and `conaled-tree-accumulator/Examples/TreeAccumulator.lean`;
- the existing ordered-word counterexample in
  `conaled-tree-fold/Examples/TreeFoldObservations.lean`.

These remain saved draft contracts, not acceptance evidence. Their existing
actual executions, callback/value bridges and declared tariffs are the basis
for the mathematical expectations here.

## 1. Left mass and the division-free sharp bound

For the existing node-labelled `BinaryTree`, let `n(t)` be its canonical node
count. Define the mathematical left mass by

```text
A(nil)        = 0
A(node a l r) = A(l) + A(r) + n(l).
```

This sums left-subtree node counts over node occurrences. Equal payloads,
equal child trees and repeated subtree descriptions are not deduplicated.
The statistic is a specification observation; using it in a theorem does
not insert its computation into the measured traversal.

The sharp bound has a particularly useful division-free form:

\[
2A(t)+n(t)\le n(t)^2.
\]

To verify the induction independently, put `x=n(l)`, `y=n(r)` and
`n=x+y+1`. The left side at a node is

\[
(2A(l)+x)+(2A(r)+y)+2x+1
\le x^2+y^2+2x+1.
\]

The remaining gap to `(x+y+1)^2` is exactly `2*y*(x+1)`, which is nonnegative.
Nil gives equality `0=0`. No positive-node premise is needed for this bound.

In standard combinatorial notation it is equivalent to

\[
0\le A(t)\le \binom{n(t)}2.
\]

Here `choose(n,2)=n*(n-1)/2`, including zero for `n=0,1`; the product is even.
Keeping `2*A+n<=n*n` as the main arithmetic statement avoids natural division
and truncated-subtraction side conditions. A useful immediate consequence is

\[
A(t)+n(t)\le n(t)^2,
\]

because `A>=0`. At `n=0` and `n=1`, these formulas force `A=0`.

### Sharp witnesses and optional equality characterization

For a supplied label `a`, define the usual left and right chains by shape:

```text
L_0 = nil                  R_0 = nil
L_(n+1) = node a L_n nil    R_(n+1) = node a nil R_n.
```

Both have `n` nodes. Directly from the recurrence,

\[
2A(L_n)+n=n^2,\qquad A(L_n)=\binom n2,\qquad A(R_n)=0.
\]

For the left chain, `A(L_(n+1))=A(L_n)+n`; substituting the induction equality
gives `(n+1)^2` without division. The right recurrence adds zero at every node.

Mathematically, `A=0` characterizes a structural right chain, and
`A=choose(n,2)` characterizes a structural left chain. Labels in these
characterizations may vary: they do not assert that all labels equal the fixed
`a` used for the witness family. The minimum characterization follows because
zero mass forces the left child to be nil and the right child's mass to be
zero. For the maximum, the inductive gap `2*y*(x+1)` forces the right child to
be nil, with equality recursively on the left. Nil and singleton satisfy both
endpoint descriptions.

**A public full characterization is not needed for the proposed worst-case
argument.** The universal bound and explicit attaining chain families suffice.
Introducing two recursive chain predicates or general subtree machinery merely
to package an unused converse would add scope without helping these clients.

## 2. Exact work of the existing executions

Write `n=n(t)`, `A=A(t)` and `E_e=e*(2*n+1)`, with `e : Nat`. The checked
client recurrences have local work `n(l)+1`, `n(l)+3`, `2*n(l)+3` and `n(l)+4`.
Structural induction therefore gives the following exact expectations:

| Actual execution | Expected natural observation |
| --- | --- |
| XT03 single append `l ++ (a :: r)` | `E_e + A + n` |
| XT03 literal right-associated `l ++ ([a] ++ r)` | `E_e + A + 3*n` |
| XT03 left-associated comparison `(l ++ [a]) ++ r` | `E_e + 2*A + 3*n` |
| XT03 actual list-valued cached annotation | `E_e + A + 4*n` |
| XT04 append-free suffix invocation, any suffix | `E_e` |

The first three return the ordinary inorder list. The annotation returns an
actual cached tree whose root read is that list; it is a different returned
object. Its `+4` already includes append's `+1` and the two charged cache reads
plus one constructor entry. Do not add three a second time. The read equality
is an observation theorem, not an additional measured `readRun` execution.

Each formula must be derived from its actual existing node recurrence. In the
append clients, that recurrence already consumes the actual returned-list
value theorem and `inorder_length`. In the cache client it consumes the actual
annotation validity/erasure/read bridge before using the list length. These
connections prevent a numerical tally from replacing an actual callback.

The existing XT04 `materializeAppend` has its inorder entry fixed to one; it
does not take a general entry parameter. Its actual contract adds `n+1` to the
single-append fold's cost, giving

\[
M(t,xs)=4n+2+A(t).
\]

Its returned value is `inorder(t) ++ xs`, for every supplied suffix. The suffix
length does not change this count because append traverses the returned prefix.
The matching source accumulator invocation at entry one costs `2n+1`, so

\[
M(t,xs)=(2n+1)+(A(t)+2n+1).
\]

Materialize/append is strictly more costly in these observations even at nil:
it costs two there, while accumulator invocation costs one. This is an actual
composition of two existing measured executions, not an append inserted into
the accumulator by rewriting its value specification.

### End-to-end construction/application comparison

The existing `buildOnce 1 1 t xs` performs an actual strict construction and
then applies its returned function once. Its supplied `buildOnce_exact`
contract gives value `inorder(t) ++ xs` and work
`(1+1)*(2*n+1)=4*n+2`. Therefore, for every tree and suffix,

\[
\begin{aligned}
\operatorname{value}(\mathrm{materializeAppend}(t,xs))
  &=\operatorname{value}(\mathrm{buildOnce}(1,1,t,xs)),\\
\operatorname{cost}(\mathrm{materializeAppend}(t,xs))
  &=\operatorname{cost}(\mathrm{buildOnce}(1,1,t,xs))+A(t).
\end{aligned}
\]

This compares two complete existing programs and retains construction work.
At nil both cost two; at a singleton both cost six; on the saved sample the
comparison is `20 = 18 + 2`. On a right chain the costs agree because `A=0`;
the left-chain gap is exactly `choose(n,2)`. No full equality characterization
is needed to state these witness cases.

The sample's invocation-only cost nine is a different program boundary. It
does not replace the construction-plus-invocation total 18. No extra staged
program or alternative closure-construction tariff is proposed here.

## 3. Chain formulas, including zero and one node

Put `q=choose(n,2)`. All entries in this table are exact for every `n>=0`:

| Execution | Left chain `L_n` | Right chain `R_n` |
| --- | --- | --- |
| Single append | `e*(2*n+1)+q+n` | `(2*e+1)*n+e` |
| Literal right-associated append | `e*(2*n+1)+q+3*n` | `(2*e+3)*n+e` |
| Left-associated append | `e*(2*n+1)+n*n+2*n` | `(2*e+3)*n+e` |
| Actual cached-list annotation | `e*(2*n+1)+q+4*n` | `(2*e+4)*n+e` |
| Existing materialize/append, entry one | `q+4*n+2` | `4*n+2` |
| Accumulator invocation | `e*(2*n+1)` | `e*(2*n+1)` |

Useful division-free left-chain identities are

\[
\begin{aligned}
2W_{\rm single}(L_n)&=2e(2n+1)+n^2+n,\\
2W_{\rm right}(L_n)&=2e(2n+1)+n^2+5n,\\
W_{\rm left}(L_n)&=e(2n+1)+n^2+2n,\\
2W_{\rm cache}(L_n)&=2e(2n+1)+n^2+7n,\\
2M(L_n,xs)&=n^2+7n+4.
\end{aligned}
\]

Consequently `n*n <= 2*W_single(L_n)` and
`n*n <= 2*W_right(L_n)` hold for **all** `n`, including zero and one, and for
every natural `e`, including zero. The callback's `+n` term absorbs the
triangular correction; no `n>=2` premise is needed. The left-associated count
even satisfies `n*n <= W_left(L_n)` under the same boundary conventions.

At `n=0`, every direct fold, cached annotation and accumulator invocation costs
`e`, and the actual materialize/append program costs two. At `n=1`, the four
fold/annotation costs are `3*e+1`, `3*e+3`, `3*e+3`, and `3*e+4`. The invocation
cost is `3*e`; materialize/append costs six.

## 4. Quadratic worst case and linear right chains

For `n>=1`, `2*n+1 <= 3*n` and `n <= n*n`. Hence the structural term is at most
`3*e*n*n`. Combining the division-free bounds with the exact work formulas gives

\[
\begin{aligned}
W_{\rm single}(t)&\le(3e+1)n^2,\\
W_{\rm right}(t)&\le(3e+3)n^2,\\
W_{\rm left}(t)&\le(3e+3)n^2,\\
W_{\rm cache}(t)&\le(3e+4)n^2.
\end{aligned}
\]

For the right-associated callback term, use
`A+3*n=(A+n)+2*n <= 3*n*n`. For the left-associated term, use
`2*A+3*n=(2*A+n)+2*n <= 3*n*n`. The cached term adds one further `n`.
The existing materialize/append program satisfies `M<=6*n*n` when `n>=1`:
single-append entry-one work is at most `4*n*n`, and `n+1<=2*n*n`.

These positive-node premises are material. If `e>0`, nil has positive work
while any expression `K*n*n` is zero. When `e=0`, the four direct fold/annotation
bounds extend to nil, but the general statements above need not split tariffs
merely to remove that one premise. Exact formulas remain valid everywhere.

For the literal source algorithm, set `e=1` and use the right-associated
variant. Every nonempty input satisfies `W_right<=6*n*n`. On the left-chain
family,

\[
2W_{\rm right}(L_n)=n^2+9n+2,
\qquad n\ge1\Longrightarrow n^2\le2W_{\rm right}(L_n)\le12n^2.
\]

Thus the explicit source-count model has a quadratic worst case. The upper
half of this sandwich needs `n>=1`; at nil it would falsely say `2<=0`.
No supremum over arbitrary labels or new asymptotic framework is needed to
express the universal upper bound and one attaining-order family.

The right chain instead has `W_right(R_n)=5*n+1` for every `n`, and for `n>=1`
it lies between `5*n` and `6*n`. The other direct variants and cache annotation
have the displayed linear right-chain formulas. Therefore a quadratic lower
bound is **not** an all-shapes claim. At source entry one, the accumulator's
exact cost `2*n+1` is linear on every shape. None of these observations identifies physical
runtime, allocation, sharing, cache behavior, or stack usage.

## 5. Compact independently calculated cases

All rows below use entry one. `P1` is a singleton, `P3=node a P1 P1` has two
equal child occurrences, and chains can have the same label at every node.
`M` means the existing entry-one materialize/append execution, with any suffix;
`I2` means one accumulator invocation, without construction work.

| Tree | `n` | `A` | Single | Right | Left | List cache | `M` | `I2` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Nil | 0 | 0 | 1 | 1 | 1 | 1 | 2 | 1 |
| `P1` | 1 | 0 | 4 | 6 | 6 | 7 | 6 | 3 |
| `R_3` | 3 | 0 | 10 | 16 | 16 | 19 | 14 | 7 |
| `P3` | 3 | 1 | 11 | 17 | 18 | 20 | 15 | 7 |
| `L_3` | 3 | 3 | 13 | 19 | 22 | 22 | 17 | 7 |
| XT01 asymmetric sample | 4 | 2 | 15 | 23 | 25 | 27 | 20 | 9 |

For the saved sample `node 1 (node 0 nil nil) (node 3 (node 2 nil nil) nil)`,
the root contributes one to `A`, the node labelled `3` contributes one, and
the other nodes contribute zero. The result is `A=2`, not a count of distinct
left-subtree values.

These rows and the symbolic chains are a compact connected set: nil/singleton
expose offsets, `P3` exposes repeated occurrences, the two chains witness both
extremes and a failed converse, and the existing asymmetric sample connects
all previously retained exact observations. No extra enumeration is needed.

### Node-count, height and output-value countercase

Give both `L_3` and `R_3` the same label `a` at every node. They have equal node
count three, equal height three, and identical inorder `[a,a,a]`, but left
masses three and zero. Their literal right-associated counts are 19 and 16.
Therefore neither node count, height, nor even the tuple of node count, height
and returned inorder determines this exact work. The countercase uses actual
shape variation and repeated labels; it needs no payload order or injectivity.

The complete three-node shape supplies the same node count and inorder with
intermediate mass one and smaller height two. The left-mass statistic is not
just another name for maximum height.

## 6. Label transport, repeated occurrences and minimal assumptions

For every map `f : alpha -> beta`, with unrelated payload universes if desired,

\[
A(t.map\ f)=A(t).
\]

The proof uses the left-mass recurrence and the existing invariance of node
count under arbitrary maps. No injectivity, decidable equality, order, finite
payload universe, or inhabitance hypothesis is needed. In particular, mapping
all sample labels to a single value preserves mass two and every cost above.
Computing a mapped input is outside this comparison of given values.

For a repeated child occurrence,

\[
n(node\ a\ t\ t)=2n(t)+1,\qquad
A(node\ a\ t\ t)=2A(t)+n(t).
\]

The statistic and actual recurrences both count the two children. They do not
identify this input with one traversal of `t`. The `P3` row is the smallest
nontrivial repeated-child example: `A(P1)=0` but `A(P3)=1`.

Every existing-value statement applies to `BinaryTree Empty`, whose only
value is nil. A positive-size chain family requires an actual supplied label
or a nonempty payload type. It is enough to choose `Unit` or a concrete Nat
label for worst-case witnesses; an unqualified existence claim for every
positive size over `Empty` would be false. No `Inhabited` instance is needed
when a label is explicitly supplied.

The quantitative collection uses natural observations and the exact existing
callbacks, not merely an arbitrary operation returning the same inorder.
The chosen models include both child evaluations and nil invocations, and
retain actual measured append and cache-helper charges. These are the only
operational assumptions needed for the listed counts.

## 7. Association and observation boundaries

The exact differences, stated without truncated subtraction, are

```text
W_right(t) = W_single(t) + 2*n
W_left(t)  = W_right(t) + A
W_cache(t) = W_single(t) + 3*n.
```

The first difference is strict for nonempty trees. The second is not: even a
nonempty right chain has `A=0`, so the two two-append executions have equal
counts despite different sequencing. List associativity proves equality of
their results; it does not erase either append or supply equality of work on
other shapes. The cache equality compares its different returned object under
the declared local-access tariff, not a value-level replacement of an inorder
program.

The generic XT03 observation equation preserves
`(left + (right + callback)) + entry`. The numerical formulas above collect
and rearrange natural additions. They must not be exported unchanged for an
arbitrary `Add` observation or a noncommutative word observation. The retained
singleton word client records `[0,0,1,0]`, whereas collecting its three entry
tokens at the end yields `[1,0,0,0]`. Equal `n` and `A` do not justify that
reordering. Likewise, the tree accumulator invokes right before left; its
natural invocation count does not make its ordered observation the same as
XT03's left-first measured fold.

## Recommendation and limits

The division-free sharp bound, explicit left/right chain witnesses, arbitrary
map invariance, repeated-occurrence identity, and actual execution-specific
cost equalities supply the useful mathematical core. The exact materialize/append
versus `buildOnce 1 1` identity connects the saved execution units without
discarding construction work. The small case table and
same-count/same-height/same-inorder countercase give meaningful connections.
The full equality characterization is true but unnecessary for the proposed
worst-case consequence; no new hierarchy or subtree framework is recommended
merely to state it.

This note does not select Lean declarations, freeze XT05, implement or run a
cost evaluator, alter the source's append association, close the Chapter 4
traversal obligations, or assert a compiler/runtime theorem. Any future result
must consume the actual saved operation's contracts and retain all existing
validation and chapter-order prerequisites.
