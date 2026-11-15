# Whole-tree fold resources: independent mathematical cases

## Status and explicit model

This is independent hand-mathematics preparation for a possible shared measured
whole-tree-fold unit. It is not a scope freeze, implementation, source-runtime
identification, final review, compiled coverage, or acceptance. Chapter 1 remains
active. Only this new note is written for this task; no enumeration, compiler,
checker, hash helper, Git/ref, cache, gate, remote operation, or child agent is
used.

The input is the existing node-labelled `BinaryTree`. Let `n(t)` be its ordinary
node count. Nil is an external leaf, so there are `n(t) + 1` nil occurrences and
`2*n(t) + 1` total fold invocations. The fold evaluates both children once and
then invokes a measured callback once at every node; it does not skip a child
because the callback happens to ignore that child's value.

Every fold invocation, including nil, has the fixed charge `e >= 0`. Let `q_v`
be the nonnegative cost of the callback on the **actual reached child results**
at node occurrence `v`. Charges are added. Arithmetic below may be read in
nonnegative real numbers, or in the existing natural-number cost model when
the parameters are natural numbers. No new cost type is selected here.

The recurrence is

```text
W_e(nil)        = e
W_e(node a l r) = e + W_e(l) + W_e(r) + q_root.
```

Tuple packaging, `pure`/`bind` scaffolding, and other uncharged operations do
not silently add ticks. Any separate callback-entry charge must already be
included in `q_v`. These are declared accounting rules, not claims about Lean
evaluation time, physical allocation, sharing, stack use, or machine runtime.

## Exact sum, constant callbacks, and reached-input bounds

Induction on the actual tree gives

\[
W_e(t)=e(2n+1)+\sum_{v\in\operatorname{nodes}(t)}q_v,
\qquad n=n(t).
\]

Indeed, a node with child sizes `n_l,n_r` has size `n_l+n_r+1`, and its invocation
count is `1 + (2*n_l+1) + (2*n_r+1) = 2*(n_l+n_r+1)+1`. There are exactly `n`
callback invocations. The sum is over structural node occurrences, not distinct
payload values.

If every reached callback costs the same `c >= 0`, then

\[
W_e(t)=e(2n+1)+cn.
\]

If every reached callback costs at most a common `K >= 0`, then

\[
e(2n+1)\le W_e(t)\le e(2n+1)+Kn.
\]

The bound need only hold on reached arguments. It need not hold on every
possible pair of accumulator values. Conversely, a bound on unrelated or
idealized callback inputs is insufficient without a value correspondence
showing that those are the reached arguments.

Boundary expectations:

- Nil costs exactly `e`, even if the callback bound is zero; its callback
  premise is vacuous.
- If `K = 0`, nonnegativity forces every reached callback cost to be zero, so
  the exact cost is `e*(2*n+1)`.
- If `e = 0`, only the actual callback costs remain. If also `K = 0`, the
  declared cost is zero for every tree, despite traversal of both children.
- A positive upper bound `K` supplies no positive callback-cost lower bound.
  With `e = 0`, the generic bounded-callback statement alone does not establish
  a positive linear lower bound.
- With `e = 0` and constant `c > 0`, the exact cost is `c*n`; nil still costs
  zero. With `e > 0`, the invocation term supplies the stated lower bound.

## Three actual inorder callback expressions

Assume the saved measured append contract: `appendRun xs ys` returns `xs ++ ys`
and costs `length(xs) + 1`. Callback scaffolding is inlined and uncharged;
constructing `[a]` or `a :: r` inserts no extra tick in this model.

At a node, write `l,r` for the actual child-result lists and `m = length(l)`.
All three callbacks below return the same inorder list. Their measured append
calls differ:

| Callback expression | Actual append calls | Callback cost |
| --- | --- | ---: |
| Single append: `l ++ (a :: r)` | `appendRun l (a :: r)` | `m + 1` |
| Right-associated two appends: `l ++ ([a] ++ r)` | First `appendRun [a] r`, then `appendRun l suffix` | `2 + (m + 1) = m + 3` |
| Left-associated two appends: `(l ++ [a]) ++ r` | First `appendRun l [a]`, then `appendRun prefix r` | `(m + 1) + (m + 2) = 2*m + 3` |

For the last row, the actual first result has length `m + 1`; the second append
therefore costs `m + 2`. For the middle row, the first append's left operand is
the singleton regardless of the right list's length. This distinction cannot
be removed merely by using associativity of the returned lists. No extra
standalone callback tick is included in any row.

To replace `m` by the left subtree's node count, the measured fold must have
the ordinary inorder value correspondence for its actual child results. The
saved append value law and `length(inorder ltree) = n(ltree)` provide that route;
a cost equation by itself does not establish it.

Define the left mass by structural node occurrences:

\[
A(t)=\sum_{v\in\operatorname{nodes}(t)}n(\operatorname{left}(v)),
\]

equivalently,

```text
A(nil)        = 0
A(node a l r) = A(l) + A(r) + n(l).
```

Under the value correspondence just stated, the exact full-fold costs are

\[
\begin{aligned}
W_{\mathrm{single}}(t)&=e(2n+1)+A(t)+n,\\
W_{\mathrm{right}}(t)&=e(2n+1)+A(t)+3n,\\
W_{\mathrm{left}}(t)&=e(2n+1)+2A(t)+3n.
\end{aligned}
\]

Thus the right-associated expression costs exactly `2*n` more than the single
append; the left-associated expression costs exactly `A(t)` more than the
right-associated expression. These are equalities of the declared charges.
For any nonempty tree, a zero bound on these actual callback costs is
impossible: the single callback costs at least one, and either two-append
callback costs at least three.

## Hand-calculated shapes

Suppress labels and write `E = nil`, `N(l,r) = node a l r`, and
`P1 = N(E,E)`. Labels can all be `Unit`, so repetition has no bearing on these
counts. The complete-three shape is `P3 = N(P1,P1)`.

Define the chains by

```text
L_0 = E                 R_0 = E
L_(n+1) = N(L_n, E)     R_(n+1) = N(E, R_n).
```

The actual XT01 four-node sample is

```text
node 1 (node 0 nil nil) (node 3 (node 2 nil nil) nil).
```

Its root contributes one to the left mass, the node labelled `3` contributes
one, and the other two nodes contribute zero. Thus its left mass is two.

| Input | Node count | Fold invocations | Left mass `A` |
| --- | ---: | ---: | ---: |
| Nil | 0 | 1 | 0 |
| Singleton `P1` | 1 | 3 | 0 |
| Complete three `P3` | 3 | 7 | 1 |
| Left chain `L_n` | `n` | `2*n+1` | `n*(n-1)/2` |
| Right chain `R_n` | `n` | `2*n+1` | 0 |
| XT01 sample | 4 | 9 | 2 |

The left-chain identity follows from `A(L_(n+1)) = A(L_n) + n`; the right-chain
identity follows from `A(R_(n+1)) = A(R_n)`. The expression `n*(n-1)/2` denotes
the integer binomial coefficient, including value zero at `n = 0`; it also has
that value with truncated natural subtraction. No enumeration is used.

| Input | Single append | Right-associated two appends | Left-associated two appends |
| --- | --- | --- | --- |
| Nil | `e` | `e` | `e` |
| Singleton | `3*e + 1` | `3*e + 3` | `3*e + 3` |
| Complete three | `7*e + 4` | `7*e + 10` | `7*e + 11` |
| Left chain of three nodes | `7*e + 6` | `7*e + 12` | `7*e + 15` |
| Right chain of three nodes | `7*e + 3` | `7*e + 9` | `7*e + 9` |
| XT01 sample | `9*e + 6` | `9*e + 14` | `9*e + 16` |

For general chains, simplification gives

\[
\begin{array}{c|ccc}
&\mathrm{single}&\mathrm{right}&\mathrm{left}\\
L_n&e(2n+1)+\frac{n(n+1)}2&e(2n+1)+\frac{n(n+5)}2&e(2n+1)+n(n+2)\\
R_n&e(2n+1)+n&e(2n+1)+3n&e(2n+1)+3n.
\end{array}
\]

For fixed `e >= 0`, these are quadratic left-chain counts and linear
right-chain counts. The distinction persists when `e = 0`, since the append
contract still charges its own invocations. A uniform reached-callback bound
of one or three applies to the respective right-chain callbacks; no fixed
bound independent of chain length applies to the left-chain callbacks.

A useful general arithmetic bound is `0 <= A(t) <= n*(n-1)/2`. One proof counts
only ancestor/descendant pairs whose path starts with a left edge, among at
most all unordered pairs of distinct node occurrences. An inductive proof
uses child sizes `x,y`: the gap between the parent binomial bound and
`choose(x,2) + choose(y,2) + x` is `x*y + y >= 0`. The lower and upper endpoints
are attained by the right and left chains. Consequently the corresponding
global upper bounds on the three fold costs are respectively
`e*(2*n+1) + n*(n+1)/2`, `e*(2*n+1) + n*(n+5)/2`, and
`e*(2*n+1) + n*(n+2)`. These are supplementary expectations, not frozen scope.

## Actual bottom-up annotation and the alternative helper tariff

Consider a fold whose nil result is an empty cached tree and whose node
callback is the existing XT01 measured smart constructor. Its measured
contract charges two cache reads and one local constructor entry, then adds
the cost `q_v` of the supplied summary callback on the two values actually
read. Both reads cost one even when a child is nil. There is no smart-constructor
invocation at a nil fold branch.

Keeping the same separate fold-invocation charge `e`, the total is therefore

\[
W_{\mathrm{annot}}(t)=e(2n+1)+3n+\sum_v q_v.
\]

For supplied callbacks of constant cost `c`, this becomes
`e*(2*n+1) + (3+c)*n`; for supplied costs bounded by `K_inner`, it is at most
`e*(2*n+1) + (3+K_inner)*n`. Nonnegative supplied costs give the lower bound
`e*(2*n+1) + 3*n`. Here `K_inner` bounds the supplied summary callback, whereas
the generic whole-fold callback includes the three smart-constructor charges.
In particular, `K_inner = 0` leaves `3*n` in place. A bound of zero on the whole
measured smart-constructor callback is impossible at a nonempty input.

For a proposed measured fold, agreement with the saved ordinary bottom-up
`Cached.annotate` result should be established from reached callback value
contracts. The existing smart-constructor value/validity laws give the inductive route: valid child
annotations expose the ordinary child-fold summaries, and the parent stores
the supplied callback's actual value. No separate recursive validity checker
or recomputation of child summaries is inserted into this cost model.

For zero-cost supplied size, height, or minimum-height combines, the measured
annotation cost is exactly `e*(2*n+1) + 3*n`. At `e = 1`, this is `5*n+1`, so the
XT01 four-node sample costs 21. At `e = 0`, it is `3*n`, including zero for nil.

For annotations carrying actual inorder lists with the three append callbacks,
the same value correspondence makes their exact costs

\[
\begin{aligned}
W_{\mathrm{annot,single}}&=e(2n+1)+A(t)+4n,\\
W_{\mathrm{annot,right}}&=e(2n+1)+A(t)+6n,\\
W_{\mathrm{annot,left}}&=e(2n+1)+2A(t)+6n.
\end{aligned}
\]

For the XT01 sample these are `9*e+18`, `9*e+26`, and `9*e+28`; at `e = 1`, they
are 27, 35, and 37.

A **different, explicitly zero-helper tariff** may charge neither the cache
reads nor the local constructor entry, while retaining the supplied callback
cost and the same fold-entry charge. Under that alternative definition,

\[
W_{\mathrm{annot,zero-helper}}(t)=e(2n+1)+\sum_v q_v.
\]

The difference from the XT01 measured-smart-constructor model is exactly
`3*n` when the same reached summary callback costs are used. If the callback is
zero-cost, this alternative costs `2*n+1` at `e = 1`, or zero at `e = 0`.
For the inorder callbacks it has the earlier ordinary-fold cost formulas.

The two tariffs must not be silently identified. The fold-entry charge and
the measured helper's local entry are separately declared charges; a source
analysis that inlines or assigns zero cost to helpers needs its own
correspondence. Likewise, equality of returned annotations does not establish
equality of these counts. All formulas here remain conditional mathematical
expectations until an actual measured fold and the required source/value
correspondences have been supplied and independently validated.
