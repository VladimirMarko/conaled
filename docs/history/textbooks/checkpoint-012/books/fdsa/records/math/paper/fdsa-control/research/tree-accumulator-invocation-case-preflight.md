# Tree suffix execution and invocation: independent mathematical cases

## Status and inspected basis

This is independent mathematical preparation for a possible shared follow-up.
It freezes no scope, implements no operation, activates no chapter, and supplies
no compilation, final-review or acceptance evidence. The active Chapter 1 gate
80227 is unchanged. Only this new note is written; no compiler, checker, hash
helper, enumeration, worktree/ref/cache mutation, remote operation or child agent
is used.

The bounded source reading covered:

- `fdsa-control/research/tree-fold-resource-source-preflight.md` and
  `tree-fold-resource-case-preflight.md`, including their creation/application
  boundary and source timing conventions;
- `book-source/Tree.thy`, the actual `inorder2` equations and the arbitrary-suffix
  theorem `inorder2_inorder`;
- the relevant invocation warning in `tree-fold-resource-api-preflight.md`;
- `conaled-builder-costs/Applications/Resources/DifferenceListCosts.lean` and
  its connected `Examples/DifferenceListCosts.lean`.

The difference-list files belong to a separate saved, unvalidated candidate;
this reading does not silently make that candidate an accepted or integrated
dependency. The retained theory mirror is also not asserted to be the book's
build revision. All earlier reports remain unchanged.

## 1. The actual suffix recurrence and its accounting boundary

Let `I(t)` be the existing ordinary inorder value. Write `E` for nil and
`N(l,a,r)` for a node. The retained source says

```text
I2(E, xs)        = xs
I2(N(l,a,r), xs) = I2(l, a :: I2(r, xs)).
```

Under its call-by-value interpretation, the right call receives the original
suffix first. Its actual returned list, with `a` prepended, is then the left
call's suffix. This dependency is part of the execution, even though the final
list has left/root/right order.

For a declared nonnegative structural charge `e`, a faithful measured version
has the following pair equations. These are mathematical execution targets,
not an implementation added by this note:

```text
S_e(E, xs) = (xs, e)

R = S_e(r, xs)
L = S_e(l, a :: R.value)
S_e(N(l,a,r), xs) = (L.value, (R.cost + L.cost) + e).
```

The node body is an actual bind of the right result into the left call. The
entry observation is posted after that body, consistently with the existing
`CallCount.tick` convention. Cons, argument packaging and inlined scaffolding
have no extra charge in this declared model. There is no append call. Preparing
the input tree or suffix is outside this invocation boundary.

For natural observations, the expected full pair theorem is

\[
S_e(t,xs)=\bigl(I(t)\mathbin{++}xs,\ e(2n(t)+1)\bigr)
\quad\text{for every }xs.
\]

It is a theorem about the actual recurrence, not permission to define a
purported executor as an unmeasured `I(t) ++ xs` with a guessed count attached.
The displayed ordinary inorder/append expression belongs to the value
specification and need not be executed.

The induction must generalize the suffix: the left induction hypothesis is
used at `a :: R.value`, not at the original `xs`. The right value theorem makes
that argument `a :: (I(r) ++ xs)`. The left theorem and list associativity then
give `(I(l) ++ (a :: I(r))) ++ xs`. For costs, each node contributes one entry
and both child costs, including empty children. With child sizes `p,q`, the
invocation count is `1 + (2*p+1) + (2*q+1) = 2*(p+q+1)+1`.

The exact cost is independent of suffix contents and length. Output length is
`n(t) + length(xs)`, whereas cost still depends only on the tree. Nil costs `e`,
not zero unless `e = 0`. At `e = 0`, this tariff records zero on every tree; it
does not assert that traversal or machine execution is physically free.

## 2. Connected finite and payload cases

| Given input | Returned value, for arbitrary suffix `xs` | Expected invocation cost |
| --- | --- | ---: |
| Nil | `xs` | `e` |
| Singleton labelled `a` | `a :: xs` | `3*e` |
| Complete three-node tree with inorder `[a,b,c]` | `[a,b,c] ++ xs` | `7*e` |
| XT01 asymmetric four-node sample | `[0,1,2,3] ++ xs` | `9*e` |
| Either chain orientation with `n` nodes | Its ordinary inorder followed by `xs` | `e*(2*n+1)` |

The actual saved sample is

```text
node 1 (node 0 nil nil) (node 3 (node 2 nil nil) nil).
```

At its root and suffix `[9,8]`, the right subtree returns `[2,3,9,8]`; the left
subtree is then invoked on `[1,2,3,9,8]`; the final result is
`[0,1,2,3,9,8]`. The right subtree has two nodes and costs `5*e`, the left has
one node and costs `3*e`, and the root adds `e`, giving `9*e`. These are hand
calculations from the actual dependency, not a finite enumeration.

Useful boundaries and failure witnesses:

- The suffix may be empty, nonempty, contain duplicates, or share values with
  the tree. No distinctness, ordering, decidable equality or inhabitance
  premise is needed for the value or count statement.
- For `t : BinaryTree Empty`, the tree is nil. Every `List Empty` suffix is
  also empty, so the result is `([], e)`. The generic nil theorem on an arbitrary
  payload type must still cover arbitrary nonempty suffixes.
- Map every label of the saved sample to `7` and use suffix `[7,7]`. The result
  has six occurrences of `7`, and the invocation costs `9*e`. A Nat-to-Unit
  relabelling supplies the same repeated-label boundary. These are comparisons
  on given inputs, not claims that computing a map has been charged.
- Equal child values still give two recursive invocations. If both children
  are the same singleton value, there are three node occurrences and seven
  invocations. Equality or sharing of their descriptions does not memoize
  either invocation.
- Simply swapping the right and left calls in the recurrence, while keeping
  the same suffix-passing pattern, produces reverse inorder. On the saved
  sample it yields `[3,2,1,0] ++ xs` with the same numerical invocation count.
  A count theorem alone cannot establish the intended traversal order.

## 3. A diagnostic ordered observation

An optional diagnostic can record post-body charge tokens: nil records `E`,
and a node labelled `a` records `N(a)`. Preserve right-before-left bind order:

```text
T(E)        = [E]
T(N(l,a,r)) = T(r) ++ T(l) ++ [N(a)].
```

On the saved sample, the full word is

```text
[E, E, E, N(2), N(3), E, E, N(0), N(1)].
```

Its length is nine. Keeping only node tokens gives `[2,3,0,1]`, whereas XT03's
left-child-first ordinary fold records node callbacks in order `[0,2,3,1]` on
this sample. Returned inorder lists agree; the execution observations differ.

These are **post-body observations**, not a claim that actual call-entry events
occur in that order. A pre-body entry trace would be a different observation.
Also, a single identical constant token for every invocation cannot distinguish
the schedules: both words would simply contain nine copies of that token.
Node-specific tags, or other independently distinguished observations, are
needed for this countercase. This optional diagnostic does not freeze a new
trace framework or a general observation API.

## 4. Function values and one actual application

The same suffix executor can be represented by a function-valued ordinary fold
whose base and node algebra return **measured functions**:

```text
F_e(E) = fun xs => (xs, e)
F_e(N(l,a,r)) = fun xs =>
  post_e (bind (F_e(r) xs) (fun ys => F_e(l) (a :: ys))).
```

The ordinary fold assembles child function values. The returned function's
body invokes the right child on the supplied suffix, then the left child on
the actual returned list. A faithful bridge must establish these application
equations, or pointwise equality of the **whole measured result** with the
suffix recurrence. Merely identifying the erased endofunction with
`fun xs => I(t) ++ xs` proves no application-cost statement.

This permits one executor rather than two: the applied function-valued fold
itself may be the actual measured execution, with its pair recurrence proved
by structural unfolding. The pure inorder is a specification. A separate
recursive cost evaluator or a second real execution is unnecessary.

The saved `DifferenceListCosts.Builder` alias already has the relevant shape
`List alpha -> Measured (List alpha) Nat`. Its two separate predicates express
different obligations:

```text
Rep f prefix : every suffix returns prefix ++ suffix
AppCost f k  : every suffix application has cost k.
```

For a faithful tree suffix function, the intended contracts are
`Rep f (Trees.inorder t)` and `AppCost f (e*(2*t.numNodes+1))`. A DList value
bridge consumes the first contract and forgets the second. No additional
wrapper record is justified by this note alone.

## 5. Repeated applications after one construction

Let an actual constructor return the appropriate measured function `f` with
observed construction work `B`. A program that binds that constructor once,
then binds `f xs` and `f ys`, returning both lists, has expected value

```text
(I(t) ++ xs, I(t) ++ ys)
```

and total work

\[
B+2e(2n(t)+1).
\]

More generally, `m` actual applications contribute `m*e*(2*n+1)`, in addition
to the single construction's actual work. This requires an actual sequencing
program or recurrence; it is not inferred from writing the function value
twice in an informal expression. Applying the same function twice is distinct
from retaining one already materialized result.

For the four-node sample at `e = 1`, two applications cost 18 when the function
is already supplied at the program boundary. The two results for suffixes
`[9]` and `[8,8]` are `[0,1,2,3,9]` and `[0,1,2,3,8,8]`.

Construction work must be declared separately. Two informative conditional
comparisons are:

- A charged capture of the already supplied tree,
  `tick (pure (fun xs => S_1(t,xs)))`, has construction observation one under
  the explicit unit-capture tariff, and invokes no suffix execution during
  capture. One such capture plus two sample applications costs `1+18 = 19`.
  This is not a compiler-allocation claim.
- A strict XT03 fold that assembles measured child closures with an inlined,
  zero-cost creation callback and construction-entry charge `b` has outer
  construction observation `b*(2*n+1)`. Its returned closures can have a
  separately proved invocation observation `e*(2*n+1)`. At `b=e=1` on the
  sample, construction costs nine, one application costs nine, and one
  construction plus two applications costs 27. The equality of the two
  single-phase numbers is incidental; the outer construction count does not
  prove the inner application count.

The unit-capture and strict-fold constructions are different actual programs
under separately declared tariffs, even if their returned measured functions
are extensionally equal. Neither construction is selected or frozen here.

## 6. Concrete failures of inference from function values

The inspected difference-list work supplies consequential existing boundaries:

1. `DifferenceListCosts.singleton a` and the tree singleton suffix execution
   both return `a :: xs` for every suffix. The former costs one application
   entry; the tree recurrence at `e = 1` costs three because it also invokes
   both nil children. Pure function-value equality does not equate those costs.
2. For any supplied builder `f`, the existing `compose f empty` has the same
   returned list as `f` at every suffix but costs exactly two additional
   invocation occurrences. Hence even an already established tree suffix
   representation can acquire a different cost without changing its erased
   endofunction or DList value.
3. Testing only `[]` is insufficient. The existing charged identity `empty`
   and the actual callback `fun xs => appendRun xs []` both return `([],1)`
   on `[]`. On `[9]` both return `[9]`, but their costs are one and two. Both
   represent the empty prefix for every suffix, yet only the former has
   constant application cost one. The append cost is obtained from its actual
   `length(xs)+1` contract, not invented as a tally.

There is also a direct tariff trap in reusing charged composition. If one
chooses the existing builders

```text
D(E)        = DifferenceListCosts.empty
D(N(l,a,r)) = compose (D(l)) (compose (singleton a) (D(r))),
```

their values have the desired inorder suffix behavior, but the application
recurrence is `C(E)=1` and `C(N)=C(l)+C(r)+3`: one singleton and two composition
entries are charged at each node. The resulting cost is `4*n+1`, which is five
on a singleton and 17 on the sample, not three and nine. Inlining the cons and
combination scaffolding of the source accumulator is a distinct tariff and
needs an actual corresponding body; a value theorem does not remove charges
from these existing builders.

Finally, `I2(t,xs)=I(t) ++ xs` does not prescribe a program that first computes
`I(t)` and then appends. If an actual comparison program runs XT03's
single-append inorder on the sample and then appends the returned four-element
prefix to `xs`, its count at entry one is `15 + 5 = 20`, independently of suffix
length. The append-free suffix recurrence costs nine. If the materialized
prefix is already supplied instead, append alone costs five, with preparation
outside that different boundary. All three programs can return the same list.

## Preparation limits

The useful future connections are the arbitrary-suffix value theorem, the
actual right-to-left dependency, the per-application count, and an explicitly
sequenced construction/application client. The examples above distinguish them
without postulating a second execution, memoization, a closure compiler, an
allocation model, or a cost attached only to a desired answer. They do not
settle stack depth, retained storage, physical sharing, evaluation strategy of
compiled Lean, or the remaining Chapter 4 algorithm obligations. All claims
about a future measured implementation still require source correspondence,
proofs and the project's independent validation; this note supplies none of
that acceptance evidence.
