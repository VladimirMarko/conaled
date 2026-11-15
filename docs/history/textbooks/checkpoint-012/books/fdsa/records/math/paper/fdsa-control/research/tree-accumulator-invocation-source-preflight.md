# Inorder suffix accumulator and later invocation: source preflight

Prepared 2026-11-02. **Bounded source preparation only.** This note proposes
proof targets, not frozen requirements, an implementation, validation or
acceptance. Chapter 1 remains the prerequisite; the old gate 80227 is unchanged.
Checkpoint 0032 was still pending when this task began. This report's path was
checked absent, and it is the sole file written by this task. Earlier source
reports, inventories, requirements and repository sources remain unchanged.

## 1. Conclusion

Exercise 4.1 has a small, precise remaining obligation: an actual cons-only
suffix accumulator, its value law for **every** suffix, and a linear count for
its own execution. The companion `Tree.inorder2` gives the intended recurrence.
Under the retained recursive-entry tariff its derived count is `2*n+1`,
independently of the suffix length. The right recursive call supplies the list
used by the left recursive call; this dependency must survive instrumentation.

The ordinary tree fold can also produce a function whose **later invocation**
follows this recurrence. Its value and invocation observations do not measure
the construction of that function. A bounded follow-up can retain these two
phases using the existing measured-value interfaces. No general higher-order
cost translator, closure syntax, executor, sharing framework or new tree
carrier is required by the book or by this proposal.

## 2. Primary evidence and correspondence boundary

| Retained source | Bounded evidence used here |
| --- | --- |
| July 27, 2026 FDSA PDF, printed pp. 48–49 (PDF pp. 54–55) | Direct inorder; Exercise 4.1 asks for cons-only accumulation, linear time and `inorder2 t xs = inorder t @ xs`. The exercise specifies an algorithm and theorem, not a closure-construction cost model. |
| Same PDF, printed pp. 6–8, §1.5 | Full function-call translation, argument/value dependencies, one recursive-entry charge, zero primitive/constructor work and removal only of nonrecursive entry overhead. The displayed translation is expressly first order. |
| Same PDF, printed pp. 347–348, Appendix B.1 | Higher-order map/filter retain the cost of each supplied callback application, including duplicate input occurrences. |
| `book-source/Tree.thy`, lines 76–83 and 430–431 | Literal direct inorder; cons-only `inorder2`; `inorder2_inorder`, proved by tree induction with the suffix generalized. |
| `book-source/Time_Functions.thy`, lines 38–41 and 63–94 | Actual append cost and the generated/manual simplified map/filter callback equations and bounds. |

The PDF is the retained official download from
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The recorded Isabelle mirror revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21` at
<https://github.com/isabelle-prover/mirror-isabelle>. The relevant original paths
are `src/HOL/Library/Tree.thy` and
`src/HOL/Library/Time_Functions.thy`. Their retained digests are,
respectively,
`1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`
and `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`.
BSD-3-Clause provenance and applicable notices remain in the saved inventories.
These are existing recorded identities; no hash helper or remote retrieval ran.

The mirror revision postdates the manuscript. Its actual recurrence and theorem
match the printed exercise, but it is not asserted to be the manuscript's build
revision. `Tree.thy` imports `Main`; the retained file contains no `time_fun`
declaration and no `T_inorder2` or `T_inorder` theorem. The comment describing
`inorder2` as linear does not supply a generated timing proof. No imported
compiler term dump, normalization trace, closure-conversion trace or physical
runtime evidence was recovered or inferred in this task.

The settled append association and earlier constructor-charge irregularity are
not new findings: use `tree-fold-resource-source-preflight.md` and the retained
Chapter 1 disposition. The original `difference-list-cost-preflight.md` also
has a retained provenance erratum,
`reviews/difference-list-provenance-correction.md`: its natural-merge theory is
from the dated AFP archive, not the Isabelle revision above. This task uses its
creation/application distinction without repeating the old attribution.

## 3. Original obligations retained

| Inventory item | Exact obligation and this possible follow-up's boundary |
| --- | --- |
| C04-004 and C04-015 | The original node-labelled inorder and its length/value observations are the specification. Existing XT01 draft observations can be reused after their prerequisites; no replacement leaf-labelled tree is justified. |
| C04-017 / Exercise 4.1 | Implement the cons-only accumulator and prove the arbitrary-suffix theorem. The empty-suffix materialization theorem alone is insufficient for the recursive step. |
| C04-018 / Exercise 4.1 | Prove linear running time of the actual accumulator in the declared source model. The derived exact count below is a useful stronger target. The introductory direct-inorder quadratic worst-case claim remains a separate part of this item. |
| Appendix B.1 higher-order observations | Retain supplied callback work at actual arguments. These are the relevant cost conventions; they do not require a new general higher-order translator. |

XT03 expressly left the accumulator/invocation bridge outside its frozen scope.
Its direct-inorder callback laws are useful comparison evidence, but they do not
discharge this different execution. Conversely, an accumulator follow-up need
not solve all-tree direct-inorder asymptotics or every Chapter 4 exercise to
establish its own shared result. Those original obligations remain queued.

## 4. Actual dependent execution and proof route

Write `E` for the empty tree, `N l a r` for a node, `I` for the existing inorder,
and `A` for the source accumulator. The source equations are:

```text
A E suffix           = suffix
A (N l a r) suffix   = A l (a :: A r suffix).
```

The inner right call executes first under the declared call-by-value model.
After it returns `rightList`, the left call receives `a :: rightList`.
Neither the supplied suffix nor the right result is traversed merely to cons
the root label. The algorithm executes no append. Its result still has the
left-root-right output order.

For existing measured pairs, a faithful invocation recurrence is:

```text
invoke E suffix = (suffix, 1)
invoke (N l a r) suffix =
  tick (bind (invoke r suffix) (fun rightList =>
    invoke l (a :: rightList))).
```

This is a proposed equation, not new Lean code. With
`R = invoke r suffix` and `L = invoke l (a :: R.value)`, its exact cost is
`(R.cost + L.cost) + 1`. `Resources.CallCount.tick` posts the entry charge after
the body; this is the existing observation convention, not a claim that machine
entry occurs afterward. The dependent left argument is the actual returned
right value, not an independently specified list.

The smallest useful theorem proves both observations for every suffix:

```text
invoke t suffix = (I t ++ suffix, 2*t.numNodes + 1).
```

Tree induction must generalize `suffix`. First use the right induction
hypothesis, then the left hypothesis at the resulting cons suffix. Standard
append associativity is used in the **specification proof**; it does not insert
append into the execution. The same universal induction proves that both
recursive invocation costs are suffix-independent, so the node cost becomes
`(2*n(r)+1) + (2*n(l)+1) + 1 = 2*n(t)+1`.

Termination is structural on the tree even though the suffix can grow. No
suffix-size measure, label order, equality decision, inhabitant, tree invariant
or nonempty-tree premise is needed. The result-length corollary is
`length(value) = n(t) + length(suffix)`, using the existing inorder length law.
The two counts are distinct: returned output length includes the untouched
suffix, whereas invocation work does not.

The empty call counts one. Thus a uniform bound should be phrased as `O(n+1)`
or asymptotic `O(n)`, with its zero-input boundary retained; a pointwise bound
`cost <= K*n` for every tree is false at `E`. In the uninstrumented source
equation the left recursive call is in tail position, but the right call is
not. That algorithm and the measured count do not establish constant stack
usage or a compiler tail-call guarantee.

## 5. Function construction and invocation are separate observations

An alternative representation reuses the ordinary fold at the existing function
type `List alpha -> Measured (List alpha) Nat`:

```text
emptyFunction suffix = tick (pure suffix)
nodeFunction left a right suffix =
  tick (bind (right suffix) (fun rest => left (a :: rest))).
K_t = Trees.fold emptyFunction nodeFunction t.
```

The equations for `K_t suffix` are precisely the invocation equations above.
This gives a small continuation-execution bridge without a new datatype or
framework. The ordinary fold receives left and right function summaries as
its node arguments; the existing measured construction wrapper sequences
those summaries left then right. Applying the constructed node function later
invokes the right function before the left. Construction order and invocation
order must not be conflated or promoted to a compiler-evaluation claim.

Under strict evaluation, constructing `K_t` can traverse the whole tree before
any suffix is supplied. Its later measured application has count `2*n+1`;
that number alone is **not** the charge for constructing and then applying the
function. The source's curried type `tree -> list -> list` does not itself
specify a separately charged partial-application or closure-creation algorithm.
The book's direct two-argument recurrence and an explicitly staged function
builder are different execution descriptions, even when their invocation
equations and returned lists agree.

If a connected construction example is useful, the existing XT03
`Resources.TreeFold.run` can measure that phase with function summaries. A
zero-cost callback returns the composed closure without invoking its children;
entry one then gives construction cost `2*n+1` in that **declared construction
tariff**. One later invocation gives total `4*n+2`; two independent invocations
give `6*n+3`. These are conditional model targets for an actual bind-composed
program, not new source claims or measured compiler allocation facts. The
same stored function must actually be invoked twice for the latter theorem;
reusing a previously materialized list is another computation.

No second implementation is mandatory. Following the direct two-argument
recurrence is the simplest book correspondence. If the chosen implementation
uses the existing fold to construct functions, its public statement should
identify the invocation boundary and any separately measured construction.
Either route needs a real linear execution theorem for the operation claimed
to satisfy Exercise 4.1; a value-level function equality alone is insufficient.

## 6. Existing higher-order reuse and tariff cautions

The relevant local reuse is already small:

- `Trees.fold`, its equations and fusion laws in
  `Applications/Trees/Observations.lean` provide ordinary function-valued
  structural construction; they do not charge later function application.
- `Measured`, `bind`, `pure`, `CallCount.tick` and `let_rule` express actual
  returned values and the right-to-left dependency. XT03's measured fold can
  observe construction separately if included.
- `Applications/Bracketing/Basic.lean` has `fringeAcc` and `fringeAcc_eq` with
  the same generalized-suffix induction pattern. Its tree is leaf-labelled,
  so it is a proof pattern, not the required node-labelled theorem or count.
- XD01's ordinary measured function type and its `Rep`/`AppCost` contracts
  match useful optional value/cost views. A value adapter to existing
  `Batteries.DList` is possible, but is not necessary for the accumulator and
  does not carry resource observations into the DList value.

The Appendix B.1 recurrence is
`T_map C (x::xs) = C x + T_map C xs + 1`, with empty cost one. It directly
rules out erasing unknown callback invocation work under §1.5's first-order
variable clause. It does not define arbitrary closure allocation/application
costs. The present fixed accumulator can expose its callbacks explicitly,
without generalizing the language model.

XD01's charged `singleton` and `compose` have their own unit application
entries. Using charged identity at `E` and expressing a node by two charged
compositions and a charged singleton would add three node-local calls; the
resulting all-tree invocation count is `4*n+1`, not the source accumulator's
`2*n+1`. An uncharged pre-cons wrapper
with one charged composition can match the displayed node recurrence, but
there is no need to import XD01 merely to write the existing bind/tick formula.
Extensional builder validity or the represented prefix length cannot justify
an application-cost bound for an arbitrary supplied function; XD01's retained
padded/shared-closure examples already explain that limitation.

This zero-cost-cons model does not change XT01's positive cache-read/smart-node
tariff or the pinned leftist source's zero-helper tariff. No cached read or
smart constructor occurs in the accumulator. Storage, physical sharing,
garbage collection and closure memory remain unmeasured. Repeated subtree
occurrences are executed repeatedly, even if host-level references happen to
be shared.

## 7. Small independent expectations and bounded recommendation

These are calculations from the recurrences, not an enumeration run or checked
Lean examples. The saved asymmetric XT01 tree has root 1, left singleton 0,
and right root 3 with left singleton 2.

| Case | Returned value | Invocation count / useful distinction |
| --- | --- | --- |
| Empty tree, arbitrary suffix `s` | `s` | 1, independently of `length s`; no copy of `s` is charged. |
| Singleton `a`, suffix `s` | `a :: s` | 3, including both empty-child calls. |
| Saved four-node tree, suffix `[9,9]` | `[0,1,2,3,9,9]` | 9; right subtree contributes 5, left singleton 3, root 1. |
| Same tree, empty suffix | `[0,1,2,3]` | Also 9; this specialization alone is weaker than the all-suffix law. |
| Same tree, ordered labels on post-body node events | `[2,3,0,1]` as node-event trace | Distinguishes invocation order from XT03's left-first callback trace `[0,2,3,1]`; empty events are omitted in this explanatory trace. |
| Three-node left and right chains | Their respective inorder followed by `s` | Both cost 7; contrast with direct-inorder shape dependence. |
| `N u a u` | `I u ++ [a] ++ I u ++ s` | `4*n(u)+3`, counting both occurrences of `u`. |
| `BinaryTree Empty` | Only the empty tree and empty suffix exist | Count 1; no artificial default label. |
| Optional measured construction on the four-node sample | Returns the function, without applying it | Declared construction 9, one invocation 9, total 18; construction plus two invocations 27. |

A small reusable follow-up is warranted if it supplies the actual suffix
recurrence, all-suffix value/count theorem, and a connected invocation example
that preserves the two phases. The optional construction example can consume
XT03 instead of adding machinery. The appendix's higher-order convention and
the existing difference-list work justify the distinction, not a larger scope.

The direct-inorder quadratic family, all remaining Chapter 4 exercises,
book-specific later algorithms and any additional source-runtime/storage
claims remain separate. No scope was frozen and no chapter was activated.
This note supplies source/mathematical preparation only; there was no compiler,
checker, project hash helper, enumeration campaign, Git/ref/cache/gate change,
remote action or final-review claim.
