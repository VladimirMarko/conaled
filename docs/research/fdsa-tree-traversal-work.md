# Shape-sensitive work of actual tree traversals

This is the **uncompiled FDSA-XT05 draft**. It contributes shared tree/resource
mathematics and connected uses of the saved XT03/XT04 executions. It does not
activate or accept Chapter 4. Accepted repaired Chapter 1, XT01, XT03 and XT04
are prerequisites to integration/acceptance; XT02 and XD01 are not dependencies.
The complete candidate still needs compilation, applicable full validation,
exhaustive audit, both independent final review axes and immediate candidate
verification. The initial Chapter 2-first integration plan remains unchanged.

Frozen local requirements have SHA-256
`454ccd268e41986bcff6abd6d48fd97fee68baad637ec1840b3cd4b39925e9f0`.
The recovery records preserve the original base, complete preflights, exact
source identities and inherited findings. This note records implementation-side
statement assessment, not an elaborated-type inspection or final approval.

## Source correspondence and observation boundary

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026 edition, available from
[the official book site](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
Printed p.48 defines direct inorder with two appends. The p.5 parsing convention
makes this right-associated. Exercise 4.1 on p.49 asks for a cons-only accumulator,
its arbitrary-suffix value law and linear work, against direct inorder's
quadratic worst case. Local obligations are C04-017/018.

The retained companion mirror is Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`.
[`Tree.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Tree.thy)
contains the direct/accumulator recurrences at lines 76–83, traversal length at
415–416 and arbitrary-suffix value law at 430–431. It contains no generated
`T_inorder` or `T_inorder2` declaration. This snapshot postdates the manuscript
and is not asserted to be its build revision. The original inventories retain
the exact book/theory identities and source notices.

Book p.56 and
[`Tree2.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree2.thy)
define a traversal that ignores annotations and uses a single append to a cons.
The whole inorder-list cache built by XT03 is a separate specialization of
generic augmentation on pp.57–58. The book does not print its full-pass timing
formula. It is useful here because its actual local append callback exposes
the same shape-dependent work.

All counts refer to the existing declared measured programs:

- A recursive tree entry, including nil, has natural charge `e`.
- Actual append has work `length(left)+1`, including its terminal invocation.
- XT01's actual cached constructor retains its two charged reads, combining
  callback and one local entry, so its helper overhead is three.
- Primitive list construction has no separate charge in these models.

No compiler normalization, source-cost translator, physical runtime, allocation,
sharing or stack bound follows. The source append association is preserved by
the literal execution even though all three callbacks have the same list value.

## One pure shape observation

`Trees.leftSizeSum t` sums the sizes of left subtrees over **node occurrences**.
Writing `A(t)` for it and `n(t)` for canonical `BinaryTree.numNodes`:

```text
A(nil) = 0
A(node a l r) = A(l) + A(r) + n(l).
```

It is the second component of one private ordinary Nat-pair fold. The first
component is connected to canonical size by existing `fold_fusion` and
`fold_numNodes`; it is not another public size API. The node equation consumes
that bridge. The statistic is an external observation in the work theorems;
the algorithms do not execute an extra analysis pass.

Arbitrary label maps preserve A, including noninjective maps and erasure of
annotation labels. Equal children retain both occurrences:
`A(node a t t)=2*A(t)+n(t)`. Neither label equality/order nor an inhabitant is
required. Source and target label universes remain independent.

The sharp structural estimates are

```text
2*A(t)+n(t) <= n(t)^2
A(t)+n(t)   <= n(t)^2
A(t)       <= n(t).choose 2.
```

The induction step for the first estimate leaves the nonnegative gap
`2*n(r)*(n(l)+1)`. A private Pascal-derived identity
`2*(n.choose 2)+n=n^2` connects it to the existing binomial coefficient.
No natural subtraction/division premise or new triangular-number operation is
needed. All three statements include nil and singleton.

Explicit supplied-label families `leftChain a n` and `rightChain a n` have
canonical size and height n and identical inorder `List.replicate n a`. Their
statistics are respectively `n.choose 2` and zero. The left family therefore
attains the bound at every n. `old_chain` proves that the generic left family
at Unit is the existing `TreeCacheExamples.chain`, without replacing that
definition or its prior clients. A positive-size witness has a supplied label;
universal facts still cover the unique empty tree over Empty.

The chosen statistic and chains are a shared proof device. The book does not
require this particular statistic, a maximum over all labelled trees or a
classification of all maximizing shapes.

## One resource theorem, four actual clients

`Resources.TreeFold.run_cost_leftSizeSum` concerns the existing actual executor.
For fixed entry, empty summary, callback and coefficients d,c, its hypothesis
quantifies over every finite pair of child trees and label. It inspects the
callback on the values returned by those actual child runs, at the same fixed
parameters, and requires work `d*n(l)+c` there.

This is a local callback contract. It does not assume the final whole-run
formula, a law on every possible summary, or a premise restricted to one chosen
tree's subtrees. Payload and summary universes remain independent. The result is

```text
cost(run e empty callback t) = e*(2*n+1)+d*A(t)+c*n.
```

The proof rewrites the actual node-cost law, discharges its actual callback
occurrence, uses the child induction hypotheses and ordinary A/size laws, then
collects Nat arithmetic. There is no second executor or recursive cost evaluator.
This numerical collection does not change the raw arbitrary-Add observation
grouping or the earlier noncommutative word examples.

The connected examples instantiate four existing programs:

| Actual program | d,c | Exact work |
| --- | --- | --- |
| Single append to a cons | 1,1 | `e*(2*n+1)+A+n` |
| Literal right-associated two appends | 1,3 | `e*(2*n+1)+A+3*n` |
| Left-associated comparison | 2,3 | `e*(2*n+1)+2*A+3*n` |
| Whole inorder-list cached annotation | 1,4 | `e*(2*n+1)+A+4*n` |

The append instances establish their premise using the actual step cost, actual
child value theorem and `inorder_length`. The cache instance uses the actual
smart-node callback, its local append cost, and `list_read` for the actual
returned child annotation before taking its length. That read contract is
supported by recursive validity and erasure; it does not assume a supplied
corrupt cache is correct. The explicit raw/wrapped bridge retains the approach
of the XT03-CP01 correction. Four already includes all three helper charges.

The first three programs return the same inorder list. The fourth returns an
annotated tree; `sample_cache_observations` connects its reader, erasure and new
work formula. No equality of a whole annotated tree with a list is asserted.
Reading a specified mathematical projection in a theorem is not another charged
execution. These formulas also do not turn sums of cache-list lengths into
physical memory or allocation bounds.

Exact natural comparisons retain the costs of both appends:

```text
Wright = Wsingle + 2*n
Wleft  = Wright  + A
Wcache = Wsingle + 3*n.
```

`right_cost_map` preserves the actual literal traversal's work under arbitrary
label maps of given inputs. Computing the map is outside that comparison.
Zero entry removes structural charges while leaving append/helper work.
The separate pure size callback uses d=c=0 and retains only structural work;
with entry zero its actual observation is zero. Thus the generic formula does
not imply quadratic growth for arbitrary coefficients.

## Worst-case qualification and standard asymptotics

For positive node count, the exact formulas give the following all-tree bounds:

| Actual work | Upper bound |
| --- | --- |
| Single append | `(3*e+1)*n^2` |
| Literal right-associated traversal | `(3*e+3)*n^2` |
| Left-associated comparison | `(3*e+3)*n^2` |
| Full list annotation | `(3*e+4)*n^2` |
| Existing materialize-then-append program | `6*n^2` |

The literal source traversal has exact family results

```text
left chain:  (replicate n a, e*(2*n+1)+n.choose 2+3*n)
right chain: (replicate n a, (2*e+3)*n+e).
```

For every n, including zero, its left-chain count satisfies `n^2 <= 2*W`.
The upper estimate needs positive size: at entry one nil costs one and no
pointwise `K*n^2` bound can cover it. `nil_not_square_bound` retains that case.

The existing `Resources.isBigO_of_nat_bound` packages these natural estimates
as standard real-cast `Asymptotics.IsTheta Filter.atTop` statements about the
**actual run projections**: quadratic for left chains and linear for right
chains. Entry e and the supplied label are fixed before the eventual index.
The upper threshold is one; lower estimates include zero. No new growth
predicate or unconnected polynomial execution is introduced.

At source entry one, `source_upper` gives `W(t)<=6*n(t)^2` for every nonempty
tree, while `source_witness` supplies a size-n left chain with `n^2<=2*W`.
`source_rightChain` has exact work `5*n+1`. Together these express quadratic
worst-case growth and a linear family, with the same returned inorder values.
They do not assert a quadratic lower bound for every shape.

## Complete suffix programs with construction included

XT04 already defines both programs used here. `materializeAppend` executes the
single-append traversal and passes its actual returned prefix to measured
append. `buildOnce 1 1` executes one measured function construction, then invokes
its actual returned function once. Both return `inorder t ++ suffix` for every
suffix. Their work laws are separately connected to their actual programs:

```text
cost(materializeAppend t suffix) = 4*n+2+A(t)
cost(buildOnce 1 1 t suffix)     = 4*n+2
cost(materializeAppend t suffix)
  = cost(buildOnce 1 1 t suffix)+A(t).
```

The construction cost is included in the second line. The construction theorem
`build_value` identifies the returned function with the invocation function of
type `List α → Measured (List α) Nat`, preserving each application's complete
inner measured result. The independent all-suffix invocation theorem supplies
the application work. The value returned by `buildOnce` itself is a list;
equality of erased lists alone does not give the displayed cost difference.

Right chains give equality of the complete measured results, with arbitrary
suffix. Left chains give exact excess `n.choose 2`. Nil and singleton give equal
totals two and six. The sample gives `20=18+2`; its invocation-only count nine
still describes a different program boundary. No extra staged execution or
alternative closure tariff is introduced.

## Connected cases and statement assessment

The independently worked entry-one expectations are retained through public
theorems, rather than by substituting unrelated arithmetic for the executions:

| Input | n | A | Single | Right | Left | List cache | Materialize | Build once |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Nil | 0 | 0 | 1 | 1 | 1 | 1 | 2 | 2 |
| Singleton | 1 | 0 | 4 | 6 | 6 | 7 | 6 | 6 |
| Three-node left chain | 3 | 3 | 13 | 19 | 22 | 22 | 17 | 14 |
| Three-node right chain | 3 | 0 | 10 | 16 | 16 | 19 | 14 | 14 |
| Saved asymmetric sample | 4 | 2 | 15 | 23 | 25 | 27 | 20 | 18 |

The code explicitly connects the new formulas to the sample and nil/singleton
boundaries. Generic formulas derive the other table entries; the chain
countercase explicitly checks equal size, height and complete returned inorder
with literal-right work 19 versus 16. The repeated-singleton case has A=1,
and the general repeated-child law retains both occurrences. A noninjective
sample map retains A=2 and literal work 23 while returning four repeated labels.
At entry zero the actual sample append/cache counts remain 6/14/16/18.

Statement assessment checks the following distinctions:

- Shape statements quantify over arbitrary labels, including Empty; witness
  families take an actual label. No hidden equality/order/inhabitant premise.
- The generic resource premise inspects actual reached summaries at fixed
  parameters; the four clients discharge it through actual value/read lengths.
- Exact formulas include nil and zero entry. Upper proportional bounds retain
  positive size; arbitrary zero coefficients receive no unsupported Theta claim.
- Natural collection is distinct from the unchanged ordered observation laws.
  Source association, both append executions and helper overhead are preserved.
- Cache-tree, root-reader and traversal-list values remain distinct, with their
  explicit bridges. Construction and invocation stay separately accounted for.
- All suffix-program comparisons quantify over arbitrary suffixes and retain
  both actual binds; equal values are not used to transfer costs.

These are source-level assessments. They do not establish that tactic proofs,
coercions, private fold fusion or concrete reductions elaborate successfully.
Inherited XT03-CP01/DOC01 remain in the review record with source correction
evidence and pending compiler/final confirmation as applicable.

This draft addresses the remaining direct-inorder work argument within C04-018
and supplies additional generic-augmentation evidence. It leaves original
chapter obligations in their inventories: enumeration, weighted paths, levels,
reconstruction, completeness/checker/subtrees, balancing and its actual wrappers,
remaining augmented clients and later search/heap/tree algorithms. No balancing
wrapper becomes linear merely because its balancer is linear. The excluded
maximizer classifier, balanced n-log-n family and generic translator/history/
closure mechanisms are not additional required deliverables. All chapters and
shared units still require their own matching validation and final acceptance.
