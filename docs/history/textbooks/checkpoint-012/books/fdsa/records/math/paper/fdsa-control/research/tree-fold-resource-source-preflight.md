# Measured whole-tree fold: source timing and reusable proof boundaries

Prepared 2026-11-02. **Bounded source preparation only.** XT02 is recorded as
committed at `974a97321a8ec174b56104c7e6efaaca881b6639` and saved in checkpoint
0030; that receipt does not establish acceptance. This note freezes no scope,
implements no algorithm and changes no existing inventory or historical report.
Its path was checked absent. It is the sole new file written by this task.

## 1. Result and evidence

The literal-book append association is now resolved: printed p. 5 expressly
says that `(@)` associates to the right. Therefore the direct inorder on p. 48
is `I l @ ([a] @ I r)`, not `(I l @ [a]) @ I r`. Under the book's printed
recursive-invocation tariff, **retaining both append invocations**, its derived
count is `5*n+1+A`, where `A` sums left-subtree node counts by occurrence.
The augmented-tree definition on p. 56 instead appends to a cons and has derived
count `3*n+1+A`. Equal list values do not identify these executions.

The existing ordinary `Trees.fold` and `Resources.Measured`/`bind` can support
a small actual measured fold. The essential contract retains the actual combine
callback, its returned value and work, and a separately declared tree-entry
charge. It can measure traversal and bottom-up annotation recurrences without
creating another recursive tree carrier or a source-language cost translator.
The companion `tree-fold-resource-api-preflight.md` owns exact proposed APIs;
this note specifies source meaning and limits, not a public API freeze.

### Retained primary material

The July 27, 2026 book PDF is
`book-source/functional_data_structures_algorithms.pdf`, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Printed p. 5 and pp. 48–49, 56–58 were reread in that PDF; the relevant
§1.5 and Appendix B passages were read from the retained extraction. Printed
pages are six less than PDF page numbers. No remote retrieval was performed.

| Source | Precise evidence |
|---|---|
| Book pp. 5–8, §1.4–1.5 | Right-associative append; call-by-value expression/equation translation; recursive entry charge; zero-cost primitives/constructors; removal of the entry overhead for nonrecursive helpers. |
| Book pp. 48–49 | Literal direct inorder, preorder, and Exercise 4.1's append-free suffix accumulator requirement. |
| Book pp. 56–58 | Augmented inorder, cached reader/smart node, and arbitrary ternary structural fold `F`. |
| Book pp. 347–350, Appendix B.1/B.5 | Higher-order map/filter callback counts; selective leftist merge and zero-overhead wrappers. |
| `book-source/Tree.thy` | `inorder`, `inorder2`, `preorder`, ordinary structural observations; no `T_inorder` or `T_inorder2` declaration is present. |
| `book-source/Tree2.thy` | The actual annotation-erasing inorder uses one append to `a # inorder r`. |
| `book-source/Time_Functions.thy` | `T_append`, `T_map_simps`, `T_map`, `T_map_bound`, `T_filter_simps`, `T_filter`, plus zero projections/head/tail. |
| `book-source/Leftist_Heap.thy` | Explicit zero-cost auxiliary timings for `mht` and `node`; actual merge-call bound. |
| `book-source/Array_Braun.thy` | Actual `list` recurrence with `splice`; higher-order timing support caveat and explicit map/filter wrappers for `list_fast_rec`. |

The Isabelle files retain the common mirror revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, which postdates the book. Their
exact hashes and BSD-3-Clause provenance remain in the Chapter 4/11/15 and
Appendix B inventories. For example, the retained `Time_Functions.thy` digest
is `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`.
These are previously recorded identities, not a new hash-helper run.

Local reuse was read in `conaled-tree-shape/Applications/Trees/Observations.lean`,
`Trees/Cached.lean`, `Resources/Measured.lean`, `Resources/CallCount.lean`,
`Resources/ListReversal.lean`, `Resources/TreeCache.lean` and the relevant
`Examples/TreeCache.lean` fixtures. These saved drafts supply actual definitions
and proposed reuse, not new compiler or acceptance evidence.

## 2. Explicit disposition of the earlier association uncertainty

The prior `binary-tree-shared-source-preflight.md` correctly separated three
parenthesized timing recurrences but did not recover the imported append
association. Its historical text remains unchanged. The newly located primary
evidence is the book's p. 5 parenthetical statement about right association.
This is enough to settle the **literal printed Chapter 4 expression**.

`Tree.thy` spells the same expression with the same append operator. The
retained theory file itself does not include the imported `HOL/List.thy` syntax
declaration, an elaborated term dump, generated inorder timing equations, or a
compiled normalization trace. Accordingly:

- It is now justified to translate the literal book expression as two
  right-associated append calls and derive its cost using the printed rules.
- It remains unjustified to assert that the Isabelle or Lean compiler retains
  those calls after rewriting `[a] @ ys` to `a # ys`, or to report the derived
  formula as an already-generated/verified Isabelle `T_inorder` theorem.
- A future explicit Lean measured implementation can retain the literal two
  calls with existing measured append. Its value/recurrence proof will identify
  precisely which source expression it models, independently of compiler
  simplifications of a different implementation.

The left-associated `5*n+1+2*A` formula is a comparison implementation, not the
literal printed algorithm. No source requirement or previous report is silently
rewritten by this clarification.

## 3. The applicable tariff, including higher-order calls

The source model counts invocations of recursive user functions, including
their terminal empty-input invocation. Constructors, projections and primitive
Boolean/numeric operations have zero cost. Call arguments are evaluated before
the function body; `let` evaluates its bound expression once and charges its
body at the resulting value. Only the selected conditional branch contributes.
`Resources.CallCount.arguments_rule`, `let_rule` and the existing `bind` express
these dependencies; `tick` places the entry charge after the body observation.

Dropping a nonrecursive helper's entry `+1` does **not** remove work in its
body. A nonrecursive helper calling recursive append still pays append's
cost. Thus a generic cached `node_f` has the work of its actual combine `f`
under the source's inlining convention, even though its own entry and root
cache projections cost zero. A size smart node whose body contains only
primitive arithmetic has zero cost in that selective model.

Chapter 1's first-order translation sets variable/constructor/primitive costs
to zero, but explicitly sends higher-order examples to Appendix B.1. There:

```text
T_map C []       = 1
T_map C (x::xs)  = C x + T_map C xs + 1
T_map C xs       = sum_over_occurrences(C, xs) + length xs + 1.
```

Filter has the same cost shape, retaining predicate work on both kept and
discarded entries. `Time_Functions.T_map`/`T_filter` corroborate the equations.
The associated bound needs `C x <= K` on the inputs actually encountered (a
global callback bound is sufficient). Duplicated values contribute once per
occurrence. This is the appropriate higher-order precedent for an arbitrary
ternary tree combine; the first-order variable clause is not permission to
declare every supplied callback free.

The worked append translation on p. 7 has the already recorded intermediate
constructor-charge irregularity in `chapter01-obligations.md`. The final
append equations on p. 8, Appendix B.1 and `Time_Functions.T_append` consistently
give `T_append xs ys = length xs + 1`. Use those final equations. This note
does not reopen or silently alter that existing source-error disposition.

There is also a concrete automation limit: `Array_Braun.thy` explains that its
generated higher-order map timing has a different interface from the simplified
manual one. It introduces `map_left`, `map_right`, `map_value` and
`filter_not_Leaf`, each with an explicit `length ts + 1` timing, before generating
the fast traversal timing. This supports proving an explicit measured callback
contract; it does not license claiming that arbitrary higher-order source
translation is already handled automatically.

## 4. Small actual measured-fold contract

Use the existing fold with summaries in the existing measured-pair type.
For the natural call-count specialization, take an empty result `z`, an actual
callback `fRun : beta -> alpha -> beta -> Measured beta Nat`, and a declared
tree-entry charge `e`. Its required execution equations are:

```text
run E = (z,e)
run (N l a r) =
  let (vl,cl) = run l
  let (vr,cr) = run r
  let (v,c)   = fRun vl a vr
  (v, cl + cr + c + e).
```

For a more general additive observation, preserve the `bind` parenthesization
and execution order rather than silently assuming commutativity. The natural
equation above has reassociated sums. A separate recursive executor is not
necessary: XT01's ordinary fold can sequence the two measured child results
and then the actual callback. Bind each result once; do not replace this with
an independently guessed cost annotation on a pure fold.

The unconditional value target is the ordinary fold whose node operation is
`(fRun vl a vr).1`. A supplied pointwise or reached-argument value law can then
identify it with a desired source `F`. The cost recurrence initially refers
to **actual returned child values**. Replacing them by pure source summaries
must consume that value bridge.

There are `n` node calls and `n+1` empty calls. For the actual node callback
costs `c_v`, the resulting natural observation is

```text
W_e(t) = (2*n(t)+1)*e + sum_over_node_occurrences c_v.
```

If every executed callback costs at most `K`, then
`W_e(t) <= (2*n+1)*e + n*K`. If every such cost equals `k`, the corresponding
equality follows. No distinctness of labels/subtrees is used. Taking `e=1`
and `K=0` gives `2*n+1`; taking `e=0` leaves only callback work, rather than
silently declaring that work zero.

The difference between actual `e` and zero-entry executions can be stated as
`W_e = W_0 + e*(2*n+1)`, after establishing equal returned values and therefore
equal reached callback arguments. That premise matters for a callback whose
cost depends on the summaries. These quantitative statements are proof targets
for the proposed unit, not existing checked results asserted by this report.

The observation counts tree **occurrences** traversed by this algorithm. Two
equal or physically shared child values are still visited twice when the
algorithm makes both recursive calls. There is no memoization, DAG-node count,
allocation, parallel-span, lazy-evaluation or target-runtime theorem here.

## 5. Exact traversal recurrences under entry charge one

Let `n(t)` count payload-bearing nodes and define the shape statistic

```text
A E = 0
A (N l a r) = A l + A r + n l.
```

It is an occurrence sum, not a set sum of distinct subtrees. The tree-entry
part alone is `2*n+1`. Each append's first argument determines its additional
call count, including append's empty invocation.

| Actual node computation | Callback work at that node | Total derived work | Source relationship |
|---|---|---|---|
| `appendRun Il (a :: Ir)` | `n l + 1` | `3*n+1+A` | Augmented inorder on p. 56 / `Tree2.inorder`; also XT01's chosen ordinary inorder value recurrence with an explicit measured append. |
| First `appendRun [a] Ir`, then `appendRun Il` on its returned list | `2 + (n l+1)` | `5*n+1+A` | Literal direct inorder on p. 48, now resolved as right-associated. |
| First `appendRun Il [a]`, then append that returned list to `Ir` | `(n l+1) + (n l+2)` | `5*n+1+2*A` | Explicitly different left-associated implementation; same output list. |
| Primitive size, maximum-height or minimum-height combine | `0` | `2*n+1` | Conditional on the source's zero arithmetic/comparison tariff; value connects to the existing structural observation. |

`Resources.ListReversal.appendRun_exact` supplies both the actual append value
and its `length+1` cost. Its nil/cons recurrence retains the terminal call.
`TreeFlattening.appendWithCost` instead counts copied cells and needs the
existing extra-charge bridge; it is not an interchangeable tariff.

All inorder variants return the same ordered list for arbitrary labels and
trees, including duplicates and empty payload types at `E`. That value law
does not remove either append from the literal source execution. On a left
chain `A=n*(n-1)/2`; on a right chain `A=0`. Exercise 4.1's quadratic claim is
therefore a worst-case statement, not a quadratic lower bound for every tree.

### The accumulator is a distinct execution

The requested p. 49 exercise and actual companion `Tree.inorder2` use

```text
I2 E suffix           = suffix
I2 (N l a r) suffix   = I2 l (a :: I2 r suffix).
```

Under the declared tree-entry tariff, its actual invocation count is `2*n+1`,
independently of suffix length. In call-by-value evaluation the right call runs
on the suffix first; its returned list becomes the left call's suffix. The
value contract is `I2 t suffix = I t ++ suffix` for every suffix. Cons is free
in this source model; no append is executed.

A strict fold returning endofunctions or difference lists is not automatically
this execution. Measuring that fold counts creation of function values. Later
applying the returned function requires its own invocation-cost contract.
The existing difference-list work already preserves this creation/application
distinction. A future accumulator proof must instrument the actual suffix
recurrence, or prove a faithful continuation-execution bridge. It cannot obtain
the per-invocation `2*n+1` merely by erasing a function-valued fold's result.

## 6. Full annotation versus cached local construction

`Trees.Cached.annotate` is already an ordinary bottom-up fold using
`smartNode`; its erase, validity and read/fold theorems are separate value
contracts. The book supplies the smart-constructor/invariant pattern on
pp. 57–58, but no printed general timing theorem for a full annotation pass.
Such a pass is a proposed client, not a previously established book cost.

XT01's **positive local-access tariff** is explicit:
`Resources.TreeCache.readRun` costs one, and `nodeRun` actually executes two
reads, the supplied callback, and one constructor-entry charge. Its local cost
is the callback's actual work plus 3. Thus a whole measured fold using that
actual `nodeRun` as its node callback, with outer entry charge one, has

```text
W_annotation = 5*n + 1 + sum_over_nodes C_combine.
```

For zero-cost arithmetic combine this is `5*n+1`, not `2*n+1`. Under the
distinct source convention that both root reads and the nonrecursive smart
constructor entry are inlined, a corresponding actual annotation recurrence
has `2*n+1 + sum C_combine`. Either is a legitimate named abstract model; do
not change XT01's existing tariff or import the smaller constant by value
equality. A pair-returning annotator that passes summaries directly is another
execution whose own accesses must be specified.

The existing list-valued cache callback provides a consequential nonconstant
case. `appendStepRun` performs `appendRun leftSummary (a :: rightSummary)`.
`nodeRun` therefore costs `leftSummary.length+4`. On correctly built inorder
annotations the length bridge makes this `n l+4`; the outer measured fold has
`6*n+1+A`. This count follows from the actual returned caches and append call,
not from assigning a cost to `smartNode` after proving only its value equation.

The pinned leftist source expressly gives `mht` and `node` zero auxiliary
timings, with the actual merge cost counted separately. It cannot inherit
XT01's positive helper tariff unchanged. Conversely, replacing a cached read
with a whole-tree minimum-height fold preserves its value only under validity
and changes its execution. A full annotation pass can establish all-node
validity; a local smart constructor requires valid children and does not repair
arbitrary corrupted descendants.

## 7. Exact clients and remaining algorithm-specific work

| Retained obligations | What the generic measured fold could supply | What remains separate |
|---|---|---|
| C04-003–018: maps, structural observations, inorder and accumulator | Actual callback/value sequencing; entry counts; callback-sensitive direct-inorder costs after its length/value bridge; ordinary map/fold compatibility. | The append-free accumulator recurrence and arbitrary-suffix theorem; literal two-append versus normalized one-append correspondence; traversal-specific growth bounds. |
| C04-062–073: annotation and structural summaries | A measured full recomputation of `F`; a full bottom-up annotation client using the existing actual `nodeRun`; value/validity composition with XT01. | The source's local cache-overhead statement is not a full traversal statement. Any changed tariff or raw maximum-cache/optional reader representation needs its own bridge. |
| C09-062–066 and C09-095–100: height annotation and one-pass conversion | A one-pass structural fold can build returned trees and summaries, with a constant-callback linear count under a declared tariff. | The reference `debal` calls structural height on the original children at every node. `debal2` must avoid those calls and ignore old balance tags in its actual single traversal; AVL preservation and reference equality remain required. |
| C11-023–025 and C11-047–048: Braun array-order list | The source `list E=[]; list(N l a r)=a::splice(list l)(list r)` is a fold with an actual measured splice callback. Its generic cost must retain all splice work. | The splice recurrence/value/length laws, Braun indexing/height bridge and the chapter's `O(n log n)` argument. The later linear forest traversal is a different algorithm. |

For the AVL one-pass client, `annotate z f (t.map fst)` has the desired erased
input but ordinarily traverses that input once for `map` and once for the fold.
The actual single-pass version instead ignores the old tag in its combine.
XT01's `fold_map` supports its **value** bridge; the measured fused recurrence
must supply the one-pass cost. The reference's calls to `h l` and `h r` still
pay their full `2*n(child)+1` work under this source tariff. Equality of final
annotations alone does not make that reference linear.

Chapter 4's list balancer recurses on a requested size and a consumed suffix,
not on an already supplied tree. Matching a `2*n+1` result there still requires
its successful-domain, suffix-consumption and execution recurrence proof.
Likewise, selective search/merge paths, the maximal-complete-subtree exercise's
algorithm restrictions, and level/forest algorithms are not discharged merely
because some final result can be expressed as a fold. No such algorithm is
included or implemented by this proposal.

## 8. Independent small expectations and recommendation

For XT01's actual asymmetric four-node sample, `n=4`, `A=2`, and inorder is
`[0,1,2,3]`. Without enumerating trees, the displayed recurrences give:

| Execution/model on that sample | Expected work |
|---|---:|
| Primitive-combine whole fold, entry one | 9 |
| Single-append inorder | 15 |
| Literal right-associated two-append inorder | 23 |
| Explicit left-associated two-append inorder | 25 |
| Actual suffix accumulator, any suffix | 9 |
| Full annotation via actual XT01 `nodeRun`, zero-cost arithmetic combine | 21 |
| Full inorder-list annotation via actual XT01 `nodeRun`/`appendStepRun` | 27 |

Nil costs the chosen entry charge and calls no combine. For the same actual
callback, changing only the tree-entry charge from zero to one adds nine on
this sample, without changing callback arguments or values. A constant callback
work `k` contributes exactly `4*k`; an arbitrary callback requires its own
reached-input bound. These are hand-derived expectations for future connected
Lean examples, not a new frozen example set or executed tests.

The minimal worthwhile unit is an ordinary measured-fold construction, its
actual nil/node and value laws, and natural entry/callback decomposition with
constant/bounded callback consequences. Existing measured append and XT01's
actual cached smart node are strong connected clients. The two-append source
variant should remain explicitly identified if used; full accumulator,
annotation-conversion, Braun, search and merge obligations stay in their owning
chapters or separately frozen shared work. No runtime, physical sharing,
retained-storage or source-compiler guarantee follows from these counts.

All prior reports and inventories remain unchanged. No compiler, checker,
project hash helper, Git/ref/cache/gate, remote action, tree enumeration or
child delegation was performed. Only this source-preparation report was written.
