# Tree suffix invocation and measured construction: FDSA shared unit XT04

## Status and source

This is the recovered **CTB-70 source unit**, based on preserved XT04 donor
`b035f1151ab4f0c7d7380818576cfe97dae434c4`. It develops against pinned `conaled`
master `c214fb0720ffc998951255a7e4b5f2e80a299186`, after the measured-fold recovery
in CTB-2 at `086b3bf1c21f6dc73419b784a2d94ac4e29bcacd`. It connects an actual
append-free suffix invocation to its arbitrary-suffix value and resource laws,
then composes a separately measured construction with actual applications.
The existing tree, measured-operation and measured-fold owners supply its
foundations; XT02 and XD01 are not dependencies.

All three new Lean modules pass the focused build and declaration audit with
the pinned compiler and dependencies. Exact candidate checks, statement review
and independent source-review outcomes belong to the checkpoint review record.
By the user's explicit workflow decision, the receiving integrator owns the
whole-library guarded build, exhaustive audit and final candidate verification;
those acceptance gates remain pending. This unit supplies C04-017 and the
accumulator portion of C04-018. CTB-71 still owns C04-018's direct-inorder
quadratic shape-family obligation, so this unit does not complete Exercise 4.1,
Chapter 4 or any whole book.

The source is the July 27, 2026
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Exercise 4.1 on printed p. 49 asks for cons-only accumulation, its all-suffix
value theorem and linear time. Section 1.5 supplies the declared recursive-entry
tariff; Appendix B.1 retains supplied higher-order callback work.

The retained Isabelle mirror revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21` supplies `Tree.inorder2` and
`inorder2_inorder` in `src/HOL/Library/Tree.thy`. The recorded file digest is
`1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`.
BSD-3-Clause provenance remains in the reconstruction records. This revision
postdates the manuscript and is not asserted to be its build revision. The
retained theory has the recurrence and arbitrary-suffix value proof, but no
generated `T_inorder2` declaration. The exact resource statement here is derived
for the declared measured execution, not attributed to a missing generated proof.

Frozen requirements, complete source/API/mathematical preparation reports,
clean starting identity and all local findings are retained in the durability
checkpoints. Those records preserve original scope and distinguish bounded
source readings from required validation and final review.

## Actual dependent invocation

The source equations are

```text
I2 nil suffix          = suffix
I2 (node a l r) suffix = I2 l (a :: I2 r suffix).
```

The right call runs on the supplied suffix first. Its actual returned list,
with the root label prepended, becomes the left call's suffix. The resulting
list has left/root/right output order even though the dependent calls run
right before left.

`Resources.TreeAccumulator.nodeRun` expresses that body with the existing
measured bind. It posts an explicit entry observation after the body, retaining
the exact grouped observation `(rightWork + leftWork) + entry` under mere
`Add`. The left work is measured at the actual returned right list. No zero,
associativity, commutativity, ordering, label equality or payload inhabitant
is required. Payload and observation universes remain independent.

`invoke` is the existing ordinary `Trees.fold` at the ordinary function type
`List alpha -> Measured (List alpha) C`. Its nil function returns `(suffix,entry)`;
its node function is `nodeRun entry`. There is no second recursive executor or
cost-only traversal. The public constructor application equations retain both
empty-child invocations. At natural entry one, the body is exactly the existing
post-body `Resources.CallCount.tick` of the right-to-left bind.

This observation belongs to later function invocation. Strict construction of
the function is separately observed below. The source's curried type does not
by itself specify a charged partial-application or closure-allocation algorithm.
The constructor equations match the declared suffix-call recurrence; no
cost-preserving compiler transformation or Lean runtime measurement is claimed.
Cons and inlined scaffolding are free in this declared invocation tariff.

## Why every suffix is required

The value theorem is

```text
(invoke entry t suffix).value = Trees.inorder t ++ suffix.
```

Its induction generalizes the suffix. The right induction hypothesis identifies
the actual returned list, and the left hypothesis applies to that list after
consing the root. A theorem only at `[]` cannot justify this recursive step.
Append occurs in the independent specification and its associativity proof;
the invocation executes no append.

For natural entry `e`, the exact pair theorem is

```text
invoke e t suffix = (Trees.inorder t ++ suffix, e*(2*n+1)),
where n = t.numNodes.
```

The cost proof also generalizes every suffix, so it applies the left cost law
at the actual dependent argument. It does not assume a uniform cost for an
unknown callback or attach a guessed count to an independently computed list.
The result has length `n+length(suffix)`, while invocation work is independent
of suffix length. Preparing the tree or supplied suffix is outside this boundary.

Nil costs `e`. At `e=0` the declared observation is zero; this is not a claim
that physical traversal is free. For positive node count, the explicit bound
is `cost <= 3*e*n`. The positive-size premise is needed: no bound `cost <= K*n`
can hold at nil with entry one. The exact affine count retains that boundary
and gives the intended linear resource behavior without a new asymptotic carrier.

`reweight_nodeRun` preserves the actual dependent argument through existing
`reweight_bind` and additive-hom preservation of the final entry charge.
Ordinary fold fusion lifts it to `reweight_invoke`. Monoid assumptions belong
only to the existing hom interface; neither law requires commutativity.

## Separate construction and repeated application

`TreeAccumulatorExamples.build` uses the actual `Resources.TreeFold.run` with natural
construction entry `b`. Its empty summary is the nil invocation function, and
its zero-cost callback captures the child functions in `nodeRun e` without
applying them. Existing `run_value_of` identifies the actual returned function
with `invoke e t`, while `run_cost_const` supplies construction work `b*(2*n+1)`.

The returned-function equality is equality into **measured results**. It
therefore preserves the inner invocation observation as well as its returned
list. Erasing the outer construction observation does not erase the inner
function's cost. The invocation count itself comes from the independent
all-suffix invocation proof above.

This construction tariff observes tree-traversal entries. It is not a physical
allocation count or a count of distinct closures; a supplied nil function can
be reused at several empty occurrences. No child application or earlier child
construction is silently charged by the zero-cost capture callback.

`buildOnce` binds the actual construction result to one suffix application.
`buildTwice` binds one construction to two actual applications of that same
returned function, retaining both lists. With `m=2*n+1`:

| Actual program | Returned value | Observation |
| --- | --- | --- |
| Construct the invocation function | `invoke e t` | `b*m` |
| Construct once, invoke once | `I(t) ++ s` | `(b+e)*m` |
| Construct once, invoke twice | `(I(t) ++ s, I(t) ++ u)` | `(b+2*e)*m` |

Construction and invocation entries remain separate parameters. On the
four-node sample, `b=e=1` gives construction work 9, one combined application
18, and two combined applications 27. The unequal-tariff case `b=2,e=3` gives
combined totals 45 and 72, exposing the distinction between the parameters.
These staged totals are not the source single-invocation count 9. Retaining one
already materialized list instead of calling the function twice is another program.

The separate XD01 draft remains unchanged. Its charged singleton and composition
operations have a different tariff: two charged compositions plus a charged
singleton at each tree node would give `4*n+1`, not this accumulator's `2*n+1`.
That distinction is recorded in the preparation reports; no unaccepted XD01
implementation is imported or duplicated here. A DList value adapter, if later
needed, must reuse its existing interface and does not transport costs by itself.

## Connected cases and comparison executions

The saved XT01 sample has root 1, left singleton 0 and right root 3 with left
singleton 2. At suffix `[9,8]`, its right invocation returns `[2,3,9,8]`; the
left invocation receives `[1,2,3,9,8]`. The final result is `[0,1,2,3,9,8]`,
with entry-one work nine. The retained cases consume the public constructor,
pair/value/cost and observation laws rather than reducing unrelated numerals.

| Case | Retained distinction |
| --- | --- |
| Nil at `[9,8]` | Returns the suffix with one charge; does not copy it under this model. |
| Arbitrary singleton and suffix | Returns `a :: suffix`, with three invocation occurrences. |
| Sample at `[]` and `[9,8]` | Same work nine, different suffix-preserving outputs. |
| Noninjective relabelling to 7, suffix `[7,7]` | Six output occurrences, work nine; no label-based collapse. |
| `BinaryTree Empty` and `List Empty` | Both are empty without a default label; generic nil separately covers nonempty suffixes. |
| `node a u u` | Both equal child occurrences are invoked; work `e*(4*n(u)+3)`. |
| Entry zero and positive-size bound | Declared tariff boundary and nil exception stay explicit. |
| Construction with two applications | Both actual returned lists and both invocation charges are retained. |

`materializeAppend` is an actual comparison program: it first runs XT03's
single-append inorder, then appends its actual returned prefix to the supplied
suffix. The existing value and length laws justify the appended prefix length.
Its cost is that actual inorder cost plus `n+1`. On the sample it returns the
same list but costs 20, compared with suffix invocation's nine. Thus the
specification `I(t) ++ suffix` does not prescribe that more expensive program.
This finite comparison does not prove the direct-inorder quadratic family.

A second witness shows why testing only materialization at `[]` is insufficient.
Nil invocation at entry one and `fun s => appendRun s []` agree as measured
results at `[]`, and their erased values agree for every suffix. At `[9]`,
their costs are one and two. The latter observation follows from the actual
append contract; representation equality does not supply a uniform work law.

## Product and ordered observations

The product example invokes once with entry `(1,2)`. Existing first and second
projection homs, `reweight_invoke`, and the natural invocation theorem yield
sample observation `(9,18)`. These components are two tariffs on the **same
invocation**, not construction and invocation phases.

The ordered diagnostic is an ordinary fold returning measured functions. It
uses the same public `nodeRun` algebra with a post-body label token in
`Additive (FreeMonoid Nat)`; nil has zero observation. Its value theorem still
returns ordinary inorder followed by every supplied suffix. On the saved
sample its node-event word is `[2,3,0,1]`, reflecting right-before-left execution.
This differs from XT03's retained left-first word `[0,2,3,1]`.

The comparison concerns words. XT03's earlier trace callback returns a size
summary, whereas this diagnostic returns a suffix list. Each keeps its own
value law. Node tokens are post-body observations, not pre-body entry
timestamps, and nil events are omitted from this diagnostic. A single
identical token at every one of the nine calls would not distinguish schedules.

## Statement review and remaining scope

| Concern | Intended statement and retained connection |
| --- | --- |
| Actual dependency | Right result is passed to the left after free cons, with exact observation grouping. |
| Quantification | Value and cost cover every suffix, including the actual recursive suffix; no payload instances. |
| Work boundary | Nil and zero-entry cases retained; proportional bound requires positive size. |
| Observation transport | Existing additive homs, bind compatibility and fold fusion; no commutative assumption. |
| Construction versus invocation | Two tariffs, actual returned measured function, one build and one/two real applications. |
| Value versus cost | Actual materialize/append comparison and empty-suffix-only agreement witness. |
| Repeated occurrences | Equal children and repeated payloads retain all calls and output occurrences. |
| Order | Actual traced function algebra and the right-first word, with an explicit post-body convention. |

The reusable operation is under `Applications/Resources`. Construction,
comparison and observation compositions are under `Examples`, as required by
ADRs 0001 and 0010. The public root imports
`Examples.TreeAccumulatorObservations`; its closure includes every new module.

This unit addresses C04-017 and the accumulator portion of C04-018, reusing existing
inorder observations C04-004/015. It does not discharge their chapter, the
direct-inorder quadratic worst-case obligation, all Chapter 4 exercises,
preorder, AVL/Braun/list-balancing algorithms, or Appendix B as a whole. Generic
higher-order translation, closure conversion, memoization and physical runtime,
sharing, stack or storage claims are outside this unit. The left recursive call
being in tail position does not establish constant stack usage: the right call
is still recursive. All original book obligations remain in their owning
chapters; excluded mechanisms do not become new framework requirements.

All 57 original named source declarations are retained. Compilation repairs
qualify the existing measured operations, rename a reserved local binder, make
the construction wrapper and suffix type explicit in its cost proof, and finish
closed list/arithmetic goals after applying the public results. Their intended
mathematical statements and independently calculated expectations are unchanged.

Source readings and statement assessment alone do not certify kernel checking
or acceptance. The checkpoint retains the exact scope of focused validation,
the immutable candidate, both independent source-review outcomes and correction
history. Final receiving verification and complete chapter acceptance remain
separate from this bounded unit.
