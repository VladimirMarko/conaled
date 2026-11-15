# Frozen requirements: actual tree suffix invocation and measured construction

Local ticket: **FDSA-XT04**. Version 1, frozen 2026-11-02 before any
implementation edits in its isolated worktree.

## Authority and baseline

The user's complete FDSA-book task, chapter order, local-only tickets and
authorized immediate durability uploads remain in force. This is a bounded
cross-cutting follow-up for actual suffix invocation and construction/application
composition, using existing folds and measured values. It neither activates a
later chapter nor replaces any original algorithm or source obligation.

Fixed initial base/head: `b0fce71fa00b2ff6250b09002176bdc75baf1f46`, the saved
but unvalidated XT03 draft. Branch: `work/fdsa-tree-accumulator`.
Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-accumulator`.
The clean pre-code state is retained in
`tree-accumulator-invocation-start.json`. Only `.lake/packages` is linked to
pinned external dependency checkouts; project outputs are isolated. No new
compiler, checker or project hash helper may run while old Chapter 1 gate 80227
is active. That gate remains unchanged.

Accepted repaired Chapter 1, accepted XT01 and accepted XT03 are prerequisites
to integrating or accepting this full unit. The invocation core itself needs
only XT01's ordinary fold and existing measured sequencing. The included
construction composition needs XT03. XT02 and the separate XD01 difference-list
draft are not dependencies. Preserve this original base, candidate history,
all frozen scope and findings when incorporating a later accepted integration
tip. Applicable full build/guards/audit, both independent final review axes
and immediate candidate verification remain mandatory.

## Source and complete preimplementation evidence

Source: July 27, 2026 book, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`,
printed pp. 48–49 (Exercise 4.1), §1.5 and Appendix B.1. The retained Isabelle
mirror is `f86f290225eebcc52c1ae7dba2e098f405f51c21`, with recorded BSD-3-Clause
provenance. Its `Tree.inorder2` and `inorder2_inorder` supply the exact cons-only
recurrence and arbitrary-suffix value theorem. The mirror postdates the book
and is not asserted to be its build revision. No generated `T_inorder2` or
compiler normalization/closure-conversion evidence is present or claimed.

Root read all three reports completely before this freeze:

| Report | SHA-256 |
| --- | --- |
| `research/tree-accumulator-invocation-api-preflight.md` | `c54f44e54b05c7b722625b874bbc440fb59d049addcdfd07632bcfe4769e2dbe` |
| `research/tree-accumulator-invocation-source-preflight.md` | `034ae89ce242230d5401f2a638eba1e613ee87ea67b0e7bbfbe068f7f738bbd3` |
| `research/tree-accumulator-invocation-case-preflight.md` | `3f503103119de1cd8df90492edfe26fe50150f5ac7c236c1e75fd5f598666d4f` |

Root also directly checked the retained `Tree.thy` recurrence and all-suffix
theorem. The existing AGENTS, architecture/domain guidance, relevant ADRs,
implement/example-driven workflow and retained review-loop rules apply.
Preflights do not start a new final-review loop or supply acceptance evidence.

## XT04-01 — Actual invocation algebra and one ordinary fold

Use the existing function type `List alpha -> Measured (List alpha) C`.
Do not add a builder datatype, callback class, reachability framework, second
recursive tree executor or separately recursive cost evaluator. A small node
algebra may be named because construction and ordered-observation clients
consume it directly.

The raw node algebra and invocation construction require only `[Add C]`, with
independent payload and observation universes. They need no zero, associativity,
commutativity, order, label equality or payload inhabitant. For explicit entry
observation `e`, arbitrary measured child functions `left` and `right`, label
`a` and suffix `s`, the node algebra executes

```text
body = bind (right s) (fun rest => left (a :: rest))
nodeRun e left a right s = (body.value, body.observation + e).
```

Its full exact equation must retain the actual dependency:

```text
R = right s
L = left (a :: R.value)
result = (L.value, (R.observation + L.observation) + e).
```

Define the invocation function by the existing ordinary `Trees.fold`, with nil
function `fun s => (s,e)` and this node algebra. Its only tree recursion is that
existing fold. Expose nil/node application equations and the exact Nat-entry-one
connection to `CallCount.tick (bind ... ...)`. Both empty-child invocations
remain present. Cons and inlined scaffolding add no separate charge. No append
is executed; append appears only in the independent value specification.

The operation observes later invocation of the returned function. It is not a
claim that strict function construction is free, a full cost-preserving source
compiler theorem or a measurement of Lean's runtime. The fully applied
constructor equations identify the source's declared suffix-call recurrence;
the separate construction program below retains its own work.

## XT04-02 — All-suffix correctness, natural work and transport

Prove the unconditional value law under the raw observation assumptions:

```text
(invoke e t s).value = Trees.inorder t ++ s.
```

The suffix is universally quantified. In tree induction it must be generalized;
the left claim applies to `a :: actualRightValue`. A theorem only at `[]` is
insufficient. Ordinary list associativity belongs to the specification proof
and must not silently introduce append into the execution.

For natural observations, retain the strong exact pair statement

```text
invoke e t s = (Trees.inorder t ++ s, e*(2*t.numNodes+1)).
```

Value/cost projections may be supplied where actual clients need them. Derive
the result-length law `n + length(s)` using the existing inorder-length theorem;
this is different from the suffix-independent invocation work. Preserve `e=0`,
nil and arbitrary-suffix boundaries. Show an explicit linear upper bound for
positive node count, such as `cost <= 3*e*n` when `0<n`, without asserting a
pointwise `K*n` bound at nil. No new size carrier or asymptotic framework is
needed to express these exact and linear bounds.

Through existing `reweight`/`reweight_bind` and ordinary fold reasoning, prove
the additive-hom transport

```text
reweight h (invoke e t s) = invoke (h e) t s
```

for existing `h : C ->+ D`. The `AddMonoid` assumptions belong only to that
interface; no commutativity is required. A product-observation specialization
must use the existing projection homs to recover the two tariffs on the same
invocation. For sample entry `(1,2)`, its observation is `(9,18)`. These are two
observations of one invocation, not construction and invocation phases.

## XT04-03 — Actual measured construction, then actual applications

Include a separate named construction program using XT03's actual
`Resources.TreeFold.run`, with natural construction entry `b`, the nil invocation
function as its empty summary, and zero-cost closure-capture callback
`fun left a right => pure (nodeRun e left a right)`. Its returned function must
be proved equal to the actual invocation function through the existing
`run_value_of` law; its construction cost must consume `run_cost_const` with
zero callback work. Capture does not apply either child function or recharge
an earlier supplied callback's construction.

For `m = 2*t.numNodes+1`, the actual construction observation is `b*m`.
This is a declared traversal-entry observation, not allocation, physical
closure count, memory retention or compiler behavior. In particular a nil
function value can be reused at multiple empty occurrences.

Define actual bind-composed programs which construct once and then invoke the
returned function once, and construct once and invoke that same returned
function twice on independently supplied suffixes. Retain both returned lists
in the twice-invoked program. Prove their complete values and costs:

```text
once:  (I(t) ++ s, (b+e)*m)
twice: ((I(t) ++ s, I(t) ++ u), (b+2*e)*m).
```

These must consume the actual construction result and invocation contracts,
not add a guessed cost to independent pure lists or rebuild the function twice.
The two-entry parameters remain separate. At `b=e=1`, a sample construction
costs 9, construction plus one application 18, and construction plus two 27.
Retain a parameter-distinguishing sample `b=2,e=3`, giving totals 45 and 72.
Neither staged total is identified with the source single-invocation count 9.
Reusing one already materialized result is a different program.

The unit-capture model and XD01 DList adapter are not selected for this unit.
Do not import XD01 merely to duplicate its `Rep`, `AppCost`, `Builder` or
`toDList` interfaces. Its charged singleton/composition tariff remains intact.

## XT04-04 — Connected boundaries and actual comparison execution

Use the public invocation laws and retained XT01 observations for:

- Nil with an arbitrary suffix, singleton with arbitrary label/suffix, and the
  saved four-node sample at both empty suffix and `[9,8]`. Work is respectively
  `e`, `3*e` and `9*e`; the nonempty sample returns `[0,1,2,3,9,8]`.
- The actual sample dependency: the right child returns `[2,3,9,8]`, and the
  left child receives `[1,2,3,9,8]`. This checks the right-before-left call
  relationship rather than only the final numeral.
- Repeated labels and suffix values through a noninjective label map, retaining
  every occurrence. Map computation is outside the given-input comparison.
- `BinaryTree Empty` and `List Empty` without a manufactured payload; the
  tree and suffix are empty, while generic nil still covers nonempty suffixes
  over inhabited types.
- Repeated child-tree occurrences `node a u u`, with work `e*(4*n(u)+3)` and
  both inorder occurrences in the result. Equal/shared descriptions do not
  memoize either actual call.
- A zero-entry value/cost boundary, without claiming physical traversal is free.

Include the actual comparison program which first runs XT03's single-append
inorder and then invokes existing `ListReversal.appendRun` on its actual
returned prefix and the supplied suffix. Its value is the same inorder suffix;
its cost is that actual inorder cost plus `t.numNodes+1`, using the existing
value/length bridge before applying the append contract. The sample costs 20,
versus the accumulator's 9. No all-tree quadratic/asymptotic claim is implied.

Retain the empty-suffix-only failure witness without importing XD01: the actual
nil invocation at entry one and `fun s => appendRun s []` agree as measured
results on `[]`, but on `[9]` their costs are one and two. Their erased values
agree on every suffix. This demonstrates why the uniform application theorem
must cover all suffixes rather than only materialization at `[]`.

## XT04-05 — Ordered invocation diagnostic

Retain a concrete ordinary function-valued fold using the same public node
algebra, with nil observation zero and node post-body observation the label's
token in `Additive (FreeMonoid Nat)`. This is a separately declared ordered
observation of the same right-before-left dependency. It needs no new trace
framework or recursive trace-only evaluator.

Connect the actual traced invocation's value to ordinary inorder for every
suffix using the public node algebra and ordinary fold reasoning. On the saved
sample its node-event word is `[2,3,0,1]`, independent of the suffix. Compare it
with the already retained XT03 word `[0,2,3,1]` to expose order inequality.
The existing XT03 trace callback returns a size summary; do not assert that
that callback itself returns an inorder list. This comparison concerns the
words, with each execution's own value law retained.

The tokens are post-body observations, not pre-body call-entry timestamps.
Nil events are omitted from this node-word diagnostic. Repeating one identical
token at all nine invocations would not distinguish the schedules. Numerical
linear counts alone likewise do not prove the intended traversal order.

## Placement, review and limits

Place the reusable invocation operation and its laws under
`Applications/Resources`; put construction/comparison/ordered compositions and
connected cases under `Examples`, with every new Lean module in the public
root's import closure. Add a reconstruction note and source-map entry retaining
source identities, actual execution/value links, tariffs, chapter mapping and
statement review. Preserve ordinary compiler/kernel discipline: no extra axiom,
`sorry`, `admit`, unsafe/partial definition, `native_decide` or skipped checking.

Statement review must inspect all-suffix quantification, actual intermediate
arguments, observation grouping, independent universes/minimal assumptions,
source invocation versus strict construction, two distinct entry parameters,
actual repeated applications, value equality versus cost equality, empty
payloads, repeated occurrences and post-body trace order.

This unit excludes the direct-inorder quadratic worst-case family, full
Chapter 4 coverage, preorder, AVL/Braun/list-balancing algorithms, generic
higher-order translation, closure conversion, a new reachability/history
framework, memoization, physical sharing/stack/storage or runtime claims.
All original book obligations remain mandatory in their owning chapters or
separately frozen work; the exclusions impose no additional general framework.
No constant-stack or compiler tail-call claim follows from this call count.

Preserve the clean pre-code scope and these reports in checkpoint 0033 and
upload it before implementation. Later committed source must be preserved
with exact identities, findings and validation limits. No chapter or shared
unit gains acceptance credit from this freeze or source preparation.
