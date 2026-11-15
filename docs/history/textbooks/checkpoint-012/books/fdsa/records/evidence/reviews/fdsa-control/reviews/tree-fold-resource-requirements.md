# Frozen requirements: measured whole-tree folds

Local ticket: **FDSA-XT03**. Version: 1, frozen 2026-11-02 before any
implementation edits in the isolated worktree.

## Authority, dependencies and baseline

The complete FDSA book remains the task, in chapter order, with the user's
explicit exception for cross-cutting concerns. This unit supplies common
measured-fold reasoning for structural traversals, cached annotation and later
tree conversions. It changes no chapter acceptance order or original source
obligation. Tickets, commits and all publication remain local except for the
authorized durability checkpoint uploads.

Fixed initial base/head: `64c6b777d828ecfe83234fc2aed94600a1f24297`, the saved
but unvalidated XT01 fold/cache draft. Branch: `work/fdsa-tree-fold`.
Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-fold`.
The clean pre-edit state is recorded in `tree-fold-resource-start.json`.
The unit uses XT01's ordinary fold, cache operations and resource interfaces.
XT02's separate shape/logarithm branch is not an implementation dependency.
Only `.lake/packages` is linked to the pinned dependency checkouts; project
outputs are worktree-local. The active old Chapter 1 gate remains unchanged.
No second compiler, checker or project hash helper may run while it is active.

Accepted repaired FDSA-001 and accepted FDSA-XT01 are prerequisites to integrating
or accepting XT03. Preserve this original base, all candidate history, scope
and findings when later incorporating an accepted integration tip. Matching
candidate build/guards, exhaustive audit, both independent final review axes
and immediate candidate verification remain required. The initial Sorting
integration sequence in the retained plan does not require this tree unit.

## Sources and preimplementation evidence

The book is the July 27, 2026 edition, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Relevant source is §1.4–1.5, Chapter 4 pp. 48–49 and 56–58, and Appendix B.1/B.5.
Later common clients include Chapter 9's one-pass annotation conversion and
Chapter 11's fold with a splice callback; their actual algorithm obligations
remain separate. The retained Isabelle mirror is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, with recorded BSD-3-Clause provenance.
It postdates the manuscript and is not asserted to be its build revision.

All three bounded reports were read completely before implementation:

| Report | SHA-256 |
| --- | --- |
| `research/tree-fold-resource-api-preflight.md` | `86792205c6116383d7214e96866428c6bbfa984b4aea06c7ddc5143d6c7ef7d2` |
| `research/tree-fold-resource-source-preflight.md` | `862b45b860fdc3b4e1ccd5168761bb6384008c5f93e3cef92ca44d82d0ca6c8d` |
| `research/tree-fold-resource-case-preflight.md` | `42843c8a4d9dcaeee95ef8e0c6a0ac0a11c6f7b44b0e737a82e5bd3c14926497` |

The literal source parsing is now settled: printed p. 5 explicitly states
that append associates right. Thus the p. 48 inorder has two right-associated
append invocations when translated literally under the printed call tariff.
The p. 56 augmented inorder instead appends to a cons. Root also independently
read the relevant PDF page. Earlier reports remain unchanged historical
records; no generated `T_inorder` or compiler-normalization result is claimed.

Reuse the existing Mathlib BinaryTree at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, XT01 `Trees.fold`/fusion/map laws,
`Resources.Measured`/`bind`/`pure`/`reweight`, `CallCount`, measured append, and
the actual measured cached smart constructor. All applicable AGENTS,
architecture/domain, implement, example-driven and review-loop rules remain
in force. Root owns source implementation; no new review loop starts merely
because these preparation reports exist.

## Exact included scope

### XT03-01 — One ordinary measured-fold specialization

Supply an operation on the existing node-labelled tree with explicit entry
observation, empty value and actual measured ternary combine callback. Payload,
summary and observation types must have independent universes. The generic
operation requires only `[Add C]`, not zero, associativity, commutativity, an
order, a default payload or equality decision.

Instantiate the existing ordinary `Trees.fold` at `Measured beta C` instead
of adding a second recursive executor. Its exact equations are:

```text
run entry empty combineRun nil = (empty, entry)

L = run entry empty combineRun l
R = run entry empty combineRun r
F = combineRun L.value a R.value
run entry empty combineRun (node a l r) =
  (F.value, (L.observation + (R.observation + F.observation)) + entry).
```

Use the existing binds to sequence left result, right result and actual callback.
Preserve the displayed parentheses under mere `Add`. The structural charge is
posted after the body, as in `CallCount.tick`; for Nat entry one give the exact
connection to that existing tick operation. Both child computations contribute
even when the callback ignores their returned summaries. There is no pruning,
memoization or separate cost-only evaluator.

Expose constructor equations and label-map transport by reusing `fold_map`.
This transport compares runs on given tree values and says nothing by itself
about the work of separately computing a mapped input.

### XT03-02 — Actual value erasure and observation transport

Prove the unconditional value statement through `Trees.fold_fusion` and
`Prod.fst`:

```text
(run entry empty combineRun t).value =
  Trees.fold empty (fun l a r => (combineRun l a r).value) t.
```

It follows that changing only the entry observation preserves values and
reached callback arguments for the same fixed callback and empty value.
It does not relate separately changed callback closures. A refinement to an
independent pure algebra must use an actual callback value law; a global
pointwise law is sufficient and must not be described as necessary. A new
callback class, validity record or reachability/subtree framework is unnecessary.

For `[AddMonoid C] [AddMonoid D]` and an existing additive hom `h : C ->+ D`,
prove the small observation-transport law

```text
reweight h (run entry empty combineRun t) =
  run (h entry) empty (fun l a r => reweight h (combineRun l a r)) t.
```

Use ordinary fold fusion and existing measured reweight/bind compatibility.
No commutativity is required for this law. The additional monoid assumptions
belong to the reused hom interface and must not leak into the raw operation
or unconditional value law.

### XT03-03 — Natural structural/callback cost separation

Specialize quantitative statements to natural observations. For the same actual
callback and empty value, prove

```text
cost(run e empty combineRun t) =
  cost(run 0 empty combineRun t) + e*(2*t.numNodes+1).
```

The zero-entry term must be an actual run of the same operation, not a residual
defined by subtracting the desired structural term. The implementation performs
one run, not both comparison runs. Value erasure justifies the identical reached
callback arguments before any cost terms are compared. Reuse the canonical
node/leaf identity where useful; no new tree-count carrier is needed.

Prove the resulting structural lower bound and the following constant/uniform
callback laws, with `n = t.numNodes`:

```text
constant reached callback cost k -> cost = e*(2*n+1) + k*n
reached callback cost at most K  -> cost <= e*(2*n+1) + K*n.
```

The main callback premise is to range over the summaries returned by this
fixed run on arbitrary finite child trees, at the given entry and empty value.
For example it can quantify over `l : BinaryTree alpha`, `a : alpha` and
`r : BinaryTree alpha` and inspect `combineRun (run ... l).value a
(run ... r).value`. This is weaker than requiring the law on arbitrary beta
values, but it is not literally restricted to one supplied input's subtrees.
State that domain honestly. A global beta-argument law can discharge it.
Do not introduce a second suite of wrappers solely to restate every premise.

One fixed `K` must serve the claimed family. A size-dependent choice is not
automatically a uniform linear complexity result. Nil costs e and calls no
combine; at e=0 only actual callback work remains. At K=0, nonnegative reached
callback costs vanish, giving the structural term exactly. No positive lower
bound follows solely from a positive upper bound on callback work.

The collected-entry identity is not to be generalized to arbitrary ordered
observations. A noncommutative counterexample is part of the connected cases.

### XT03-04 — Actual primitive and append clients

Use actual zero-cost arithmetic callbacks to specialize the fold to canonical
node count and maximum height. Obtain their values through existing ordinary
fold specialization, and their natural work `e*(2*n+1)` through the generic
constant-callback result. Preserve arbitrary payloads and an explicit
`BinaryTree Empty` boundary.

Define actual measured callbacks from the existing `ListReversal.appendRun`:

```text
single: appendRun l (a :: r)
right:  bind (appendRun [a] r) (fun suffix => appendRun l suffix)
left:   bind (appendRun l [a]) (fun prefix => appendRun prefix r).
```

Prove their value and callback-work laws using the actual append contract.
Their respective work at a node is `length(l)+1`, `length(l)+3`, and
`2*length(l)+3`. For the left case the second append must use the actual first
result, whose length is `length(l)+1`. Callback scaffolding and constructors
are inlined under this declared tariff.

For each resulting measured fold, prove its returned value is the existing
ordinary inorder and derive its actual node-cost recurrence. Replacing the
left result's length by the left subtree's node count must consume the value
bridge and `inorder_length`. The right-associated variant models the literal
printed source with both append calls retained; the left-associated variant
is a comparison execution. Do not identify their work by list associativity.

Retain meaningful nil/singleton boundaries and XT01's asymmetric four-node
sample. At entry one the sample has inorder `[0,1,2,3]` and respective work
15, 23 and 25. Nil costs one; a singleton costs 4, 6 and 6. Prove these cases
through the generic/client recurrence and actual callback laws. The shared
unit need not introduce the all-tree left-mass statistic or prove the later
quadratic/linear shape families; those book obligations remain open.

### XT03-05 — Actual full cached annotation

Use the existing `Resources.TreeCache.nodeRun` as the actual node callback of
the measured fold, with empty returned tree nil. Under a sufficient callback
value law, identify the returned tree with existing `Cached.annotate`; then
reuse its erase, recursive validity and reader/fold laws. Do not replace the
measured callback with a guessed charge on an independently computed tree.

For the saved size/height arithmetic combines, the actual measured smart node
costs three: two reads and one local constructor entry. Prove whole-pass work
`e*(2*n+1)+3*n`, hence `5*n+1` at e=1. The sample therefore costs 21, and its
actual returned annotation agrees with the saved corresponding sample.

Also retain a list-valued annotation client using actual `appendStepRun` inside
the measured smart constructor. Connect actual child reads to ordinary inorder
through the annotation validity/value laws before using the list-length cost.
At entry one the four-node sample costs 27 and reads `[0,1,2,3]`. Do not claim
that this arbitrary-combine annotation pass is always linear merely because
every node is visited once.

A zero-helper arithmetic comparison may use the explicit pure size smart-node
callback: its primitive arithmetic/root reads have zero declared observation.
Its value is the same actual size annotation and its work is `e*(2*n+1)`.
If included, keep it named and distinct from XT01's positive local tariff.
No unknown inner callback work may be erased by calling its helper nonrecursive.
The existing leftist selective tariff and its queue algorithm remain unchanged.

### XT03-06 — Ordered and product observations, reachable-value boundary

Retain an actual ordered-word callback using an existing additive free monoid.
At zero structural entry it returns size four on the saved sample and records
the postorder callback word `[0,2,3,1]`. The value proof consumes the generic
erasure/size connection; the observation retains left/right/callback order.
For a singleton, entry word E and callback word K produce `E E K E`, whereas
zero-entry callback work followed by three entries produces `K E E E`.
Prove their inequality. This explains the Nat-specific collected-charge law.

Use a product observation `Nat × Nat`, entry `(1,0)`, and the actual callback
lifted with existing `AddMonoidHom.inr`. Through the reweight law and the
existing first/second projection and sum homs, recover structural work
`2*n+1`, the original callback-only run at entry zero, and the original total
run at entry one. These are observations of the same operation, not a second
synthetic tally. Retain sample pairs `(9,6)` for single-append inorder and
`(9,12)` for actual size-cache annotation, with totals 15 and 21.

Show why the reached-child-summary premise is useful: an actual callback may
always return summary zero and cost zero on the reachable pair `(0,0)`, while
charging a positive amount on an unreachable summary input. Prove the zero
reached-cost law and structural whole-fold count through the public result,
and exhibit the nonzero unreachable callback case. This must not be claimed
as a stronger global zero-cost law. Both subtrees remain measured even though
the callback discards their summary values.

## Integration, statement review and limits

Place the reusable construction/laws under `Applications/Resources`, and the
connected clients/compositions under `Examples`. Every new Lean module must
be in the public root's import closure. Add a reconstruction note and source
map entry recording the settled literal append association, declared tariffs,
callback domains, actual execution/value connections and remaining scope.

Statement review must inspect independent universes, minimal algebraic
assumptions, noncommutative grouping/order, fixed versus changed callbacks,
actual reached arguments, global versus reachable laws, source tariff choices,
empty cases and the distinction between value equality and cost equality.
No new axiom, `sorry`, `admit`, unsafe/partial definition, `native_decide` or
skipped kernel checking is permitted.

This bounded unit does not implement a source cost translator, all-tree inorder
left-mass/asymptotic theory, the suffix accumulator or closure invocation bridge,
AVL `debal`/`debal2`, Braun splice/forest algorithms, list balancing, selective
search/merge, arbitrary subtree/history machinery or physical sharing/storage
analysis. A function-valued fold result measures construction under its declared
model, not its later invocation. A value fold/map law does not pay for a separate
erasure pass or establish a one-pass algorithm. All such original book work
remains mandatory in its owning chapter or separately frozen shared follow-up.

Source preflights and committed drafts supply no acceptance credit. Preserve
the clean pre-code scope in checkpoint 0031 before implementation, and later
preserve any committed draft with its exact identities, local findings and
validation limits before relying on it as recoverable progress.
