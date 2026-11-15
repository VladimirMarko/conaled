# Measured whole-tree folds: bounded API and reuse preflight

Status: preparation only, after XT02 draft `974a97321a8ec174b56104c7e6efaaca881b6639` and checkpoint 0030. No scope is frozen by this note. No repository source, requirement, ticket, Git state, compiler/checker output, cache or active gate was changed. The sole new artifact is this report; absence was checked before creation. All implementation-looking declarations below are proposals, not compiled Lean or accepted results.

## 1. Recommendation: specialize the existing fold

The smallest suitable operation is an ordinary specialization of `Trees.fold` at summary type `Resources.Measured β C`. There is no need for another recursive executor, tree carrier, callback class, syntax, monad instance, or execution-history record.

Supply three explicit parameters: a structural-entry observation, an empty summary, and the actual measured combine callback. Each node sequences the computed left result, computed right result and callback, then adds the declared structural charge in the same post-body position used by `CallCount.tick`. The callback sees returned child values, and its returned value is the parent summary. The operation needs only `[Add C]`; payload, summary and observation universes remain independent.

For the natural-number analysis, compare that same operation at entry tariffs `e` and `0`. Prove value erasure first, so both executions are known to reach the same callback arguments. Then the exact split is:

```
(run e empty combineRun t).2 =
  (run 0 empty combineRun t).2 + e * (2 * t.numNodes + 1).
```

The first summand is an actual zero-entry execution of the same callback. It is not a recursively invented residual, a subtraction from the desired formula, or a second execution performed by the implementation. This gives a clean structural/callback separation without a new cost-function language.

Keep the basic operation and value/sequence laws observation-polymorphic. State this collected split and the first quantitative bounds for `Nat`. Collecting charges across callback events is false for an arbitrary noncommutative additive observation; the generic operation must retain execution order.

Possible placement is `Applications/Resources/TreeFold.lean`, namespace `Resources.TreeFold`, with `run` as the ordinary fold specialization. These names are proposals only. The core should import `Applications.Trees.Observations` and `Applications.Resources.CallCount`; client files can import append/cache and trace libraries. No real-analysis import is required.

## 2. Inspection boundary and existing reuse

Inspected checkout: `/workspace/scratch/845aa1048b05/conaled-tree-shape`, at the root-reported saved XT02 head above. Its XT01 dependency is saved but unvalidated. Mathlib remains pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679` with Lean 4.35. No Git or compiler command was run for this preflight.

This note reuses the previous shared-tree source/API/case preflights and the saved XT01/XT02 scope. The independently owned `tree-fold-resource-source-preflight.md` supplies the additional book-specific execution and tariff assessment. This note does not rewrite older immutable reports or enlarge the earlier units retroactively.

| Inspected interface | Exact reusable content and limitation |
|---|---|
| `Trees.fold`, `fold_nil`, `fold_node` in `Applications/Trees/Observations.lean` | Existing structurally recursive node-labelled fold. Instantiate its result type with an ordinary measured pair. |
| `Trees.fold_fusion` | Arguments: source empty/combine, target empty/combine, observation, empty equation, universal node equation, tree. Taking `Prod.fst` proves unconditional value erasure. |
| `Trees.fold_map`, `fold_numNodes`, `fold_height`, `inorder`, `inorder_length` | Value correspondences and child-result lengths. They alone say nothing about execution costs. |
| `Resources.Measured α C` | Abbreviation for `α × C`; independently universe-polymorphic. |
| `Resources.bind [Add C] r f` | Let `s := f r.1`; return `(s.1, r.2 + s.2)`. No commutativity or associativity premise for the operation. |
| `Resources.pure [Zero C] a` | `(a,0)`. Useful for actual zero-cost callbacks and the zero-entry base. |
| `Resources.bind_value` | `(bind r f).1 = (f r.1).1`. |
| `Resources.bind_assoc [AddSemigroup C]` | Reassociates binds, preserving their order. |
| `Resources.bind_pure`, `pure_bind [AddZeroClass C]` | Remove an actual zero-cost boundary; they do not discard callback work. |
| `CallCount.tick` | Nat-only `(value,cost+1)`, explicitly charged after the body's observation. |
| `CallCount.arguments_rule [Add C] r s f` | `bind r (fun a => bind s (f a)) = ((f r.1 s.1).1, r.2 + (s.2 + (f r.1 s.1).2))`. Exact reached arguments and order. |
| `CallCount.primitive_rule [AddZeroClass C]` | Binding an actual pure value transformation retains the preceding cost. |
| `Resources.reweight_bind` | Additive-hom transport exists if a later concrete multi-observation client requires it. No new reweighting framework is needed now. |

The following existing folds were checked to avoid a duplicate executor:

- `Resources.run` in `Workload.lean` is a list/state transition execution. `run_state`, `run_append`, `run_invariant` and `run_value_fusion` are useful design precedents, but a bottom-up tree fold cannot be substituted by this list executor without introducing a schedule/stack and proving a different algorithm correspondence. That extra layer is unnecessary here.
- `Resources.FoldCompiler.target` interprets a finite **list-fold AST** using `run`; `run_constant_cost` proves `xs.length*k` for an actual constant-cost list step. Its abstract-syntax and scalar compiler machinery does not fit a plain tree callback. Do not pull it into a new tree interpretation merely to count nodes.
- `StructuredLinear.Costs.measuredFold` is a list fold with a supplied event-charge function. It is specific to the structured-matrix observation and is not a tree executor.
- `Resources.TreeFlattening.fromTWithCost` and `fromTsWithCost` traverse **leaf-labelled** `Bracketing.Tree`. Their existing exact counts distinguish recursive append from a pending-stack algorithm; they remain valuable clients but are not the node-labelled tree fold or its nil convention. `appendWithCost` charges copied cells, whereas `ListReversal.appendRun` additionally charges the final empty append call.
- `Bracketing.Tree.fold` is a different leaf/fork algebra over the leaf-labelled carrier. XT01 already supplied the matching node-labelled operation; do not switch carriers or duplicate either fold.
- `BinaryTree.traverse` invokes a label callback before recursively traversing children. A bottom-up algebra consuming child summaries is not that traversal merely under a different callback type.

## 3. A minimal proposed operation and exact recurrence

For independent `α : Type u`, `β : Type v`, and `C : Type w`, the proposed definition shape is:

```lean
-- Proposal only; no source file was created.
def run [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Resources.Measured β C)
    (t : BinaryTree α) : Resources.Measured β C :=
  Trees.fold (empty, entry)
    (fun left a right =>
      let body := Resources.bind left (fun l =>
        Resources.bind right (fun r => combineRun l a r))
      (body.1, body.2 + entry)) t
```

The seed is directly `(empty,entry)`, so no unnecessary zero capability is imposed on the generic operation. When entry is zero, it is `pure empty`. For natural entry one it is `CallCount.tick (pure empty)`. No new general tick operation is required merely to name the inline pair adjustment.

At a node, let `L := run entry empty combineRun l`, `R := run entry empty combineRun r`, and `F := combineRun L.1 a R.1`. The exact result is

```
(F.1, (L.2 + (R.2 + F.2)) + entry).
```

Retain those parentheses under mere `[Add C]`. Under an additive semigroup they can be reassociated but not reordered. At natural entry one the whole node equation is exactly

```
CallCount.tick
  (bind L (fun left => bind R (fun right => combineRun left a right))).
```

Thus the ordinary fold specialization has the existing call-count recurrence; no separately recursive `runOne`, `runZero`, or tally executor is needed.

Both subtrees' observations are included even when the callback discards their returned summaries. This is an eager structural fold observation. It is not a pruning algorithm, a general lazy-language theorem, or a statement about whether a compiler avoids or shares computations.

## 4. Value erasure and honest callback premises

### Unconditional erasure

The central unconditional theorem should be:

```
(run entry empty combineRun t).1 =
  Trees.fold empty (fun l a r => (combineRun l a r).1) t.
```

Prove it by `Trees.fold_fusion` with `Prod.fst`. The empty and node compatibility equations reduce directly through the existing pair/bind operations. There is no callback-correctness hypothesis because the target fold uses the actual callback's value component.

This also shows that the result, and hence the child arguments supplied to the callback, are independent of the outer entry tariff **for the same fixed callback and empty value**. If a caller changes a callback closure when it changes the tariff, it has changed another parameter; the theorem does not silently relate those different callbacks.

An erasure theorem to an unrelated supplied pure algebra `combine` needs an actual value law. A global law

```
∀ l a r, (combineRun l a r).1 = combine l a r
```

is sufficient, not logically necessary. Do not call that stronger theorem unconditional.

### Reached values without a new reachability record

For discussion only, write

```
V t := Trees.fold empty (fun l a r => (combineRun l a r).1) t.
```

`V` need not become a new public definition. One economical sufficient premise is

```
∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
  (combineRun (V l) a (V r)).1 = combine (V l) a (V r).
```

Structural induction then yields refinement to `Trees.fold empty combine`. The induction first knows the child results and applies the law at their actual reached values. This avoids requiring correctness on arbitrary β values which no tree execution can produce.

This premise quantifies over values reachable from **any** finite child tree for these fixed parameters; it is not literally restricted to the subtrees of a single supplied input. State that boundary honestly. If a later client needs a truly input-local contract, it may prove the relevant induction locally. Do not preemptively add a global subtree/reachability framework solely for the first unit.

The same form is useful for cost laws, replacing `.1 = ...` with `.2 = k` or `.2 ≤ K`. A global callback law immediately specializes to it. An invariant-restricted callback law can also discharge it after proving the pure-fold results satisfy that invariant. Existing `Workload.run_value_fusion` demonstrates the same distinction between global operations and laws valid on reachable states, but its executor need not be reused on a different data shape.

A frozen API can choose either global convenient corollaries or this child-tree form as its main cost theorem. It need not export both suites of wrappers. A public predicate/record representing callback validity is not needed.

## 5. Exact Nat tariff separation and bounds

Let `n := t.numNodes`, `W_e(t) := (run e empty combineRun t).2`, and keep the callback fixed. The first exact theorem is

```
W_e(t) = W_0(t) + e * (2*n + 1).
```

Both `W_e` and `W_0` here are abbreviations for the same actual operation at different instrumentation parameters, not new mutually recursive cost functions.

Proof route:

1. Use unconditional erasure to replace both runs' child values by `V l` and `V r`.
2. The parent callback cost is now literally the same term in both recurrences.
3. Induct on the input tree using the exact node recurrence.
4. For the structural coefficient, one may first use `t.numNodes + t.numLeaves`, whose node recurrence adds the two child counts and one. Reuse `BinaryTree.numLeaves_eq_numNodes_succ` to obtain `2*n+1`.
5. Use natural multiplication distribution explicitly before arithmetic automation. In particular, variable products such as `e*n` are not solved by treating `omega` as a nonlinear procedure.

This is not circular: the zero-entry cost comes from actually executing the supplied measured callbacks, and the tariff difference is proved separately. The implementation does not evaluate both runs to produce its result. Nil has `W_e=e`, `W_0=0`, and structural coefficient one.

For a fixed natural callback cost `k` on reached child summaries:

```
W_0(t) = k*n
W_e(t) = e*(2*n+1) + k*n.
```

For a fixed uniform upper bound `K` on those same actual callback costs:

```
W_0(t) ≤ K*n
W_e(t) ≤ e*(2*n+1) + K*n.
```

At entry one this yields `W_1(t)≤(K+2)*n+1`; at callback cost zero it is exactly `2*n+1`. These are bounds on the observation, not on physical machine time. If `K` depends on the input size, the displayed pointwise bound remains true but is not a uniform linear-complexity conclusion. Keep the quantifier order visible: one fixed K must bound the whole claimed input family.

Useful proposed public surface is small: `run`, constructor equations, unconditional `run_value`, the Nat tariff split, one exact constant-cost result and one uniform-bound result, plus a callback-value refinement result if the actual clients need it. Names and argument orders remain subject to a future freeze.

### Noncommutative boundary

The definition/value theorem needs only `[Add C]`. Do not impose commutativity on it to simplify the Nat proof. Conversely, do not state the collected tariff identity for arbitrary `C`.

For an additive word observation, let every nil/entry charge be the letter E and a singleton's callback charge be K. The actual singleton execution emits

```
E E K E
```

while zero-entry callback work followed by three E charges is

```
K E E E.
```

They differ. The Nat split uses commutativity; an optional generalization would require a commutative observation or a specific commuting-charge hypothesis and a genuine client. It is not needed merely for notation.

A useful positive sequencing case uses `C = Additive (FreeMonoid Nat)`, zero entry charge, and a size-valued callback that returns `left+right+1` while recording its node label. On the saved asymmetric sample it returns size 4 and callback word `[0,2,3,1]`: left subtree, right subtree, parent. This differs from its inorder `[0,1,2,3]`. Such a concrete existing additive word type tests sequencing without a new event framework. Type-tag/FreeMonoid imports can stay in the example file.

## 6. Connected actual inorder callbacks

`Resources.ListReversal.appendRun` is already an actual recursive append observation. Its public exact theorem states

```
appendRun xs ys = (xs ++ ys, xs.length + 1).
```

The additional one is the final empty-list invocation. Do not substitute the copied-cell count from `TreeFlattening.appendWithCost` without its explicit tariff bridge.

### One append to a cons

Use the actual callback

```
fun l a r => appendRun l (a :: r).
```

Its returned value is exactly the existing `Trees.inorder` algebra, and its cost is `l.length+1`. Apply the measured fold's value result to derive returned inorder. Then `Trees.inorder_length` identifies the actual left child summary length with the left child's node count.

If a later chapter wants a closed shape formula, let A be the independent statistic with `A(nil)=0` and `A(node a l r)=A(l)+A(r)+l.numNodes`. The resulting proved formula at entry one is `3*n+1+A(t)`. A can be obtained by an ordinary size/statistic pair fold; it is not necessary to introduce a new recursively defined cost executor in the shared core. Its equality to the actual cost must be proved using `appendRun_exact` and the value/length laws.

A first bounded unit can instead retain the actual callback recurrence and a connected finite case, leaving the all-tree shape statistic and asymptotic families to Chapter 4. A one-visit-per-node argument alone does not prove linear work because append's reached cost grows with the left summary.

### Literal right-associated two-append source

The source companion preparation recovered the book's explicit rule on printed p. 5 that append associates right. Thus the literal `I l @ [a] @ I r` means `I l @ ([a] @ I r)`. The actual callback retaining both appends is

```
fun l a r => bind (appendRun [a] r) (fun ar => appendRun l ar).
```

Its work is `2 + (l.length+1) = l.length+3`. Its value is the same inorder algebra. At entry one its derived shape formula is `5*n+1+A(t)`, two extra append invocations per internal node compared with the one-append-to-cons callback. This is an explicit source-expression and tariff correspondence, not an equality inferred by associativity.

The earlier shared-tree report presented both parenthesizations conditionally because that source convention had not yet been recovered; preserve that earlier artifact and retain the new evidence separately. A left-associated two-append expression has a different cost and is not the literal source interpretation now identified. No generated `T_inorder` or compiler-normalized term is asserted to have been recovered.

On the actual saved four-node sample, left-subtree sizes sum to A=2:

| Actual declared operation, entry tariff 1 | Returned inorder | Work |
|---|---|---:|
| One append to cons | `[0,1,2,3]` | `3*4+1+2 = 15` |
| Retained right-associated two appends | `[0,1,2,3]` | `5*4+1+2 = 23` |

These numbers were obtained from the displayed recurrences, not a new enumeration campaign. Future formal examples should consume the generic fold recurrence and existing append theorem. Equality of outputs alone is not their cost proof.

For a right chain A=0; for an n-node left chain A=n(n−1)/2. The different shape costs prevent a claim that every input has quadratic work. Those general-family proofs are chapter-specific follow-ups, not automatically part of the smallest shared unit.

## 7. Connected actual cache annotation

The existing `Trees.Cached.annotate empty combine` is already an ordinary fold with empty cached tree and `smartNode empty combine` as its algebra. Therefore the measured whole fold can return its actual annotation using the existing measured smart constructor as callback:

```
run entry BinaryTree.nil (Resources.TreeCache.nodeRun empty combineRun) t.
```

Here the outer summary type is `BinaryTree (α × β)`, independently of the payload universe. The inner callback `combineRun : β → α → β → Measured β Nat` is supplied to the existing local constructor; it is not replaced by a synthetic cost.

Use `TreeCache.nodeRun_value` at the reached child reads to connect the callback to `Cached.smartNode`. With that value law, the whole-fold erasure connects to the existing actual `Cached.annotate`; existing `annotate_valid`, `erase_annotate`, and `read_annotate` then supply validity, shape/payload erasure, and summary correctness. For laws restricted to valid generated children, prove child correctness before applying the reached law; do not silently require or infer correctness of arbitrary malformed caches.

The exact local cost theorem is already

```
(nodeRun empty combineRun l a r).2 =
  (combineRun (Cached.read empty l) a (Cached.read empty r)).2 + 3.
```

The three units are two actual root reads and one local constructor entry. If the reached inner callback has cost k, outer fold work is

```
entry*(2*n+1) + (k+3)*n.
```

For the actual saved zero-cost size or height callbacks, k=0. With outer entry one, annotation has cost `5*n+1`; on the saved four-node sample it is 21. Entry zero counts only those actual local constructor callbacks and gives `3*n`. The annotation preparation is now the very computation being measured; unlike XT01's local smart-node theorem, no pre-existing cached children are assumed to have appeared for free.

Do not conflate three distinct models:

1. Inlined pure smart-node/read primitives inside a source-style fold may carry zero helper observation, giving `2*n+1` plus actual combine work.
2. The actual XT01 `nodeRun` callback deliberately charges its two reads and constructor, giving `5*n+1` plus actual combine work when the outer fold entry also costs one.
3. The pinned leftist source assigns its `mht` and `node` auxiliaries zero in its selective tariff. That does not establish either measured annotation count or authorize altering the existing queue model.

The fold-entry charge and callback's smart-constructor entry are distinct named charges in model 2. Counting both is justified only by that declared layered model, not by calling one logical operation twice.

A later Chapter 9 `debal2` client can also fold directly over labels carrying old annotations and ignore each old tag in the actual combine. The pure value is related to `annotate ... (t.map Prod.fst)` by `fold_map`, but that expression itself includes an additional erasure pass. A one-pass cost must belong to the fused measured fold, not be transferred from a value equality. This is a future algorithm-specific composition, not a request to implement AVL conversion here.

## 8. Boundaries worth retaining in a future freeze

- **Empty payload:** `BinaryTree Empty` supports nil; the explicitly supplied empty summary suffices. Empty work is entry, not zero when entry is one. There is no `Inhabited α` requirement.
- **Independent universes:** α, β and C have separate universe parameters. Measured product summaries and cached-tree summaries require no universe equality. Do not route the core through a stronger-universe `erasureSquare` packaging interface merely to reuse the pair abstraction.
- **Callback correctness versus work:** Value erasure does not imply a bound. The actual append callback is a consequential nonconstant-cost case. Likewise a constant work law says nothing about agreement with a desired pure algebra.
- **Reached arguments:** Laws refer to the child's computed summaries, not original subtrees, arbitrary cached values, or a cost-only recurrence whose value computation was never connected.
- **Function-valued summaries:** A strict measured fold returning closures measures their construction. It does not measure later applications. In particular, a difference-list/endofunction value proof alone does not prove the source accumulator `inorder2` invocation recurrence or its `2*n+1` count. That source calls the right subtree on a suffix and then the left on the returned suffix; it needs its own execution bridge or recurrence.
- **Higher-order callback work:** The source's measured map/filter conventions retain actual callback charges. Treating unknown callbacks as zero because a first-order source clause lists variables as free is unsound. A supplied zero-cost callback is a specific declared model, not a theorem about all user functions.
- **Sharing:** Counts refer to structural occurrences in the logical tree. Equal or physically shared child values do not automatically acquire memoization or a physical allocated-node bound. No runtime/space claim follows from the measured pair alone.
- **Noncommutative observations:** Preserve left/right/callback/post-charge order. Only the Nat aggregate proof may collect and rearrange the terms without an extra commutation law.

## 9. Small-first-unit decision and stopping point

There is a genuine small theorem layer to add, but not a need for a new recursive executor. The recommended first shape is:

1. Ordinary measured specialization of `Trees.fold`, generic in the observation operation.
2. Exact constructor/sequence equations and unconditional actual-value erasure.
3. Nat entry-zero comparison, constant-callback equality, and a uniform reached-callback upper bound.
4. Connected actual append/inorder and existing measured smart-node annotation cases, plus a noncommutative trace case if generic observation polymorphism is retained.

The all-tree inorder statistic/asymptotics, accumulator invocation, Braun interleaving, AVL conversion, queue adapters, arbitrary histories, physical sharing, and a general tariff/closure compiler remain outside this recommendation. No existing public operation needs to be refactored merely to make the new theorems available.

The proof route is feasible against inspected declarations. Main future elaboration risks are ordinary fold-fusion universe inference, explicit grouping of noncommutative observations, rewriting child values before comparing actual callback costs, and Nat distribution before arithmetic automation. These are source-assessment risks, not compiler outcomes. A later freeze must choose the exact public callback-premise form and client scope; this preflight does not choose an acceptance status or start a new review loop.

## 10. Bounded follow-up: one product observation and existing reweighting

After the main note was drafted, root proposed a concrete product-observation client. This is a useful reason to consider one small additional law, without a new resource representation or executor.

Using the same standard assumptions as `Resources.reweight_bind`, propose:

```
[AddMonoid C] [AddMonoid D] (h : C →+ D)
reweight h (run entry empty combineRun t) =
  run (h entry) empty
    (fun l a r => reweight h (combineRun l a r)) t.
```

Prove this by existing `Trees.fold_fusion`, observing measured summaries through `Resources.reweight h`. The empty equation is immediate. For the node equation, reuse `reweight_bind` twice and `map_add` for the final entry observation; `reweight_value` keeps the reached callback arguments unchanged. No commutativity is needed for either C or D. A weaker algebraic statement might be possible, but the existing additive-hom API already fits this concrete client and avoids a second transport abstraction.

Pinned product APIs from `Mathlib.Algebra.Group.Prod` are the generated additive forms:

```
AddMonoidHom.fst Nat Nat : Nat × Nat →+ Nat
AddMonoidHom.snd Nat Nat : Nat × Nat →+ Nat
AddMonoidHom.inr Nat Nat : Nat →+ Nat × Nat
```

`inr` maps c to `(0,c)`. Their application equations and `fst_comp_inl` / corresponding projection-inclusion laws already exist. `Resources.SymmetricCosts.measuredRun_charge` and `measuredRun_work` are real existing clients using the first two homs with `reweight_run`; they provide a close precedent without requiring any changes to that list executor.

Pointwise addition of additive homomorphisms into a commutative additive target is also existing API. `Mathlib.Algebra.Group.Hom.Basic` supplies `AddMonoidHom.add` and `AddMonoidHom.add_apply` (generated from the displayed multiplicative declarations). Consequently

```
AddMonoidHom.fst Nat Nat + AddMonoidHom.snd Nat Nat
```

is the ordinary sum hom `(x,y) ↦ x+y`. Nat's commutativity justifies this hom; it does not justify swapping events in an arbitrary observation type.

For a fixed actual natural-cost callback f, run the generic operation with entry `(1,0)` and callback

```
fun l a r => reweight (AddMonoidHom.inr Nat Nat) (f l a r).
```

One actual measured fold now returns its ordinary result and a pair of observations. The proposed reweight law identifies:

| Existing observation map | Recovered execution and meaning |
|---|---|
| `fst Nat Nat` | Entry-one run whose callback retains f's returned values and has zero first-component cost. The constant-callback theorem gives exactly `2*n+1`. |
| `snd Nat Nat` | Entry-zero run of the same original f, so exactly the actual callback-work term `W_0(t)`. |
| `fst Nat Nat + snd Nat Nat` | Entry-one run of the original f, including its actual callback work and structural entries. |

For the saved one-append inorder sample this pair is `(9,6)` and the sum is 15. For the actual size-cache annotation callback `TreeCache.nodeRun` it is `(9,12)` and the sum is 21. These are observations of the same generic operation under the product algebra; no independent synthetic tally is substituted for actual callback work.

This is a consequential composition and may justify `reweight_run` for the proposed tree-fold namespace in a later freeze. It remains a design option, not an extra frozen requirement. The existing one-node word counterexample still rules out the collected-entry identity for noncommutative observations. No other source inspection or implementation is needed for this follow-up.
