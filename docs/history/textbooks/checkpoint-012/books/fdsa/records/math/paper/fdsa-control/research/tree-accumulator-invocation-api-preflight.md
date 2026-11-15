# Tree accumulator invocation: API and reuse preflight

Prepared 2026-11-02. **Read-only preparation, not frozen scope, implementation,
compilation or final review.** The report path was checked absent before writing.
This is the sole new file written for this assignment. Chapter 1 and the original
chapter sequence remain unchanged; all referenced shared drafts remain unaccepted.
The old gate 80227 was left untouched.

## 1. Recommendation

The existing ordinary `Trees.fold`, `Resources.Measured`, `bind`, `pure`, and
`CallCount.tick` suffice to express an actual measured suffix-builder invocation.
Use the ordinary fold at the function summary type
`List α → Measured (List α) Nat`. Its nil callback returns the supplied suffix
with one entry charge. Its node callback invokes the **right** child on that
suffix, invokes the left child on the actual returned list after consing the
node label, and posts one entry charge. No append occurs in this operation.

Prove an exact pair theorem for **every suffix** by structural induction,
generalizing the suffix. That supplies both the inorder-prefix value and the
`2 * t.numNodes + 1` application count. It avoids a new builder datatype,
executor, cost-only recursion, reachability framework, or probability-style law
record. Ordinary fold fusion supplies an additional value-semantic connection
when it is useful; it does not by itself prove the invocation count.

The saved XD01 difference-list module is not a necessary core dependency.
Its `Builder` is exactly the ordinary function type above, and its `Rep`,
`AppCost`, and `toDList` are useful optional consumers of the result. Its generic
charged singleton/composition execution is a different tariff unless the cons
step is deliberately fused into an uncharged callback wrapper. Keep that
comparison explicit rather than importing a convenient but wrong count.

The measured XT03 whole fold is useful for a **separate construction client**.
Its cost when the summary is a function concerns construction of that function;
its value theorem does not include a later invocation. If a combined program
constructs and invokes, use actual measured bind and add both observations.

## 2. Inspected sources and exact existing APIs

Source files read in the assignment:

- `conaled-tree-fold/Applications/Trees/Observations.lean`;
- `conaled-tree-fold/Applications/Resources/Measured.lean`;
- `conaled-tree-fold/Applications/Resources/CallCount.lean`;
- `conaled-tree-fold/Applications/Resources/TreeFold.lean`, the source root
  identifies with the saved XT03 draft `b0fce71`;
- `conaled-builder-costs/Applications/Resources/DifferenceListCosts.lean`,
  its connected example file, and `docs/research/fdsa-difference-list-costs.md`;
- the retained XT03 source preflight, especially its accumulator subsection;
- the existing `TreeFlattening/Core.lean` and `Observation.lean` to check for
  an already matching traversal; and the saved four-node fixture;
- pinned Lean 4.35.0 list lemma source. No compiler was invoked.

The Mathlib dependency remains the retained pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`; no dependency or remote was changed.
The source correspondence comes from the already retained July 27, 2026 book
and Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
The sibling `tree-accumulator-invocation-source-preflight.md` owns the focused
manuscript/companion-theory assessment. No fresh book retrieval is needed here.

### Ordinary fold

The existing declarations have these explicit argument orders:

```lean
Trees.fold (empty : β) (combine : β → α → β → β) : BinaryTree α → β

Trees.fold_fusion empty combine empty' combine' observe
  h_empty h_node t

Trees.fold_map empty combine label t
Trees.inorder t
Trees.inorder_node a l r
Trees.inorder_length t
```

`fold_fusion` assumes
`observe empty = empty'` and
`∀ l a r, observe (combine l a r) = combine' (observe l) a (observe r)`.
It requires no monoid, equality or order on the summary. Its source, summary
and observed-summary universes are independent.

### Measured sequencing

```lean
Resources.Measured α C := α × C
Resources.pure [Zero C] (a : α) : Measured α C
Resources.bind [Add C] (r : Measured α C)
  (f : α → Measured β C) : Measured β C

Resources.bind_value r f : (bind r f).1 = (f r.1).1
Resources.bind_assoc r f g       -- requires AddSemigroup C
Resources.bind_erases f g f₀ g₀ hf hg x

Resources.CallCount.tick (r : Measured α Nat) : Measured α Nat
Resources.CallCount.tick_value r
Resources.CallCount.tick_cost r
Resources.CallCount.let_rule r body
```

In particular, `bind r f = ((f r.1).1, r.2 + (f r.1).2)` and
`tick r = (r.1, r.2 + 1)`. These retain the actual right result before the left
invocation. Constructor/cons work is zero under this declared source tariff.

### Existing measured whole-fold contracts

The relevant XT03 APIs are:

```lean
Resources.TreeFold.run entry empty combineRun t
Resources.TreeFold.run_value entry empty combineRun t
Resources.TreeFold.run_value_of entry empty combineRun combine hvalue t
Resources.TreeFold.run_cost_const entry empty combineRun k hcost t
Resources.TreeFold.run_cost_le entry empty combineRun K hcost t
Resources.TreeFold.reweight_run h entry empty combineRun t
```

`run` sequences its *construction* child results left then right, followed by
the actual combine callback. Function-valued child results are values at this
boundary. Nothing in this contract invokes either returned function.
`run_cost_const` ranges over callbacks on actual child summaries, as frozen;
it is appropriate for a zero-cost closure-capture callback in a separately
named construction model, not a substitute for a suffix invocation proof.

### List rewriting at the pin

The exact small equations required are present in Lean's
`Init/Data/List/Basic.lean`:

```lean
List.nil_append (xs) : [] ++ xs = xs
List.cons_append : (a :: xs) ++ ys = a :: (xs ++ ys)
List.append_nil (xs) : xs ++ [] = xs
List.append_assoc (xs ys zs) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
```

The arbitrary-suffix value proof needs associativity of **specification lists**;
this does not introduce an append into the measured operation.

## 3. Proposed smallest source interface

The following is a **proposal**, not a written or compiled declaration. A
possible home is `Applications/Resources/TreeAccumulator.lean`, under a small
ordinary namespace such as `Resources.TreeAccumulator`:

```lean
universe u
variable {α : Type u}

def inorderRun (t : BinaryTree α) : List α → Measured (List α) Nat :=
  Trees.fold
    (fun suffix => CallCount.tick (pure suffix))
    (fun left a right suffix =>
      CallCount.tick
        (bind (right suffix) (fun rest => left (a :: rest)))) t
```

This uses the already existing structural fold as its only tree recursion.
The returned function has an actual measured application body. A public builder
alias or a second pure accumulator definition is not required. The concrete
source uses the same payload type for labels and suffix elements, so a single
arbitrary universe `u` is the correct domain. No `Inhabited α`, `DecidableEq α`,
order, finiteness, or nonempty-tree assumption is justified.

Suggested useful public contracts, with names still provisional:

```text
inorderRun_nil suffix:
  inorderRun nil suffix = (suffix, 1)

inorderRun_node a l r suffix:
  inorderRun (node a l r) suffix =
    tick (bind (inorderRun r suffix)
      (fun rest => inorderRun l (a :: rest)))

inorderRun_exact t suffix:
  inorderRun t suffix = (Trees.inorder t ++ suffix, 2*t.numNodes+1)
```

Projection corollaries `inorderRun_value t suffix` and
`inorderRun_cost t suffix` are practical only if clients need them repeatedly;
the pair theorem is the main proof obligation. Avoid another suite of equivalent
wrappers. Materializing at `[]` is a corollary, not the induction invariant.
The operation should not traverse or measure the supplied suffix.

The exact node work equation is

```text
cost(right suffix)
  + cost(left (a :: value(right suffix))) + 1.
```

This is right-before-left invocation despite left-before-right prefix order.
It is also different from XT03's strict left/right/callback evaluation order.
The same natural total `2*n+1` does not establish equality of those execution
orders. Post-body entry charging follows the existing `tick` convention.

### Proof route

For the pair theorem, use tree induction generalizing `suffix`.

1. Nil reduces to the actual ticked suffix pair.
2. At a node, rewrite the public node equation and the right induction
   hypothesis at the supplied suffix.
3. Apply the left induction hypothesis at the actual intermediate suffix
   `a :: (Trees.inorder r ++ suffix)`. An induction theorem only at `[]`
   cannot justify this step.
4. Normalize the first projection with `Trees.inorder_node`,
   `List.append_assoc` and `List.cons_append`.
5. Normalize the second projection using `BinaryTree.numNodes` and ordinary
   natural arithmetic:
   `(2*nR+1)+(2*nL+1)+1 = 2*(nL+nR+1)+1`.

This proof retains the actual intermediate value. It does not need a separately
recursive call-count function, a cost assumed for the final callback, or an
inferred constant-time application rule.

A useful value-only fusion observation is
`erase f := fun suffix => (f suffix).1`. Apply `Trees.fold_fusion` from the
measured-function algebra to the pure-function algebra
`id` and `fun left a right suffix => left (a :: right suffix)`.
The empty/node preservation proofs are function extensionality followed by the
existing `tick_value`/`bind_value` equations. A second ordinary fusion with
`observe prefix := fun suffix => prefix ++ suffix`, or the same suffix
induction, identifies that pure function with `Trees.inorder t ++ ·`.
There is no need to expose a generic higher-order erasure framework for this.

Core imports can stay at `Applications.Trees.Observations` and
`Applications.Resources.CallCount`, plus only the actual arithmetic tactic
needed by a final proof. XT03 and XD01 are not logical prerequisites to this
invocation core. If a construction composition is included, that example
imports XT03; a DList bridge example imports XD01. Acceptance/integration
prerequisites still follow the existing tickets rather than these import facts.

## 4. Construction and invocation are separate programs

Evaluating a strict ordinary fold to obtain the callback is not automatically
free. The proposed operation above supplies a measured **invocation**
observation; it does not report the physical evaluation work of building that
callback. Its two-argument equations match the declared source recursion, but
a runtime/cost-preserving compiler transformation to a separately constructed
closure graph would require additional evidence. No such transformation is
part of this proposal.

A small connected construction example can reuse XT03 directly. Let `base` be
the nil invocation function and `step left a right` be the node invocation
function above. Use

```text
TreeFold.run constructionEntry base
  (fun left a right => pure (step left a right)) t.
```

`run_value_of` identifies its actual returned function with `inorderRun t`.
`run_cost_const` with callback cost zero gives construction-traversal observation
`constructionEntry*(2*n+1)`. These callbacks capture the already supplied child
functions without applying them.

At construction entry one, binding this actual returned callback to a later
suffix application gives `4*n+2`. Constructing once and applying twice gives
`6*n+3`. If the callback is already supplied, two actual applications cost only
`4*n+2`. These are distinct program boundaries; none replaces the source
single-invocation `2*n+1` theorem.

The construction entry charge counts the declared traversal entries. It is not
by itself an allocation count or the number of distinct closures: in particular,
the same supplied nil callback may be returned at several empty children. A
fixed-size capture/creation charge would need to be separately declared and
retained in the actual construction callback. Do not silently call the traversal
observation a physical closure-creation measurement.

## 5. Exact XD01 reuse and its tariff boundary

The inspected public interface is:

```lean
Resources.DifferenceListCosts.Builder α
Resources.DifferenceListCosts.Rep f prefix
Resources.DifferenceListCosts.AppCost f k
Resources.DifferenceListCosts.compose f g
Resources.DifferenceListCosts.compose_cost f g suffix
Resources.DifferenceListCosts.compose_rep f g p q hp hq
Resources.DifferenceListCosts.compose_appCost f g k l hk hl
Resources.DifferenceListCosts.toDList f prefix rep
Resources.DifferenceListCosts.toDList_apply f prefix rep suffix
Resources.DifferenceListCosts.toList_toDList f prefix rep
Resources.DifferenceListCosts.toDList_eq_ofList f prefix rep
```

`Builder α` is an abbreviation for the proposed ordinary function type.
`Rep f prefix` means `∀ suffix, (f suffix).1 = prefix ++ suffix`;
`AppCost f k` means `∀ suffix, (f suffix).2 = k`.
The pair theorem therefore directly supplies
`Rep (inorderRun t) (Trees.inorder t)` and
`AppCost (inorderRun t) (2*t.numNodes+1)`.
`toDList` then provides a Batteries value bridge without a new DList datatype.
Its value erasure carries no application count into the DList value.

The exact XD01 node composition that matches the proposed invocation is

```text
compose (fun suffix => left (a :: suffix)) right.
```

The wrapper performs a free cons and the actual left invocation; it has no
additional charged entry of its own. XD01's `compose` invokes right first and
adds exactly the node entry, so this expression has the required cost equation.
If `left` represents `p`, the wrapper represents `p ++ [a]`; its uniform
application cost is the same as left's. This is a legitimate optional semantic
reuse route, but extracting a public generic wrapper merely to name this lambda
would add no useful abstraction.

In contrast, `compose left (compose (singleton a) right)` has application cost
`cost(right)+cost(left-at-the-produced-suffix)+3`. It introduces a charged
singleton and a second charged composition. With the same charged nil bases,
that recursively encoded tree has total `4*n+1`, not `2*n+1`. A one-node tree
already distinguishes five from three calls. Likewise `pushRun` belongs to
XD01's explicit creation model; its fused Batteries push theorem preserves
values only. Do not identify either model's work with the accumulator solely
from its represented list.

The existing XD01 examples make the logical boundary concrete:
`padded` preserves an empty represented prefix while application work grows,
and `doubled` creates five callbacks after four extensions but applies them in
31 unfolded occurrences. Thus neither `Rep` nor construction size alone proves
the accumulator's application bound. Its own occurrence recurrence does.

Recommendation: keep XD01 out of the new core, and add a bridge client only if
it demonstrates an actual consumer. There is no need to duplicate `Rep`,
`AppCost` or `toDList` in another resource module.

## 6. Existing traversal and meaningful cases

`Resources.TreeFlattening` is not an already matching algorithm. It operates
on the leaf-labelled `Bracketing.Tree`, using a pending forest/worklist; the
source here is node-labelled `BinaryTree` with empty leaves. Its
`flattenAppend` first materializes and then executes an actual measured append,
so it is not the cons-only suffix accumulator. Its append counts copied cells,
whereas the retained book call tariff also counts the terminal append call.
No replacement or automatic carrier/cost bridge is warranted.

Useful future connected cases, without expanding the unit into a new testing
or enumeration campaign:

| Case | Exact intended observation |
| --- | --- |
| Nil with arbitrary suffix | Returns that suffix; invocation count 1. |
| Singleton label `a` | Returns `a :: suffix`; count 3. |
| Saved asymmetric four-node tree | Returns `[0,1,2,3] ++ suffix`; count 9 for every suffix. |
| Nonempty repeated suffix, e.g. `[9,9]` | Both suffix occurrences remain after the entire ordered prefix; count unchanged. |
| Duplicate node labels | Their inorder occurrences remain; no set or equality-based collapse. |
| `BinaryTree Empty` | Only the nil boundary is possible, requiring no manufactured payload. |
| Two actual applications | Retains both results and pays both invocation counts; no memoization. |
| Optional XD01 bridge | Existing DList value and all-suffix cost contracts, with no transferred creation claim. |

An optional order diagnostic on the saved sample would record right-first
postorder `[2,3,0,1]`, distinct from XT03's left-first callback word
`[0,2,3,1]`. The explicit node equation already records the sequencing; a new
generic trace framework is unnecessary merely to restate it.

The node's left invocation is in tail position after the right result is
available; its right invocation is not. Linear call count is not a constant
stack-space theorem. The specification's suffix preservation does not establish
physical pointer sharing or a memory-retention bound either.

## 7. Remaining obligations and status

No mathematical obstruction was found. The genuinely new work is the concrete
append-free invocation function and its uniform suffix theorem, plus a narrowly
chosen construction/DList composition if it is useful. Exact source entry
correspondence remains explicit: the source recursion counts nil and node
invocations, cons is primitive, and no unproved generated `T_inorder2` theorem
is cited. The retained companion source has a value recurrence and arbitrary-
suffix proof, not a generated timing declaration.

This preflight does not formalize the source's quadratic worst-case direct
inorder family, prove all Chapter 4 exercises, add a source cost translator,
prove physical execution/stack bounds, implement preorder/AVL conversion/Braun
forest traversal, or change any ticket's scope or acceptance. Those original
obligations remain in their owning chapters. All named new declarations above
are proposals only. Ordinary source inspection cannot certify Lean elaboration.

No worktree source, previous report, requirement, tracker, Git ref/index,
dependency, cache, gate or remote was changed. No compiler, checker, project
hash helper, finite enumeration or child delegation ran. The source-only note
is ready for the root's normal durability capture; writing is stopped.
