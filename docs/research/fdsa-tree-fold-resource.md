# Measured whole-tree folds: FDSA shared unit XT03

## Status and scope

This is the recovered **CTB-2 source unit**, based on the preserved XT03 work
at `b0fce71fa00b2ff6250b09002176bdc75baf1f46`, and developed against pinned
`conaled` master `c214fb0720ffc998951255a7e4b5f2e80a299186`. It supplies shared
measured-fold mathematics for structural traversals, cached annotation and
later tree conversions, reusing the tree and measured-operation foundations
already integrated in that master. Its four Lean modules pass the focused
build with the pinned compiler and dependencies.

The complete FDSA reconstruction remains organized by chapter. This unit is
a prerequisite of local ticket CTB-23 (Chapter 4), and does not complete that
chapter. The local tracker and review record distinguish focused compilation,
the focused declaration audit, independent Standards and Spec review, and
final acceptance. By the user's explicit workflow decision, the receiving
`conaled` integrator owns the whole-library build, exhaustive audit and final
candidate verification. Those gates remain pending; focused checks do not
replace them.

The source is the July 27, 2026 edition of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Relevant passages are §1.4–1.5, Chapter 4 pp. 48–49 and 56–58, and Appendix
B.1/B.5. Later consumers include Chapter 9's annotation conversion and Chapter
11's tree fold with a splice callback. Their algorithm-specific obligations
remain separate. The retained Isabelle mirror revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, with BSD-3-Clause provenance recorded
in the reconstruction map. That mirror postdates the manuscript; it is not
identified as the manuscript's build revision.

The exact pre-code requirements, source/API/mathematical reports, starting
identity, local tickets and review findings travel in the durability
checkpoints. They retain the original full-book scope. This narrative does not
replace those records or certify gates outside the recorded validation scope.

## Construction and transport

`Applications.Resources.TreeFold` specializes the existing `Trees.fold` at
`Resources.Measured beta C`. It introduces neither a new tree carrier nor a
second recursive evaluator. The caller supplies the empty summary, actual
measured callback, and structural entry observation. The raw operation needs
only `Add C`; payload, summary and observation types have independent universes.

Writing `L` and `R` for actual child runs and `F` for the callback on their
returned values, its observation is exactly

```text
nil:                 entry
node:                (L.observation + (R.observation + F.observation)) + entry
```

Both child runs contribute even when the callback ignores their summaries.
The entry charge is posted after the body; `run_node_tick` identifies entry one
with the existing `CallCount.tick`. The grouping is retained under mere `Add`,
with no associative or commutative rewrite hidden in the generic statement.

`run_value` uses ordinary fold fusion with `Prod.fst`. It unconditionally erases
observations to the ordinary fold of the callback's actual returned value.
`run_value_entry` therefore preserves reached summaries when only the entry
observation changes. Its empty value and callback stay fixed. The separate
`run_value_of` refinement uses a sufficient pointwise callback-value law to
connect an independent pure algebra; that law is not claimed to be necessary.

`reweight_run` transports the same measured operation through an existing
additive hom, using ordinary fold fusion and `Resources.reweight_bind`.
`AddMonoid` assumptions belong to that hom interface and do not leak into the
raw construction or value erasure. No commutativity is needed for this
transport. `run_map` similarly reuses `Trees.fold_map` for label transport on
given input trees. The theorem does not account for separately computing a
mapped or erased input.

## Natural structural and callback costs

Let `n` be the canonical number of nodes and let `W_e` denote the observation
of the actual run with natural entry charge `e`. The cost separation is

```text
W_e = W_0 + e * (2*n + 1).
```

`W_0` is an actual zero-entry run with the same callback and empty value, not
a residual defined by subtraction. The executable definition performs one
run. The comparison proof first uses value erasure to identify both reached
callback arguments, then collects the natural structural charges.
The `2*n+1` occurrences comprise the `n` nodes and `n+1` empty children.

The constant and bounded callback results are:

| Callback premise | Whole-run conclusion |
| --- | --- |
| Reached work equals `k` | `W_e = e*(2*n+1) + k*n` |
| Reached work is at most `K` | `W_e <= e*(2*n+1) + K*n` |
| No callback hypothesis | `e*(2*n+1) <= W_e` |

The main premise quantifies over the summaries returned by this fixed run on
**arbitrary finite child trees**, and over their node label. It is weaker than
a law on every possible summary value, but is not restricted to one supplied
input's subtrees. One fixed `K` must cover the family for the displayed uniform
bound. Choosing `K` as a function of the input size does not by itself establish
linear complexity.

Nil costs `e` and invokes no callback. At `e=0`, only actual callback work
remains. A zero upper bound on nonnegative reached callback work makes the
structural lower and upper bounds agree. A positive upper bound does not
provide a positive lower bound on callback work. All these are observations
under the declared model, not claims about physical traversal time or storage.

## Actual append executions and source association

The book states on printed p. 5 that append associates right. Consequently the
literal p. 48 inorder expression has two right-associated append invocations.
The augmented inorder on p. 56 instead appends a left list to a cons.
The previous conditional source discussion remains a historical record; no
generated `T_inorder` equation or uninspected compiler rewrite is being claimed.

`Examples.TreeFold` uses the existing actual `ListReversal.appendRun` with
its exact cost `length(left)+1`, including its final empty invocation.

| Client callback | Actual execution | Callback work |
| --- | --- | --- |
| Single append | `appendRun l (a :: r)` | `length(l)+1` |
| Right associated | Append `[a]` to `r`, then append `l` to that result | `length(l)+3` |
| Left associated | Append `l` to `[a]`, then append that result to `r` | `2*length(l)+3` |

The first callback reuses XT01's `appendStepRun`. The other two bind actual
append results, including the intermediate list consumed by the second
append. Primitive cons and this callback scaffolding add zero observation
under the declared tariff. List associativity proves equality of values; it
does not identify these executions' observations.

Each measured fold returns the existing ordinary inorder. Its node-cost
recurrence uses that value bridge and `Trees.inorder_length` to replace the
length of the actual returned left list by the left subtree's node count.
The finite cases consume these recurrences and callback laws.

| Entry-one input | Single append | Right associated | Left associated |
| --- | ---: | ---: | ---: |
| Nil | 1 | 1 | 1 |
| Singleton | 4 | 6 | 6 |
| Saved asymmetric four-node sample | 15 | 23 | 25 |

The sample has nine structural entries. Its left-subtree sizes at the four
callbacks sum to two, so the callback totals are six, fourteen and sixteen.
All three executions return `[0,1,2,3]`. The worked calculation is independent
of the Lean derivation; the retained propositions must connect it to the
public execution equations. No all-tree left-mass statistic or shape-family
asymptotic theorem is implemented in this shared unit.

## Actual cached annotation

`TreeFoldCacheExamples.annotateRun` combines the measured fold with the
existing `Resources.TreeCache.nodeRun`. The latter executes two charged root
reads and the actual inner callback before posting its constructor entry.
Under a sufficient callback-value law, the returned tree equals existing
`Trees.Cached.annotate`. The generic annotation validity and erasure laws then
yield the actual returned root's fold observation.

The arithmetic size and height callbacks have zero declared inner work. The
actual measured smart constructor costs three, giving

```text
whole annotation work = e*(2*n+1) + 3*n
entry-one work        = 5*n+1.
```

Both sample annotations therefore cost 21, and their returned values agree
with the saved `sizeSample` and `heightSample`. This tariff retains XT01's
positive local charges; it does not change the separate zero-helper tariff
used by the source leftist heap. The optional zero-helper arithmetic comparison
is not needed by this unit's connected cases.

The list annotation uses the actual measured append inside the smart
constructor. Its actual child root read is identified with ordinary inorder
through the annotation value, recursive validity and erasure laws. Applying
the existing local cost then gives `leftSubtree.numNodes+4`; the four already
includes the three helper charges and append's empty invocation. The sample
has callback work eighteen and structural work nine, hence cost 27, and its
returned root reads `[0,1,2,3]`. A single visit per node does not make an
arbitrary combining callback constant-cost.

The primitive size and height folds separately return the canonical
observations with work `e*(2*n+1)`. They and the full annotation operation retain
an explicit `BinaryTree Empty` boundary without a default or inhabited payload.

## Ordered observations, paired observations and reached summaries

`Examples.TreeFoldObservations` uses `Additive (FreeMonoid Nat)` for a
size-valued callback that records its node label. At zero entry the saved
sample returns size four and callback word `[0,2,3,1]`: left subtree, right
subtree, then node. The generic value theorem supplies the size connection.

For entry token `E` and callback token `K`, a singleton records `E E K E`.
The zero-entry callback word followed by three entries is `K E E E`. The
concrete distinct decoded words prove inequality, exposing why the collected
structural-charge formula is confined to natural observations.

The product client runs the same operation with observation `Nat × Nat`, entry
`(1,0)`, and the actual callback lifted through `AddMonoidHom.inr`. Three
reweightings connect its observations to existing runs:

| Existing hom | Result of transporting the actual run |
| --- | --- |
| First projection | Entry one; callback retains its actual value with zero work |
| Second projection | The original callback with entry zero |
| Sum of projections | The original callback with entry one |

The target of the sum hom is commutative Nat. This additional fact is local
to that client. The generic transport theorem remains valid without
commutativity. The first projection preserves the callback's returned summary;
it does not replace it by the empty summary. `cache_pair` proves the complete
size-annotation observation `(2*n+1, 3*n)` for every input tree by the public
projection and annotation-cost laws. The sample observations are `(9,6)` for
single-append inorder and `(9,12)` for actual size annotation, connected to the
original totals 15 and 21 by the sum-hom theorem.

Finally `resetStep` always returns summary zero. It charges zero on the
reachable pair `(0,0)` but seven on `(1,0)`. Value erasure proves that every
child-tree run returns zero; the public reached upper bound and structural
lower bound then give exact work `e*(2*n+1)`. An explicit payload argument
supplies the witness for the nonzero unreachable callback case. Both child
runs remain measured. This example does not assert a global zero-cost law.

## Statement review and remaining work

| Concern | Intended statement and retained check |
| --- | --- |
| Parameters and assumptions | Independent payload, summary and observation universes; raw `Add` only; no payload equality, order or inhabitant. |
| Execution order | Exact grouped node equation, existing post-body tick and noncommutative word case. |
| Value versus work | Unconditional value erasure, sufficient independent value refinement and three append executions with unequal work. |
| Changed entries | The same callback and empty value on both runs; child-value equality precedes cost separation. |
| Callback domain | Arbitrary finite child trees under fixed parameters; reset example separates reachable and arbitrary summaries. |
| Uniform bounds | One fixed `K`, natural nonnegative costs, exact zero-bound boundary and nil entry. |
| Actual annotations | Returned-tree equality, recursive validity, erasure, reader law, and actual local measured callbacks. |
| Observation transport | Existing additive homs and bind compatibility; product projections preserve actual callback values. |
| Source model | Literal right association retained, both recursive appends charged, positive helper tariff kept explicit. |

The core belongs under `Applications/Resources`; clients and cross-component
compositions belong under `Examples` in accordance with ADRs 0001 and 0010.
The public root imports `Examples.TreeFoldObservations`, whose closure includes
all new modules. No new callback class, reachability record, tree-count
carrier, source translator or cost-only evaluator is introduced.

Outside this unit are a source cost translator, all-tree inorder
left-mass/asymptotic theory, suffix-accumulator execution and its
closure-invocation bridge, AVL `debal` and `debal2`, Braun splice/forest
algorithms, list balancing, selective search and merge, arbitrary
history/subtree machinery, and physical sharing or storage analysis. All
original book obligations remain mandatory in their owning chapters or
separately frozen shared follow-ups. This exclusion list does not require a
particular auxiliary statistic or a new general translator/history framework
beyond those source obligations. A function-valued fold measures its
construction under its declared model, not later invocation. A value-level
fold/map equality does not pay for an erasure pass or establish a one-pass
conversion.

The recovered original definitions and theorem statements are retained.
Compilation repairs make the measured algebra and constructor types explicit,
qualify overlapping names, and stage the ordered-trace simplification. The
additional general `cache_pair` lemma replaces an expensive concrete unfolding
in the sample proof; it does not weaken that sample's claim.

Source assessments and this statement review do not alone establish kernel
checking, proof audit, final review or acceptance. The checkpoint review
record retains the exact candidate, coverage of each check, independent review
outcomes and correction history. Chapter and whole-library acceptance remain
separate from this focused unit.
