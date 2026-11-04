# Demand, retained dependencies and cleanup

Research for [#273](https://github.com/VladimirMarko/conaled/issues/273), using
repository base `50cdd4b3cf78e04c245f0d90a3d252ed91aaa2a6` and the issue requirements
updated 2026-10-30. Continue separate treatments of demand, heap accessibility,
resource accounting and reversible cleanup. There are useful compatibility
questions between them, but the cases below do not justify one new calculus or
a duality between laziness and garbage collection.

All candidate relationships and hypothetical cases below are paper-only
specifications and calculations. Existing Lean declarations are cited as local
contract evidence, not as proofs of the new proposals. No formal implementation,
benchmark, physical experiment or external proof-artifact replay was performed.

## Primary accounts and their commitments

Discovery began with what a future use demands, what a suspended computation
retains, and what licenses reuse of storage. Local APIs were inspected afterward.
The sources answer different parts of that question:

| Primary account | Semantic commitment and applicable evidence | Missing bridge for this question |
|---|---|---|
| [Mariño, Herranz and Moreno-Navarro, *Demand Analysis with Partial Predicates*, §§3–5](https://arxiv.org/pdf/cs/0602008) | Partial predicates express demanded definedness; demand equations support sound analysis in the stated functional-logic setting. Correlated demands can lose precision when approximated by the selected set constraints (§5.2). | Demanded definedness does not specify ownership, heap reachability or a reclamation event. |
| [Karkare, Khedker and Sanyal, *Liveness of Heap Data for Functional Programs*, §§2 and 5](https://arxiv.org/pdf/cs/0703155) | Future uses of access paths distinguish live links from reachable dead data in a first-order eager language. Safe nullification also needs alias and availability analyses. | Its language is not a lazy heap with suspended environments; those roots and forcing behavior need separate treatment. |
| [Launchbury, *A Natural Semantics for Lazy Evaluation*, §§3, 6.2–6.3](https://launchbury.blog/wp-content/uploads/2019/01/semantics-of-lazy-evaluation.pdf) | Heap bindings make sharing explicit. Collection uses reachability from both the current expression and active names; §6.2 says collection does not preserve whole-heap denotation and needs a separate equivalence proof. Cost accounting is an additional extension. | Value semantics alone cannot establish a space bound. The GC extension is not already certified by the preceding value-correctness theorem. |
| [Atkey, *Amortised Resource Analysis with Separation Logic*, §§3.4–3.5](https://arxiv.org/pdf/1104.1998) | Mutable heap assertions and consumable resource assertions compose through separated heap/resource portions. Soundness preserves a bound on consumed plus available resources. Locality supports a frame argument; the presented procedure-call rule carries it implicitly. | Consumable credits are not automatically current live bytes or clean quantum workspace. Select the resource model and prove its operational connection. |
| [Bennett, *Logical Reversibility of Computation*, pp. 525–529](https://worrydream.com/refs/Bennett_1973_-_Logical_Reversibility_of_Computation.pdf) | Retain computation history, copy classical output, then reverse the computation to restore intermediate storage. Input and output remain. | This licenses cleanup using retained information, not erasure of arbitrary source state or reclamation through unreachability. |

Breitner's [formalization of Launchbury correctness and adequacy](https://isa-afp.org/entries/Launchbury.html)
provides later machine-checked semantic evidence. This assessment does not infer
from it a certified collector or space theorem for our candidate schedules.
The originally supplied Chalmers and Princeton source URLs were inaccessible;
the table links the author's Launchbury copy and a scan of Bennett's original
article. The scan's mathematical construction, not a secondary account, was read.

## Distinct carriers and candidate relationships

The following definitions specify possible comparison boundaries. They are local
proposals, not claims that the sources prove a common theorem.

**Observation.** Fix a semantic carrier `V` and a family `O` of permitted maps
`o : V → A_o`. Define `v ≈_O w` when every permitted observation agrees.
A representation `S` supplies a meaning map `m : S → V`. Replacing `s` by `s'`
requires `m(s) ≈_O m(s')`; this relation says nothing about their storage. For
partial computation, replace returned values by a domain or behavior carrying
termination/divergence explicitly. Comparing only results on terminating runs
would wrongly validate an implementation that never returns.

A later client `c : V → W` preserves this equivalence for observations `P` only
if every `p ∘ c`, for `p ∈ P`, is respected by `≈_O`. For example, parity
observations cannot justify a later client that reads the first element. Merely
retaining the old equation names does not discharge this extension condition.
For effectful clients, state and trace observations must be included instead of
assuming the total-function condition suffices.

**Dependence of evaluation on inputs.** For partial semantic carriers `D,E`, a
computation `f : D → E`, and an output test `q : E → {⊥,true}`, the exact pulled
back test is `q ∘ f : D → {⊥,true}`. Composition satisfies
`q ∘ (g ∘ f) = (q ∘ g) ∘ f`. An implementable demand analysis needs a specified
abstract domain and sound approximation of that test. This compositional law
concerns definedness, not addresses. A dependency map from a closure's environment
to addresses is extra representation data. No map from semantic demand alone
to the exact set of retained heap cells is proposed.

**Accessibility.** Let `H : Loc ⇀ Cell` be a finite heap, with explicit pointer
edges, and let `R ⊆ Loc` contain all roots held by the expression, suspended
continuations, handles and admitted external readers. `reach_H(R)` is the least
edge-closed superset of `R`. Restriction `H ↦ H|reach_H(R)` removes inaccessible
cells. For a memory-safe sequential language without address fabrication,
finalizers, weak-reference observations or hidden roots, an intended collector
proof relates states that agree on their rooted reachable graphs, possibly up
to address renaming. It must preserve permitted future behavior and safe
allocation; whole heaps need not be equal. This is a proof obligation, not a
collector implemented here. Dropping one alias does not remove other roots.
A pointer returned to a caller becomes part of the interface and its root set.

**Retention schedules.** For one fixed machine and input, let `Sched` contain
legal executions with materialize, use, retain, release and recompute events,
plus a named state and dependency version at every boundary. A recompute event
must read dependencies with the specified original meaning, not merely addresses
that have since been reused. Interpret a schedule by observable behavior `B(σ)`
and a resource trace `r(σ)`: work, owned cells and live sizes at every event.
Define `σ ≈ σ'` by equality of admitted behavior including termination; compare
resource traces separately. Define a budgeted refinement only after fixing the
work bound and storage bound and proving both schedules legal. Equality of
`B` does not imply either resource bound, and smaller work and smaller storage
need not order the same pair of schedules.

For composition with a client, schedules must return related semantic states
**and** an interface invariant describing live outputs, handles and retained
recomputation inputs. Each possible subsequent request must be matched while
maintaining that invariant. A finite stuttering simulation needs a progress
condition if silent work could continue forever. This interface obligation is
stronger than equality of the first returned value; it prevents the gap-client
failure below. It does not assert full abstraction or a universal schedule model
for all the cases.

**Cleanup.** Reversible scratch has another carrier. In the function instance,
let `S` be retained state and `A` the whole workspace state; initialization is
`i : S → A`. Let `C,U,D : A → A` be compute, use and undo, and let `f : S → S`
be the independent intended output. The obligations are
`D ∘ C ∘ i = i` and `U ∘ C ∘ i = C ∘ i ∘ f`; they yield
`D ∘ U ∘ C ∘ i = i ∘ f`. The actual local
[`cleanup_correct`](../../Applications/Uncomputation/Core.lean) already proves
this compositional equation under its categorical associativity laws. The
inverse need only act correctly on admitted initialized states. A heap collector
has no corresponding inverse-on-initialization obligation, and a pointer graph
alone cannot establish this use compatibility.

No pair of contravariant functors, inverse correspondence or involution relating
lazy evaluation and collection has emerged. Backward demand propagation and
forward execution compose, but reversing the direction of information flow is
not itself a duality theorem.

## Five independently specified cases

These fixtures choose observable behavior and a resource model before comparing
implementations. Counts refer to the stated toy model, not Lean allocation or
measured runtime memory.

### 1. Unused delayed computation

Specification: return the integer 7 without inspecting a computation `e`, even
when `e` diverges. In a non-strict language, `let x = e in 7` meets that task;
an eager implementation that forces `e` can fail to return. In a concrete lazy
heap, installing a binding may allocate a closure before it is used. Assume one
closure cell with an environment of references. The schedule can perform zero
steps of `e` while owning that cell until collection or a valid dead-binding
elimination removes it. Thus absence of demand establishes neither zero allocation
nor immediate reclamation. An optimizer that omits the binding entirely needs
its own preservation argument under this observation contract.

### 2. A thunk retains a large dependency

Specification: after a gap, answer the sum of a finite immutable array `a` of
length `N`; addition is total and exact in this fixture. In an explicit heap,
root `k` points to a thunk `sum a`, whose environment points to all `N` array
cells. Assume no other array roots. Before forcing, reachable size is `N+1`
cells under this representation, even if no element is demanded during the gap.
An alternative forces the sum now, updates `k` to a scalar and drops the array
reference. After a collection, it retains one scalar cell, under the additional
assumption that the scalar representation contains no array pointer.

The two schedules answer the same later request. They differ in timing of `N`
element reads and in gap retention. Eager forcing is not admissible if the
computation may diverge and the eventual client might never force it. Returning
a closure that still mentions `a` would also invalidate the claimed saving.
This case tests a representation and a demand policy together.

### 3. Repeated uses with a gap client

Specification: two requests return `f(d)` in order. `f` is pure and total;
`d` remains immutable and available throughout. Let computing the result take
`c > 0` work units and let retaining it take `s > 0` cells. Charge dependency
storage in both schedules equally and omit the identical output-copy costs.
Retain computes once, costing `c`, with `s` cells live in the gap. Recompute
computes twice, costing `2c`, with zero result cells live in the gap; it still
retains `d`. Neither schedule dominates on both work and storage. If `d` mutates,
a fresh computation may answer a different question; a snapshot, version proof
or immutable copy is required.

A discriminating composition inserts a client that needs `b > 0` unrelated cells
only during the gap, releasing them before the second request. Assume computing
`f` has peak `s` beyond the shared dependency baseline, and returned answers have
already been copied to equally accounted external storage. Retain then needs
peak `s+b`; recompute needs `max(s,b)`. Standalone both peak at `s`. Consequently,
equality of results and standalone peak counts does not compose into equality
of combined peaks. This is a local counterexample to a proposed scalar-summary
law, not an optimal scheduling theorem.

Resource traces, or summaries at every client interaction boundary, repair that
loss. For straight-line segments without interleaving, a useful toy summary is
`(w,δ,l,h)`: work, net live-size change, minimum and maximum prefix live-size
change, including the empty prefix. Composition is
`(w+w', δ+δ', min(l,δ+l'), max(h,δ+h'))`. Starting capacity and nonnegative live
size must be checked against those extrema. This arithmetic summary still loses
which cells are owned and which aliases survive. It cannot alone certify safe
release or hide the gap as if no client ran there.

### 4. Inaccessible ordinary storage

Specification: a client reads the cell rooted at `r`; a separate allocated cell
`u` has no path from any admitted root, including the client's continuation.
The machine can remove `u` and reuse its address if its allocation and memory
safety rules validate that step. The old bits need not be reset to zero. This
permits reclamation without recovering the construction history or inverting any
operation. Conversely, a still-rooted but never-read cell can be semantically
dead for this client while a tracing collector conservatively retains it.

Add an external handle to `u` and the proposed collection becomes invalid. That
handle is a root even when absent from the current expression. Add pointer-identity
or finalizer observations and the earlier behavioral equivalence also needs
revision. Non-injective observation, such as returning only a pair's first field,
does not perform any of these root or storage changes.

### 5. Reversible scratch with preserved or mutated dependencies

Specification: on bits `a,b,y` with scratch initially zero, return
`(a,b,y XOR (a AND b))` and zero scratch. The independent output includes the
original inputs and arbitrary caller output. Compute the AND into scratch,
XOR scratch into `y`, then undo the computation. The existing
[`and_oracle` and `oracle_clean`](../../Applications/Uncomputation/Oracle.lean)
establish that contract; their general statement supplies the useful reuse.
For a smaller negative fixture, compute `t=a` from `(a,t)=(false,false)`, mutate
`a` to true, then undo using the new control. Scratch becomes true.
`mutated_control` checks exactly that failure. An inverse operation exists, but
the intervening use no longer satisfies the required compatibility premise.

[#264's schedule evidence](../../Applications/Uncomputation/Schedules.lean)
separates retaining scratch through two uses from uncomputing and recomputing.
`gap_workspace` records one live scratch bit versus zero at the gap; both
schedules peak at one and finish clean. `execute` checks zero-state release,
owned gate support and caller-wire exclusion. Those conditions are stronger than
ordinary heap unreachability. The coherent/reference and discard examples in
[the implementation record](clean-ancilla-implementation.md) also rule out replacing
joint-state preservation by agreement on basis probabilities. No quantum cloning,
physical erasure, energy saving or thermodynamic conclusion follows here.

## Local fit and author obligations

| Existing route | What can already be reused | Additional obligation exposed here |
|---|---|---|
| [Measured computations](../../Applications/Resources/Measured.lean) | Separate returned values from additive observations; sequencing and erasure laws | Peak storage and named ownership need suitable observations/state; `same_value_different_cost` already defeats value-only accounting |
| [Memoization assessment](elegant-memoization-fit.md), #263 | Representation laws and a separate retained-table/workload contract | Delay does not prove sharing or a cache bound; hit/miss and eviction proofs must describe retained state |
| [Retention ownership](../../Applications/Durability/RetentionOwnership.lean) | Affine handles, reader exclusion and restart fencing distinguish loss of access from reuse | A local heap model must supply all its roots; do not import service-specific crash and publication rules without a client |
| [Clean ancillas](clean-ancilla-implementation.md), #264 | General cleanup equation, typed gates, zero release, coherent observations and schedules | Preserve dependency meaning and admissible use; no need to rebuild this theory |
| [Finite constructor/observer composition](compositional-constructor-observer-laws.md), #268 | Local semantic compatibility of finite composites | No theorem about heap lifetime, demand, scheduler progress or physical storage follows |
| Observation equivalence, #267 | Specify which later clients may distinguish states | Enlargement of observations or retained handles requires new compatibility evidence |

For ordinary pure code, an author already states the value function and can use
it directly. A schedule proof adds the workload, dependencies and their versions,
allocation/release semantics, outputs owned by the caller, and the metric being
bounded. A collector proof adds roots and alias discipline. Reversible cleanup
adds initialization, inverse and use compatibility. A proposed common wrapper
would require all these concepts or optional fields whose interactions still
need proofs. It would not remove the mathematical obligations. This is a design
assessment, not a measured usability result or a claim that Lean cannot encode
such an interface.

## Recommendation and remaining research

Keep the separate theories and their direct interfaces. The useful common
question is which future observations and ownership obligations a representation
change must preserve. It is already expressible through explicit preservation
relations; the five cases do not identify a missing universal abstraction.
Close this bounded research lead with that conclusion rather than making it a
prerequisite for #263, #264 or #267. #235 owns reassessment if a concrete client
exposes repeated adapter proofs; #174 owns a representation/workload comparison.

A later experiment would be justified by an actual memo-table client that can
release a result during a gap while retaining a reproducible dependency. Its
separate spec should fix a finite acyclic computation, immutable inputs, two
requests, one gap allocation, an explicit heap/ownership machine, and independent
value and resource observations. Compare retain and recompute against the same
answers, prove validity under client composition, and retain the `s+b` versus
`max(s,b)` discriminator. Reject dependency mutation without a snapshot proof,
release through a surviving alias, and replacement of peak/live traces by total
allocation. This identifies a testable target if needed; no implementation is
selected or started by this research.

The search covered demand predicates, eager heap liveness, lazy sharing,
separation/resource assertions and reversible history cleanup. It did not assess
concurrent tracing collectors, weak-memory reclamation, probabilistic demand,
full checkpoint pebbling algorithms, dependent ownership systems, physical
measurement instruments or device thermodynamics. Hofmann–Jost's heap-analysis
paper was discovered but its full PDF was unavailable in this run; no result
beyond the accessed primary sources is attributed to it. These omissions limit
claims of optimality or completeness, not the explicit failures in the fixtures.

Documentation validation checks relative links, local declaration references and
whitespace. No new Lean statements require a proof audit. Independent Standards
and Spec reviews and the coordinator's recovered-intent assessment remain the
acceptance gates for this candidate.
