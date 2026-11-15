# Observing queue peek: staged traversal counterexample

This is a small cross-cutting preparation artifact for the VFA queue discussion.
It does not complete the ADT chapter, implement the full queue interface, or
claim integrated conaled acceptance. The parent implementation/review loop
owns any eventual integration.

## Source and claim boundary

The reference is *Verified Functional Algorithms* 2.1, release header
`2026-08-24 10:11`, `ADT.v`, module `TwoListQueueAbs` at lines 1078–1141.
The downloaded chapter SHA-256 is
`87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2`.
The public chapter is <https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html>;
the source distribution is
<https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz>.
These URLs move; the version/hash inventory in `work-state/source/` identifies
the inspected release. No copy of the chapter is included in this artifact.

Relevant source locations:

| Source location | Relevant obligation |
| --- | --- |
| ADT.v 1074–1076 | Prose claims amortized constant-time performance for the implementation. |
| ADT.v 1081–1086 | A state is `(front, back)`, denoting `front ++ rev back`. |
| ADT.v 1088–1089 | The empty state has two empty lists. |
| ADT.v 1097–1098 | Enqueue conses the value onto the back without normalizing the front. |
| ADT.v 1111–1120 | Peek reverses the back when the front is empty; its result is only an element, not a replacement queue. |
| ADT.v 1131–1134 | The extensional peek specification observes the head of the denoted list. |

The official [Rocq 9.0 standard-library List documentation](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Lists.List.html)
defines `rev` by empty-list and `rev tail ++ [head]` cases. The same page
separately defines the tail-recursive `rev_append` / `rev'` variant and proves
their value equivalence. The parent verified those primary-source definitions
while this preparation was implemented. The costed structural recursion here
therefore matches the direct `rev`/append equations used by the VFA source;
using a linear accumulator reverse instead would require an explicit
implementation change and its refinement proof.

The instrumented code models visits to nonempty list constructors while
performing structural reverse and append. Its result is proven equal to the
source's value specification. It deliberately does not identify the complexity
of Lean's optimized `List.reverse` implementation with the complexity of a
particular Rocq evaluator or extracted target.
The counterexample needs only that a full reversal visits every back-list
element, and therefore remains a counterexample for a linear full-traversal
reverse. There is no claim about runtime, allocation, garbage collection,
compiler optimization, laziness, or an external memoization cache.

## Definitions and independent specifications

`QueuePeekCost.lean` uses namespace
`Applications.Resources.QueuePeekDraft`; checked clients are in
`Examples.QueuePeekCostDraft`. It imports
`Batteries.Data.List.Lemmas` and the actual
`Applications.Resources.Potential` stack. The queue's element type is generalized to any
`Type u`, with explicit default and enqueue values; source-specialized examples
use `Nat`.

There are three distinct layers:

1. **Values and reachable states.** `denote`, `empty`, `enqueue`, and `peek`
   give the source's relevant semantics. `peek_relate` proves head agreement.
   `EnqueueReachable` records actual finite sequences of source enqueues, and
   `enqueueCopies_reachable` plus `enqueueCopies_shape` prove that an empty
   front with arbitrarily large nonempty back is reachable from empty. These
   are not arbitrary invalid representation states: the source explicitly
   omits a queue representation invariant, and enqueue itself creates them.
2. **Independent size bound.** `peekReversalInputBound` reads only the
   representation: it is back length for empty front and zero otherwise. It
   does not inspect an instrumented cost or assume a polynomial answer.
3. **Instrumented recursions and refinement.** `appendMeasured` recurses over
   its first list, adding one for each nonempty node. `reverseMeasured`
   recursively reverses the tail, invokes measured append, and charges the
   current nonempty reversal input node. Their output projections are proven
   to be ordinary append/reverse. `peekMeasured` follows the source's three
   branch cases and invokes the instrumented reverse only in the relevant
   branch. Its projected value agrees with both `peek` and the denotation.

The observation does not count nil tests, branch dispatch, reading the head,
pair construction, or enqueue. It does count append's first-list visits in
the chosen structural reverse. In particular, the checked recurrence is

`cost(reverseMeasured (x :: xs)) = cost(reverseMeasured xs) + xs.length + 1`.

This equation is a theorem derived from the instrumented algorithm and erasure
of its recursive value. It is not the definition of the measured result. The
general counterexample uses the weaker proved bound
`xs.length ≤ cost(reverseMeasured xs)` and therefore does not depend on
deriving a closed quadratic cost formula.

## Repeated observations and potentials

`peekStep d q` converts the measured observation into a state/observation
transition `(q, cost)`. It preserves the whole queue state exactly; no reversed
front is installed. `runPeeks` recursively threads the actual result of that
transition. `runPeeks_state` proves the final queue is the initial queue.
`runPeeks_cost` derives total observation
`repetitions * cost(peekMeasured d q)` by induction over the executor.

The useful semantic conclusion is quantified, not just a timed example:

- `no_uniform_local_charge`: for every potential `Queue α → Nat` and any
  fixed default/enqueue value, no constant charge bounds every reachable
  observing-peek step using conaled's local inequality
  `cost + potential(next) ≤ potential(current) + charge`.
- `runPeeks_potential_iff`: the corresponding repeated-step inequality with
  both boundary potentials is equivalent to the same inequality without the
  potentials, because initial and final queue states are equal.
- `repeated_peeks_exhaust_initial_credit`: even the weaker bound that discards
  final potential cannot save a uniform charge. Given any state-only potential
  and proposed charge `c`, choose the reachable queue obtained by enqueuing
  `c + 1` copies, then perform `potential(q) + 1` peeks on that fixed queue.
  The proved traversal lower bound exceeds all initial potential plus
  `c * repetitions`.

Thus the issue occurs on a single ordinary sequential trajectory. It does not
depend on branching persistence, sharing queue versions, or omitting an
initial-potential term. The final theorem explicitly allows arbitrary initial
credit and proves enough repeated observations exhaust it.

## Checked concrete clients and boundaries

The file contains connected cases, not stand-alone arithmetic claims:

| Case | Checked result |
| --- | --- |
| Enqueue 4, 9, 2 from empty | Reachable state `([], [2, 9, 4])`; source peek is 4; measured peek is `(4, 6)`; three actual repeated steps preserve the state and observe 18 visits. |
| Empty queue | The requested default is returned and any checked repeated sequence has zero traversal observation. |
| Nonempty front with nonempty back | Peek returns the front head and records no reversal visits, preserving state. |
| Arbitrary stored credit | A concrete three-element back still fails a local charge of 2 even when both boundary potentials are 1000. |
| Back-length potential | A reusable client specializes the general theorem and rules out uniform observing-peek charge with the usual back-length potential. |
| Existing conaled workload and budget | The same reachable three-element enqueue example is executed through `Resources.run`: the observation is 18, the constant-charge budget is 6, and adding initial back-length credit 3 still cannot cover it. The proof consumes the executor bridge and the original checked source example. |

The zero-cost cases are explicitly zero **traversal observations**, not
zero-time runtime claims. The source's dequeue normalizes when it reverses,
so this result must not be transferred to dequeue without analyzing its state
transition. No dequeue definition or unrelated ADT algorithm was ported here.

## Relation to conaled's resource interfaces

The inspected existing files are
`Applications/Resources/Measured.lean`, `Workload.lean`, and `Potential.lean`.
Their relevant APIs are:

- `Resources.Measured α Nat`, definitionally `α × Nat`;
- `Resources.run`, which threads measured state transitions and adds their
  observations in execution order;
- `Resources.run_potential`, with local premise
  `cost + potential(next) ≤ potential(current) + charge`;
- `Resources.run_constant_charge`, retaining both boundary potentials;
- `Resources.run_cost_le`, retaining initial credit after dropping the final
  nonnegative potential.

The first staging revision used cached basic imports because project resource
artifacts were unavailable. The parent later authorized the environment agent
to build the existing `Measured`, `Workload`, and `Potential` targets in the
main checkout. After that successful build, this bounded follow-up imported
the actual interfaces. This subtask performed no project build or main-source
edit.

`runPeeks_eq_resourcesRun` now proves the full pair equality

```lean
runPeeks d n q =
  Resources.run (fun _ : Unit => peekStep d) (List.replicate n ()) q
```

by induction on `n`, using the actual `Resources.run_cons` equation. Both
the final queue and accumulated observation are preserved; this is not merely
equality of projected queue states.

The follow-up also connects the actual potential and budget APIs:

- `resources_exact_accounting` applies `Resources.run_potential_exact` to
  this actual queue transition, with its measured traversal as the per-state
  charge. Its local identity is proved from unchanged state and commutativity
  of natural addition. This legitimate charge depends on the queue; it is not
  falsely presented as a uniform constant amortized charge.
- `resources_peeks_exhaust_initial_credit` transports the existing reachable
  counterexample to `Resources.run` and `Resources.budget`, using the executor
  equality and the existing `Resources.budget_constant` theorem. It retains
  arbitrary initial potential, a positive repetition count, and the reachable
  state witness.
- `resource_workload_observation` is the concrete client in the table above.
  Its transition is explicitly typed as `Resources.Measured (Queue Nat) Nat`.
  The proof uses the original enqueue example and the new executor bridge,
  rather than independently reducing a disconnected workload.

The original measured append/reverse, source-value refinement, lower bounds,
reachability, and potential counterproofs were not changed by these adapters.
`VALIDATION.md` records the follow-up focused-check result and exact current
source hash. Integrated chapter acceptance remains separate. The local
Nat-indexed executor can be removed on eventual integration if consumers are
stated directly for `Resources.run`; retain the value erasure and independent
input-size bound in either presentation.

The reusable generic self-loop arithmetic lemma could live in
`Applications/Resources/Potential.lean` if an integrated client justifies it;
the source-specific queue observer and counterexample belong in a dedicated
ADT example/resource case-study module. The draft namespace is deliberately
not an accepted public API choice.

## Statement review

- The failing bound ranges over states explicitly reachable by the supplied
  enqueue transition; no invalid-state shortcut is involved.
- A value-only observer has unchanged original queue state. The proof does
  not smuggle the reversed list into a hidden next-state component.
- Cost is derived by the measured recursions, with separately proved value
  refinement and a size-only lower bound.
- The potential can be any function to `Nat`, including functions that
  initially assign very large credit. Quantifiers put the candidate charge
  before the adversarial reachable queue and repetition count.
- The no-constant theorem concerns this traversal interpretation of this
  observing API. It does not assert that every extensionally equal program
  must evaluate in the same way, or that normalization/caching in a changed
  representation would fail.
- Only equality, natural arithmetic, and list facts are required; there are
  no order/decidable-equality assumptions on payloads, no admitted proofs,
  no new axioms, and no native decision procedure shortcuts.
- This is assigned implementation preparation, not an independent final
  Standards/Spec review or a chapter-completion certificate.

See `VALIDATION.md` for the exact read-only compiler invocation and file hash.
