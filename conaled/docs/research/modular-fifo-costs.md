# Modular FIFO resource bounds

Issue [#211](https://github.com/VladimirMarko/conaled/issues/211) extends the
[shared FIFO client](abstract-fifo-client.md) with public operation budgets and
initialization credit. One theorem applies to ordinary lists and valid symmetric
lists. Client proofs do not name either implementation's potential formula.
The implementation uses ordinary Lean propositions and measured transitions;
it does not implement a new cost language or enforce a modal phase distinction.

## Public contract and retained accounting

[FIFOContracts](../../Applications/Resources/FIFOContracts.lean) leaves the
behavior-only `AbstractFIFO.Ops` interface unchanged. `Instrumentation` supplies
measured enqueue/delete transitions and an erasure theorem for every command
and state. `Accounting` separately supplies a simulation to the independent
list interpretation and an existential accounting witness. The witness must
satisfy two obligations:

```text
initialized q credit → potential q ≤ credit
cost(step c q) + potential(next c q) ≤ potential q + profile c (decode q)
```

The public profile depends only on the command and decoded list.
`abstractBudget` sums it along the independent list trajectory, not a trajectory
chosen by the cost model. `budget_abstract` identifies that sum with the existing
concrete budget using behavior preservation and erasure.

`client_bound` states, for every command word and initialized state,

```text
cost(run commands q) ≤ credit + abstractBudget profile commands (decode q).
```

Its statement contains no potential parameter or formula. It opens the
implementation certificate internally and invokes
[Resources.run_potential](../../Applications/Resources/Potential.lean), retaining
both boundary potentials before dropping the nonnegative final term. It does
not reproduce the telescoping induction. `Accounting` exposes the existence
and obligations of a potential; it does not expose the implementation's chosen
formula as a client parameter. The symmetric witness is a private definition,
but this is proof-interface abstraction, not protection against arbitrary Lean
reflection or an AFAT sealing modality. `symmetricInitialized` is a public
predicate, and `symmetric_empty_initialized` supplies its zero-credit empty case.

`abstractBudget_append` and `sequential_bound` use the existing budget and
measured-run composition laws. A composed word starts with one initialization
credit. The proof applies the retained-potential theorem to the whole trajectory;
it does not restart accounting at the intermediate state or sum two independent
initialization allowances. Final potential can finance later commands because
`run_potential` retains it at every boundary. Persistent branches require a
separate splitting discipline, as the checked counterexample below shows.

`reobserved_bound` changes resource observations along an additive map
`Nat →+ Nat`. `reweight_run` transports sequencing and a separate monotonicity
hypothesis transports the inequality with `reweight_bound`. Arbitrary maps or
nonmonotone observations receive no such bound. The concrete doubling example
changes units of structural work; it is not a change in machine runtime.

## Actual operations and client obligations

`appendRun` recursively constructs the appended list, charging one visit per
cons and one for the terminal nil. `appendRun_exact` proves both the resulting
list and exact cost `length + 1`. Delete uses actual `List.tail` with cost one.
The list public profile is therefore `length + 1` for enqueue and one for
delete. Its accounting witness is zero, so any nonnegative initial credit is
admissible; examples choose zero.

The symmetric realization adapts
[SymmetricCosts.execute](../../Applications/Resources/SymmetricCosts.lean),
including its instrumented tail rebalancing. It neither assigns an unrelated
cost after erasure nor copies the existing rebalance recursion. Its state type
is `{q // Inv q}`; operation closure and abstraction use the existing FIFO
simulation. This makes the potential inequality universal on the actual state
type. The private witness is twice the existing imbalance potential, and
`execute_work_potential` supplies the public charge eight per command.
Imported states must have their stated initial credit; only empty construction
is automatically initialized with zero. No reachability from empty is required
beyond the symmetric representation invariant.

The modeled observations count the declared structural visits. Neither
implementation measures elapsed time, Lean allocations, or garbage collection.
The final head observation is explicitly **uncharged**: the workload cost covers
enqueue and delete only. Behavior erasure and the common endpoint observation
remain separate from upper bounds; exact costs are not identified merely
because behaviors agree.

[Checked clients](../../Examples/FIFOContracts.lean) author `ordinary_bound`
once and instantiate it for both realizations without unfolding potentials.
The caller supplies accounting evidence, a command word, a state and its public
initialization certificate. The representation author proves step erasure,
behavior simulation and the per-step/initial accounting obligations. No internal
syntax or compiler target is required. The opt-in syntax route from #210 remains
behavior-only; this work does not assert a cost-preserving compiler theorem.

The word enqueue 1, enqueue 2, delete, enqueue 3 leaves `[2,3]` and observes head
2 in both realizations. The exact work is six list visits versus nine symmetric
visits. The same public theorem yields the list trajectory budget and the
symmetric bound `8 * commands.length`. Further checked examples compose arbitrary
words, double the resource observation, and initialize a nonempty valid queue.

## Noninterference and failure cases

`cost_noninterference` quantifies over every command word, initial state and two
instrumentations of the same operations. Erasure makes their final head
observations equal. Together with the separate behavior simulation, this also
explains agreement between the two concrete representations. It says nothing
about a function allowed to read the cost projection. `paidObservation` is a
Boolean counterexample: an actual charged enqueue and a zero-cost
instrumentation have identical state transitions but different answers to
whether any cost was paid.

A second checked failure starts from the valid symmetric queue
`([0], [1,2,3,4,5,6,7])`, with initialization credit twelve. A delete costs eighteen,
within its public allowance `12 + 8`. Two independent deletes from that same
persisted state cost thirty-six, exceeding `12 + 2*8`. Duplicating the immutable
queue does not justify counting its credit once while spending it twice. The
sequential theorem threads the actual resulting state and does not permit this
branching substitution.

## Relation to Harper's frameworks and remaining scope

[Calf](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf) distinguishes behavior
from cost through an internal phase distinction and proves noninterference for
its language. This example reconstructs only the consequence for the explicitly
restricted operation-only word client. Lean functions in general may inspect
measured costs, as the negative example demonstrates.

[Decalf](https://arxiv.org/abs/2307.05938v4) compares effectful programs through
intrinsic preorders; its bounds may themselves be programs. Here the order is
ordinary natural-number inequality on an external structural resource
observation. No intrinsic ordering on all terms or augmented-simplicial model
has been reconstructed.

[Abstraction Functions as Types](https://arxiv.org/abs/2502.20496v4) internalizes
abstraction functions and uses phase structure and sealing for modularity.
The present contract recovers a reusable bound whose caller omits concrete
potential formulas, using conventional Lean interfaces. It does not supply
AFAT's linguistic guarantee against access to private implementation details.

[Potential Functions as Types](https://arxiv.org/abs/2607.08547v2) combines
abstraction and potential in types and introduces credit/debit operations and
the graded language Giralf. Here a certificate explicitly supplies the local
inequality, and existing potential telescoping proves the workload bound.
There is no Giralf interpretation, automatic inference, full credit modality,
or general persistent-sharing theorem.

[#174](https://github.com/VladimirMarko/conaled/issues/174) retains data-structure
scope, [#177](https://github.com/VladimirMarko/conaled/issues/177) retains the
general resource assessment, and [#193](https://github.com/VladimirMarko/conaled/issues/193)
retains FRP and numerical consumers. This example uses their existing resource
machinery without requiring those umbrellas to close. A new resource consumer
can reuse the contract once it supplies erasure, behavior and local accounting.
Persistent clients need an explicit credit-splitting contract; a cost-aware
internal compiler needs a separate preservation theorem before either can be
claimed as an extension of this result.
