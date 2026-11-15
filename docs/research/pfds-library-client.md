# A persistent FIFO client with complete declared work

[Issue #564](https://github.com/VladimirMarko/conaled/issues/564) connects the
existing FIFO implementations to persistent histories and resource accounting.
The client builds an empty queue, executes one prefix, retains that version,
executes two suffixes independently from it, and observes both heads. A suffix
never starts from the other suffix's result. This is a small application of the
existing interfaces, not another queue implementation.

The public entry points are
[`fromEmpty` and `execute`](../../Applications/Resources/Persistent/FIFOClient.lean).
They accept `FIFOContracts.Instrumentation` and ordinary FIFO command lists.
`fromEmpty` includes initialization; `execute` starts with an already supplied
version whose construction is outside that invocation. The returned record
retains the prefix version, both resulting versions, and both observations.
The [checked clients](../../Examples/PersistentFIFOClient.lean) compare
`listMeasure` with `symmetricMeasure` through these entry points.

## Behavior and tariff

`observations` reuses `AbstractFIFO.Simulation.run_preserves` and `client_eq`.
It proves the meanings of all three retained versions and the two endpoint
observations against independent ordinary-list execution, for arbitrary command
words and any representation supplying the simulation. Persistent reuse here
means that both branches can read the same immutable input version. It does
not assert that Lean retains a particular pointer or memoizes either branch.

The declared tariff accounts for every operation of this client:

- Empty-queue initialization costs one unit, once.
- List enqueue executes recursive append and charges every cons and terminating
  nil visit. List delete costs one unit, including deletion from empty.
- Symmetric enqueue costs one unit. Symmetric delete uses `tailRun`: one unit
  for its outer dispatch, with the rebalance case additionally charging the
  complete length, split and reverse traversals, including their terminal
  visits. The exact singleton-front cost is twice the rear length plus four.
- Each endpoint head costs one unit, including an empty result.

Pairing results, retaining an immutable version, command-list dispatch and
natural-number arithmetic have zero weight in this structural tariff. All
three queue runs are nevertheless executed, and both observations are charged.
The model measures these specified structural operations. It does not count
host allocation, garbage collection, arithmetic bit costs, physical sharing,
or elapsed time. Those are distinct observations requiring another execution
model and correspondence; they are not estimated by the potential.

Two checked workloads show why representation choice depends on the client:

| Workload from empty | List work | Symmetric work | Observations |
|---|---:|---:|---|
| Enqueue 1, 2, 3, 4 once; two empty suffixes | 13 | 7 | `(some 1, some 1)` |
| Enqueue 1, 2 once; delete independently in both suffixes | 8 | 17 | `(some 2, some 2)` |

The first row includes list append visits `1 + 2 + 3 + 4`, versus four
symmetric enqueue visits, plus initialization and two heads. In the second row,
each symmetric delete rebalances a rear of length one and costs six. The list
prefix costs three and each list delete costs one. Both rows use actual
measured runs, not an independently invented estimate.

## Accounting across the fork

`execute_cost` retains the cost of the prefix once and both suffix costs.
`symmetric_bound` applies the existing local work/potential law to each actual
trajectory. Writing `P` for twice the symmetric-list imbalance, it proves

```
work + P(left result) + P(right result)
  ≤ P(input) + P(retained prefix) + 8 × total command count + 2.
```

The extra prefix potential cannot generally be dropped: both strict branches
can spend it. `symmetric_fromEmpty_bound` includes the initialization unit and
uses the empty input's zero potential. `signed_boundary` uses the shared
`budget_amortized` theorem, whose proof is the generic mapped exact-potential
law also exercised by `Examples/MappedPotentialAccounting.lean`. It retains
signed charges and both boundary terms; this identity alone is not a runtime
bound or a claim that charges are nonnegative.

The loaded-queue case has front `[0]` and rear `[1, 2, 3, 4, 5, 6, 7]`, whose
ordinary meaning starts `[0, 7, 6, …]`. Its initial credit is twelve. Two
independent deletes each cost eighteen and the two heads cost two, for a total
of thirty-eight. Counting the initial credit once with two eight-unit charges
and the heads gives thirty, which is insufficient. Equal branch observations
and equal resulting versions do not justify charging a rebalance once.
Construction of this preexisting input is deliberately not included in that
counterexample; the from-empty workloads above include their whole setup.

## Histories and realization

The three block occurrences have a small `Persistent.History` quiver: the
prefix supplies an argument to each branch, and neither branch supplies an
argument to the other. `use_input` connects each edge to the actual measured
block input and output. The complete finite scope is history-closed, and the
prefix lies in both branch histories. Equal command words do not identify
operation occurrences.

`realization_cost` prices these actual blocks with the shared
`Persistent.Realization` executor. The prefix includes initialization and each
branch includes its head. Shared debit support is empty because this strict
client has no memoized evaluation; all execution work is unshared. The theorem
proves equality with the actual client's total tariff. It does not obtain a
sharing discount merely by associating an identity with an immutable value.
Physical immutable-cell constructions remain in the existing PFDS persistence
library; this client does not replace or duplicate them.

## Remaining connections and coverage

The suspension libraries retain stronger, different evidence.
`Suspensions.Core.Observation.body_realization_observe_cost` connects distinct
body addresses to actual body-entry occurrences under nonrepetition premises.
`Suspensions.Pure.History.BodyHistory` records executed pure prefixes, and its
completion theorem constructs a finite pure evaluation. Neither theorem prices
all transitions, all work inside a primitive, or allocation. Connecting a
memoized queue or delayed computation to a complete cost model still requires
that correspondence, including cache lookup/write and body costs. This client
establishes no arbitrary persistent amortization theorem.

The remaining architectural work belongs with
[#174](https://github.com/VladimirMarko/conaled/issues/174) and the textbook
integration effort [#558](https://github.com/VladimirMarko/conaled/issues/558):
choose an actual memoized consumer before extending shared-debit accounting;
add explicit allocation/representation evidence if a consumer needs physical
sharing; and assess representation policies against declared workloads and
costs. No universal persistent-container interface is adopted here.

Coverage remains exactly as recorded in the preserved ledgers:

- [Common coverage, PFDS section and evidence locators P1–P10](../history/textbooks/checkpoint-012/books/common/COVERAGE.md)
  records 83 book exercise headings, six in Chapter 2 and **77 later headings
  unproved**. This client closes none of those later exercises.
- [Book/thesis union coverage](pfds-union-coverage.md#book-exercise-navigation-and-acceptance)
  retains per-chapter counts and twelve numbered theorem/lemma headings.
  Subparts, algorithms and unnumbered arguments are additional obligations.
- [The preserved mixed ledger](../history/textbooks/checkpoint-012/books/pfds/records/research/coverage/coverage.json)
  has 135 non-exhaustive rows and is not a percentage denominator. The common
  ledger's P6–P8 locators retain the later chapter readiness and paper work.
- [Persistence](pfds-persistence.md), [suspensions](pfds-suspensions.md), and
  [pure suspensions](pfds-pure-suspensions.md) retain their own source and
  acceptance boundaries. Current validation of this client does not confer
  whole-chapter acceptance on those historical candidates.

The paper records, coverage denominators and historical wrapped-output trees
are unchanged. No second active copy of that historical source tree is created.
