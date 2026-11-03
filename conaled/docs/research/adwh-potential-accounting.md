# Potential accounting for actual workloads

Issue #173 reconstructs all named declarations of checkpoint 233's `Timing`,
`Amortized`, and `SymmetricListCosts` modules. Two clients use one shared
measured executor and potential laws: binary writes and symmetric-list charge
and structural work. The [ledger](adwh-potential-accounting-ledger.json) maps all
107 source declarations to checked destinations. No declaration in this scope
is deferred.

## Shared execution and architectural change

`Resources.run` executes each supplied operation on the actual preceding state
using the existing `Measured.bind`. It returns final state and ordered combined
observations. `run_cons` is exactly the source recurrence. `run_append` is bind
composition, `run_state` is the ordinary foldl equation, and `reweight_run`
commutes additive observation maps with execution. None of these laws assumes
commutative addition. The FreeMonoid example checks ordered observations `[1,2]`.

`run_invariant` and `run_value_fusion` let clients reuse invariant preservation
and independent value refinement. The latter uses existing reachable foldl
fusion. `budget` sums charges at the same actual states; it is separate from the
returned cost. It is not a fixed list of charges or an average over inputs.

`Measured.bind` and its composition/value/reweighting laws now allow independent
input, intermediate and output value universes. Previously they forced these
types into one universe. The concrete consumer is the symmetric rebalance:
a measured `Nat` length feeds a measured split of `List α`, then reversal. The
existing erasure-square interface still has its same-universe boundary, imposed
by `Squares.Rep`. Neither square representation was changed. Existing resource
clients and examples are regression targets.

The three source generic execution shapes are not copied as competing public
executors. Counter `advanceWithCost` is shared `run` on replicated unit
operations. Counter `totalCost` is the shared trajectory budget. Their explicit
successor equations preserve the source recurrences. `advance` uses Function
iteration and `iteratePrefix` uses Mathlib `List.iterate`; length, indexing and
membership use its existing laws. These aliases have the source's finite
zero/successor behavior for every seed. No infinite list implementation is
introduced.

## Clients and composed observations

The counter's independent meaning is the least-significant-first place-value
sum. Carry increment writes every changed bit, including the final one when
extending the representation. The exact local identity is
`flipCost bs + ones (inc bs) = 2 + ones bs`. Shared exact telescoping derives
the whole-run identity, retaining both initial and final one-bit potentials.
Canonicality is required only where the theorem states it. Noncanonical Boolean
states still satisfy numeric increment and write accounting.

`advanceSquare` uses the existing measured erasure-square constructor.
`observedCounter` composes it with numeric observation, preserving the write
count. Its independent output is `value bs + n`; its resource observation is
`totalCost n bs`. `numericSquare` also exposes the input numeric interpretation
rather than requiring callers to view the input as an uninterpreted bit list.

Symmetric operation semantics reuse #170. `lengthRun`, `splitRun`, and
`reverseRun` instrument actual recursion, including terminal visits.
`rebalanceRun` sequences them with measured bind. Its work is `2*k+3`; singleton
side deletion adds dispatch, giving `2*k+4`. The source's abstract deletion
charge is only `k`. These measures are kept distinct.

The six operations return actual state and optional selector observation.
A mutation has observation `none`; an empty selector has `some none`.
`measuredStep` obtains both charge and work from one execution. `measuredRun`
accumulates their pair on one state trajectory. Additive projections recover
exactly the separate source charge and work runs. The old source state-equality
contract is also retained.

`observedWorkload` composes the measured workload square with final-head
observation, retaining both totals. This final observation is a semantic
consumer and does not add a counted operation dispatch. To charge a selector,
include `.head` or `.last` in the workload. The workload returns final state and
costs, not a history of selector observations. Local selector contracts are
proved separately.

## Statement review and EDD

Initial obligations were the source recurrences' connection to measured bind,
source iteration's connection to standard finite iteration, and resource
preservation through composed consumers. Checked examples derive the independent
expected conclusions through the public contracts. Straightforward concrete
branch equations supplement those uses; they do not replace the generic proofs.

- Workload contracts quantify arbitrary operation/state/observation types.
  Zero and addition suffice for execution and state refinement; associativity
  and zero laws are required for append/reweighting. The ordered FreeMonoid
  case prevents accidental commutative interpretation. Empty and appended
  workloads exercise the same public laws for the counter and symmetric client.
- Natural potential inequalities use `cost + after ≤ before + charge`.
  `charge_iff_signed` proves equivalence to signed subtraction, avoiding
  truncated natural differences. Exact and inequality telescoping retain both
  boundaries; cost-only bounds discard only nonnegative final potential.
  Zero-initial bounds require an explicit zero premise. Constant and bounded
  charges have separate budget laws. A bounded `Fin 3` charge example has
  satisfiable premises. The retained counterexample spends initial potential
  even when the new charge is zero.
- Counter values, length bounds, increment erasure, and local write identities
  quantify all Boolean lists. Canonical preservation is conditional on canonical
  input; generated zero-start prefixes are canonical. Noncanonical `[false,false]`
  checks the broader numeric/accounting domain without asserting canonicality.
- Four increments from zero produce `[false,false,true]` (binary 100) and seven
  writes. The example obtains state from erasure and cost from exact potential
  accounting. Five observed states have values `[0,1,2,3,4]` and require only four
  transitions. All-one input checks nonzero initial potential and growth writes.
  Numeric and write conclusions also pass through the composed consumer.
- Integer-digit correspondence is exact encoded list equality. `sourceInc`
  validates only encountered digits: `[2]` fails, `[0,2]` succeeds unchanged in
  its tail. Source prefixes of lengths zero and one do not increment, so even
  `[2]` is observable there; length two fails. These are finite Option-totalized
  source branches, not a global digit-validation assertion.
- Structural length/split/reversal statements preserve values as well as exact
  work. Split past the end, nonempty reversal accumulator, and odd/even half
  splits are checked. Rebalancing uses accepted `splitSL` semantics.
- Symmetric absolute side-length-difference potential and local resource bounds
  apply to raw pairs, without `Inv`. Validity is required only for independent
  ordinary-list semantics and valid-state preservation. No stronger balance
  invariant is introduced. Tail on `([0],[1,2,3])` produces `([3,2],[1])`, source
  charge three and structural work ten. Singleton deletion has abstract charge
  zero but nonzero work. Empty selectors and mutations remain distinguishable.
- The arbitrary-workload bounds are exactly charge plus final potential at most
  initial potential plus twice operation count, and work plus twice final
  potential at most twice initial potential plus eight times operation count.
  Their paired-run form follows from additive projection equalities, so the
  two costs cannot silently follow different trajectories. Empty-start bounds
  use proved zero initial potential. The source valid-state counterexample
  refutes dropping initial potential for arbitrary starting representations.
- A mixed insert/query/delete workload refines to ordinary sequence `[2,3]`,
  preserves validity, and its composed endpoint result is `some 2`. Resource
  projection and final-observation resource-retention theorems are exercised
  alongside this value agreement. Value erasure alone is never used as a cost
  bound.

The resource universe generalization changes only implicit type universes;
operations, observation order, and premises of existing laws remain the same.
The generic rebalance and existing resource regressions check its concrete uses.
A full independent review and transitive proof audit remain integration gates;
checked examples do not establish every informal intent by themselves.

Targeted validation passed with 764 build jobs: `Examples.PotentialAccounting`,
`Examples.Resources`, `Examples.SymmetricLists`, and `Examples.KnapsackWorkload`.
This checks both existing direct measured clients and the workload client affected
by the universe generalization. Only module-system import warnings remain.
Full project checking and the exhaustive axiom audit are reserved for the
integration gate.

## Source identity and boundaries

Archive bytes were preserved unchanged and rehashed as
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Actual ZIP member bytes were compared with the inspected extraction before
implementation. Member identities under `project/adwh-lean/ADWH/` are:

| Member | Named declarations | SHA-256 |
| --- | ---: | --- |
| Chapter02/Timing.lean | 43 | `6dea2ad79dc7a0395021a9d47c61f4f17cc04f3ddab9dc4453d6dc3445067366` |
| Chapter02/Amortized.lean | 17 | `1c4a6678ac6d8dcca48a6978a1d3bf3b87adc27744dd3fa365fa5801bd556cb8` |
| Chapter03/SymmetricListCosts.lean | 47 | `471d2e0e69d68ae55b32142ca8dd19969f427fab3b46cd6b52645cd94c87877c` |

Counts include same-line declaration attributes. Anonymous source examples are
covered by connected examples rather than counted as named declarations.
The ledger validates every selected destination against local declarations.
Source-local branch proofs are retained where they express the concrete
algorithm; generic execution, iteration and global potential proofs are reused
as described above.

These are exact finite modeled counts. They establish no compiled runtime,
allocator behavior, sharing, lazy semantics, machine overflow, probabilistic
average, or hardware bound. Delayed-output symmetric prefix costs, random-access
costs, general asymptotic-growth theory and recurrences remain outside #173 and
under #149.
