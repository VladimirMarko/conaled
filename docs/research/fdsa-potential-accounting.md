# Mapped, signed and invariant-aware potential accounting

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This shared accounting development originated as FDSA-41 under issue #174,
at retained donor commit `12cb14fc98b8617b3b625620da8e60936daba340`. The textbook
integration reconciles it with PFDS's generic, state-preserving and signed
accounting APIs in the existing
[workload and potential interfaces](adwh-potential-accounting.md). It introduces
no additional executor or accounting framework. The integration checkpoint's
local tracker owns candidate validation and independent review; this source
correspondence does not assert whole-book or Chapters 19–23 acceptance.

## Source and mathematical scope

The primary source is the [official FDSA book](https://fdsa-book.net/), edition
July 27, 2026, printed pages 227–232. Its PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The chapter's equation (19.1) defines an amortized charge by actual work plus
the change in potential. It uses signed real arithmetic. Its telescoping
argument follows the actual successive states, retains initial credit, and
drops the final potential only when that value is nonnegative.

The retained checkpoint inventory at
`books/fdsa/records/research/coverage/fdsa-control/research/chapter19-obligations.md`
records the pinned AFP archive and its separate framework variants. The inspected
`Amortized_Framework0.thy` has SHA-256
`905899004289e7a68601a2f416ba33926135f31288c2396a0ae1abcac7133eff`.
It provides the closest unary source correspondence. No external theorem is
introduced as an axiom and no Isabelle rebuild is claimed.

| Source obligation | Shared correspondence |
| --- | --- |
| C19-011: valid-state potential and explicit initial boundary | `run_potential_map_of_invariant`, `run_cost_le_map_of_invariant` |
| C19-012: signed charge `work + Phi(after) - Phi(before)` | The charge expression in `budget_amortized`, in an additive commutative group |
| C19-013: exact telescoping along actual states | `budget_amortized`, supported by `run_potential_map_exact` |
| C19-014: upper bound with initial credit | `run_cost_le_map_of_invariant`, requiring nonnegativity on preserved states |
| C19-015: zero-initial specialization | The arbitrary-workload zero-start fractional example, obtained from the preceding bound |
| C19-016: state-dependent local bounds on a preserved domain | `run_potential_map_of_invariant` and the existing `run_invariant` |
| C19-017–018: two input potentials and operation histories | Remain open; a unary state trajectory does not prove these claims |

These rows locate the common accounting argument. The book's counter, dynamic
tables, queues and heaps still require their own exact algorithm, potential,
local-law and cost-model correspondence. The toy fractional transition below
is not a dynamic-table implementation.

## Change relative to the existing interface

`Resources.run` still executes the supplied measured transition and combines
its raw work observations in order. Neither its definition nor its contracts
change. `Resources.budget` keeps its four explicit arguments and its empty and
nonempty recurrences, but its charge type is now independent of the step's raw
observation type. A real or signed charge therefore follows the same natural
work transition without creating a reweighted executor.

An explicit additive homomorphism `h : C →+ D` interprets accumulated raw work
in the accounting carrier. This is an algebraic observation map. It is not a
runtime estimate or an assertion that the map preserves order. The local law
already compares the mapped observation. The retained reweighting interfaces
remain available to clients that need a measured computation whose returned
observation itself has changed.

| Declaration | Raw-work requirements | Charge/accounting requirements |
| --- | --- | --- |
| `budget` | None | `Zero`, `Add` |
| `budget_append` | `Zero`, `Add`, to use the existing executor's state | `AddMonoid` |
| `budget_map` | None | `AddZero` on both charge carriers and an additive homomorphism |
| `budget_congr_state` | None on either transition's raw-work carrier | `Zero`, `Add`; equality of the transitions' next states |
| `run_potential_map_exact_of_invariant`, `run_potential_map_exact` | `AddZero`, to form the homomorphism and run | `AddMonoid` |
| `run_potential_map_of_invariant`, `run_potential_map` | `AddZero` | `AddMonoid`, `Preorder`, `AddLeftMono`, `AddRightMono` |
| `run_cost_le_map_of_invariant` | `AddZero` | The preceding ordered additive structure and a stated nonnegativity premise |
| `budget_amortized` | `AddZero` | `AddCommGroup`, because the displayed signed formula uses subtraction |

The boundary proofs associate sums without commuting their terms. They require
neither cancellation nor commutativity, and the inequality version does not
require a linear order. The raw work carrier need not be associative: the
existing executor's actual right-associated observation is mapped as it stands.
Request, state and observation types keep independent universes. No payload
equality, finiteness, inhabitance or ordering requirement is added.

The same-carrier theorems `run_potential` and `run_potential_exact` retain PFDS's
generic public statements and delegate to the mapped laws using the identity
homomorphism. The exact theorem requires only `AddMonoid`; the inequality
theorem additionally requires `Preorder`, `AddLeftMono` and `AddRightMono`.
Their original natural-number statements remain specializations, and the
natural constant-charge and cost-bound contracts remain unchanged.
`FIFOContracts.abstractBudget` annotates its unused raw
cost literal as `(0 : Nat)`: previously the natural-only budget fixed that type
implicitly. This is a compatibility annotation, not a change in its trajectory
or charges.

PFDS's `run_cost_le_of_nonneg_final` retains its weaker premise that only the
actual final potential is nonnegative. The invariant-domain mapped bound
provides another useful route: preserved validity proves that final premise.
Neither route drops initial credit. `budget_congr_state` separately explains
why changing a measured observation leaves charges unchanged when the next
states agree. None of these contracts identifies the costs of different
implementations merely from equality of their results.

The named `potentialCharge` and `debtCharge` interfaces in
`Applications.Resources.SignedPotential` remain the savings and opposite-sign
debt presentations. Their exact laws use `run_potential_exact`, hence the same
mapped invariant-aware core. `budget_amortized` also supports a distinct raw
work carrier interpreted into the signed accounting group. No implication
about shared credit or suspension forcing is added by these algebraic links.

## Connected cases and statement review

`Examples.MappedPotentialAccounting` retains the XP01 cases alongside
`Examples.PotentialTransport` and `Examples.SignedPotential` from PFDS. These
clients belong in the public entrypoint and its normal proof-audit closure.
The expected calculations were recorded in the original exact requirements
before these definitions and proofs were written. The integration checkpoint
records checked commands and review outcomes separately; the following states
the mathematical connections and scope.

### Existing counter interpreted in real numbers

`Counter.real_boundary` uses the existing `BinaryCounter.incWithCost` and its
local natural identity `flipCost + ones_after = 2 + ones_before`. It casts that
local identity, invokes `run_potential_map_exact`, and uses `budget_map` together
with the existing `budget_constant` to interpret the constant budget in `Real`.
It does not obtain its theorem by casting the already proved global bound.

For every Boolean list and every number of increments the intended conclusion
is `totalCost + finalOnes = initialOnes + 2*n`, in `Real`. There is no canonicality
or initialization premise. Existing value and cost refinement identify the
same execution. From the empty counter, four increments have numeric value
four, final one-bit potential one and work seven; the real boundary gives
`7 + 1 = 0 + 8`. The zero-start specialization still retains final potential.

The PFDS counter client uses `reweight_run` to identify both the actual final
state and the mapped work of the same measured execution. Its `realBudget`
uses `budget_congr_state` and `budget_map`, and its `realRun_potential` uses the
same-carrier exact theorem. The mapped observation and reweighted execution
therefore connect through the existing workload transport, while both
accounting proofs specialize the shared mapped core.

### Negative charges spend initial credit

`InitialCredit.clearStep` has natural state and work, resets its state to zero,
and costs one per call. Its integer potential is twice its state. The signed
charge is `1 - 2*s`. Starting at one, the first charge is minus one and the
second is plus one, because the second transition starts at zero. Raw work is
two, initial potential is two, final potential is zero and the trajectory
budget is zero.

The arbitrary-workload boundary is obtained from `budget_amortized`. The
two-step clients use that result to obtain the budget and refute both the
bound with initial credit omitted and the substitution of the first state's
charge for both actual charges. The potential is nonnegative for every natural
state; negative amortized charge does not mean negative actual work.

### Fractional accounting on a preserved domain

The valid natural states are zero and one. The total transition alternates
those states at natural cost one; on all other states it stays in place at
cost one hundred. Potential is one half at state one and zero elsewhere.
The charge is three halves at state zero and one half elsewhere.

On valid states, the independently calculated local equations are
`1 + 1/2 = 0 + 3/2` and `1 + 0 = 1/2 + 1/2`. The validity predicate contains
zero, is preserved, and justifies the local equality. The generic
invariant-aware theorem yields budgets three halves and two after one and two
steps from zero, respectively. The cost-only bound uses the proved
nonnegativity premise; the arbitrary-workload zero-start bound specializes its
initial boundary to zero.

At state two the local inequality would assert `100 ≤ 1/2`, which is false.
That counterexample records why the local-law premise is restricted; no
unconditional bound is inferred from this client. The exact and inequality
results quantify an arbitrary request list, not just the concrete examples.

### Ordered observations and retained natural clients

An additive free-monoid observation records requests in their execution order.
An instance of `run_potential_map_exact` with zero potential equates that work
to its actual budget, and the concrete requests `[1,2]` retain precisely that
order. This exercises the boundary theorem without assuming commutative
addition. The old counter, symmetric-list, FIFO and random-access clients
remain validation targets for the generalized definition.

The PFDS signed cases additionally retain a negative-final-potential
counterexample, a positive final-state bound despite negative intermediate
charges, and opposite-sign debt with outstanding terminal debt. They exercise
the final-state-only premise and named signed laws without imposing global
nonnegativity of charges or potentials.

## Remaining boundaries and acceptance

These are mathematical modeled observations. They assert no compiled runtime,
allocation, machine overflow, lazy evaluation or hardware bound. Persistent
reuse of the same starting object is not repeated execution on its successor
states. A binary merge must account for both input potentials and their
occurrences in an operation history. Neither fact follows from unary `run`.

The original exact requirements, preflight and source reviews are preserved
under `docs/history/textbooks/checkpoint-012/books/fdsa/records/`.
The current integration requirements and evidence are recorded by its local
tracker. Acceptance requires a committed
immutable candidate, applicable focused builds, the full guarded check and
exhaustive proof audit, both independent review axes, and final candidate
identity verification. A checkpoint may preserve this draft before those
gates; it does not confer acceptance on this unit or any later chapter.
