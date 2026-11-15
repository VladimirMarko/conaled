# Shared potential accounting — bounded design preflight

Prepared 2026-11-02. **Read-only design evidence, not implementation,
compilation, Standards/Spec review, or chapter acceptance.** Inspected conaled
`1aabd512284fe86254278ac631eda061d311050b`, with the relevant APIs already at
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The parent subsequently froze `FDSA-XP01` requirements in
`../reviews/potential-requirements.md`, before implementation, on shared
candidate `c80eec92f5458eccfd1c34c8314d666c2a1e3847`. The compatibility and
example recommendations below are aligned with that bounded unit.

## Recommendation

Generalize the existing trajectory `budget`, preserve the executor and all
current Nat-facing contracts, and add one shared family of mapped,
invariant-local boundary theorems. The basic telescoping proof can preserve
noncommutative addition. Only the book-form signed-charge expression needs a
commutative group. This is a small extension of
`Applications/Resources/Potential.lean`, not another resource representation,
executor, budget function, or public accounting framework.

The concrete gap is real: Chapter 19 dynamic tables use real, sometimes
half-integral potentials and signed amortized charges; Chapter 21 uses real
logarithmic potentials; Chapter 22 casts natural raw work to an integer
potential expression and then to a real bound; Chapter 23 also uses real
potential. Existing natural `run_potential` cannot express those local laws.
Merely casting its conclusion works for the existing counter but does not
solve the later cases where the potential is not the cast of a natural number.
The precise source boundaries are recorded in `chapter19-obligations.md`
C19-011–018, C19-037–052, `chapter21-obligations.md` C21-062–065, and
`chapter22-obligations.md` C22-028–064.

## Existing reuse and minimal algebra at this pin

The relevant source files are `Applications/Resources/Measured.lean`,
`Workload.lean`, `Potential.lean`, `BinaryCounter.lean`, `FIFOContracts.lean`,
`SymmetricCosts.lean`, `RandomAccess/End.lean`, and their examples. The current
architecture/provenance explanation is
`docs/research/adwh-potential-accounting.md`.

| Result or operation | Sufficient capabilities and reason |
|---|---|
| Existing `Measured`, `bind`, `run` | Leave unchanged. `run` requires only `Zero C` and `Add C` for the raw observation; `run_append` separately requires `AddMonoid C`. Execution preserves observation order. |
| Generalized `budget step charge` | `step : ι → σ → σ × C`, `charge : ι → σ → D`, with only `Zero D` and `Add D`. It never uses a raw C value or C operation, only each transition's next state. Keep the same four explicit arguments and recursive equations. |
| Generalized `budget_append` | `Zero C`, `Add C` because the statement mentions `run step`; `AddMonoid D` for ordered charge reassociation and zero laws. No associativity or commutativity on C is used in this proof, because only the run's final state appears. |
| `budget_map` for a map `g : D →+ E` | `AddZero D`, `AddZero E`, and no algebra on the step's raw C. Induction using `map_zero` and `map_add` gives `budget step (fun i s => g(charge i s)) is s = g(budget step charge is s)`. No commutativity, associativity or order is required for this transport. |
| Raw-work map `h : C →+ D` | At this pin `AddMonoidHom` is defined using **`AddZero C` and `AddZero D`**, not necessarily additive monoids. `AddZero` bundles addition and zero with no axioms. `map_add` and `map_zero` are exactly the needed laws. |
| Generic boundary equality | `AddZero C`, `AddMonoid D`, explicit h, and the local equality. No order, cancellation, subtraction or commutativity is needed. |
| Generic boundary inequality | `AddZero C`, `AddMonoid D`, `Preorder D`, `AddLeftMono D`, `AddRightMono D`, explicit h, and the local inequality. Both monotonicity capabilities matter if D is noncommutative. No order or monotonicity on C or h is required. |
| Dropping final potential | Same ordered capabilities, plus `0≤Phi(final)`; on a valid-state theorem derive this from preservation and nonnegativity on valid states. No global nonnegativity of Phi or of the supplied amortized charge is needed. |
| Signed charge `h(work)+Phi(after)-Phi(before)` | `AddZero C` and `AddCommGroup D` suffice for its exact accumulated identity. No order is needed for the identity itself. An ordered bound adds the relevant preorder/monotonicity assumptions. |
| Constant generalized budget, if later needed | `AddMonoid D` gives `budget step (fun _ _ => k) is s = is.length • k`, with no algebra on C. This extra theorem is **not needed for XP01's real counter client**: `budget_map` plus existing Nat `budget_constant` already suffices. Keep the latter's public `k*is.length` statement and avoid adding a generic constant-law wrapper without a remaining consumer. |

The exact definitions were read in
`Mathlib/Algebra/Group/Monoid.lean` (`AddZero`, `AddZeroClass`),
`Mathlib/Algebra/Group/Hom/Defs.lean` (`AddMonoidHom`), and
`Mathlib/Algebra/Order/Monoid/Unbundled/Defs.lean`
(`AddLeftMono`, `AddRightMono`). The latter aliases are the two ordinary
`CovariantClass` capabilities for adding on the left/right. Their monotonicity
lemmas, including additive versions of the displayed multiplication lemmas,
are in `Unbundled/Basic.lean`, already imported through `Measured`.

`IsOrderedAddMonoid D` in `Algebra/Order/Monoid/Defs.lean` assumes
`AddCommMonoid D`. It is conventional for commutative scalar clients but is
unnecessarily strong for the boundary proof. Likewise, neither
`IsOrderedCancelAddMonoid`, a linear order, a ring, nor a Real-specific class
belongs in that generic theorem. In a commutative specialization the pin
supplies the missing opposite-side monotonicity instance, but the general
statement should state both sides rather than silently assume commutativity.

## The boundary calculation really is noncommutative

For one head operation, let `s'` be its actual returned state, `c` its raw
work mapped by h, `r` the mapped remainder's accumulated work, `a` the head
charge, and `b` the remaining budget evaluated from s'. The inductive and
local inequalities are

```text
r + Phi(final) ≤ Phi(s') + b
c + Phi(s')   ≤ Phi(s) + a.
```

The complete induction step is

```text
(c+r) + Phi(final)
  = c + (r+Phi(final))
  ≤ c + (Phi(s')+b)
  = (c+Phi(s')) + b
  ≤ (Phi(s)+a) + b
  = Phi(s) + (a+b).
```

Only associativity, left-addition monotonicity and right-addition monotonicity
appear. `map_add` connects `(c+r)` to the raw run observation. Replace the two
inequalities by equalities to obtain the exact theorem without any order
capabilities. `map_zero` and D's zero laws handle the empty list. This also
shows why no raw-C associativity is needed for these results: the map is
applied to the exact parenthesization returned by the existing run.

The target boundary theorem should retain its useful form

```text
h(work(run step is s)) + Phi(state(run step is s))
  ≤ Phi(s) + budget step charge is s,
```

with an equality companion. Do not reorder the right side into `budget+Phi`
in the generic noncommutative theorem. Concrete Nat/Int/Real clients may use
commutativity locally when matching a source equation.

## Invariant-local laws and the signed identity

Use an ordinary predicate `P : σ → Prop`, a preservation premise
`∀ i s, P s → P (step i s).1`, the starting proof `P s`, and a local law
required only when `P s` holds. Induction passes the starting proof to the
actual returned state, exactly as `run_invariant` already does. This allows
potentials that are negative or otherwise unsuitable outside the source's
valid domain; it does not strengthen every operation law to all raw states.

The local mapped inequality is

```text
P s → h((step i s).2) + Phi((step i s).1)
        ≤ Phi(s) + charge i s.
```

An implementation can make this invariant-local theorem the primitive and
derive its all-states form using `P=True`; the equality family has the same
pattern. There is no need to duplicate the induction for every scalar type
or to construct a second executor on a validity subtype. Existing validity
subtype clients can still use it without alteration.

For `D` an `AddCommGroup`, define the amortized expression locally, or pass
it directly as the existing budget's charge:

```text
A i s = h((step i s).2) + Phi((step i s).1) - Phi(s).
```

Its identity is

```text
budget step A is s
  = h((run step is s).2) + Phi((run step is s).1) - Phi(s).
```

This follows from the exact additive boundary theorem and group algebra. It
does not require nonnegative A, nonnegative Phi, an order on C, or an order
on D. The book's position of the subtraction is why this particular
expression is commutative-group-valued: in a noncommutative additive group,
`Phi(before)+(c+Phi(after)-Phi(before))` need not equal `c+Phi(after)`.
Do not broaden the signed expression to that domain without changing the
formula, and do not change the book's formula just to obtain more generality.

For an upper bound on A, require the bound only on P states and convert it
to the additive local inequality. After telescoping, dropping final Phi
uses its nonnegativity on the actual final state. Dropping initial Phi is
permitted only under an explicit zero-initial premise (or a separate bound
on initialization credit). Signed charges can remain negative throughout.

This addresses unary actual-state trajectories. It does **not** prove the
binary-input usage-tree/ownership theorem from Chapter 19 or justify
spending the potential of an aliased persistent heap twice. That later
obligation remains separate even though a two-argument local inequality can
already be written in the same scalar domain.

## Smaller reuse routes considered

`reweight_run` already transports additive observation maps through the
executor. One could first reweight the whole step into D, prove an unmapped
D theorem, and show the budget follows the same states. This is valid, but
the direct h theorem avoids that additional transport at each call site and
admits raw `AddZero C` instead of `reweight_run`'s existing `AddMonoid C`
premise. No replacement for `reweight_run` is needed; it remains the ordinary
composition law when its assumptions apply. Additivity and monotone
transport of a previously established inequality are different questions:
the direct local theorem does not need h to be monotone, whereas
`reweight_bound` correctly asks for monotonicity when transporting a bound.

Mathlib's `Finset.sum_range_sub` already proves the scalar telescoping sum
for an indexed commutative-group-valued function. Reusing it alone would
still require constructing a state sequence and proving its connection to
`run`, mapping costs, and reconstructing the trajectory-dependent budget.
The short induction above is the smaller adapter to the repository's
existing executor and preserves the weaker noncommutative boundary theorem.
There is no reason to introduce another indexed-history API solely to use
that standard scalar identity.

Retain `run_potential`, `run_potential_exact`, `run_cost_le`,
`run_zero_potential`, `run_constant_charge`, `budget_constant`,
`budget_le_constant`, and `charge_iff_signed` with their current Nat-facing
argument order and statements. Their proofs can delegate to the generic
theorems using `AddMonoidHom.id Nat` and `P=True`. Avoid inserting an
explicit h argument into those existing names. Generalizing the definition
of budget and its append theorem does not itself change their Nat behavior.

## Concrete compatibility edits and affected callers

| Existing caller | Impact to check or preserve |
|---|---|
| `FIFOContracts.abstractBudget` | **Concrete edit:** annotate its discarded raw work as `(0 : Nat)` in `budget (fun c xs => (step (lists α) c xs, 0)) profile`. Previously budget forced this component to Nat; an independent C no longer does. Preserve the public definition's existing result and specialization rather than relying on numeral defaulting. |
| `FIFOContracts.budget_abstract`, `abstractBudget_append`, `client_bound`, `sequential_bound` | Keep existing equations, observation refinement and initialization-credit semantics. The proof unfolding budget must continue to expose the same recurrence; append invokes the newly generalized theorem at C=D=Nat. |
| `FIFOContracts.abstractBudget_append`'s local `e` | Its zero work is already constrained by `e : Instrumentation (lists α)`, whose measured result has Nat work. No extra annotation is necessary there. |
| `BinaryCounter.totalCost`, `totalCost_succ`, `counter_potential` | `incWithCost` already fixes C=Nat and `flipCost` fixes D=Nat. Preserve definitional zero/successor behavior and the old exact telescope call. |
| `SymmetricCosts.run_charge_potential`, `run_work_potential` | Both call the old `run_constant_charge`; preserve their natural source-charge versus structural-work distinction. |
| `RandomAccess.End.pushManyRun_potential` | Calls `run_potential_exact` and rewrites `budget_constant`; both old names/statements must remain compatible. |
| `Examples.PotentialAccounting` | The bounded-charge lambda's work is `i.val : Nat`; the initial-potential example explicitly types its step `Unit → Nat → Nat × Nat`. No unconstrained raw zero remains in those calls. Preserve the existing free-monoid run example. |
| `Examples.FIFOContracts` | Rewrites `abstractBudget` and `budget_constant` in public client-bound proofs; preserve those simplification shapes. |

A scoped search of all Lean budget-facing callers found only the first-row
unconstrained step-cost literal. Other identifiers named `budget` in search,
numerical execution and `Resources.BoundedSummary` are separate definitions,
not callers of `Resources.budget`; this change does not warrant modifying
those domains. The dependent list/reversal and random-access clients inherit
the existing potential imports but need no new Real assumptions.

## Connected examples aligned with the frozen requirements

### 1. Existing counter with real accounting and independent numeric meaning

Use the existing `BinaryCounter.incWithCost`, mapped by
`Nat.castAddMonoidHom Real`, and `Phi bs=(ones bs:Real)`. Obtain the local
equality from `flipCost_potential` and `incWithCost_eq`; apply the new generic
exact theorem to the **existing run**, not just a cast of the already proved
whole-run theorem. The target for arbitrary n and arbitrary Boolean bs is

```text
(totalCost n bs:Real) + (ones(advance n bs):Real)
  = (ones bs:Real) + 2*n.
```

Combine this with existing `value_advance`/`advanceWithCost_eq`. Four
increments from empty have represented value 4, actual work 7 and terminal
potential 1, so the boundary identity is `7+1=0+8`. An all-one seed retains
its nonzero initial potential. Canonicality is unnecessary for either the
local write law or this resource identity; do not add it merely to exercise
the invariant parameter.

The scalar-dependent imports belong in the example, not the generic library.
At this pin the current basic Real module is `Mathlib.Basic.Real.Basic`;
`Mathlib.Data.Real.Basic` is a deprecated forwarding module. The exact cast
hom is in `Mathlib.Data.Nat.Cast.Basic`, with `AddMonoidWithOne` on its
target. The planned `budget_map` transports the existing natural
constant-budget theorem here, so an additional generic constant-budget
theorem is unnecessary for this unit.

### 2. Negative amortized charge and explicit initial credit

The parent's chosen small measured transition has natural state and work,
with `clear () s=(0,1)` and `Phi s=2*(s:Int)` (or the same expression in
Real). It is an explicit accounting example, not a new book algorithm.
Its source-form signed expression is

```text
A () s = 1 + 0 - 2*s.
```

Starting at 1, the first charge is **-1**. The second transition starts at
the actual returned state 0, so its charge is 1. Both potentials and actual
work are nonnegative, but the first amortized charge is negative. Two
transitions satisfy

```text
final state = 0
sum actual work = 2
budget of signed charges = -1+1 = 0
2 + 0 = 2 + 0.
```

The signed identity must be obtained through `budget_amortized`, retaining
both boundaries. Dropping the initial potential would falsely claim `2≤0`.
Reusing the first state's charge twice would give -2 rather than zero, so
this example also checks the budget's actual-state dependency. Do not
introduce a public signed-charge definition solely for this example; use the
planned explicit lambda.

As an alternative illustration already available from existing counter
algebra, the potential `2*ones` on the actual binary counter gives charge
`4-flipCost`, which is -1 at four initial true bits. It is not an extra
required XP01 example; the parent's simpler clear-state case already
exercises the requested distinction.

### 3. A genuinely local law with a fractional potential

A concrete small realization of the frozen validity-domain case is a Nat
state machine with invariant `s≤1`: at 0 return `(1,1)`, at 1 return
`(0,1)`, and at any other state return `(s,100)`. Take Real potential 1/2
at state 1 and zero otherwise, and charges 3/2 at 0 and 1/2 otherwise.
For valid states the exact local laws are

```text
s=0: 1 + 1/2 = 0 + 3/2
s=1: 1 + 0   = 1/2 + 1/2.
```

The two valid states are preserved. Starting at 0, one step has work 1,
final potential 1/2 and budget 3/2; two steps have work 2, final potential
0 and budget 2. At the invalid state 2, the claimed local inequality would
be `100≤1/2`, which is false. This makes the invariant premise substantive
and demonstrates that the global all-raw-states theorem cannot be used with
that local law. The valid two-step equality also checks fractional charges
on successive actual states.

This is a proposed concrete accounting client satisfying the parent's
frozen case, not a model of dynamic-table execution or acceptance evidence
for Chapter 19. It avoids introducing a gratuitous canonicality premise on
the counter merely to exercise the invariant parameter. No Lean example was
written or compiled during this preflight.

## Scope of subsequent validation

The meaningful compatibility surface is the existing potential examples,
FIFO contracts, symmetric workload and random-access end-cost clients, plus
the frozen connected examples. The generic proof must retain empty-run
behavior, both boundary terms, actual-state charge evaluation, and the
noncommutative theorem's ordered additions. No new executor, global
nonnegativity restriction, Real import in the generic API, binary-ownership
claim, or additional implementation/review loop is warranted by this preflight.

