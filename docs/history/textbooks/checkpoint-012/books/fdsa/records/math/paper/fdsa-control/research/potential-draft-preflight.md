# XP01 draft: bounded statement and proof-shape preflight

Prepared 2026-11-02 against immutable draft
`c28ba71863d2a35ee1c3a089caa90464e4cca692`, relative to
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

**This is read-only preflight evidence, not compilation, the independent final
Standards/Spec review, or acceptance.** No Lean files, Git state, tickets, builds,
or acceptance states were changed. Root retains the existing implementation
and review workflow. The preceding requirements are
[potential-requirements.md](../reviews/potential-requirements.md); the design
analysis is [potential-generalization-preflight.md](potential-generalization-preflight.md).

## Finding

No mathematical or public-contract blocker was identified in this bounded pass.
The draft matches the frozen split between arbitrary additive raw observations,
ordered additive boundary accounting, and signed commutative-group charges.
The checked proof shapes do not require stronger algebra than the statements
advertise. This does not establish that the proposed proof terms elaborate or
that all downstream files compile.

## Inspected implementation and dependencies

The inspected draft files were `Applications/Resources/Potential.lean`,
`Applications/Resources/FIFOContracts.lean`,
`Examples/MappedPotentialAccounting.lean`, `SquareApplications.lean`,
`docs/research/fdsa-potential-accounting.md`, and the reconstruction-map diff.
The read also checked the actual `Workload.run`, `run_cons`, `run_invariant`,
`Measured.bind`, and the existing counter interfaces used by the examples.
Pinned Mathlib declarations for `Nat.castAddMonoidHom`, its coercion simp law,
and `FreeMonoid.of/ofList` were inspected directly.

| Draft result | Statement/proof-shape assessment |
|---|---|
| `budget` | Charges are evaluated at the actual current state and recursive budget at the actual next state. The raw observation is unused, so no raw algebra is requested. Charge requirements remain just `Zero` and `Add`. |
| `budget_append` | Only the executor's state appears on the right. Raw `Zero/Add` suffice; target associativity and zero laws discharge the induction. No raw associativity is smuggled in. |
| `budget_map` | The induction uses only `map_zero` and `map_add`; both charge carriers' `AddZero` assumptions match the pinned homomorphism API. |
| Invariant-local boundary inequality | The induction passes `closed i s hs` to the actual tail state. Its addition order is `(headWork+tailWork)+finalPotential`, reassociated before applying the tail law and then the local law. Both left and right monotonicity are used; commutativity and cancellation are not. |
| Invariant-local exact boundary | The same reassociation uses equalities and `congrArg`, so no order or commutativity is needed. The all-state convenience wrappers specialize to the satisfiable predicate `True`. |
| `run_cost_le_map_of_invariant` | `run_invariant` supplies final validity; the supplied nonnegativity premise gives `0≤Phi(final)`. Adding mapped total work on the left justifies dropping that final term. Initial potential remains in the result. |
| `budget_amortized` | The charge is exactly `h(work)+Phi(after)-Phi(before)`. In a commutative group, adding `Phi(before)` cancels the subtraction and yields the local boundary identity. The final rearrangement gives budget equal to mapped total work plus final minus initial potential, with the correct sign. No positivity hypothesis is needed for this identity. |
| Existing natural wrappers | `run_potential` and `run_potential_exact` keep their statements and explicit argument order, delegating through `AddMonoidHom.id Nat`. The remaining natural public bound/constant-charge declarations keep their conclusions. |

The concrete compatibility edit is present: `FIFOContracts.abstractBudget`
uses `(0 : Nat)` for its otherwise unconstrained raw observation. The existing
counter, FIFO, symmetric-list, random-access, and natural example call shapes
remain normal validation targets; the read-only search found no additional
untyped raw zero requiring a proposed edit. Other unrelated definitions named
`budget` are not consumers of this interface.

## Connected examples

- **Existing counter:** `Counter.real_boundary` casts the local
  `flipCost_potential` identity, invokes the generic exact boundary theorem,
  and obtains its real constant budget using `budget_map` plus the old natural
  `budget_constant`. It does not merely cast an existing global theorem. Both
  starting and final potentials survive for arbitrary bits and increment count.
  The four-increment target is consistent: work `7`, final one-bit potential
  `1`, and budget `8` from the empty state.
- **Initial credit:** the reset transition has work `1` per call and integer
  potential `2*s`. Starting at one, its actual charges are `-1` and `+1`, not
  two copies of the first charge. The general signed identity yields budget
  `0`, raw work `2`, final potential `0`, and initial potential `2`. Both
  displayed counterexamples test the intended failure modes through that
  identity.
- **Fractional valid domain:** `s≤1` contains zero and is preserved. The two
  local equalities are `1+1/2=0+3/2` and `1+0=1/2+1/2`; budgets after one and
  two calls from zero are `3/2` and `2`. The invalid state two gives the false
  unconditional local inequality `100≤1/2`. Arbitrary-workload exact and
  inequality results use the invariant-aware public laws.
- **Noncommutative observation:** the additive free monoid records the actual
  request order. The zero-potential exact boundary instance needs no
  commutativity, and the concrete list `[1,2]` has the expected ordered word.
  The pinned `ofList`/multiplication definitions support the stated reduction
  shape; no compiler result is inferred from that inspection.

The documentation accurately identifies these as accounting examples and
keeps binary-input potentials, ownership histories, persistent reuse, and
later algorithm-specific bounds open. The new example is imported by
`SquareApplications.lean`. The source-map correspondence with C19-011–018
retains the initial boundary and the multiple-input limitation.

## Handoff boundary

No source change is requested from this pass. Proceed with the already
required immutable-candidate validation and independent reviews; do not add a
new implementation loop on the strength of this note. Compilation, proof
audit, downstream compatibility, and final candidate identity remain unverified
by this read-only assessment.
