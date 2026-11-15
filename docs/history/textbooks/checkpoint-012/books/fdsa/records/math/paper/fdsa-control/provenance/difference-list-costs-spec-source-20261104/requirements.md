# Shared difference-list closure observations: exact scope

Frozen 2026-11-02 before code. This is a cross-cutting resource-model unit,
not activation or acceptance of Chapter 2. Read the whole-book request,
`../research/difference-list-cost-preflight.md`, the Chapter 2 inventory's
C02-110/111 and the earlier explicit frozen-requirements clarification.
The existing Chapter 1 and shared candidate gates remain in force.

Starting candidate: `a14977b9e316cc484ffad8a470d26b15615956c0` (uncompiled
Chapter 1 repair). Separate branch/worktree: `work/fdsa-builder-costs` /
`conaled-builder-costs`. Do not modify any active validation checkout or
launch a compiler concurrently with the frozen full gate.

## Ordinary operations and separate contracts

Use namespace `Resources.DifferenceListCosts` and the ordinary alias
`Builder α := List α -> Measured (List α) Nat`. No new DList datatype,
expression tree, source-language interpreter, timing class, executor or
measured-builder Monoid instance is required.

Define separate predicates:

```text
Rep f prefix := forall suffix, (f suffix).1 = prefix ++ suffix
AppCost f k  := forall suffix, (f suffix).2 = k.
```

Provide charged `empty` and `singleton a` callbacks, with application cost
one, and `compose f g suffix := tick (bind (g suffix) f)`. The public cost
equation must first retain its actual value-dependent second invocation;
then derive composition of the uniform AppCost contracts. Composition
represents prefix_f followed by prefix_g, preserving order and duplicates.
Rep alone must imply no application-cost bound.

Provide `createEmpty`, `createSingleton a`, and `createCompose f g` as measured
creation operations with observation one. They return the corresponding
callback without applying it. This is an explicit fixed-size capture tariff;
do not claim to prove compiler allocation or machine time. Supplied callbacks
are already constructed values at this boundary. Their prior work is not
charged again merely because references are captured.

`pushRun a f` creates a singleton then composes f with it through existing
`bind`, hence has creation cost two. `buildFrom items f` uses existing
`Resources.run pushRun items f`; it does not charge creation of its supplied
seed. `build items` first performs `createEmpty`, then `buildFrom`.

For an arbitrary supplied seed, prove separately:

- `buildFrom_cost`: construction cost `2*items.length`.
- `buildFrom_rep`: Rep f prefix implies the final callback represents
  `prefix ++ items`.
- `buildFrom_appCost`: AppCost f k implies final application cost
  `k+2*items.length` at every suffix.

Derive `build_cost`, `build_rep`, and `build_appCost`, giving construction and
application counts `2*n+1` from identity. Values, costs and premises must remain
separate. Use existing composition/executor/value-fusion laws where they fit;
ordinary induction is appropriate for the new cost contract. Do not infer
cost equality from a value-erasure theorem.

## Existing DList correspondence

Provide `toDList f prefix rep` using the existing Batteries.DList record with
its ordinary application function `(f suffix).1`. Its invariant must follow
from Rep. Retain application and toList equations and a value bridge for
composition/push using the existing DList laws. A compact general equality to
`Batteries.DList.ofList prefix` may supply the representation bridge.

The measured compositional push and Batteries' fused push have the same
ordered list value. Their exact construction/application observations are
not identified. Arbitrary source D-law workers keep their semantic generality;
no executable cost is inferred from their extensional invariant alone.
No payload equality, order or inhabitance is permitted merely for this model.

## Connected cases and negative boundaries

Retain independently expected examples connected through the public laws:

1. Compose singleton prefixes [1] and [2], then apply to [9], obtaining [1,2,9]
   with application count three. Include its standard DList value bridge.
2. Capture callbacks of arbitrary supplied application counts p and q:
   composition creation costs one; later application costs p+q+1.
3. Build [3,1,3] and apply to a nonempty suffix. Construction costs seven,
   application seven, and the combined measured program fourteen. Empty and
   singleton cases, including empty input at payload type Empty, are required.
4. Use the generic seed theorem with a singleton-prefix seed and subsequent
   pushes. Record that its seed creation is outside buildFrom's boundary.
5. Construct once, apply twice, retain both returned values, and derive total
   count `6*n+3` through actual measured binds. Do not cache the materialized
   result silently.
6. Retain empty-prefix composition histories whose application count is
   unbounded despite identical DList values. A linear history gives a direct
   checked counterexample to any bound from output length alone.
7. Retain actual shared self-composition: after m construction extensions,
   construction count is m+1, application count is `2^(m+1)-1`, and the
   represented prefix is empty. Count unfolded invocations, not merely the
   distinct creation events. The exact recurrence family and a concrete
   instance must be proved; no universal Big-O countertheorem is required here.
8. Expose that charged identity is not an identity for the full cost
   observation: composition with it adds two application entries while
   preserving values.

Root owns the connected examples and documentation integration; the core
contributor must coordinate the listed public names and argument order.

## Scope retained for chapter implementation

The source asc starts from a singleton-prefix callback, not identity, and
applies it to [last]. Its precise correspondence and the conditional
`2*r-3` application count for a run of length r>=2 remain Chapter 2 work.
C02-112 still needs actual scanner/control, descending construction, emitted
run construction and merge dispatch observations. C02-109 still needs the
actual ordinary append/reverse construction comparison. None is discharged
merely by this reusable interface.

If representation size is mentioned, distinguish unfolded application
occurrence weight from distinct shared closure allocations. The generic
positive cost laws use explicit AppCost contracts; the actual push chain
will later justify its linear weight from its own recurrence.

## Validation

Record per-claim statement review, meaningful satisfiable uses and exact
cost boundaries. No admissions, axioms, unsafe/partial definitions or kernel
bypasses are permitted. Draft code may be committed for durability before
elaboration, clearly marked uncompiled. Final acceptance requires the pinned
environment's focused build, public integration, immutable candidate full
check/audit, both retained independent axes, and immediate final candidate
verification. This unit and every chapter remain unaccepted until those gates.
