# Checked selected witnesses under two exception policies

[#373](https://github.com/VladimirMarko/conaled/issues/373) implements the bounded
experiment in [the earlier paper report](effectful-witness-interpretation.md).
[StateException](../../SquareKit/StateException.lean) defines independent `Keep`
and `Undo` meanings and a finite scoped interpreter.
[The checked clients](../../Examples/StateException.lean) retain the selected
natural in `P`, reject recomputation in `Q`, and connect an existing measurement
record to both policies. Existing clients and their interfaces are unchanged.

## Meaning and composition

The carriers are `S → Except E A × S` and `S → Except E (A × S)`.
`handle` implements catch: Keep starts the handler in the failed computation's
last state; Undo starts it in the enclosing scope's entry state. Success bypasses
the handler. `Scoped` permits nested scopes. `Tree` contains return, read, write
and raise, with continuation substitution `Tree.bind`; it has no catch constructor.
This separation prevents substitution from silently expanding a handler's scope.

`Algebra` supplies operations. `LocalLaws` requires four constructor-level
compatibilities with bind. Induction derives `fold_bind` for every finite tree
and continuation. Both interpretations discharge those local obligations by their
semantic clauses. The whole-program composition theorem is not an assumption.
`StateLaws` separately checks write/write, write/read, read/write and read/read;
catch-return, catch-throw, monadic right unit and associativity are checked too.
The syntax is unquotiented. This supplies equation checks, not a construction of
the paper's quotient free model or a general effect system.

For `P`, `p_keep` returns `(w(s), true)` and `p_undo` returns `(w(s), s)`.
`selected_preserved` compares the exact subtype value, including its selected
natural, while forgetting the final state. `final_states_differ` rejects a
stronger state-preservation claim. `q_keep`, `q_undo`, and
`recomputation_changes_selection` reject selected equality when the handler
reads again: from false the naturals are respectively 1 and 0. Both still
satisfy the same bound. No universal translation preserving all operations is
inferred from the relation on this client.

## The changed law and its repair

`Keep.catch_put` pushes a preceding write into the protected computation.
`Undo.catch_put` must also put that state at the start of the handler.
`keep_catch_law_fails_for_undo` and `undo_catch_law_fails_for_keep` establish that
neither law can be transferred unchanged to the other policy. The repair is to
select the appropriate scoped law, not to weaken selected-result equality.

The pure `witness`, tree composition proof, both local-law constructions, state
laws, and captured return survive the change. The catch case and final-state
postcondition change. `Undo.put_throw` and `undo_read_raise` establish the relevant
exception commutations; `bad_mixed_law` refutes write/throw commutation for Keep
at false with a write of true. Individually valid state and exception operations
therefore do not justify that mixed tensor law.

## An existing external observation

The client uses `Interaction.Measurement.record`, whose existing
`recording_safe` theorem retains `ResultValid`. `measurement_contract` proves
that both policies return precisely `record s o`, retaining `some o` and that
postcondition. Only a separate local Boolean is tentative. The measurement
controller is captured evidence outside the rollback scope.

The native `measurementKeep` and `measurementUndo` use the two semantic APIs
directly. `measurementTree` expresses the same protected write, exception and
captured record once; `measurement_handler_keep` and `measurement_handler_undo`
prove exact agreement with the native computations. The direct route uses the
catch clauses and the existing `recording_safe` proof. The handler route adds
finite syntax, interpretation and scope, then reuses the same record contract.
There was no timed independent author trial, so this comparison establishes
matched contracts and proof reuse, not a productivity advantage.

`measurement_no_retry` invokes the existing `no_reexecution` theorem. The
`missing_reply_retained` control rolls back the Boolean while preserving an
unknown completion, a false success result, and the prohibition on another
launch. `measurement_world` still requires the existing primitive `Corresponds`
contract before deriving `Completed`. The code does not execute an external
attempt or infer that a physical effect was undone. Recording evidence is the
existing operation being interpreted; external launch, crash and reply semantics
remain the existing module's boundary.

## Sources, scope and next obligation

The inspected local starting revision is
`be1dfca1f57a950950a4e77d81f9fed5140161ee`; Lean and Mathlib remain at the
repository's checked-in pins. The following primary PDFs were inspected on
2026-11-08, with hashes fixing the retrieved editions:

- [Plotkin and Pretnar, Handling Algebraic Effects](https://homepages.inf.ed.ac.uk/gdp/publications/handling-algebraic-effects.pdf),
  Definitions 4.2 and 4.5: handlers must supply total operations satisfying the
  chosen equations. SHA-256 `723e7f4518cdd1eb9b5ac828e84aa97368230c4e8751cccbb7fca3e35e5e0334`.
- [Delaware et al., Modular Monadic Meta-Theory](https://skeuchel.org/files/papers/2013-icfp-modular-monadic-metatheory.pdf),
  §6.1 and Figure 11: state/exception combination changes the catch proof case;
  the two alternative interaction laws have different transformer meanings.
  SHA-256 `731922999513f74818208493dfd220621b4c7470bbd10a6bf96c2275f11a27ef`.

The checked development specializes those obligations independently; it does
not import either paper's full soundness theorem. There is no operational
adequacy theorem, divergence model, concurrent runtime, CBPV migration,
classical pole or EffHOL modality. A scoped exception handler does not provide
classical control or witness extraction from a proposition. These distinctions
remain relevant to the other frontier tasks: a pole or logical translation
must justify its own observations rather than borrowing this result relation.

The concrete next obligation for #196/#235, coordinated with #288/#290, is a
client whose observation is produced *during* the protected computation. It
needs a separate retained external-event component and local rollback laws
that preserve that event trace. This implementation deliberately captures an
existing record before the tentative local work; it does not settle that larger
interaction model. #107 stays paused, #108's held-out theorem unselected, and
#260 inactive.
