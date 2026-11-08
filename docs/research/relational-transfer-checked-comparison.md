# Checked relational transfer on FIFO and intervals

[#374](https://github.com/VladimirMarko/conaled/issues/374) supplies a checked
comparison using the existing registration interfaces. The two routes already
construct typed implementations and relation witnesses for this bounded work;
no new annotation engine is needed. The new
[comparison module](../../Examples/RelationalTransfer.lean) checks exact
agreement with direct constructions, selected-output composition, and the
partial-domain and representation-reset controls left as paper work in the
[#295 report](relational-proof-transfer.md).

The second client is rational interval arithmetic. Its relation `Contains I x`
is many-to-many: one interval contains several points, and several intervals
contain the same point. FIFO's relation `Inv q ∧ fromSL q = xs` is functional
on valid states but noninjective, with an invariant-restricted domain. These
relations have different observation and type obligations. Neither is replaced
by a universal equality or PER. Interval enclosure is also distinct from the
metric error contracts in #372.

## Frozen outputs and existing derivation mechanisms

The FIFO input remains the report's word
`[enqueue 1, enqueue 2, delete, enqueue 3]`. The required output is the actual
state produced by the chosen symmetric-list operations, a witness relating it
to the ordinary list execution, and equality of the final `Option Nat` head.
The empty-input abstract result is `[2,3]`, with head `some 2`.

`FIFO.direct` proves the frozen certificate by applying enqueue, enqueue,
delete and enqueue witnesses in that order. `FIFO.registered` invokes the
existing `AbstractFIFOSyntax` registration and compiler for any command word.
`FIFO.registered_selected` proves that the generated state is exactly the
ordinary `run symmetric` result. `FIFO.direct_registered` compares the complete
subtype outputs, so it cannot pass by replacing one selected layout with another
layout having the same decode. `FIFO.registered_head` then uses the existing
public head witness.

The interval input is the existing shared arithmetic source term

```text
let p = x*y in p*p + x
```

For related inputs `Contains I x` and `Contains J y`, the output must retain
`add (mul (mul I J) (mul I J)) I` and its enclosure witness for
`(x*y)*(x*y)+x`. `Interval.direct` applies the local product, square and addition
lemmas, sharing the first product witness. `Interval.registered` uses the
existing `IntervalAnalysis.primitives` and `FirstOrderRelations` compiler.
`Interval.direct_registered` proves equality of the selected subtype outputs.
This is the same contract on both routes, not a comparison between direct
endpoint equality and a weaker generated existence statement.

The code inspected initially was pinned at
`1e2ebdfaae9899898fe84f1d6a0a0f16443eecaf`. These existing modules already provide
the mechanisms used by the comparison:

| Existing mechanism | Obligation it already discharges |
|---|---|
| [AbstractFIFO](../../Applications/Sequences/AbstractFIFO.lean) | Operation simulations, word recursion, observation equality and matching-middle representation composition. |
| [AbstractFIFOSyntax](../../Applications/Sequences/AbstractFIFOSyntax.lean) | Command primitive registration, typed word construction by `plug`, interpretation, exact selected execution, source substitution and append. |
| [STLCRelations](../../SquareKit/STLCRelations.lean) | Type-directed relations for unit, products, arrows and sums; relational compilation from primitive certificates. |
| [FirstOrderRelations](../../SquareKit/FirstOrder.lean) | Unit/product type interpretation, local arithmetic registration and correctness for every admitted first-order term, including let-sharing. |
| [IntervalAnalysis](../../Applications/Intervals/Arithmetic.lean) | Four arithmetic primitive cases and whole-term enclosure. |
| [Relational](../../SquareKit/Relations.lean) | Relation-preserving maps, their composition, and total-witness squares retaining both selected values. |

This stronger starting inventory matters. Treating registration of FIFO
commands or composition of interval primitive certificates as new mechanisms
would overstate #374's contribution. The new result is the checked comparison
and its stronger selected-output controls.

## Term, type, recursor and equality obligations

The FIFO state carrier changes from a list to a symmetric pair. `Nat`, commands
and command words remain the same values. `Syntax.plug` recursively constructs
a typed state expression from the word; its existing `eval_plug`, `compile_plug`
and `program_runs` theorems connect that recursion to the native client.
`FIFO.registered_function` additionally compiles a lambda and uses
`STLCRelations.compile_apply_preserves` on related state arguments. The arrow
relation is quantified preservation of related arguments, not equality of
arbitrary runtime functions or a decoder for them. The checked source
substitution case reuses `Syntax.subst_plug` for arbitrary well-typed holes.

The queue compiler has a single base sort for state. It does not encode
`Option Nat` as that base sort. Endpoint observation remains a separate
operation with the existing equality witness in `Simulation.head`. Likewise,
word recursion takes place in the host definition `plug`; these results do not
claim that the STLC source has a list recursor constructor or that arbitrary
Lean induction principles have been translated.

The interval client uses first-order unit/product types and `letE`, without
arrows or an endpoint observer. The product relation requires enclosure of both
coordinates. Sharing reuses the actual interval result, while its relation
permits several possible represented points. The source type indices and the
primitive registration's domain/codomain indices enforce these obligations;
they are not an untyped operation table.

`transport_equalities` is ordinary equality elimination in an arbitrary binary
relation. Both FIFO generated certificates consume it to align source evaluation
with the native word result. The interval case uses it on the semantic equality
`x + -x = 0` to transport an enclosure witness. It never infers equality of raw
interval representations. The existing wider-than-singleton cancellation
counterexample remains checked. This bounded use of equality does not supply
a general dependent type translation, universe annotation inference, or a
proof importer for arbitrary Lean theorems.

The source comparison remains with Cohen, Crance and Mahboubi,
[Trocq v1, Theorem 4.7 and §4.5](https://arxiv.org/html/2310.14022v1).
Its certified conclusion depends on successful term and type translations,
with registered constants at suitable annotations. The local compilers above
already construct those ingredients for their fixed source languages. This
comparison neither reimplements that full calculus nor establishes a Trocq
plugin result. Kappelmann's
[partial Galois transport v1, Theorem 4.10](https://arxiv.org/pdf/2303.05244v1)
also makes the matching middle relation explicit in composition. The local
comparison uses relation-preserving maps directly, without manufacturing
encoders, restricted orders or inverse laws unnecessary for the selected work.

## Composition and rejection controls

`FIFO.registered_append` equates execution of a concatenated word with two
generated executions. The second consumes the exact first selected state and
its relation witness. `FIFO.routeWitness` retains the ordinary intermediate list
as data when comparing two implementation routes; `route_middle` identifies it
with the selected list execution. `route_observation` composes the public head
equalities without identifying hidden layouts.

Both clients also instantiate the same existing total-witness composition law.
`FIFO.witness_append` pastes word certificates; `Interval.witness_negated` pastes
compiled arithmetic with negation. `selected_witness` and the concrete interval
case check that these packages retain the implementation component. The new
`selected_composition` theorem specializes the existing `witness_compose` law;
it is not presented as a newly discovered composition theorem.

The checked controls are:

| Control | What fails and what remains allowed |
|---|---|
| FIFO hidden layout observer | `no_layout_registration` rules out an equality-preserving front-length observer using the existing two valid layouts. Public heads remain equal. |
| FIFO partial domain | `invalid_domain` shows that `([], [1,2])` decodes to `[2,1]` but has the wrong head. Dropping `Inv` invalidates even the empty-word observation. |
| FIFO selected reset | `no_selected_reset` rules out every list encoder claiming to recover the selected raw output for all related inputs. The empty-word client retains the original layout, so the two valid layouts already refute such a reset. |
| Interval nonfunctionality | `nonfunctional` proves that the same unit box contains two distinct points. A decoded-point graph cannot equal this relation. |
| Interval partial domain | `partial_domain` proves that the reversed interval `[1,0]` has no related point. No total valid-input assumption is silently added. |
| Interval hidden endpoint observer | `no_endpoint_registration` rules out a point observer agreeing with every related interval's lower endpoint. |
| Interval selected reset | `selected_reset_fails` proves that replacing the shared term's selected wide interval by `[0,0]` changes the chosen output, even though the replacement still encloses the semantic result at zero. |

All negative controls are statements about these supplied relations and
observations. They are not failures of all possible transfer systems. A different
consumer could permit normalization, but it would have a different contract.

## Setup and recurring obligations

This ledger counts explicit obligations for the two retained fixtures. It is
not a time measurement, a code-size comparison, or evidence of productivity.
Existing generic proofs are charged as prior setup, not counted as new savings.

| Work | FIFO | Interval shared arithmetic |
|---|---|---|
| Existing representation setup | `Inv` plus decode; four simulation fields: empty, enqueue, delete, head. | `Contains`; four primitive cases: literal, add, multiply, negate. |
| Existing registration setup | One command-primitive constructor with enqueue/delete behavior; the existing `stepSquare` consumes the two mutation fields. Empty and head remain native boundary evidence. | The four existing arithmetic cases provide typed primitive implementations and relation proofs. |
| Existing type/recursion setup | Unit/product/arrow interpretation for the tested syntax; word recursion, source substitution and compilation already proved. | Unit/product interpretation, typed term recursion and let-sharing already proved. |
| Direct recurring certificate in the frozen fixture | Four mutation-witness applications; final head consumes the observation field. | Three arithmetic-witness applications: shared product, square, addition. |
| Generated recurring certificate | Supply the typed word term and related input; invoke existing compilation and the evaluation alignment. | Supply `Arithmetic.shared` and both input witnesses; invoke existing whole-term enclosure. |
| New comparison obligations | Exact selected-state equality, compiled arrow application, selected composition, domain and reset controls. | Exact selected-interval equality, shared witness composition, domain and reset controls. |

Both routes still need local operation evidence when a representation changes.
Both retain ordinary clients without compiler imports in their operation-only
interfaces. The direct route remains short for the frozen clients, while the
existing compilers derive certificates for their admitted source syntax.
This result does not rank either route for future authoring tasks.

#290 and #235 retain the next obligation: choose an independently specified
indexed-output client whose result relation depends on related indices, then
compare complete term-and-type transport with the direct proof. It should
preserve the selected fiber data and expose any equality-transport premises.
The present comparison supplies neither arbitrary dependent relators nor
canonical representative transport. #107 stays paused, #108's held-out theorem
stays unselected, and #260 stays inactive.
