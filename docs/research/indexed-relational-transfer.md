# Indexed relational transport with selected cursor data

[#383](https://github.com/VladimirMarko/conaled/issues/383) extends the
[#374 comparison](relational-transfer-checked-comparison.md) to varying result
fibers. The checked [cursor client](../../Examples/IndexedRelationalTransfer.lean)
uses the existing indexed rule certificates and relational squares. It adds
no general transport interface.

## Independent client and matching observations

`Cursor n` stores a position in `Fin n` and an ordered Boolean command history.
A command adds one available position. `true` also advances the selected
position; `false` leaves it unchanged. Both append the command to history.
The native client `direct` performs advance, reserve, advance. Starting at
position 1 in capacity 2 with empty history, it returns position 3 in capacity
5 with history `[true,false,true]`.

The specification was frozen before constructing the rule interpretation.
`direct_reserve` proves the native comparison directly from `reserve_step`.
Reserving `k` additional positions changes the capacity from `n` to `k+n`
without changing the position value or history. Reserving 2 and then 3 before
the client gives capacity 10, position 3 and the same ordered history.
These expected values are checked through `generated_direct`, which connects
the transported derivation to the independent client.

The index relation is `m = k+n`. The result relation compares position values
and complete histories in `Cursor n` and `Cursor m`. This is a genuine change
of fiber: `Fin 2` and `Fin 5` are different bounded types, both inhabited in
the retained cases. `reserve` is not surjective: a cursor in capacity 3 selecting
position 2 has no preimage in capacity 2. No type equivalence or reverse
translation is claimed.

`generatedCertificate` and `directCertificate` return the selected cursor
paired with its relation proof. `certificates_agree` proves equality of these
complete subtype outputs under matching assumptions. The equality uses Lean
propositional equality and proof irrelevance for the proposition field; position
and history are retained data. It is not merely an existence comparison.

## Reused interfaces and local obligations

| Existing interface | Use and boundary |
|---|---|
| `DependentOperation.Local.compile_meaning` | Inspected but not applied: its meaning map preserves the same index `n`. That theorem alone cannot justify this capacity change. |
| `DependentBranchTheoryMaps.TheoryMap` | `expansion k` changes judgment `n` to `k+n`, supplying one primitive command certificate with one transformed premise. |
| `DependentBranchSemantics.LocalMeaning` | `expansion_local` checks the single command's selected-value law using `reserve_step`. |
| `TheoryMap.interpret_transport` | Derives `expand_selected` for every admitted command tree, including its output fiber and complete cursor. |
| `TheoryMap.comp_transport` | Derives `twice_terms`, equality of the actual transported derivations across two changes. |
| `Relational.RelSquare` and `Relational.compose` | `stepSquare` supplies local relations between arbitrary cursor capacities; `directSquare` composes three matching interfaces and proves `direct_related`. |

The type action is explicit in the indexed certificate, rather than a Nat tag
attached to an untyped output. The term action follows by the existing dependent
recursion. `expansion` does not assume a whole-program preservation theorem.
`twice_selected` and `generated_direct` retain the selected value after both
changes; `twice_terms` separately retains the rule tree.

For this client the admissible index relation is functional once the reserve
amount is fixed, and the value relation determines a unique target cursor at
a fixed target capacity. This tests a graph-like dependent relation. It does
not establish a general many-to-many dependent relator. #374's interval client
continues to supply its separate genuinely many-to-many comparison.

## Equality transport and negative controls

`cast_related` eliminates an explicit equality of capacities. `reserve_twice`
uses `Nat.add_assoc` to compare the nested output fiber `l+(k+n)` with
`(l+k)+n`, preserving the complete record. `transport_equalities` allows both
indices to be rewritten only when their respective equalities are supplied.
No relation between position values is treated as equality of capacities.

The checked controls distinguish the obligations:

- Two cursors can inhabit the same fiber with different selected positions.
  An inhabitance result does not recover the required output.
- Reflexive witnesses for two different middle cursors do not compose into a
  relation between their endpoints. `related_trans` requires the actual same
  middle cursor, and square composition requires matching intermediate carriers.
- Advancing and reserving have the same output capacity but different positions
  and histories. Matching type actions do not supply the local term law.
- A cursor and its reservation have related values at unequal capacities.
  The value relation cannot supply the equality needed for an index cast.
- Reservation misses target values selecting newly introduced positions, so
  preservation cannot be advertised as equivalence or reflection of all outputs.

## Author obligations and remaining scope

The direct route needs the operation law and three rewrites for this fixed
client. The registered route additionally supplies the rule table, its model,
a local certificate, and the local interpretation law. Once supplied, the
existing transport theorem handles arbitrary finite command trees, and existing
certificate composition handles repeated index changes. New command operations
would require corresponding certificates and local laws. Both routes remain
available; no timing or independent author trial was performed here, and code
size establishes no productivity advantage.

The fragment has unary commands, a Nat capacity base, selected finite positions
and list histories. It does not implement arbitrary dependent contexts,
higher-identity witnesses, recursor import, automatic representative selection,
or arbitrary Lean proof translation. No existing FIFO, interval or dependent
operation client changes. The bounded comparison exposes no missing generic
operation, so #290 and #235 retain broader dependent-relator exploration without
another interface being introduced solely for this fixture.
