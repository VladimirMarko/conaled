# Computational equivalence witnesses

Issue [#453](https://github.com/VladimirMarko/conaled/issues/453) supplies a
bounded checked design for Felix's `Equivalent q`. The source is `Equiv.agda`
at `6f36d28097db7ea5f5df3263db3e8be08f74e490`, lines 17–49 and 114–118.
Its relation takes values in `Set q`; reflexivity, symmetry and transitivity
are operations. It does not ask for equations between these operations.

## Chosen boundary

[WitnessEquivalence](../../SquareKit/WitnessEquivalence.lean) retains the
relation in `Type w`, with independent object, arrow and witness universes.
It leaves the existing `HomEquiv` unchanged. `induced` recovers `H-equiv` by
pulling back the actual witness type along a raw interpretation.

`erase` maps witnesses to `Nonempty`, supplying the existing setoid relation.
`ofHomEquiv` embeds the existing proposition-valued relation using `PLift`.
`erase_ofHomEquiv` proves recovery of that relation, while `liftCongr` and
`liftLaws` embed existing congruence and category laws. Erasure in the other
direction cannot recover the original computational witnesses in general.
The retained Boolean example proves this loss explicitly for comma squares.

The separate layer is preferable to replacing `HomEquiv`: the existing quotient
adapter deliberately identifies arrows according to a proposition and has no
place for distinct witnesses of that proposition. Ordinary Lean callers and
accepted proof-erased results acquire no new parameters, instances or syntax.
A mere squash of witnesses would recover inhabitation but fail #453's contract.

## Law transport and comma prototype

`Congr`, `Laws` and `Preservation` contain computational witnesses. `Reflection`
returns a selected source witness for a target witness. `transportLaws` composes
these operations to produce source witnesses, using the same sequence of
category equations as existing law transport. It requires neither uniqueness
nor a coherent inverse to reflection. Each structure has an explicit erasure
adapter where used by the old API. A reflection with only a `Prop`-valued
existence result would not supply this computational transport interface.

[WitnessComma](../../SquareKit/WitnessComma.lean) is the bounded prototype.
Its square retains both sides and a witness of commutativity. Identity and
composition use the target witness congruence/laws and interpretation
preservation; source category laws are unnecessary for these operations.
`erase_ident` and `erase_comp` recover the existing comma constructions.
The existing `Comma.Hom.ext` cannot be lifted to equality of retained squares:
it intentionally ignores the proposition-valued commutativity field. An
equality theorem for retained squares must also account for that field.

A future comma hom relation can compare only the two sides with their retained
relation witnesses, as the source construction does. That relation need not
identify all square witnesses as equal Lean data. Adding higher cells between
commutativity witnesses, or proving coherence equations between them, is a
separate contract. No claim of a higher category is made here. Lawful Mathlib
functors and hom quotients remain explicit erased adapters.

## Checked cases and statement review

[The examples](../../Examples/WitnessEquivalence.lean) use a one-object,
one-arrow category with Boolean relation witnesses. Reflexivity chooses false,
symmetry negates, and transitivity is NAND. NAND's failure of associativity is
proved. This is a valid model of the exact operations-only interface, showing
why higher coherence cannot be inferred from it.

False and true witnesses remain distinct. Two choices of reflection produce
distinct transported unit-law witnesses. Two comma squares with identical sides
remain distinct, while their erasures are equal. The erased category laws feed
the unchanged `HomQuotient.category`; the prototype's identity and composition
recover the old comma operations after erasure. Existing proposition-valued
relations recover their meaning through the lift/erase round trip.

Statement review checked independent universes, retained data versus erased
proofs, reflection direction, and the absence of hidden coherence assumptions.
The example is deliberately not a groupoid of witnesses: that stronger
structure is not a premise of Felix's `Equivalent q`.

## Coordination and limits

[#36](https://github.com/VladimirMarko/conaled/issues/36) owns actual higher
identity and model construction. This interface neither supplies nor replaces
its paths, higher cells or coherence proofs.
[#235](https://github.com/VladimirMarko/conaled/issues/235) owns broader
preservation evolution and author trials. The mismatch demonstrated here is
precise: proposition-valued laws and comma commutativity erase distinguishable
witnesses. The separate layer resolves that mismatch for this bounded design;
a broad retrofit and independent usability trials are not claimed. Future
clients can request additional coherence while retaining this weaker contract.

Focused checks cover both modules and examples. Full integrated build,
exhaustive audit and independent Standards/Spec review remain pending.
