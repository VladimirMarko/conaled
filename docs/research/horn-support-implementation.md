# Checked finite Horn support

[#379](https://github.com/VladimirMarko/conaled/issues/379) implements the
[fixed-basis construction](atomic-base-support-construction.md) in two modules.
[HornSupport](../../SquareKit/HornSupport.lean) defines finite Horn rules,
inductive atomic derivability, atoms/implication formulas, and support over an
explicit permitted basis. [HornDerivations](../../SquareKit/HornDerivations.lean)
adds optional selected trees and ordered traces. Support clients need only the
first module.

The source boundary remains Gheorghiu and Pym, Definitions 2.1–2.6 and Figure 2,
[primary manuscript](https://www.cantab.net/users/david.pym/Proof_theoretic_Semantics_for_Second_order_Logic.pdf),
with the SHA-256 recorded in the construction report. Only zero/first-level
rules, empty atomic assumptions, and closed atoms/implication are used. Finite
bases, empty-context consequence, and labelled traces are local choices.
No second-order completeness claim is formalized.

## Interfaces and assumptions

A `Rule Atom` has a finite premise set and a conclusion; `Base Atom` is a finite
rule set. `Derivable B a` is inductive in `Prop`. Its only constructor requires
proofs of every premise of a rule in `B`. Thus a cycle without a leaf cannot
supply an atom. `Derivable.invariant` proves closure invariants, including the
negative fixtures. `Derivable.weaken` copies the inductive derivation along
rule inclusion.

`Support K B A` recurses on the formula. Implication quantifies over every
`D ∈ K` containing `B`, with antecedent and consequent both interpreted at `D`.
The definition is total on finite bases; clients claiming a judgment within a
basis supply `B ∈ K`. `application` and `empty_agreement` require that membership
because their proofs use the reflexive extension. `persistence` proves a
stronger statement needing only inclusion, with the same `K` on both sides.
No closure of `K` under union or base extension is assumed. `Consequence` uses a
finite list context with universal membership, so repeats and order do not alter
its meaning. `introduction` transports every retained context member to the
inner future base; `consequence_application` evaluates both premises there.

The selected-data layer specializes existing
[finite rules and derivations](../../SquareKit/DependentTheoryMaps.lean).
A fixed ambient table assigns each label a list of distinct premises and a
conclusion. A finite active-label set determines a presentation. Inclusion of
these sets retains the exact ordered signature of every old label; new labels
have their signatures in the same ambient table. This representation covers
compatible additions within that table. Changing a label's signature in place
is not an inclusion: the repair fixture uses a fresh label `bprime`.

`Tree` is the existing `Derivation` with empty open-assumption fibers. `map`
copies a selected tree under inclusion; its identity and composition laws are
actual tree equalities. `trace` visits children in premise order, then the root.
`size` counts its entries, one per node. `trace_map` and `size_map` preserve those
observations. `eraseTree` supplies atomic derivability of the finite erased
base. `erase_map` compares proofs of that target proposition; proof irrelevance
makes it a commuting square, not an equality or recovery of trees.

## Checked cases and statement review

[Support examples](../../Examples/HornSupport.lean) retain the complete B0/B1/B2
truth table, including strict inclusions and the implication `p → q` at B0
where no atom is derivable. The refutation of `q → r` at B0 uses B1 as a future
base. Singleton-basis vacuity and failure under a larger basis keep the current
empty base and formula unchanged. Nested and curried implication cases consume
`introduction`, `application`, `empty_agreement`, and `persistence`; the curried
case applies introduction with a nonempty retained context.

[Selected-tree examples](../../Examples/HornDerivations.lean) check postorder
traces, minimum node counts, and a minimum-proof reselection that changes the
trace. Every minimum at L3 has trace `[d]`, so tie breaking cannot retain
the copied trace. At the same L3, two actual trees erase to the same atomic proposition
but have unequal traces. `no_trace_recovery` rules out a function of that
proposition's proof recovering every selected trace. It does not rule out
finding some proof or choosing a canonical one.

Lminus derives only `p`; both `q` and `p → q` fail. The `repairMap` supplies local certificates to the existing `TheoryMap`
transport. Its recursive `repair` translates every L1 tree, replacing a `b` use
by `bprime` with an added `e` child.
The selected q tree changes from `[a,b]` to `[a,a,e,bprime]`, with four nodes.
`repair_support` proves `p → q` directly at every future extension of Lrepair.
Neither this implication proof nor the tree translation invokes inclusion
between the old and replacement bases.

Statement review checked quantifier order, finite-rule membership, the absence
of implicit assumptions, fixed-basis recursion, and the distinction between
Prop equality, tree equality, and trace equality. The positive fixtures establish
usable bases and actual trees; the empty-base and replacement negatives check
vacuity and missing-premise boundaries. These cases do not establish arbitrary
basis-change or rule-replacement transport for formulas. That compatibility
question remains with [#235](https://github.com/VladimirMarko/conaled/issues/235).
The implementation requires no adapter to the incumbent graph or scalar calculi,
no migration of their consumers, and no universal selected-witness recovery.
