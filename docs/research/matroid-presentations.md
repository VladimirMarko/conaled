# Finite matroid presentations

[The presentation API](../../Applications/Matroid/Presentations.lean) connects
five descriptions through Mathlib's `Matroid`. Each bridge reconstructs the
entire labelled matroid and recovers the original presentation record. Compose
`FiniteMatroid.basisEquiv`, `independenceEquiv`, `circuitEquiv`, `closureEquiv`
and `rankEquiv` to change descriptions; `route_agreement` proves that inserting
an intermediate description does not change the result.

These are equivalences of object types. Carrier relabellings use `mapEquiv`;
`relabel_indep`, `relabel_circuit`, `relabel_closure` and `relabel_rank` preserve
the corresponding observations. No category equivalence is asserted.

## Inputs and reconstruction

The ambient type can be infinite, but the specified ground set must be finite.
Independence and circuits exclude outside elements. Closure and rank ignore
them by intersecting inputs with the ground. Keeping the ground is necessary:
the empty independent set alone cannot distinguish empty ground from all loops.

| Presentation | Supplied laws | Construction |
|---|---|---|
| Bases | Nonempty family, basis exchange, containment in finite ground | Mathlib `Matroid.ofIsBaseOfFinite` |
| Independence | Mathlib `IndepMatroid` axioms and finite ground | Mathlib `IndepMatroid.matroid` |
| Circuits | Nonempty circuits, containment, antichain, augmentation of circuit-free sets | Bounded independence constructor, followed by recovery of minimal dependent sets |
| Closure | Ground normalization, extensivity, monotonicity, idempotence, Steinitz exchange | Independence means that no element lies in the closure of the others; maximal independent sets span the ground |
| Rank | Natural-valued, zero at empty, ground normalization, monotonicity, insertion increases rank by at most one, zero increments persist under inclusion | Closure consists of ground elements whose insertion does not increase rank |

The circuit exchange field is stated on circuit-free sets. This adapter does
not itself derive augmentation from the usual circuit-elimination axiom; the
standard-axiom adapter below supplies that derivation. The rank
interface uses local increments rather than taking submodularity as a field.
Neither interface asks for a matroid realization or assumes reconstruction.
Both recover their supplied data exactly; native finite matroids supply all
their laws. In particular, native submodularity can be reused after rank
reconstruction. The finite hypothesis is used to construct maximal independent
sets and to show that adjoining the rank closure does not change rank.

## Standard submodular rank axioms

[SubmodularRank.lean](../../Applications/Matroid/SubmodularRank.lean) also accepts
the familiar natural-valued rank axioms: empty rank zero, monotonicity, a
cardinality bound and submodularity. `SubmodularRankPresentation` retains a
finite ground in an arbitrary ambient type, with `rank (X ∩ ground) = rank X`
and `rank X ≤ (X ∩ ground).ncard` for every ambient subset. Thus infinite
ambient subsets cause no ambiguity in the natural-valued cardinality bound.

`insert_le` derives unit increments from submodularity and the singleton bound;
`persist` derives persistence of zero increments from submodularity. `toRank`
then uses the existing local-rank constructor. `matroid_eRk` recovers the supplied
rank on every subset, and `matroid_ofMatroid` recovers the entire presentation.
`ofMatroid` extracts the standard axioms from a native finite matroid.
`rankEquiv` proves the two rank presentations equivalent, while
`FiniteMatroid.submodularRankEquiv` connects the new presentation to every
existing hub route. These are equivalences of object types, without a new
choice of matroid morphisms.

`relabel` retains both the ground and ranks under an ambient carrier equivalence.
`relabel_matroid` identifies the reconstructed matroid with native `mapEquiv`;
`relabel_refl` and `relabel_trans` recover the whole presentation under identity
and composed relabellings. The existing local-increment API remains available
when an author's input is already given by insertion behavior. The standard
interface suits inputs where submodularity and cardinality bounds are the
available facts; callers supply no extra exchange or realizability premise.

[Checked applications](../../Examples/SubmodularRank.lean) supply truncated
cardinality directly, prove agreement with the existing uniform-matroid
constructor, and recover `U₂,₃`. They cover empty ground, loops, parallel
elements, outside-ground and infinite ambient subsets, presentation routes and
two nonidentity relabellings. A monotone cardinality-bounded function on `Bool`
violates submodularity at the two singleton sets, separating the missing axiom.

This completes the rank portion of [#628](https://github.com/VladimirMarko/conaled/issues/628).
The result
reuses the existing reconstruction proof and preserves its direct clients;
it does not establish an author-productivity result. It supplies application
evidence for [#636](https://github.com/VladimirMarko/conaled/issues/636).

## Standard circuit elimination

[CircuitElimination.lean](../../Applications/Matroid/CircuitElimination.lean)
accepts a finite ground, nonempty contained circuits, an antichain law, and
elimination of a common element from two distinct circuits. It derives
augmentation of circuit-free sets. No matroid realization or exchange premise
is required from the caller.

The proof first shows that adjoining an element to an independent set creates
at most one circuit. Removing another element of that circuit preserves
maximal independence. Finite induction then extends an independent set using
only it and a chosen maximal independent set, which yields augmentation.
`toCircuit` feeds this result to the existing reconstruction.

`matroid_isCircuit` recovers every supplied circuit; `ofMatroid` extracts the
standard axioms from native finite matroids. Both round trips preserve the
whole presentation, including its ground. `circuitEquiv` connects the two
circuit interfaces, and `FiniteMatroid.circuitEliminationEquiv` connects the
new input to all existing presentation routes. `relabel` preserves circuits
under ambient carrier equivalences and satisfies identity and composition.

Use this interface when elimination is the available circuit law. The existing
`CircuitPresentation` remains useful when circuit-free augmentation is already
known. Independence requires ground containment, so adding an outside-ground
element is forbidden even when it lies in no supplied circuit.

[Checked applications](../../Examples/CircuitElimination.lean) supply a single
circuit directly, recover the existing U₂,₃ client, and check loops, parallel
elements, empty ground, outside elements, presentation routes and relabelling.
The nonempty antichain `{0,1}`, `{0,2}` fails elimination at `0`, showing that
the other circuit conditions do not suffice. Together with the rank adapter,
this completes the constructors requested by
[#628](https://github.com/VladimirMarko/conaled/issues/628).

## Reuse of Mathlib

The pinned Mathlib already supplies basis and independence constructors,
observational characterizations by circuits, closure and extended-natural rank,
and extensionality theorems. It has no constructor from closure or rank axioms
or standard-circuit-axiom constructors in these modules. The new constructions reuse its independence constructor,
closure exchange, basis extension and rank theorems. They do not copy the
native matroid API into each presentation.

## Flats and information loss

[`Flat M`](../../Applications/Matroid/Flats.lean) uses the closed elements of
Mathlib's closure operator on subsets of `M.E`. Its complete lattice comes from
the closure operator's Galois insertion. `Flat.carrier` retains the embedding as
labelled subsets; its order is inclusion. `Flat.span` closes the ground portion
of an ambient set and satisfies the least-flat property.

[Checked examples](../../Examples/MatroidPresentations.lean) include uniform
matroids, `U₂,₃`, a one-edge graphic matroid with independence characterized by
Mathlib's graph acyclicity, rank data supplied directly, relabelling, conversion
route agreement, and closure-exchange reuse through rank and circuits. Outside
ground elements are explicitly tested. The graphic example is a forest; no
general graph-to-matroid constructor is claimed.

All-loop matroids on grounds of different sizes have isomorphic one-element
flat lattices. Nonempty parallel classes of different sizes have isomorphic
two-element flat lattices. The examples prove these order isomorphisms and show
that the one- and two-element carriers cannot be equivalent. A two-element
parallel class is checked to be a circuit. Thus the abstract lattice forgets
loop counts and parallel multiplicities.

[#626](https://github.com/VladimirMarko/conaled/issues/626) owns reconstruction
between finite simple matroids and finite atomistic upper-semimodular lattices.
It follows this deliverable under the owner's approved staging. The closure
constructor here provides the route from atom-generated closure to a matroid.
