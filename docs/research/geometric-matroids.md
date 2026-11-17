# Geometric lattices and simple matroids

[The geometric-matroid API](../../Applications/Matroid/Geometric.lean) proves
both reconstruction directions using the closure constructor from
[#620](https://github.com/VladimirMarko/conaled/issues/620).

## From a lattice to a matroid

Supply a type `L` with `CompleteLattice L`, `Finite L`, `IsAtomistic L` and
`IsUpperModularLattice L`. These state the geometric axioms explicitly. The
complete lattice interface provides joins of sets; upper modularity is
Mathlib's upper semimodularity law: if `a ⊓ b` is covered by `a`, then `b` is
covered by `a ⊔ b`.

`Geometric.matroid L` has all atoms of `L` as its ground. The closure of a set
of atoms consists of the atoms below their join. Upper semimodularity proves
closure exchange: adjoining an atom not already below a join produces a cover.
Atomisticity proves that an element is recovered as the join of the atoms
below it. These are proved consequences of the supplied lattice axioms, not
assumed reconstruction fields.

`Geometric.flatsIso L` is an explicit order isomorphism from `L` to the flats
of the constructed matroid. It sends an element to its atoms-below subset;
its inverse takes the join. The matroid is simple: empty closure is empty,
and singleton closures are singletons. The one-element lattice, whose atom
set is empty, is included.

## From a matroid to its flats and back

`IsSimple M` states empty and singleton closure conditions on the actual ground.
The existing `Flat M` retains labelled subsets. This module proves that its
lattice is upper semimodular, that it is finite when `M` is finite, and that it
is atomistic when `M` is simple. The upper-semimodularity proof uses native
matroid closure exchange; it also applies to nonsimple matroids.

`Flat.groundEquivAtoms M` sends each element of `M.E` to its singleton flat,
viewed as an atom. The proof of bijectivity uses simplicity. `Flat.reconstruct`
identifies the geometric reconstruction with the ground restriction of `M`,
relabelled by this particular equivalence. This checks the mathematical
structure; a carrier bijection alone would not suffice.

`Flat.restore M` reverses that relabelling and embeds the ground subtype into
the original ambient type. `Flat.restore_eq M` proves equality with `M`.
Consequently ground membership, independence, circuits, closure and rank are
preserved on every ambient subset, including subsets containing outside
elements. The ambient complement is retained as outside the ground.

The round trips have different result types: the lattice round trip is an
order isomorphism, while the matroid round trip is equality after the specified
relabelling and embedding. No categorical equivalence or cubical path theorem
is claimed. Ordinary Lean equality, order isomorphisms and the presentation
bridges suffice for these results.

## Checked uses and limits

[The examples](../../Examples/GeometricMatroids.lean) use the Boolean lattice
of subsets of a two-element set, including a calculation showing that one atom
does not generate the other. They also cover the empty atom set. For the
uniform matroid `U₂,₃`, singleton flats generate a geometric lattice with a
checked failure of distributivity. Its reconstruction recovers `U₂,₃` and
agrees with the rank-presentation route. A free matroid on a proper subset of
an ambient finite type checks outside-ground behavior.

The loop and parallel-class controls from #620 remain in the examples. Their
abstract flat lattices forget multiplicities; the simple-matroid hypothesis
is what permits recovery by atoms. The constructions do not extend that
recovery claim to arbitrary matroids.

The pinned Mathlib supplies closure exchange, closure operators, Galois
insertions, atomistic lattices and the upper-semimodularity class. This module
connects those interfaces and reuses their order and matroid theorems. It does
not introduce a competing lattice hierarchy.
