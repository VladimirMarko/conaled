# ADR 0002 — Relations for many-valued interpretations, pullbacks for agreement

**Status:** Accepted.

## Context

A decoding function suffices for redundant exact representations. It cannot
faithfully express that an interval contains many values or that one signal
has a particular value over a chosen stability interval. Choosing one point
would discard the property the analysis is supposed to establish.

## Decision

Add `Relational.RelRep` and `Relational.RelSquare`. Their primitive contract is
preservation of an explicitly given relation. Define composition, products,
and function relations and prove their category/product/exponential laws.
Embed ordinary squares as graph relations. Present relational squares as
ordinary commuting squares on total relation-witness spaces via
`witnessSquare`, and prove this presentation preserves composition.

For independent exact implementations of the same specification, use the
pullback `Squares.synchronized`. Its carrier consists of pairs that decode to
the same semantic value. `synchronize` proves the outputs still agree. This
is stronger than merely putting two unrelated certificates in a pair.

Add a relational target for the existing first-order compiler. The theorem
`FirstOrderRelations.compile_preserves` lifts locally proved primitive
obligations to every source term and environment.

## Alternatives

* Treat interval operations as an exact interpretation of point functions:
  invalid, since extensionally equal point functions can have different
  enclosure computations.
* Demand injective decoders or representation isomorphisms: excludes the
  redundant encodings that motivated this design.
* Claim witness presentations are efficient runtime encodings: the semantic
  value in a witness is data, and an erasure theorem has not been supplied.

## Consequences

Exact equality, enclosure, differentiability, and stability keep their distinct
contracts while sharing composition. The relation-witness construction is a
mathematical bridge and never a justification for deleting semantic data.
The independent dependent-family development in `Dependent.lean` continues to
handle indexed transport; a relation is not used to conceal an ill-typed
dependent substitution.

## Checked evidence

`Relational.compose_assoc`, `first_pair`, `pair_eta`, `uncurry_curry`,
`curry_uncurry`, `toSquare_ofSquare`, `witness_compose`,
`Squares.synchronize_agrees`, and `FirstOrderRelations.compile_preserves`.
