# Finite universe loops and permutation observations

Issue #531 specializes native univalence to constant finite codes. The checked
client is `Examples/FiniteUniverseLoops.lean`; the reusable arguments are in
`DiscreteEquivalences.lean` and `UniverseLoopObservations.lean` under
`SquareKit/Internal/Cubical/`.

## Closed loops and native families

For a host type `S : Type`, `loops S` is the native path family from the constant
code for `S` to itself, over the raised terminal context. `loopPermutation p`
assigns a host permutation to each closed section `p` of this family.
`twoPath_iff_permutation` proves

```
Nonempty (Term (homogeneousPath (loops S) p q)) ↔
  loopPermutation p = loopPermutation q
```

The left side asks for a native two-path. It is stronger than the host
inequality between chosen terms used by the earlier compositional examples.
The result classifies closed loop components without constructing a quotient.
`loopPermutation_ua` proves that every permutation occurs.

This classification requires an argument for discreteness. A native
contractible-fiber equivalence between constant families induces a bijection
of their sections: its inverse takes the chosen fiber center, and its inverse
laws follow from native contraction paths and `discretePath_endpoints`.
Over the terminal context, naturality along the map to the zero-dimensional
cube makes each section constant. `closedSections` identifies these sections
with their values. No premise equating arbitrary native paths with host
identity is added.

`permutationMap` recovers the entire transport map of a closed loop from the
resulting permutation. `classifyLoop` then applies the existing transport
homotopy comparison to connect the permutation's ua loop to the original
loop. The implication in the other direction uses `transportTwoPath`: a native
path between universe paths induces a native path between their actual
transported outputs. Observation into constant coefficients gives host
equality only at that final discrete observation.

At the native family level, `booleanLoopFamilyEquivalence` retains the full
univalence equivalence between the Boolean loop family and the self-equivalence
family, including chosen contractible-fiber data. The closed permutation
classification does not replace this with an equality of records or assert
that all choices of contraction are definitionally equal.

## Boolean separation and noncommuting permutations

`booleanPermutation_cases` proves that a Boolean permutation is identity or
negation. `booleanLoop_cases` therefore gives a native two-path from every
closed Boolean loop to one of those two representatives.
`booleanLoops_no_twoPath` separates the representatives: identity transports
`true` to `true`, while negation transports it to `false`.
`booleanLoops_not_path_unique` states precisely the resulting failure of
native path uniqueness for this closed Boolean loop family.

For `Fin 3`, `swap01` exchanges 0 and 1, and `swap12` exchanges 1 and 2.
Concatenation applies the first loop's permutation first:
`loopPermutation_concat e d` yields `e.trans d`. In the two orders, input 0
produces 2 and 1, respectively. `compositeLoops_no_twoPath` rules out a native
two-path between those actual concatenated loops using these transport
observations. `swaps_do_not_commute` records the corresponding permutation
inequality.

`swapComposition` also retains the supplied native equivalences and invokes
`NaturalUnivalenceLaws.composition` directly. Its comparison runs from ua of
the actual composite map and composed fiber witness to concatenation. This
records the selected witness comparison in addition to the computed values.
`swapComposition_reindex` proves exact equality of the entire comparison
square after arbitrary substitution, so it also applies to an interval
parameter.

## Recovery under an interval parameter

`recoverLoop_path` connects the actual round trip
`equivToPath (pathToEquiv p)` to the original path `p`.
`recoverLoop_reindex` proves that its recovered endpoint commutes with
substitution, using the full map-and-fiber-witness substitution laws.
`recoverLoop_path_reindex` restricts the whole recovery path and corrects its
endpoints to those recomputed expressions. The client specializes this to the
interval projection in `intervalLoopRecovery` and `intervalRecovery_endpoint`.
This is a transported recovery witness; no claim identifies it with a
separately recomputed choice of `leftInverseAt`.

The accepted Boolean recovered-loop and full chosen-equivalence-witness clients
remain directly available as `acceptedBooleanRecovery` and
`acceptedBooleanWitness`.

These results concern the implemented native universe, constant codes, closed
sections, and the stated substitution laws. They do not establish circle
homotopy groups, a general classifying-space theorem, or a global truncation
principle. Higher coherence and classifications for varying families require
additional statements and consumers.
