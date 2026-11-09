# Cubical theories and judgment preservation

Research for [#405](https://github.com/VladimirMarko/conaled/issues/405).
Local inspection at `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
The chosen De Morgan implementation matches an actual retained connection
consumer. That is evidence for reuse, not proof that it is the best foundation
for every compiler or higher-language task.

## Reference versions and feature matrix

Sources are [CCHM arXiv:1611.02108v1](https://arxiv.org/html/1611.02108v1),
[Agda 2.8.0.2 cubical documentation](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html),
and [Angiuli–Hou–Harper, CSL 2018, §§2–6](https://doi.org/10.4230/LIPIcs.CSL.2018.6).
The CSL PDF has SHA-256
`59aa7222523befa2b82f24518ac9a1c9229a38b54fc5a2c563535de5bb251de9`.
The Agda source examples use the experiment's Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, not an unpinned latest library.

| Feature | CCHM v1 | Agda 2.8.0.2 | Cartesian CSL 2018 |
|---|---|---|---|
| Dimensions | Free De Morgan algebra | De Morgan interval, special sort | Names and endpoints |
| Faces | Endpoint face lattice | Partial elements on faces | Dimension equations/constraints |
| Connections/reversal | Primitive dimension expressions | Primitive dimension expressions | Not dimension expressions |
| Transport/composition | Composition; derived transport/filling | Generalized `transp` and `hcomp` | `coe` and `hcom` with Kan conditions |
| Universe equivalence | Glue | Glue, split operations | V-types and fibrant universe hierarchy |
| Equality | Path; marked identity extension | Path; cubical and indexed inductive identity facilities | Path; exact equality in non-fibrant fragment |
| HIT computation | Named extensions including circle | Datatypes with path constructors | Circle; indexed schema belongs to later Cavallo–Harper work |

This is a rule inventory, not an equivalence theorem. In particular, renaming
`comp` to `hcomp` leaves missing premises and equations.

## A precise obstruction using the retained source

The [construction record](cubical-model-construction.md) selects the archived
`Orbifolds.CubicalShells.contract-cube`. At dimension one its body is
`H c j i = c (i ∧ j)`, with endpoints `H c 0 i = c 0` and
`H c 1 i = c i`. The local
[`Cube.connection`](../../SquareKit/Internal/Cubical/Dimensions.lean) and
`face_zero_connection`, `face_one_connection` supply the corresponding cube
maps and equations. They do not import the entire polymorphic Agda definition.

Consider a proposed syntax translation that preserves the interval object,
its two endpoints and dimension substitution, maps variables identically,
and represents each source dimension expression by a Cartesian dimension
expression. Its translation of `i ∧ j` must be one of `0`, `1`, `i`, `j`.
None satisfies both required faces as expressions in free `i`: at `j=0`
it must be `0`, and at `j=1` it must be `i`. Thus this particular translation
cannot preserve the source connection judgments. This is a grammar-level
obstruction, not a theorem that Cartesian fibrant types lack path contraction
or that no semantic comparison exists.

A replacement proof using Cartesian Kan composition can be investigated for
fibrant `X`. It would use additional capability evidence absent from the
original interval-function statement. It must also justify the desired endpoint
conversion and substitution behavior, rather than merely produce a homotopic
term. Restriction of a De Morgan presheaf along Cartesian cube maps is another
candidate comparison, but does not automatically transport the chosen Kan
structure, reflect judgments, or provide a source importer.

## Separate translation obligations

For `contract-cube` and subsequently the retained cover, proposed admission
must record the following independently:

| Contract | Required evidence |
|---|---|
| Typing | Each source context, family, term and capability premise has an admitted target interpretation. |
| Substitution | Translation commutes with term and dimension substitutions, including endpoint and diagonal maps; comparisons compose. |
| Conversion | Each used source conversion rule has a target judgment/semantic equation of the promised kind. A path witness alone is insufficient. |
| Witness | The interpreted dependent pair and identity terms retain their observations; do not identify all paths with host equality. |
| Operational behavior | If requested, simulate the named evaluation relation and prove adequacy at integer/Boolean observations. Semantic conversion preservation is not this theorem. |

Local [restricted transport](../../SquareKit/Internal/Cubical/RestrictedTransport.lean)
requires constancy on the face and proves its computation and substitution.
The [source rules](../../SquareKit/Internal/Cubical/Judgments/TransportRules.lean)
validate those provider-annotated judgments. The local marked-identity adapter
proves reflexive computation; it does not thereby interpret Agda's
`PathIsoEq` or arbitrary indexed matching. These distinctions survive even when
two systems use the same De Morgan dimension algebra.

## Recommendation and controls

Keep the selected De Morgan construction as one candidate for the unchanged
[cover consumer](computational-higher-inductive-consumers.md). Compare its full
admission cost with a Cartesian rederivation and the direct ordinary Lean
integer-action proof. Label the rederivation as a changed proof when it changes
source capabilities. Do not make an external importer mandatory for native
Lean clients. The [universe milestone](cubical-universe-glue-milestone.md) and
[computational-univalence contract](computational-univalence-transport.md)
identify what remains after dimension compatibility succeeds.

A proposed negative translation test must reject a Boolean interval quotient:
`i ∧ ~i = 0` is not a De Morgan dimension law. Another must reject replacing
`i ∧ j` by `i`: the `j=0` face fails. A witness-erasure test must retain the
cover's unequal integer observations. These controls target different errors;
passing the dimension tests cannot replace the higher-witness test.

No new translation or checker run is claimed. The recommendation is to attach
these obligations to the same consumer follow-up, not create a general
cross-calculus framework from this comparison. If the source admission cost
outweighs the benefit, retain the native proof and record exactly which source
judgment was not preserved. That is a useful rejection result, not evidence
that the mathematical construction itself is impossible.
