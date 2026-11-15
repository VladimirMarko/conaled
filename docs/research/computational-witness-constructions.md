# Computational witness constructions

This #456 checkpoint reuses `CategoryProduct` raw objects, arrows, operations,
projection maps and structural comparisons. `WitnessProduct.equiv` retains a
pair of computational relation witnesses. Reflexivity, symmetry, transitivity,
category congruence and structural laws act componentwise. Both projections
return their selected component witness, and paired interpretations retain both
preservation witnesses. Comparison inverse laws reuse the generic identity
comparison rather than assuming witness uniqueness.

`erase_relation` identifies explicit erasure with the accepted product
relation. `Examples.WitnessProduct` distinguishes Boolean component witnesses
and checks the selected projections and componentwise symmetry. These statements
compare the actual witness values. They do not identify all witnesses or impose
higher coherence on equivalence operations.

The [complete construction inventory](computational-construction-witnesses.md)
extends this initial product checkpoint through the other active construction
families and records their source correspondence and validation boundary.
