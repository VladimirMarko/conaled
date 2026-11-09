# Local-universes and modal/higher research results

The bounded investigations [#424](https://github.com/VladimirMarko/conaled/issues/424)
and [#425](https://github.com/VladimirMarko/conaled/issues/425) answer different
model-construction questions. Their reports contain new paper derivations and
comparisons with existing code. They add no Lean declarations and do not establish
agent-productivity gains.

## Results and their limits

The [local-universes comparison](local-universes-concrete-comparison.md) works
through finite sets presented by maps: full comprehension, the slice hom-set
bijections required by LF, weakly stable dependent sums, and a local-universes
presentation with strictly stable formation and dependent elimination. The
selected pair and motive survive two substitutions. Raw iterated pullbacks
have different presentations, so the coherence question is real. Direct indexed
families already avoid that work with less setup in this example. The result
supports retaining local universes as an option, not replacing the direct model.
It does not test difficult choices of higher fillers or nontrivial higher cells.

The [joint modal/higher comparison](joint-modal-higher-comparison.md) gives a
small semantic construction where keys act on a dependent higher family.
The family over `B²G` sends a second cell to a fiber arrow; key pullback changes
that action. In the integer example, a selected cell produces `1`, then `2`
under a key, and `6` under the composite of two keys. Forgetting the family
pullback or erasing the cell gives the wrong observation. The total-context
boundary and pullback property check the interaction beyond those numbers.
A separate projection-based access policy makes a hidden Boolean unavailable.
The report distinguishes base substitution, which retains fibers, from a map
between fiber types.

This is a restricted key diagram with dependent transport. It does not construct
full multimodal dependent type theory, arbitrary-motive identity elimination,
parallel proof-relevant keys, or a smooth/cohesive model. Existing stronger
higher-identity results remain separate until an actual source connection is made.

## What can be combined

The two investigations were commissioned together and each scope asked about
its possible connection to the other. That explains this cross-check; it does
not establish that these approaches are uniquely compatible or that their
combination should take priority over other uses.

The more immediate comparisons are local universes with weakly stable model
constructors, and the key diagram with existing `TwoFamily` reindexing and
source interpretation. The former could concern a homotopical provider with
noncanonical fillers; the latter can reuse already constructed higher structure.
Cubical family-code and Glue work (#419/#420) has distinct size, filling and
source-rule obligations. Local universes cannot be assumed to discharge those
merely because both constructions use the word universe.

Local universes can address substitution coherence once the relevant weak
semantic operations and theorem hypotheses are supplied. The finite-set example
does not provide the higher operations or key interactions of the second report.
Conversely, the explicit strict key diagram has no demonstrated need for local
universes. Combining the names or independently strictifying two fragments would
not prove their mixed compatibility laws.

The practical result is permission to pursue either route on its own evidence:
use the simplest direct construction when it suffices, and retain a coherence
construction for models where stable choices are genuinely difficult. Neither
investigation needed a second existing client or an adapter to the incumbent
architecture before it could begin.

## Bounded successor choices

The leading recommendation is to formalize the explicit higher-family/key
diagram using `TwoFamily` reindexing and total-context machinery, comparing it
with the direct construction. Retain all-cell pullback laws, the selected arrow,
invalid-boundary control and forbidden Boolean-dependent substitution. This is
a test of reuse in existing higher code, not a prerequisite to adopting a full
modal framework. If source-level transport is claimed, connect an actual source
expression to the semantic action rather than merely proving its arithmetic
observation again.

A separate research successor could select a weak homotopical model with a
noncanonical eliminator/filler choice and compare local-universes coherence with
a direct stable construction. Establish the actual LF, weak stability, size and
required mixed laws; do not infer them from the finite-set case. Coordinate with
#419/#420 where the chosen provider overlaps their cubical family/Glue work,
without duplicating those tickets or assuming that local universes supply their
internal classifier.

Formalizing the finite-set slice LF comparison and dependent sum eliminator
remains a smaller optional regression task. It would turn the paper calculation
into checked evidence, including arbitrary motives, hom-set inverses, naturality
and repeated substitution. It is not needed to justify the higher-key experiment
and would not itself answer where local universes outperform direct families.

The approved successors are [#426](https://github.com/VladimirMarko/conaled/issues/426)
for the TwoFamily experiment and [#427](https://github.com/VladimirMarko/conaled/issues/427)
for the weakly stable model study, in that priority order. Their specifications
are tracked; implementation has not started as part of this scheduling update. The later scheduling decision resumes #107 and separates #103 into technical
construction #433 and assessment #434. #108 retains its reviewed-freeze and
independent-author safeguards. The component reports give source versions, detailed
calculations, local-code comparisons and validation boundaries.
