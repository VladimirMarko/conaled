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

The detailed reports specify two possible formalization successors:

- Extend the existing local-universe specialization with dependent sum elimination
  and formalize the finite-set slice LF comparison, retaining arbitrary motives,
  hom-set inverses, naturality and repeated-substitution controls.
- Formalize the explicit higher-family/key diagram and compare direct construction
  with reuse of `TwoFamily`. Retain all-cell pullback laws, the selected arrow,
  invalid-boundary control and forbidden Boolean-dependent substitution.

These would turn paper constructions into checked examples. They are not evidence
for adopting a general framework. A stronger local-universes experiment would
need a weak homotopical model with a demonstrated filler-stability obligation;
that question remains distinct from the finite-set formalization.

These are recommendations for #289/#36/#235, not newly scheduled implementation
waves. The #102/#103 source-transfer gates, #107 pause and #108 independent-author
test remain unchanged. The component reports give source versions, detailed
calculations, local-code comparisons and validation boundaries.
