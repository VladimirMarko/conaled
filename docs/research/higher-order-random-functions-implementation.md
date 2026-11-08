# Checked random-function values and sampling

Issue [#370](https://github.com/VladimirMarko/conaled/issues/370) implements the
bounded function and sampling fragment below. It starts from
[higher-order random functions](higher-order-random-functions.md) and the
[nonlinear maintenance comparison](architecture-scaling-study/binding-probability-controls.md).
The incorporated integration base is
`c214c878635c5ea2f58f3c1bc6f4fb317d6e1d70`.

## Model and source boundary

[QuasiBorel.lean](../../Applications/Probability/QuasiBorel.lean) constructs
real random elements closed under constants, measurable reparameterization and
countable measurable selection. Morphisms preserve those elements. Products
use coordinatewise randomness. Exponentials contain all admitted morphisms;
their random families test a measurable real reparameterization and a random
argument jointly. Evaluation and arbitrary currying preserve randomness, and
curry/uncurry are inverse. No interpretation theorem is a structure field.

These constructions follow Definitions 7/11 and Propositions 14/18 of
[Heunen–Kammar–Staton–Yang, arXiv v4](https://arxiv.org/html/1701.02547v4).
The pinned primary text was inspected for those definitions, the standard
Borel retraction/comparison in Propositions 5/15, and the distinction between
probability representations and the later probability monad. Countable
measurable selection presents the countable measurable partition axiom.
The generated sigma algebra tests preimages under every random element.
Its preservation of products is neither assumed nor asserted.

Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`measurableEmbedding_embeddingReal`, `measurable_invFun` and
`leftInverse_invFun` supply the standard Borel retraction used by
`Hom.measurable_source`; the empty source is handled separately.
These are checked dependencies, not an appeal to the paper for a missing proof.

## Sampling fragment and comparison

[RandomFunction.lean](../../Applications/Probability/RandomFunction.lean)
constructs `law μ f` as an actual pushforward measure on the generated sigma
algebra. `law_probability` proves normalization for a probability source.
`law_map` proves composition of deterministic pushforwards; `law_observe`
compares the complete measure on a measurable output. `law_dirac` preserves
Dirac unit, `deterministic_bind` identifies bind into Dirac with pushforward,
and `independent_observations` preserves the product law under separately
admitted observations. These suffice for the two independent source draws and
subsequent pure operations here.

There is no object of all probability distributions with its own QBS
structure, quotient construction, general dependent bind, general monad laws,
strength or commutativity theorem. The product law above concerns independent
source measures and their observations. The implementation does not identify
the sigma algebra of a QBS product with the product of its sigma algebras.
A future higher-order dependent-sampling client would require the probability
object, well-defined bind and its random-element preservation before using it.
That is residual probability-library work, not a missing hypothesis of this
fragment or a reason to replace native kernel clients.

The function carrier is unchanged by squaring. `repair_meaning` identifies
its result at every real input with coefficients `(A²,2AB,B²)`;
`repaired_law` transports the joint coefficient distribution. Sampling these
coefficients separately is not this operation. `embedAffine_meaning` preserves
the old affine family. The sampled affine and squared functions are continuous,
although the carrier also admits noncontinuous measurable functions.

[HigherOrderRandomFunction.lean](../../Examples/HigherOrderRandomFunction.lean)
fixes its independent meaning directly as the pushforwards of `U⊗U` and
`(U⊗U)⊗(U⊗U)`, where `U` is Lebesgue measure restricted to `[0,1]`.
The higher-order consumers equal those entire joint measures. Shared and fresh
observations have equal marginals, but `P(Y<X)` is respectively `0` and `1/6`.
The checked calculation integrates a triangle of area `b²/2` over `b∈[0,1]`.
Squaring preserves the discriminator on the nonnegative fixture, and the
three-input repaired polynomial observation has the same full output law.

## Statement review and controls

The new claims were reviewed by their families:

- Space, morphism and exponential operations quantify arbitrary admitted
  objects and arguments. Extensional equality compares values, not proof terms.
  The real measurable model discharges all closure axioms, so the interface is
  inhabited. The exponential test includes varying arguments and parameters.
- Sigma and law transport use native output measurability and standard Borel
  source hypotheses. Function spaces themselves are never assumed standard
  Borel. General measures are allowed by transport; normalization has its own
  probability hypothesis. Neither equality of laws nor the sigma algebra
  reconstructs a selected sample.
- Affine and polynomial laws quantify all real coefficients and inputs. The
  positive cases use public curry, preservation and law-transport results.
  The nonlinear three-input case checks a client the affine representation
  cannot satisfy. A retained pair `(e, squaredFunction e)` keeps the selected
  coefficient payload; no representative is recovered from a measure.
- The event calculation uses the actual continuous product measure, including
  its almost-everywhere support. Equal marginals are proved separately from
  unequal joints. Squaring's event theorem requires nonnegative outputs; a
  negative-input counterexample shows why the hypothesis matters.
- The repaired coefficients satisfy `D²=4CE`. Mixing individually attainable
  coordinates violates that equation in a checked case. This is a pointwise
  representation control; it is not an additional computed event probability
  for independently resampled polynomial coefficients.

The initial missing connections were the admitted exponential, ordinary
measurability of its sampled family, and transport to the independent joint
measure. Those connections are now checked. The finite correlation and kernel
clients remain unchanged and included in the full library check.

## Assessment and limits

Both routes meet the same continuous joint-law contract. The coefficient route
uses ordinary measurable polynomial maps and the pushforward of their joint
source. The higher-order route additionally accepts arbitrary admitted
functions and supports currying independently of a coefficient representation.
Neither route is required to adapt to the compiler engine. This does not rank
all closure-conversion strategies or justify a language-wide migration.

A plausible shared blind spot is confusing easier nonlinear extension with
lower total authoring cost: the QBS route pays for the value model and its
measurable comparison. No matched author experiment or runtime measurement
was performed. There is no source-language compiler or operational sampling
adequacy claim. Recursion, conditioning and general dependent probabilistic
sequencing remain outside this bounded outcome. #107 remains paused, #108's
held-out theorem unselected and #260 inactive.

Validation uses the README's incremental candidate build and exhaustive proof
audit. Exact candidate and verification evidence belongs to the implementation
handoff; it does not turn the excluded probability-monad or runtime claims into
checked results. Independent Standards and Spec review is coordinated by the
parent implementation loop.
