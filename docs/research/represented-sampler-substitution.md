# Replacing represented higher-order samplers

[#391](https://github.com/VladimirMarko/conaled/issues/391) proves that equal
first-stage laws remain equal after an admitted randomized continuation. The
result retains the input and intermediate semantic values when requested.
It does not identify the selected seeds of two representations.

## What was missing

The [#370 construction](higher-order-random-functions-implementation.md) already
supports adaptive operations on explicit joint seeds. Its `law_observe` accepts
an arbitrary standard Borel source measure and admitted family. Applying that
theorem to another affine or polynomial sampler would not supply a new
probability interface. `law_map` also already preserves deterministic operations,
while `deterministic_bind` handles Dirac continuations and
`independent_observations` compares independently sampled observations.

The new obligation is representation independence: the continuation should use
the first sampler through its law even when its seed space and representation
change. The proof below discharges that obligation without constructing the
full QBS probability object.

## Generic theorem and its hypotheses

[SamplerSubstitution](../../Applications/Probability/SamplerSubstitution.lean)
uses the existing QBS `Space`, `Hom`, products and generated sigma algebras.
Carriers and seed spaces are in `Type`. Let S,S',T be standard Borel spaces,
a:S→X and a':S'→X admitted families, and k:X×T→Y an admitted continuation.
For input measures μ,μ' and fresh-noise measure ν, `law_substitution` proves

```
law μ a = law μ' a'
  → law (μ.prod ν) (seeded a k) = law (μ'.prod ν) (seeded a' k).
```

The implemented theorem permits arbitrary input measures and requires only
that ν is s-finite. Probability measures therefore satisfy its assumptions,
without extra normalization proofs in the replacement argument. S and S' may
be different; no source inhabitance premise is added. Equality compares complete
measures on `sigma Y`, rather than a list of moments or marginals.

`event_measurable` proves the essential parameterized measurability: for every
E measurable in `sigma Y`, the function x↦ν{t | k(x,t)∈E} is measurable for
`sigma X`. Its proof tests an arbitrary random curve α:ℝ→X. The seeded family
on ℝ×T is admitted and hence ordinarily measurable by the existing
`Hom.measurable_source`. Mathlib's measurable section-measure theorem then
makes the event probability a measurable function of the real parameter.
This constructs an admitted real-valued observer and its generated-sigma
measurability; no global compatibility hypothesis supplies the conclusion.

`seeded_apply` applies product integration and pushforward integration to write
the output event probability as an integral against `law μ a`. Replacement
then follows by equality of those input measures. The proof never equates
`sigma (prod X Y)` with the product of `sigma X` and `sigma Y`.

`retain` pairs the semantic input with the output of k. Applying the same
replacement theorem to that admitted continuation gives
`retained_law_substitution` on the actual generated sigma algebra of the QBS
product. `two_stage_substitution` applies it again to a continuation receiving
the retained pair, with a second fresh noise source. It retains all three
semantic values. `seeded_deterministic` recovers the existing deterministic
pushforward when a continuation ignores its fresh noise.

## Independent client and ordinary kernel comparison

[SamplerClient](../../Applications/Probability/SamplerClient.lean) specifies the
finite client independently of QBS. Three fair Boolean seeds b,t,u produce
f_b(x)=b xor x, y=f_b(t), and z=y xor u. The independent pair law is an explicit
sum of four Dirac measures of mass 1/4; the triple law is the flattened product
of three fair measures. `native_pair` and `native_three` prove the joint laws.
The selected native record keeps b,t,y,z; the later realization record also
retains u.

The native Markov kernel is b↦fair.map(xor b). Its normalization and equality
to the fair law are proved. `kernel_pair` and `kernel_three` use actual
`Measure.compProd`, including the second kernel indexed by the retained pair.
They agree with the independent joint laws, without invoking QBS definitions.

[SamplerSubstitution examples](../../Examples/SamplerSubstitution.lean) construct
f_b in the existing exponential from Boolean values to Boolean values. The
continuation is actual function evaluation, and the second continuation
receives the earlier semantic pair. The public generic theorem transports the
whole retained law from the original seed representation to the complemented
one and then to the twice-complemented one. `two_kernel_agreement` observes the
result after these replacements and connects it to the ordinary two-stage
kernel baseline. These are finite higher-order clients of a theorem quantified
over arbitrary admitted QBS values and continuations, not claims that a finite
kernel represents all higher-order values.

The native route supplies finite measurable transitions and product integration.
The QBS route additionally supplies admitted function values, evaluation and
the generic law-replacement theorem. Both retain their ordinary APIs; neither
must be encoded through the compiler's rule engine.

## Rejected alternatives and selected records

Complementing a fair seed preserves its function law, but at the same seed
`false` the original and recoded functions differ. An explicit coupling b↦not b
aligns the whole functions and both-stage semantic records. `record_seeds`
retains each realization's own three seeds; those records differ across the
coupling even when their semantic components agree. `selected_agreement`
recovers the frozen native selected record pointwise. No sample is recovered
from equality of measures.

Copying b into both outputs has the same two fair marginals as independent
sampling, but `copied_not_fresh` distinguishes their complete laws at the event
{(false,true)}. Thus observing only the final marginal loses a retained
correlation. Reusing b as its own noise instead makes xor b b constantly false;
`reused_seed_wrong` detects even the changed marginal. These failures retain
the specified observation contracts rather than changing the meaning until a
comparison passes.

## Source and disposition

Heunen–Kammar–Staton–Yang, [*A Convenient Category for Higher-Order Probability
Theory*, arXiv:1701.02547v4](https://arxiv.org/html/1701.02547v4), §V-C/D defines
probability representations modulo equality of induced measures and constructs
bind; Theorem 21 and Proposition 22 state its stronger monadic structure. The
discussion after Proposition 19 distinguishes generated QBS product sigma
algebras from ordinary measurable products. The present theorem isolates one
representation-independence obligation, using the already constructed value
model. It does not import the paper's full monad theorem as an assumption.

Adopt the replacement lemma for represented samplers: it removes the need to
repeat parameterized integration whenever a semantic input sampler changes.
The retained and two-stage results demonstrate composition, while the ordinary
kernel baseline remains convenient for finite clients. No runtime or authoring
advantage was measured.

A QBS probability object, quotient random-element construction, general bind,
strength and commutativity remain separate #200/#36 work. Conditioning, recursion,
and executable sampling adequacy also remain outside this result. The example
supplies no reason to replace native kernels or impose a universal probability
interface. #107 remains paused, #108 unselected, and #260 inactive. Acceptance
uses the repository candidate build and exhaustive proof audit; exact candidate
and independent-review evidence is retained by the enclosing orchestration.
