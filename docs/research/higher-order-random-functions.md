# Random functions beyond a fixed closure environment

Research for [#298](https://github.com/VladimirMarko/conaled/issues/298),
2026-11-05, at local revision
`497daa15afc2a38a0640eccfcc5e96100709aa74`.

**Retain ordinary kernels for the fixed affine client. Investigate a bounded
probability-only QBS interpretation when clients must accept arbitrary
admissible random functions. Defer an ambient model migration and recursive
probability semantics.** The matched paper experiment below succeeds through
both routes on the affine joint law. Only the QBS route supplies the required
unrestricted admissible function interface; that mathematical result is not
a new Lean implementation.

This follows [#199's model assessment](probability-model-comparison.md) and
[#280's computation comparison](external-discovery-280/computation-comparison.md).
It executes their proposed mathematical comparison rather than repeating the
survey. The distinction between independent meaning and behavioral observations
also follows [#285's checked comparison](higher-order-extensional-comparison.md).

## Frozen contract and evidence

The contract was recorded before adapting either route, after reading #199's
fixture, the primary theorem statements and the current interpretation
interfaces. This is informed continuation, not blind discovery or a fresh-author
trial. The durable contract is:

| Component | Required meaning |
| --- | --- |
| Values | Real numbers, finite products and the full admissible function object `F = Real ⇒ Real`; function equality is pointwise equality of values. |
| Function admission | Every QBS morphism `Real → Real`, not just affine functions; a random function family must satisfy the exponential's random-element condition. No claim admits every set-theoretic function or every pointwise-measurable family. |
| Pure operations | Evaluation and currying, arithmetic, and `obs(x₀,x₁,f) = (f x₀,f x₁)`. The consumer chooses inputs after receiving f. |
| Computations | A commutative strong probability monad P, unit, bind and `uniform01 : 1 → P Real`. Sampling precedes pure duplication of a returned value. |
| Observations | Equality of the ordered two-output law on every Borel subset of `Real × Real`. Moments are additional discriminators only when integrable. |
| Selected data | For the affine fixture, retain the sampled coefficient pair and its pointwise graph equation when a client requests it. Equality in distribution does not itself supply a coupling or recover a sampled witness. |
| Exclusions | Recursion, weighting, normalization, conditioning, execution costs and hardware randomness are not part of this experiment. |

The result type keeps the two input positions in order. One may identify it
with `Fin 2 → Real`, but may not quotient by permutations or reduce it to two
marginal laws. The affine coefficient payload is selected mathematical data;
its equation proof is not an execution trace or a claim about equality of
object-language proof terms.

**Evidence classes.** The cited paper theorems are source results. The
calculations and commuting diagrams below are paper derivations. Existing
Lean declarations are inspected local evidence, not rerun builds. This change
introduces no formal theorem and records no author performance measurement.

## Primary hypotheses used

For QBS objects X,Y, the exponential has carrier `QBS(X,Y)`; its random elements
α are precisely those whose uncurrying is a QBS morphism. Proposition 18 gives
evaluation and currying. Theorem 21 gives the strong probability monad from
random-element/real-measure pairs modulo equal pushforward law; Proposition 22
gives commutativity and the faithful Kleisli comparison with Giry. The measure
comparison is an isomorphism on standard Borel spaces. Proposition 23 permits
standard Borel sample spaces. Theorem 26 makes pointwise kernels a quotient of
random functions, not an identification retaining all joints.
[Heunen–Kammar–Staton–Yang, §§IV–V, VII.A, arXiv v4](https://arxiv.org/pdf/1701.02547v4).

The recursive alternative uses ω-QBS: a QBS plus an ω-cpo, with random elements
closed under pointwise chain suprema; morphisms also preserve chain suprema.
Its statistical powerdomain T is built from randomizable expectation operators
and chain closure. Theorem 4.6 gives commutativity; Corollary 4.11 identifies
operators by characteristic-function observations, with s-finite measures for
discrete-order standard Borel objects. Section 5 solves locally continuous
mixed-variance equations through a bilimit-compact partial-map category.
Theorem 6.9 gives denotational equality implying contextual equivalence for
closed, same-typed SFPC terms under the paper's operational semantics.
Corollary 6.11 reorders t,s typed in the same Γ, with neither depending on the
other's result. [Vákár–Kammar–Staton, §§3–6, arXiv v3](https://arxiv.org/pdf/1811.04196v3).

These results have different uses here. QBS supplies the selected total
higher-order interface. The domain result is a qualification of the later
recursion option, not a premise of the affine calculation. Neither theorem
identifies independent resampling with copying a sampled value, nor establishes
a compiler theorem for this repository.

Technical passages inspected included the exponential definition, monad unit
and bind, the standard-Borel qualifications, the quotient map in Theorem 26,
ω-QBS Definition 3.5, powerdomain construction, valuation comparison, recursive
hypotheses and adequacy proof boundary. This was selective full-text inspection,
not an audit of all referenced proofs. #199's AFP exponential link was
inaccessible through this session's browser; no new AFP verification is claimed.
Both primary arXiv texts were accessible. No new survey queries were needed.

## Independent meaning of the source argument

Let U be normalized Lebesgue measure on `[0,1]`, regarded as a Borel probability
measure on Real. Use the following recursion-free monadic source fragment:

```text
make : P F
make = do a ← U; b ← U; return (fun x => a*x + b)

shared : P (Real × Real)
shared = do f ← make; return (f 0, f 1)

fresh : P (Real × Real)
fresh = do f ← make; g ← make; return (f 0, g 1)
```

Its specification is fixed without an evaluator. Put
`h(a,b) = (b,a+b)` and `j(a,b,a',b') = (b,a'+b')`. The required measures are

```text
D_shared = h_* (U ⊗ U)
D_fresh  = j_* (U ⊗ U ⊗ U ⊗ U).
```

For every Borel S in `Real²`, this requires, respectively,

```text
D_shared(S) = ∫₀¹ ∫₀¹ 1_S(b,a+b) db da
D_fresh(S)  = ∫₀¹ ∫₀¹ ∫₀¹ 1_S(b,a'+b') db' da' db.
```

The unused coefficient a integrates to one in the second equation. Both maps
are continuous, hence measurable. The displayed integrands are nonnegative
and bounded, so product integration applies without a signed-integral
ambiguity. These formulas specify the entire joint law; computing a moment
alone would not establish them.

### Fixed-environment interpretation

Use the environment E=`[0,1]²` with product measure and
`evalE((a,b),x)=a*x+b`. A closure is its sampled environment paired with this
fixed evaluation rule. This is the first-order route already proposed by #199;
there is no claim that an affine closure interpreter is installed locally.

Shared sampling draws e once and applies the deterministic measurable map
`e ↦ (evalE(e,0),evalE(e,1))`. Its pushforward is exactly `D_shared` because
that map is h. Fresh sampling draws `(e,e')` from the independent product and
applies `((a,b),(a',b')) ↦ (b,a'+b')`, so it is `D_fresh`. This uses ordinary
kernel composition and pure measurable maps. It preserves correlation; a new
ambient model is unnecessary for this client's output law.

### QBS interpretation and comparison

For the QBS interpretation, define
`c : E → F` by `c(a,b)(x)=a*x+b`. Its uncurried map is measurable arithmetic
on a standard Borel product, so currying makes c admissible. The same argument
makes `obs : Real² × F → Real²` admissible by evaluation and pairing. This
construction checks admission for the entire parameterized observer, not only
its two closed evaluations.

Interpret `make` as `P(c)(U⊗U)`. By functoriality of pushforward,

```text
P(obs(0,1,-))(P(c)(U⊗U))
  = P(obs(0,1,-) ∘ c)(U⊗U)
  = P(h)(U⊗U).
```

For fresh, monadic sequencing uses two independent copies of the same
function-valued law. Substitution of c in both places gives `P(j)(U⁴)`.
On the standard Borel result `Real²`, the measure comparison therefore gives
exactly `D_shared` and `D_fresh`. Only the sample/result objects use the
standard-Borel identification; the argument does not require F itself to be
standard Borel or claim a product-preserving forgetful functor for all QBS.

The commuting square is explicit: `obs(0,1,-) ∘ c = h`, before taking
pushforwards. Thus the coefficient route and the function route agree for
each environment, a stronger claim for this fixture than equality in law.
For arbitrary chosen inputs x₀,x₁ the same square uses
`hₓ(a,b)=(a*x₀+b,a*x₁+b)`, preserving the input indices.

To retain a selected coefficient payload, interpret e as `(e,c(e))`, with
its graph equation `∀x, c(e)(x)=a*x+b`. The first projection still returns the
same e after interpretation and observation. At inputs 0 and 1 it can also be
reconstructed by `(a,b)=(second-first,first)`. This is a fixture-specific
identity, not a natural choice of representatives for arbitrary probability
laws or a coefficient representation of every f in F.

## Joint-law discriminator and rejected replacements

For shared outputs X=B and Y=A+B, independence of A,B gives

```text
E[X] = 1/2,    E[Y] = 1
E[XY] = E[AB] + E[B²] = 1/4 + 1/3 = 7/12
Cov(X,Y) = 7/12 - (1/2)*1 = 1/12.
```

For fresh outputs X=B and Y=A'+B', X and Y are independent, so `E[XY]=1/2`
and covariance is zero. Each coordinate has the same marginal as in shared.
All these random variables are bounded on their respective sample spaces,
which supplies integrability of their products. No finite-moment assumption
is made for arbitrary random functions admitted by the interface.

There is also a bounded, directly measurable discriminator. Shared always
satisfies Y≥X. For fresh, conditioned on B=b in `[0,1]`, the triangle
`{(a',b')∈[0,1]² | a'+b'<b}` has area `b²/2`. Hence

```text
D_shared({(x,y) | y < x}) = 0
D_fresh ({(x,y) | y < x}) = ∫₀¹ b²/2 db = 1/6.
```

This paper derivation rejects a transformation that replaces shared with fresh.
Commutativity permits reordering independent draws; it cannot erase the common
B used by the two shared outputs. The project already retains this distinction
in the checked finite examples
[`shared_first`, `independent_first`, `joint_distributions_differ`,
`copy_after_draw`, `draw_twice`](../../Examples/ProbabilityCorrelation.lean).
The new calculation does not diagnose a bug in those interfaces.

A second rejection control targets **pointwise kernels as the function law**.
With a fair Boolean B, take one random function on Bool that always returns B
and another that returns B at false and its complement at true. At each input,
both output laws are fair; the ordered two-output laws are respectively always
equal and always unequal. Therefore a representation remembering only
`x ↦ law(f(x))` fails the frozen joint-law contract. No quotient theorem can
turn those marginals into the missing joint data.

Finally, the fixed affine environment fails the **full interface**, although it
passes the matched affine calculation. The admitted deterministic function
`q(x)=x²` cannot have an affine representation preserving evaluation at every
input: x=0 forces b=0, x=1 forces a=1, while x=2 would require 2=4. This is a
consistency test of full evaluation, not a change to the two-output fixture.
Even enlarging the affine coefficient range to all reals would not repair it.
A tagged polynomial environment could handle this next example, but would
still owe coverage and evaluation/currying laws for the full admitted object.
No impossibility claim is made about all closure-conversion strategies.

## Mapping the existing interfaces

The inspected local APIs separate several obligations:

| Existing interface | Proposed mapping and missing obligation |
| --- | --- |
| [`Compiler.Target` and `compile`](../../Compiler.lean) | Its pure product, lambda and application operations map to QBS products, curry and evaluation. `Ty` has no probability constructor or sampling/bind syntax; adding a stochastic primitive alone does not provide the monadic source above. |
| [`STLCNaturality.Model`, `Preserves`, `naturality`](../../SquareKit/STLCNaturality.lean) | Use QBS objects at the object-polymorphic boundary for the pure value fragment, with exact hom equality and primitive admission. Prove every local operation-preservation obligation. Its syntax induction does not automatically cover probability computations. |
| `Compiler.Sound` | Its `Val` uses all Lean functions at arrows. It is not an off-the-shelf faithful closed interpretation of QBS. A relation restricting function inputs, or the object-polymorphic interface, must preserve the admitted carriers without pretending they are all set functions. |
| [`tableMeaning_laws`, `kernel_comp`](../../Applications/Probability/FiniteKernel.lean) | Retain the existing finite-table interpretation into Mathlib `Stoch`. A new comparison on the standard Borel probability fragment must preserve Dirac, bind and independent product. The affine case is a continuous ordinary-kernel fixture, not an existing finite-table theorem. |
| [#285's function-input relation](higher-order-extensional-comparison.md) | Reuse the discipline of related inputs and environment extension if comparing representations. Its total deterministic, cost-forgetting result is not a probability-adequacy theorem. |

A bounded extension would have separate value arrows `X → Y` and computation
arrows `X → P Y`, with explicit strength and bind preservation. Pure copying
of a returned f belongs to the value category. Treating all Kleisli arrows as
cartesian and applying ordinary pair-eta would collapse distinct joints with
equal marginals. The existing [probability contracts](../probability.md) already
exclude that mistake.

For this paper experiment, the interpretation of `make` and the two consumers
is given directly. There is no new frontend or universal AST. A future compiler
comparison must state the chosen probabilistic source fragment and prove its
substitution, value/computation and observation laws; it cannot inherit them
merely by naming a QBS target.

## Decision, cost and owned residual work

| Claim | Decision and owner |
| --- | --- |
| Continuous affine output laws need an ambient higher-order model | **Reject**: both paper routes meet the independent joint-law specification. #235 retains ordinary-kernel clients. |
| Fixed affine closures implement the full admitted function interface | **Reject**: the nonlinear evaluation control fails. This does not reject richer closure representations. |
| A probability-only QBS interpretation is mathematically suitable for the frozen higher-order contract | **Investigate bounded formalization** under #36, coordinated by #235. Evaluation/currying and observation comparison justify the candidate; no implementation adoption yet. |
| General recursion or soft constraints must accompany this experiment | **Defer**: #235 owns selecting a concrete recursive client and #36 the model comparison. Plain probability laws cannot account for divergence mass by normalization. |
| Existing proof or author evidence establishes QBS compiler adequacy or easier authoring | **Reject**: neither was measured or proved here. #235 coordinates a separately scoped interpretation and any later author trial. |

If arbitrary admissible random functions become a required client interface,
the bounded model proposal is:

1. Construct QBS random-element closure, morphisms, products and exponentials;
   prove evaluation/currying for arbitrary admitted objects. Reuse Mathlib
   measurable spaces, products and probability measures wherever hypotheses
   match. A record of unproved QBS laws does not count as model construction.
2. Construct the probability-only interpretation and its standard-Borel
   Dirac/bind/product comparison. Prove the affine commuting squares, full joint
   measure equalities and the event discriminator. Check q as a non-affine
   admitted value and retain the selected coefficient graph payload where used.
3. Connect only the pure value fragment to `STLCNaturality`, and state/prove
   the separately required sampling and sequencing preservation. Require the
   finite correlation examples and existing kernel callers to retain their
   original contracts. Apply statement review, old/new/failure examples and the
   README build/proof audit to that future formal change.

The expected costs are function-space infrastructure, quotient well-definedness,
probability comparison, and source interpretation proofs. The fixed closure
route pays per representation and consumer; QBS pays once for larger shared
structure. This is a qualitative cost assessment, not timing or a measured
author advantage. The proposal does not fund a whole probability library port.

**Still unproved locally:** construction of that QBS model and its monad;
its Mathlib comparison; compilation of the displayed probabilistic source;
operational adequacy of local sampling/evaluation; and a recursive domain
interpretation with the required continuity, bilimits and observation theorem.
There is no general comparison identifying every valuation on every higher-order
object with an ordinary measure. The primary domain result concerns its stated
objects and operators. Numerical sampling, random-bit adequacy, conditioning,
normalization and resource behavior remain separate contracts.

A requirement for recursion, nonmeasurable observers, internal lower-real
probability or retained sample histories would reopen the model choice. #199's
valuation and probability-sheaf alternatives remain evidence for those different
contracts. #299's quantitative observations and #300's system composition are
not answered by equality of these probability laws. This study does not resume
#107, prepare #108 or activate #260.

## Validation

This is a documentation-only paper experiment. Relative links, whitespace and
exact rational arithmetic in the discriminator were checked; arithmetic checks
are not formal measure-theory proofs. No Lean build, proof audit or new checked
claim is reported. Independent Standards and Spec review belongs to the
coordinating implementation loop. The exposure, frozen contract, omissions and
source hypotheses above remain part of the result when it is reviewed.
