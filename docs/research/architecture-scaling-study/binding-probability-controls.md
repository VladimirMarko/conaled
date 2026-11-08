# Dependent binding and random-function maintenance controls

Research for [#365](https://github.com/VladimirMarko/conaled/issues/365),
2026-11-08, against `0bf03c56876f52f3fd72f91ff0d34c29290800f4`.

Both representations of the binding fixture preserve its selected finite
element through two substitutions. Nominal abstraction removes the choice of
bound spelling from the contract; it does not supply dependent typing or model
coherence. Both the coefficient and QBS interpretations preserve the probability
fixture's joint law. A nonlinear maintenance change requires repairing the
coefficient representation, while QBS admits the changed function by composition.
Neither result establishes an author-productivity advantage.

These are **paper derivations**, including the concrete substitutions, finite
tables and integrals below. The source trace identifies existing Lean definitions
and theorems, inspected but not rebuilt for this documentation change. No new
Lean claim, nominal model, QBS model or compiler theorem is delivered. This is
the research-only outcome permitted by #365, not completion of those models.
The author previously performed the Spec review of #362's disposition and read
the earlier reports before choosing these fixtures. This is informed follow-up,
not a blind assessment or the deferred #358 trial. Independent acceptance is
coordinated by the enclosing workflow.

## Binding contract and two dependent declarations

Work in ordinary set-valued dependent families. Write `Fin(r)` for natural
numbers strictly below `r`, and `|a|` for the underlying number of `a`. The
context is `Γ = (n : Nat, z : Nat)`. Define the following binder constructor
semantically, without presuming its presence in a current source calculus:

```text
bind₂(A,B,t)(γ) = λ a : A(γ). λ b : B(γ,a). t(γ,a,b)
A(n,z)         = Fin(n+1)
B((n,z),a)     = Fin(|a|+1)
K(n,z,a)       = z+|a|
D((n,z),a,b)   = Fin(K(n,z,a)+1)
t((n,z),a,b)   = the element of D with underlying number |b|
```

The first binder depends on `n`; the second depends on the first selected
element. The result's type depends on `z` and that first element. Its typing
is derived from `|b| ≤ |a| ≤ z+|a|`, not supplied as a global substitution
assumption. An observer returns `(K, |t|)` in `Σ k : Nat, Fin(k+1)` with the
bound proof retained. It must preserve the selected `b`, not merely produce
some element of that fiber. Equality here is equality of finite values;
no distinction between proof terms of the same arithmetic inequality is claimed.

For any base substitution `σ : Δ → Γ`, set

```text
σ⁺(δ,a)     = (σδ,a)
σ⁺⁺(δ,a,b)  = (σδ,a,b)
Aσ(δ)      = A(σδ)
Bσ(δ,a)    = B(σδ,a)
tσ(δ,a,b)  = t(σδ,a,b).
```

The domain of `σ⁺⁺` is `δ:Δ, a:Aσ(δ), b:Bσ(δ,a)`. Thus both transported
types are specified, and the displayed identity on `a,b` is well-typed. For
`τ : Θ → Δ`, pointwise evaluation gives
`σ⁺⁺(τ⁺⁺(θ,a,b)) = (σ(τθ),a,b) = (σ∘τ)⁺⁺(θ,a,b)`.
Consequently `tσ[τ⁺⁺] = t[σ⁺⁺∘τ⁺⁺]`, and abstraction on both sides yields
the two-stage substitution equation for `bind₂`. This derivation uses strict
reindexing of set families. In a weak comprehension model it would require
the specified comparison isomorphisms and their coherence; this calculation
does not construct those isomorphisms.

Here are two nonidentity substitutions that also stress named capture:

```text
Δ = (m : Nat, a : Nat)     σ(m,a) = (m+1, a+2)
Θ = (k : Nat, b : Nat)     τ(k,b) = (2*k, b+3)
(σ∘τ)(k,b)                      = (2*k+1, b+5).
```

The free names `a` and `b` deliberately coincide with the original bound
spellings. Under the first substitution rename the bound `a` to fresh `c`.
The type of the second binder must change with it:

```text
bind₂σ = λ c : Fin(m+2). λ b : Fin(|c|+1).
           (the element |b| in Fin(a+2+|c|+1)).
```

Under the second substitution rename that bound `b` to fresh `e`, because
the image of the free `a` now contains free `b`:

```text
(bind₂σ)τ = λ c : Fin(2*k+2). λ e : Fin(|c|+1).
              (the element |e| in Fin(b+5+|c|+1)).
```

Direct substitution by `σ∘τ`, with the same fresh representatives, gives
exactly this expression. For `k=1`, free `b=0`, `c=2`, `e=1`, both routes
return `(7,1)` in the observation. Replacing the selected `e` by zero is
well-typed but returns `(7,0)` and fails the contract.

Skipping the first renaming captures the free `a` in `a+2` and changes the
result index from `a_free+2+|c|` to `2*|c|+2`. At `m=1`, `a_free=0`,
`c=1`, `b_bound=1`, these are 3 and 4. Skipping the second renaming after
the first captures the free `b` in `b+3`; at the final fixture it changes
the index from 7 to 8. Capture affects the dependent result type, not only
pretty-printing.

## Contextual and nominal derivations

In the nameless representation, the two newest variables have indices 0
and 1, and old variables start at 2. A lifted substitution fixes indices
0 and 1 and shifts each substituted old expression under both binders.
The body refers to bound `b` by 0, bound `a` by 1, and free `z` by its old
index plus 2. Therefore the free `a` in `σ(z)` never becomes index 1,
and the free `b` in `τ(a)` never becomes index 0. Typing still requires
substituting the second family's type under the first lift. Index shifting
alone is not that typing proof.

For the nominal route take infinitely many atoms with finite permutations,
finite support and abstraction `[a]u`. The source's abstraction equality
requires the fresh replacement atom to be absent from the body support;
its structural iteration theorem requires the abstraction branch's output
to be fresh for the bound atom: for finitely supported branch functions
`f,g,h`, its condition is `И a. ∀x. a # h(a,x)`. These are conditions, not unrestricted
recursion over representatives. See Gabbay–Pitts, Lemma 5.1, Corollary 5.2,
Theorem 6.5 and Example 6.9 in the
[2002 paper](https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas-jv.pdf).
Those results concern binding syntax; dependent typing below is our additional
obligation, not a theorem attributed to that paper.

Represent the two-binder annotated form by
`(A, [a](B, [b](D,t)))`: `a` scopes over `B,D,t`, while `b` scopes over
`D,t` but not its own annotation `B`. Substitution recursively replaces free
atoms, first choosing `a,b` outside the finite supports of its images and
the surrounding data. It acts on annotations as well as terms. The two
freshenings above are swaps on the respective bodies, including `B` for the
outer swap. They produce the same final annotated abstraction as simultaneous
substitution by `σ∘τ`. Freshening to other names gives alpha-equivalent
annotated terms, since all affected bound occurrences and annotations move
together. The numerical denotation ignores spelling, so the two routes return
the same selected payload.

This fixture's annotations use equivariant constructors `Nat`, `Fin`, addition,
variables and finite-element inclusion. Their typing is preserved under a
simultaneous permutation of context and term. The substitution proof above
then follows by replacing the two free parameters and rechecking the displayed
inequality. A reusable dependent nominal calculus would still owe this typing
lemma for every admitted constructor and its interpretation into the intended
model. Nominal abstraction alone does not prove semantic substitution.

The attempted observer `boundName([a]u)=a` fails: freshening the first binder
from `a` to `c` represents the same abstraction but changes its answer. Even
an equivariant raw-pair operation returning the binder fails to descend to
abstraction. Repair the consumer to return the finite selected element or
a binder position, as the contract does. If literal spelling is required,
retain separate presentation metadata and state that it is not an observation
of alpha-equivalence classes. Do not replace the selected value by a mere
inhabitedness proof while performing that repair.

### Maintenance: a third dependent binder

Extend the contract with `r : Fin(|b|+1)` after the two binders, retaining
the original output as the first projection. The new payload is

```text
(K, b', r') : Σ K : Nat, Σ b' : Fin(K+1), Fin(|b'|+1)
b' = the inclusion of b; r' = r.
```

Inclusion leaves the underlying number unchanged, so `|b'|=|b|` and the
last field needs no arbitrary choice or reset. At the final fixture, `r=1`
returns `(7,1,1)`; replacing it by zero changes the last observation while
preserving the old one. The substitution map is now
`σ⁺⁺⁺(δ,a,b,r)=(σδ,a,b,r)`, whose two-stage equation follows by the same
pointwise calculation. This is an executed paper extension, not a timing test.

Nameless terms shift old indices by 3 and preserve the three newest indices;
the new annotation must use the selected second binder. Nominal terms become
`(A,[a](B,[b](R,[r](D,t₃))))` with `R=Fin(|b|+1)`, and substitution
freshens the third atom against its images too. The representation repair is
to traverse the annotated telescope, not maintain a separate untyped list of
names. Both routes reuse the pointwise family argument. Their recurring costs
differ: lifting and dependent type alignment for indices; support,
freshening independence, equivariance and typing for names. This does not
measure which cost is smaller for an author.

### Current binding source trace

All paths below refer to the pinned baseline. These are existing source facts;
the new `Fin` fixture has not been encoded in these modules.

| Source | Trace and exact boundary |
|---|---|
| [ReferenceCalculus](../../../SquareKit/Internal/DependentJudgments/ReferenceCalculus.lean) | `Derives.extend`, `weaken`, `generic`, `pair`, `subTy` and `subTm` express object binding and substitution. `subTyComp`/`subTmComp` are inference rules in this calculus; counting their presence is not a derivation of model coherence. |
| [ReferenceDerived](../../../SquareKit/Internal/DependentJudgments/ReferenceDerived.lean) | `Derives.lift` builds the typed lifted substitution through the contextual operations. It can be applied at each of the two successive family boundaries. |
| [FiniteTail](../../../SquareKit/Internal/DependentJudgments/FiniteTail.lean) | `Tail.reindex` handles `.cons A rest` by substituting `A` then recursively using `liftSyntax`; `Tail.map` iterates that lift. The third-binder maintenance follows this recursion's shape. |
| [ReferenceSubstitution](../../../SquareKit/Internal/DependentJudgments/ReferenceSubstitution.lean) | `Derives.instantiate` and `Tail.instantiate_reindex` concern replacement of schematic leaves. They must not be advertised as capture avoidance for an arbitrary named source. |
| [DependentFunctions](../../../SquareKit/Internal/DependentFunctions.lean) | `Sub.funcSub` handles `.lam t` using `depSub σ.lift t`; `Sub.lift_comp`, `depSub_comp` and `funcSub_comp` prove composition for that bounded nameless fragment. Its lambda extends a base context; it is not already our arbitrary two-family dependent lambda. |

The contextual source therefore supplies reusable telescope mechanics, and the
bounded nameless source supplies a concrete substitution proof pattern. Neither
trace supplies the new binder's full dependent product formation or nominal
interpretation. A useful next formal comparison can use these mechanics without
claiming that absence of a nominal adapter disproves the alternative.

## Probability contract and correlation control

Let `A,B` be independent uniforms on `[0,1]`, `E=[0,1]²` with its Borel
product probability `μ`, and `c(A,B)(x)=Ax+B`. A consumer accepts a function
before choosing its inputs. Shared observation samples `e` once and returns
`(c(e)(x₀),c(e)(x₁))`; fresh observation samples independent `e,e'` and returns
`(c(e)(x₀),c(e')(x₁))`. The contract is the entire ordered joint measure on
`Real²`, not just moments. All maps in this fixture are continuous. Output
measures are respectively `(hₓ)_*μ` and `(jₓ)_*(μ⊗μ)`, where

```text
hₓ(A,B)          = (A*x₀+B, A*x₁+B)
jₓ(A,B,A',B')    = (A*x₀+B, A'*x₁+B').
```

At `(x₀,x₁)=(0,1)` these specialize to `(B,A+B)` and `(B,A'+B')`.
The [earlier affine comparison](../higher-order-random-functions.md) derived
covariances `1/12` and `0`, and event probabilities
`P(Y<X)=0` and `1/6`. We retain those results as paper regressions; the new
maintenance calculation is below.

A finite control exposes the precise information lost by
`P(X⇒Y) → (X→P Y)`. For a fair bit `C`, define two random functions on Bool:
`f_C(x)=C` and `g_C(false)=C, g_C(true)=not C`. Both have fair output at
each argument. Their ordered pairs at `(false,true)` have these full tables:

| Pair | Shared constant function | Shared alternating function | Fresh calls with fair marginal |
|---|---:|---:|---:|
| `(false,false)` | 1/2 | 0 | 1/4 |
| `(false,true)` | 0 | 1/2 | 1/4 |
| `(true,false)` | 0 | 1/2 | 1/4 |
| `(true,true)` | 1/2 | 0 | 1/4 |

Each column follows by enumerating one fair bit, or two independent bits for
the last column. Evaluation at each single input gives the same marginal;
the diagonal event gives probabilities 1, 0 and 1/2. Thus a pointwise-kernel
representation cannot reconstruct the required distribution on functions.
Finite kernels can represent these entire tables by retaining the common
sample or a finite function table. This is a failed *forgetful representation*,
not a failure of finite probability semantics.

### Equal-assumption coefficient and QBS interpretations

The coefficient route uses measurable `evalE:E×Real→Real` and the maps
`hₓ,jₓ`. No higher-order object is needed to derive these laws. The QBS route
uses the exponential `F=Real⇒Real`, whose elements are admissible morphisms;
random elements must have admissible uncurrying. Evaluation and currying follow
from Proposition 18. Theorem 21 and Proposition 22 give the strong commutative
probability monad, its pushforward action and measure comparison, with an
isomorphism at standard Borel objects. QBS objects require random elements
closed under constants, measurable reparameterization and countable measurable
case splits; morphisms preserve random elements. See
[Heunen–Kammar–Staton–Yang, arXiv v4, §§IV–V](https://arxiv.org/pdf/1701.02547v4).

For our own fixture, currying the continuous map `evalE` admits `c:E→F`.
Evaluation twice admits `obsₓ:F→Real²`; moreover `obsₓ∘c=hₓ` pointwise.
Hence `P(obsₓ)(P(c)(μ))=P(hₓ)(μ)`. Repeating with two independent coefficient
pairs gives `P(jₓ)(μ⊗μ)`. The result space is standard Borel, so the specified
joint laws agree with the coefficient route. We do not assume `F` is standard
Borel, identify all set functions with admissible functions, or infer general
measurability from pointwise evaluations alone. These restrictions keep the
two calculations on equal assumptions.

For arbitrary parameters `W`, a claimed higher-order interface must support
currying every admitted `W×Real→Real` and evaluation of its result. A fixed
affine environment only supplies the particular curry `c` and its evaluation
equation. It does not supply that general universal property. Conversely,
the QBS theorem is not an implementation of a Lean model or a sampling runtime.
No order structure, chain suprema or domain-theoretic adequacy assumptions are
used here. Recursion and conditioning remain excluded; requiring either would
reopen the model contract rather than follow from these probability laws.

## Nonlinear maintenance and a repaired coefficient representation

Change the function before passing it to the observer:
`N(f)(x)=(f(x))²`. Also permit a third observation at input 2. This keeps
the original affine construction as a named regression and changes both the
admitted operation and the observer. For the same coefficient sample,

```text
N(c(A,B))(x) = A²*x² + 2*A*B*x + B²
v(A,B)       = (B², (A+B)², (2*A+B)²).
```

At inputs 0 and 1, all values are bounded. The shared product expectation is

```text
E[B²(A+B)²] = E[A²]E[B²] + 2E[A]E[B³] + E[B⁴]
            = 1/9 + 1/4 + 1/5 = 101/180
E[B²]       = 1/3
E[(A+B)²]   = 1/3 + 1/2 + 1/3 = 7/6
Cov         = 101/180 - (1/3)*(7/6) = 31/180.
```

Fresh calls use independent coefficients and covariance zero with the same
marginals. Squaring is strictly increasing on these nonnegative outputs, so
the earlier event discriminator remains `0` versus `1/6`. The complete joint
laws are the pushforwards by `v` or its independently sampled-coordinate
analogue; moments are consequences, not a substitute for those measures.

The unchanged affine representation fails the third observation: its second
finite difference at 0,1,2 is always zero, while
`v₂ - 2*v₁ + v₀ = 2*A²`. At `A=1,B=0`, that difference is 2; under `μ`
its expectation is `2/3`. Interpolating only the first two observations would
therefore hide the failure.

A concrete repair uses `E₂=Real³`,
`eval₂(C,D,E,x)=C*x²+D*x+E`, and
`repair(A,B)=(A²,2AB,B²)`. Equip it with `repair_*μ`, not independent
coefficient marginals. Then
`eval₂(repair(A,B),x)=N(c(A,B))(x)` for every real input, by expansion.
All maps are polynomial, hence measurable. Pushing this pointwise identity
through the three-input observer proves the entire law `v_*μ` for the
repaired ordinary-kernel route. It also preserves the old affine family
through `(A,B)↦(0,A,B)`. Sampling the new coefficients independently is not
this repair: the genuine coefficients satisfy `D²=4CE` with probability one.

In QBS, define `N` by currying `(f,x)↦square(eval(f,x))`. Composition and
currying admit it without changing the function carrier. The identities
`N∘c = curry(eval₂)∘repair` and
`obs₃∘N∘c=v` give the same pushforward law. These are our applications of
the stated exponential and probability structure. QBS still owes that
structure's construction, source interpretation and selected observer laws
in a local formalization; naming the category removes none of those tasks.

Both routes can retain the original sampled environment explicitly as
`(e,N(c(e)))` when the consumer requests its graph witness. Equality of output
laws alone does not recover that chosen `e`. Further repeated squaring grows
the required polynomial degree for this coefficient scheme, whereas the QBS
carrier remains `F`; neither observation is a measured cost or a claim that
all closure representations must grow in that fashion.

### Current probability source trace

| Source | Trace and exact boundary |
|---|---|
| [ProbabilityCorrelation](../../../Examples/ProbabilityCorrelation.lean) | `shared` maps one fair bit to a diagonal pair; `independent` uses its product measure. `shared_off_diagonal` and `independent_off_diagonal` give 0 and 1/4; `joint_distributions_differ` rejects equality. `copy_after_draw` and `draw_twice` identify the actual kernel compositions. These are existing Lean theorems, not the continuous calculation above. |
| [FiniteKernel](../../../Applications/Probability/FiniteKernel.lean) | `Table.comp`, `kernel_comp`, `kernel_deterministic` and `tableMeaning_laws` interpret rational finite tables compositionally in `Stoch`. They support the finite common fragment; they do not construct `Real⇒Real` or the continuous polynomial repair. |
| [Compiler](../../../Compiler.lean) | `Target.curry`/`apply` and the `Term.lam`/`app` cases expose pure function obligations. `Ty` has no probability constructor; its `Val` arrow is the full Lean function space, which cannot simply be identified with admitted QBS morphisms. |
| [STLCNaturality](../../../SquareKit/STLCNaturality.lean) | `Model`, `Preserves` and `naturality` provide an object-polymorphic pure interpretation and its preservation requirements. Probabilistic source sequencing, strength and bind need their own laws; pure syntax induction does not derive them. |

## Decisions, remaining obligations and shared architecture

| Formulation | Outcome of this probe | Next bounded obligation and owner |
|---|---|---|
| Contextual/nameless binding | Retain. The two-lift derivation and third-tail extension preserve the selected value. Existing contextual machinery is reusable but does not already encode the fixture's whole lambda interface. | #289 owns a checked two-family binder admission with these substitutions and third-tail regression; coordinate the model interpretation boundary with #366. |
| Nominal annotated abstraction | Investigate as an alternative representation. The worked freshening and selected payload pass; raw bound-name observation fails and is repaired. | #289 owns equivariant dependent typing and a semantics-preserving comparison for the bounded annotated telescope. Count generic support setup separately; do not require a maximal incumbent adapter first. |
| Pointwise laws as a random-function representation | Reject for this contract. The three finite joint tables have the same marginals. | #235 retains the existing correlation regression; any proposed abstraction must preserve joint observations or retain the common sample. |
| Finite kernels and fixed coefficient closures | Retain for their fragments; revise the affine representation for the nonlinear client. The polynomial repair passes pointwise and in law. | #235 with probability owners can formalize this bounded repair if a consumer needs it, preserving old affine clients and the original sample payload where requested. It does not discharge arbitrary currying. |
| Probability-only QBS | Investigate. The source theorem and worked composition meet the mathematical higher-order contract. No model implementation or productivity win is established. | #200/#235 coordinate a bounded acceptance decision; #36 owns model construction. The next formal scope is probability-only evaluation/currying plus the common-fragment Dirac/bind/product comparison and these joint-law regressions, not a whole library replacement. |
| Recursive domains, conditioning and internal valuations | Defer. None is a hypothesis of either worked probability calculation. | #36/#235 revisit on an explicit recursive, conditioned or lower-information consumer contract; these require additional model and adequacy hypotheses. |

Institutions and shared meaning can publish the admitted operations and their
preservation requirements. They do not automatically derive freshness-safe
dependent substitution or preserve the common sample after it has been
forgotten. A comparison must retain the selected substitution and observation
maps, not just show that endpoints have isomorphic carriers.

Dependent coherence is relevant to the binding lift equations when the family
model is weak rather than strictly reindexed. It is not supplied by nominal
alpha-equivalence. Extension interaction appears concretely when the binder
gains its dependent tail, or squaring is combined with sampling: copying a
sampled function is a pure value operation, while repeating sampling changes
the joint law. #364's interaction accounting can record those obligations;
existential relational hiding alone loses the selected finite element and
does not specify a probability law.

The orbifold comparison shares the need to retain designated maps and selected
data. Its higher identity and smooth model requirements are different from
syntactic bound names, finite-family values and QBS random elements. None of
these results supplies that joint geometric model or depends on the external
Myers investigation. They justify keeping the independent binding and
probability comparisons visible alongside #363/#366, without combining all
structures into one interface.

## Validation and limits

Whitespace, local links, the exact finite probability tables, the rational
moment calculations and the concrete finite binding fixtures were checked.
These mechanical checks do not certify the paper's general substitution or
measure arguments. No Lean sources changed; no new build or proof audit is
claimed. The primary-source inspection covered the cited abstraction,
iteration, exponential and monad statements, not a new audit of all their
proofs. #107 remains paused, #108 unselected and #260 inactive.
