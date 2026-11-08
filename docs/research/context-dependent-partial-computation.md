# Partial computation with selected indexed certificates

Research deliverable for [#337](https://github.com/VladimirMarko/conaled/issues/337),
under [#289](https://github.com/VladimirMarko/conaled/issues/289). The external
construction below preserves a selected result and its certificate through
arbitrary reindexings of set-indexed families. A synthetic-domain-theory (SDT)
construction has the same property under explicit completeness and base-change
hypotheses. Fixed-point existence alone supplies neither result selection nor
base-change coherence.

The original #337 assessment below contains paper proofs and source results;
its local comparisons refer to `b8731310f05efdac29f994706fbc1f32eb77de20`.
[#346](https://github.com/VladimirMarko/conaled/issues/346) now formalizes the
external construction. [#347's concrete effective-topos assessment](effective-topos-selected-solutions.md)
now discharges the SDT package for this certificate family on paper, including
slice comparisons and two substitutions. It does not add a Lean SDT provider.
[#354's multiple-certificate construction](effective-topos-multiple-certificates.md)
extends the paper provider to two distinguishable records in each fiber and
preserves an independently selected alternating result.

## Checked external construction

[SelectedFixedPoint](../../SquareKit/SelectedFixedPoint.lean) uses Mathlib's
`OmegaCompletePartialOrder`, `ContinuousHom`, and supremum of the iteration
chain. `solution_fixed` and `solution_le` recover fixedness and leastness;
`map_approximants` and `map_solution` derive transport from strictness and
continuous intertwining. Neither selected-solution preservation nor a
whole-client theorem is an input field.

[IndexedPartialComputation](../../Examples/IndexedPartialComputation.lean)
specifies `Cert` and `meaning` independently of that construction.
`approximants_eq_bounded` computes the finite approximants;
`solution_eq_meaning` identifies their supremum with the specified enabled
countdown, including the disabled bottom case. `reindex_solution` applies the
generic transport theorem, and `two_reindexings` uses it twice to retain
4 : Fin 5 and [2,1,0]. `observe_solution` applies the same theorem to forget
only the trace. The examples retain the non-strict constant-map failure and
Boolean-negation obstruction. A successful result beyond current fuel shows
why finite exhaustion is unknown rather than divergence evidence.

The checked statements concern mathematical partial denotation and successful
finite traces. They do not prove adequacy for an external evaluator, provide
an SDT model, or measure productivity. The abstract solver is noncomputable.
The bounded formula is identified with its approximant; its bottom outcome
has no divergence certificate. The intended claims were checked against the
independent value/trace contract, including the direction of both substitutions
and retention of the entire certificate before observation.

## Contract fixed before either construction

A context Γ supplies `enabled : Γ → Bool` and `size : Γ → Nat`. A computation
at γ starts with a counter k. When enabled, it counts down to zero and returns
the selected value `size γ : Fin (size γ + 1)`. When disabled it diverges.
The intended partial meaning is specified by its graph:

```text
Result(γ,k) is defined iff enabled γ = true.
When defined it is (size γ, [k, k-1, ..., 0]).
```

The trace is retained data, not merely a termination proposition. Define the
independent family `Cert(γ,k)` to consist of a value `v : Fin(size γ + 1)` and
a list τ, with `v.val = size γ` and `τ = [k,k-1,...,0]`. These equations specify
the client without mentioning a solver, fixed-point operator or evaluator.
Write `c(γ,k)` for that displayed record. Its correctness proof is unique in
this set-valued setting; its value and list still have to be transported.
For example `size γ = 3`, `k = 2` requires the value 3 in `Fin 4` and trace
`[2,1,0]`. An arbitrary inhabitant of `Fin 4` or a Boolean success report fails.

Equality in this setting means equality of partial graphs and exact equality
of their returned value/list records. The proposition fields of `Cert` carry
no additional observations. This is the specification's contract, not a claim
that higher identity witnesses in other settings are irrelevant.

For `σ : Δ → Γ`, the reindexed family is definitionally
`Certσ(δ,k) = Cert(σ δ,k)`; both context functions are precomposed with σ.
For `τ : Θ → Δ`, demand preservation of this complete record and equality of
the sequential and composite transports. No injectivity, surjectivity or
inhabitedness condition on σ or τ is allowed.

## External construction and its proof

**Source basis.** Abramsky and Jung develop pointed directed-complete orders,
continuous maps, products and function spaces. Their least-fixed-point
construction iterates a continuous endomap from bottom and takes the supremum.
The relevant ingredients here are the flat lifting and pointwise products;
we need only increasing countable chains, rather than all directed suprema.
See [*Domain Theory*, Theorem 2.1.19, Lemma 2.1.21 and §3.2](https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf).

**Paper construction.** Let `Dγk = Cert(γ,k)⊥` be the flat order: bottom lies
below every returned record, and different returned records are incomparable.
Every increasing countable chain is either constantly bottom or eventually
constant at one record. Let `XΓ = ∏ γ,k Dγk`, ordered pointwise. Bottom and
chain suprema are pointwise, so XΓ is an ω-cpo with bottom.

There is a strict map `stepγk : Dγk → Dγ(k+1)`. It sends bottom to bottom;
on a record it prepends `k+1` to the trace, retaining v and deriving the new
trace equation. Define an endomap FΓ of XΓ by

```text
FΓ(q)(γ,k)   = q(γ,k)                         if enabled γ = false
FΓ(q)(γ,0)   = return c(γ,0)                  if enabled γ = true
FΓ(q)(γ,k+1) = stepγk(q(γ,k))                 if enabled γ = true.
```

The disabled clause models an unproductive self-call. Each coordinate is a
projection, a constant or a strict map of flat orders after a projection.
Each preserves increasing-chain suprema; thus so does FΓ. This verifies
continuity for this functional rather than assuming arbitrary functions are
continuous.

Put `q₀ = ⊥`, `qᵢ₊₁ = FΓ(qᵢ)` and `q* = supᵢ qᵢ`. Monotonicity makes the
chain increasing. Continuity gives
`FΓ(q*) = supᵢ qᵢ₊₁ = q*`. If FΓ(r) = r, induction gives `qᵢ ≤ r`, hence
`q* ≤ r`. The selected fixed point is therefore the least one.
A second induction computes every approximant:

```text
qᵢ(γ,k) = return c(γ,k)  iff enabled γ = true and k < i;
qᵢ(γ,k) = ⊥             otherwise.
```

Taking the supremum proves exactly the independently specified graph. In
particular the disabled branch remains bottom although its fixed-point
equation alone would allow any value. The returned trace has length k+1;
this is a semantic trace count, not an instruction-count or wall-clock claim.

### Two successive reindexings

Define `Rσ(q)(δ,k) = q(σ δ,k)`. It is strict, preserves chain suprema, and
satisfies `Rσ ∘ FΓ = FΔ ∘ Rσ` by the three displayed clauses. Induction on i
therefore gives `Rσ(qᵢΓ) = qᵢΔ`; taking suprema gives

```text
Rσ(q*Γ) = q*Δ.
Rτ(Rσ(q*Γ)) = R(σ ∘ τ)(q*Γ) = q*Θ.
```

The equalities compare complete `Cert` records in the correct fibers, so the
selected value, trace and correctness predicate all survive. They do not
first forget to fixed-point existence and later choose a fresh certificate.
For a concrete nonidentity composition, take Γ = Bool × Nat,
`σ(b,m) = (b,2m)`, and `τ(t) = (true,t+1)`. At t = 1 and k = 2, either route
returns 4 in `Fin 5` with `[2,1,0]`. Replacing `true` by `false` gives bottom
through both routes.

More generally, the same proof works for a strict, ω-continuous H satisfying
`H ∘ F = G ∘ H`: H sends the least fixed point of F to that of G. Strictness
and supremum preservation are the local obligations from which the final
selected-solution comparison follows. It is not a required final field.

## SDT in slices: sufficient assumptions and the remaining model obligation

**Source result.** Van Oosten and Simpson work in a topos with a natural
numbers object and dominance Σ ⊆ Ω: truth belongs to Σ, and
`p ∈ Σ ∧ (p ⇒ q ∈ Σ)` implies `p ∧ q ∈ Σ`. The associated partial-map lift
L has initial algebra I and final coalgebra F. An object X is complete when
restriction along `I → F` gives an isomorphism `X^F → X^I`. Their Theorem 1.13
constructs a fixed point for every endomap of a complete strict L-algebra;
its proof uses the unique extension to F of an iteration map on I and evaluates
at infinity. See [Definitions 1.1, 1.11 and Theorem 1.13](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf).

**Conditional paper construction, additional to that source theorem.** Work
internally in each slice E/Γ. For this client require the following package:

1. A topos E with NNO, a dominance, and false in the dominance, so empty
   partial results exist. In each used slice fix the induced dominance and
   its lift `LΓ`, unit η and multiplication μ.
2. The certificate families, dependent products over k, and an object
   `XΓ = ∏k LΓ(Cert(γ,k))`. Require XΓ to be complete and to carry its
   pointwise strict LΓ-algebra `a : LΓ XΓ → XΓ`, satisfying the unit and
   multiplication laws. These are hypotheses to prove in a model; merely
   being an object of the slice is insufficient.
3. The countdown constructors and FΓ as morphisms in that slice. The
   underlying comparison to the independently specified certificate family
   retains v and τ. We do not replace it by the proposition of existence.
4. For each used pullback σ*, specified coherent comparisons for L, X, I,
   F, their structure maps, `I → F` and infinity. These identify the pulled
   iteration structure with the chosen structure in the new slice. Require
   the pulled X to remain complete, and the comparisons to respect η, μ,
   a, countdown constructors and FΓ. Identity and composite base changes
   must agree under the usual canonical pullback isomorphisms.

Here “strict L-algebra” has the source's monad-algebra meaning, expressed by
the unit and multiplication laws. It is not an extra demand that FΓ preserve
bottom. FΓ's enabled zero clause does not preserve bottom.

The hypotheses are deliberately sufficient rather than claimed minimal.
In particular no theorem that completeness automatically survives every
base change is used. Nor is completeness of a lift inferred merely from
completeness of its unlifted object. A concrete SDT provider must establish
this whole package for the required family and substitutions.

Let h be the unique map from the initial strict algebra with successor into
`(XΓ,a,FΓ)`. Let h̄ extend h along `IΓ → FΓ∞`, where `FΓ∞` here denotes the
final lift coalgebra, to avoid confusing it with the countdown functional.
Define `fixΓ(FΓ) = h̄(∞)`. After a specified pullback, the comparison of h is
again a structure-preserving iteration map, so initiality identifies it with
the new h. The comparison of h̄ extends that map, so completeness identifies
it with the new h̄. Infinity compatibility then proves preservation of the
selected fixed point. Applying the argument twice and using the package's
composite coherence proves the same two-reindexing equation as above. This
uses the construction's uniqueness properties, not uniqueness of arbitrary
fixed points.

For the actual countdown contract, restrict to the enabled and disabled
Boolean subcontexts. The enabled fixed-point equation proves by induction
on k that the result is `return c(γ,k)`. In the disabled subcontext F is the
identity. Its iteration map is constant bottom: that map preserves the strict
algebra and successor structures. Its extension is also constant bottom,
uniquely by completeness. Thus the selected solution is bottom there. The
Boolean case split proves the independent graph in the original slice.
The base-change package must include these two restrictions as well as σ, τ.

This #337 argument is a conditional solution to exactly the same client,
without assuming a least-fixed-point order internally. It does **not** itself
construct a concrete SDT topos or discharge completeness of this XΓ.
The [#347 follow-up](effective-topos-selected-solutions.md) discharges that
model obligation on paper in Eff for this family; it also states the narrower
internal-morphism substitution boundary and the cost of formalizing a provider.
The external family construction already supplies an unconditional classical
set-based instance; it is not evidence that classical Set satisfies the SDT
package for arbitrary objects and maps.

## Two distinct rejection controls

**No unrestricted fixed points.** On classical Bool, negation has no fixed
point: both cases contradict `b = not b`. Thus a model interpretation admitting
Bool and negation as a complete strict-algebra/endomap instance of the SDT
fixed-point theorem cannot exist. This does not contradict the external
construction: a discrete Bool is not pointed, and a bottom-preserving lift of
negation has bottom as a fixed point without a total Boolean result.

**Existence and intertwining do not preserve selection.** On the flat lifted
Bool domain D, let F = G = identity and choose their least fixed points bottom.
The constant map H(x) = return true is continuous and satisfies `H F = G H`.
It sends fixed points to fixed points and therefore preserves existence, but
`H(lfp F) = return true ≠ bottom = lfp G`. H is not strict. Even in a setting
without an order, the identity map between two copies of Bool with identity
endomaps and different selected solutions false/true preserves every fixed-point
equation but fails selected-solution preservation. These controls isolate the
extra requirement from the absence-of-fixed-points control.

## Operational and architectural consequences

The semantic fixed point exists whether the enabled flag is true or false.
The selected partial result includes divergence. A fuel-bounded evaluator
can compute qᵢ with structurally decreasing fuel and return bottom/unknown
when fuel is exhausted. That evaluator terminates for every fuel, but it
cannot label its bottom result as proven divergence. An unbounded evaluator
for this specification terminates precisely on enabled inputs; the disabled
loop is not productive. No infinite-output productivity theorem is needed
or obtained. The finite trace theorem concerns successful runs only.

The existing [guarded stream construction](../../SquareKit/GuardedStreams.lean)
uses coordinate guardedness to derive a **unique** solution and `map_solution`.
Our disabled identity functional is not guarded and has many solutions.
Consequently that uniqueness proof cannot be reused to justify selection here.
The external construction replaces it with bottom, continuity and leastness;
the SDT route replaces it with initial iteration and unique extension. Both
fit the project's practice of deriving a global comparison from local laws,
but their premises differ.

The bounded external implementation in #346 supplies the partial certificates,
approximants and transport above. It reuses Mathlib's order infrastructure and
leaves the guarded-stream API unchanged. #347 and #354 supply the concrete
paper SDT providers linked above; checked SDT infrastructure remains deferred.

The external cost is explicit order/continuity infrastructure and proofs that
chosen operations preserve approximants. SDT could move these obligations into
the ambient setting, but adds dominance, completeness, internal-model and
base-change construction costs. Its concrete next research test is a provider
of the four-item package above, including the Boolean restrictions. Failure
of one item should identify that item and model, rather than be reported as
failure of all SDT. There is no measured agent or human productivity comparison.
