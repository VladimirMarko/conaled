# Weak higher-order behavior with partial meaning

Issue [#303](https://github.com/VladimirMarko/conaled/issues/303) extends
[#285's total comparison](higher-order-extensional-comparison.md) with a typed
silent loop. Adapt its explicit input relation to partial computations. Adopt
the proved return/divergence comparison for this bounded client. Defer a general
weak bialgebraic denotational framework and higher-order full abstraction.

The checked implementation is
[WeakHigherOrder.lean](../../SquareKit/WeakHigherOrder.lean). It leaves the
ordinary/indexed APIs, exact witnesses, and #285's definitions and theorem
contracts unchanged.

## Frozen fragment and client

Types are naturals and arrows; terms are typed variables, numerals, lambda,
application, and `omega` at any type. Contexts use #285's typed de Bruijn
variables. The sole recursion mechanism is the equation `omega → omega`.
This supports indefinite silent execution without a total fixed-point axiom.
It does not support general recursive definitions or data-dependent recursion.
The mechanism was selected because the experiment concerns whether weak
observations preserve undefinedness through higher-order application, rather
than the expressive power of a recursive programming language.

`client f` applies the higher-order function `λf. f 0` to `f`. Supplying identity
returns zero. Supplying `λx. omega` diverges. The divergent function itself is a
value; divergence occurs when the client invokes it. These instances and their
observations were fixed before the comparison proofs.

The mathematical interpretation uses lifted sets: ground values are naturals,
function values map values to `Option` results, lambda returns a function,
application is Kleisli application, and omega denotes undefinedness. `denote`
does not refer to operational computations, transitions, counts, or fuel.
`none` means undefinedness, not an evaluator timeout or an exception.

The separate operational interpretation `run` composes `Comp` computations.
A computation either returns a value after a finite beta count or spins.
Function values carry latent computations. Application evaluates the function,
argument, and body in order and adds one beta contraction. `Comp.step` exposes
one silent transition per finite beta count; spin takes a silent self-loop.
Divergent finite prefixes are collapsed into spin. This is a compositional
behavior model, not an implemented CEK machine or a term-reduction semantics.
The theorems establish agreement with this model only. Recovering a conventional
machine's behavior would require a separate simulation proof.

## Observations and checked comparisons

`Returns c n` is an inductive finite execution ending in numeral `n`.
`Diverges c` requires an infinite sequence of silent transitions starting at
`c`. `spin_diverges` constructs that sequence. `done_not_diverges` rules it out
for every finite computation by descent on its count. `returns_iff` and
`divergence_iff` characterize both observations against the computation's
result projection. There are no stuck states or nondeterministic choices in
this model.

The frozen weak observation exposes the returned numeral or divergence and
hides beta and omega steps. `Pre` is inclusion of may-return observations.
It is directional: divergence is below zero, but zero is not below divergence
(`preorder_not_equivalence`). `mutual_pre_iff` proves its symmetric part is
exactly equality of result projections. Thus equivalence distinguishes
termination from divergence even though one direction of the preorder does not.
No claim identifies this definition with a source paper's mixed-variance weak
similarity.

`Rel` compares behavioral and mathematical values. At arrows it quantifies
over related inputs and requires exact lifted agreement of the outputs,
including undefinedness. `Lift` is neither a termination-only implication nor
an assumption that all functions are total. `comparison` constructs this
relation for every term in related environments. `extend_related`,
`binding_comparison`, and `application` expose the binding and application
obligations.

For closed ground terms, `observed_return` and `observed_divergence` prove both
directions of agreement with independent meaning. `weak_iff` proves equality
of weak observations iff equality of denotations. `pre_iff` identifies the
return preorder with inclusion of defined mathematical results.
`client_terminates` and `client_diverges` use these public comparison theorems;
`invoke_partial_comparison` also applies the general application law to the
higher-order caller and its looping argument.

`fuel` approximates the transition system. `exhaustion_not_divergence` shows
that one unit of fuel gives the same inconclusive result for identity applied
to zero and omega, while the former cannot diverge and the latter does.
`fuel_spin` alone would not establish divergence; the infinite path does.

## Contexts, substitution, and failures

`Context` supports holes, application on either side, and lambda binding.
`context_congr` proves preservation of open denotational equality in every
such finite typed context. `context_weak` connects that result to closed ground
weak observations. This is a direct bounded contextual soundness result,
without using a categorical congruence theorem. It does not assert that closed
observations alone characterize open higher-order denotational equality.

For the selected higher-order caller, `client_pre` proves preservation of the
may-return preorder under the pointwise return obligation on supplied lambda
bodies. `looping_client_pre` discharges it for the divergent and identity
functions. Preorder preservation for every higher-order context is not proved;
the supported general contextual theorem concerns semantic equality, and the
preorder theorem concerns this caller with its explicit obligation.

Capture-avoiding `rename` and `subst` have mathematical preservation laws.
`denote_subst` requires substituends to denote values in the supplied
environment. `substitution_comparison` then compares substituted execution
with the original term's meaning. The example closes the free variable in
`λy.((λz.z) x)` with seven beneath the binder, and passes the resulting function
through the client. `bound_substitution_comparison` and `bound_client_weak`
exercise the general laws. Costs need not survive arbitrary substitution.

`unrestricted_beta_fails` rejects removing the value obligation: applying
`λx.0` to omega diverges under call-by-value, although replacing its unused
variable leaves zero. `no_strong_adapter` rejects recovering finite beta
counts from partial mathematical meaning: zero and identity applied to zero
have equal meanings but different counts. Neither observation was weakened to
make these obligations pass.

`embed` recovers #285's total syntax. `TotalRel` preserves latent costs on
related total inputs; it does not cast partial functions to total functions.
`recovery` proves termination and the old count for every embedded term in
related environments. `recovery_ground` gives the exact old count and numeral;
`recovery_meaning` connects to #285's independent meaning.
`recovered_bound_context` reuses the old binding/context theorem, including
its existing substitution contract. The old APIs remain available directly.

## Primary-source assessment

The versions inspected are pinned below; these are source assessments, not
Lean dependencies.

Urbat et al., [*Weak Similarity in Higher-Order Mathematical Operational
Semantics*, v4, 28 September 2023](https://arxiv.org/pdf/2302.08200v4),
Theorem VIII.6 assumes IV.1 and VIII.1: a complete, cocomplete, well-powered,
locally distributive base with pullback-stable strong epimorphisms; syntax
`Σ = V + Σ′` preserving strong epimorphisms and generating a free monad;
a preordered mixed-variance behavior bifunctor with a relation lifting good
for simulations; and a pointed GSOS law admitting a relation lifting.
Definition VIII.2 requires lax-to-strict simulation conversion, reflexivity on
identity relations, and its composition inequality. The weakening must satisfy
Definition VI.4 and form a lax bialgebra (VIII.4): the rules remain valid for
weak transitions. Appendix E checks these obligations for the call-by-name
lambda calculus, including substitution; Theorem IX.2 obtains applicative
similarity congruence. Our call-by-value lifted-set comparison does not inherit
that instance. We prove the bounded context results directly and construct no
GSOS law or categorical lifting. Operational congruence alone supplies no
comparison with our independent denotation.

Goncharov et al., [*Towards a Higher-Order Bialgebraic Denotational Semantics*,
v2, 30 June 2026](https://arxiv.org/pdf/2602.18295v2), assumes final
`B(X,−)` coalgebras (3.1). Its locally final domain is final for `B(Z,−)`
(3.2). Theorem 3.9 requires relative flatness with well-founded constructor
ranks (3.5); nested fixed-point syntax can violate it (3.8). Theorem 3.11
establishes denotational equality implies behavioral equality for a compatible
bialgebra. Theorem 4.13 constructs domains under a stable M-category with
terminal object and chain limits, contravariant local contractiveness,
covariant local non-expansiveness, inhabited `C(1,B(1,1))`, and convergent
final sequences; inhabited hom-sets add uniqueness. Section 6 leaves weak
denotational semantics and the converse/full-abstraction question open.
Our Option meaning is not supplied as a locally final domain. In particular,
`no_strong_adapter` prevents factoring our step-sensitive observation through
this chosen ground meaning. The paper's adequacy theorem cannot be silently
reinterpreted as a weak comparison theorem for it.

## Adoption boundary

Soundness and adequacy terminology varies. Here the checked ground equivalence
has both explicit directions: equal partial meanings imply equal weak
observations, and equal weak observations imply equal partial meanings.
Return and divergence agreement also have both directions. Semantic equality
is sound for the supported finite contexts. Reflection from contextual
indistinguishability to higher-order denotational equality, definability of
arbitrary semantic inputs, and language-wide full abstraction remain unproved.

Adapt the lifted comparison, explicit input obligation, and value-substitution
contract for this client. Retain the strong obstruction and the CBV beta
counterexample as guards against invalid extensions. Defer the source
frameworks until another client warrants categorical relation liftings,
lax-bialgebra proofs, locally final domain construction, or a general recursion
model. No shared-interface mismatch requires migration here. Broader weak-domain
and full-abstraction work remains with [#235](https://github.com/VladimirMarko/conaled/issues/235),
coordinated with #36/#200. Ordinary/indexed and exact-witness clients gain no
proved benefit from adopting these extra obligations.
