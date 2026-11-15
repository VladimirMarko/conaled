# Higher-order behavior and independent function meaning

Issue [#285](https://github.com/VladimirMarko/conaled/issues/285) supplies a
checked negative fit result and a working logical comparison. Keep mathematical
function equality as the meaning contract for this total fragment. Retain
step-sensitive behavior as a separate contract when a client needs it. A
step-sensitive model cannot replace that meaning while preserving its equations.

## Source obligations

The sources below were consulted as full papers, including the theorem
hypotheses and relevant proofs, rather than relying on their abstracts.

**Strong congruence.** Goncharov et al., [*Higher-order bialgebraic semantics*,
v5](https://arxiv.org/pdf/2405.16708v5), Assumptions 4.2, Definition 4.3 and
Theorem 4.14 require finite limits/colimits, a variable object V, syntax
Σ = V + Σ′ with free algebras, and a final B(μΣ,−)-coalgebra. The law is
natural in outputs and dinatural in V-pointed inputs. Congruence additionally
requires regularity, preservation of reflexive coequalizers by Σ, and
preservation of monomorphisms by B (epimorphisms in its contravariant input).
The kernel of the behavioral map is then a congruence. Section 5 handles
binding with presheaves and substitution behavior. The call-by-value case
explicitly differs from standard strong applicative bisimilarity. Consequently,
our cost projection below is not claimed to instantiate that entire model.

**Denotational construction.** [*Towards a Higher-Order Bialgebraic Denotational
Semantics*, v2](https://arxiv.org/pdf/2602.18295v2), Assumption 3.1 requires final
B(X,−)-coalgebras. Definition 3.2 fixes a locally final Z: final for B(Z,−),
not final among higher-order coalgebras. Definition 3.5 stratifies constructors
by a well-founded rank: transition targets have lower-rank constructors except
possibly their head. Theorem 3.9 extends locally final Z under this relative
flatness. Nested Y in `Y e → e (Y e)` violates the usual rank condition
(Remark 3.8). Theorem 3.11 gives denotational equality ⇒ behavioral equality
for compatible bialgebras; its proof factors behavior through denotation.
Theorem 4.13 needs a stable M-category with terminal object and chain limits,
contravariant local contractiveness, covariant local non-expansiveness,
inhabited C(1,B(1,1)), and convergent final sequences. Inhabited hom-sets add
uniqueness. Section 6 leaves behavioral equality ⇒ denotational equality
(soundness, hence full abstraction with adequacy) and weak denotational
semantics open. None of these assumptions is silently supplied by our experiment.

**Weak congruence.** Urbat et al., [*Weak Similarity in Higher-Order Mathematical
Operational Semantics*, v4](https://arxiv.org/pdf/2302.08200v4), Theorem VIII.6
uses Assumptions IV.1 and VIII.1: complete, cocomplete, well-powered base;
pullback-stable strong epimorphisms; local distributivity; Σ = V + Σ′ preserving
strong epimorphisms and generating a free monad; preordered mixed-variance B
with a relation lifting good for simulations; and a pointed GSOS law admitting
a relation lifting. Definition VIII.2 requires lax-to-strict simulation
conversion, reflexivity on identity relations, and its stated composition
inequality. A weakening satisfying Definition VI.4 must form a lax bialgebra:
rules remain sound for weak transitions. Howe closure proves congruence.
Examples III.4–6 show this last condition can fail. Section IX-B and Appendix E
instantiate the result to open call-by-name lambda terms, including substitution;
Theorem IX.2 gives applicative-similarity congruence. This supplies neither a
weak locally final denotational construction nor full abstraction for an
independently chosen D.

## Constructed experiment

[HigherOrderComparison.lean](../../SquareKit/HigherOrderComparison.lean) defines
only ground naturals, function types, variables, tagged numeral constants,
lambda and application. Finite contexts use typed de Bruijn variables. Terms
are finite but have no fixed size bound. There is no recursion, effect,
divergence or syntax inspection among the admitted constructors.

`D ground = Nat` and `D (a → b) = D a → D b`; `denote` interprets lambda as
mathematical function formation and application as function application. This
specification does not mention execution, steps, `run`, or behavioral equality.
It is an independent set/function interpretation, comparable with the existing
compiler's `Val`/`eval` account, rather than a quotient chosen to fit a desired
operational theorem. The broader comparison of semantic traditions remains
with [#280's assessment](external-discovery-assessment.md); #286/#287 are
separate experiments.

`V` interprets functions as maps from behavioral values to costed computations.
`run` evaluates function, argument and body in call-by-value order. Constants,
variables and formation of a closure cost zero; each application adds one beta
contraction. Function values retain latent body costs. This is a constructed
total evaluator, with a count of beta contractions, not wall-clock time, heap
usage, or a measured implementation. At ground type `delayStep` turns the
count/result pair into a finite chain of silent steps followed by a numeral.
It is a projection of execution; no finality or universal trace characterization
is claimed.

`Rel a : V a → D a → Prop` compares the carriers. At functions it quantifies
over **related inputs** and compares results, forgetting costs. That input
obligation is essential: arbitrary behavioral functions need not respect
extensional input equality. We therefore do not assert a total erasure map on
all behavioral functions. `comparison` constructs relation evidence for every
term in related environments. `application` gives the typed application law;
`extend_related` discharges its binding obligation. These are directly proved
specializations of the comparison method, not formalizations or instantiations
of the categorical source theorems.

Ground observations admit two contracts:

- `strong t` exposes the beta count and numeral. `strong_implies_denote`
  proves equality implies equal mathematical results.
- `weak t` exposes the numeral only. `weak_iff` proves its equality is exactly
  equality of closed ground denotations. This is a proved agreement for this
  total ground fragment, not higher-order contextual full abstraction or the
  source paper's weak-similarity relation.

The value `0` and `(λx.x) 0` denote zero, but their strong observations are
`(0,0)` and `(1,0)`. `strong_distinguishes`, `weak_identifies`, `delay_redex`
and `delay_zero` retain the distinction and its disappearance under the weaker
observer. `no_strong_adapter` proves that **no** map from mathematical ground
meaning can recover these strong observations. This refutes the converse of
`strong_implies_denote`, and rules out adopting this strong observation as D's
equality without changing the intended equations. The successful alternative
is `Rel` and the ground result projection.

## Substitution, binding and rejected observers

`rename`, `liftSub` and `subst` implement capture-avoiding substitution.
`denote_subst` proves the mathematical substitution law;
`substitution_comparison` connects substituted execution to the original term's
meaning under a compatible environment. It deliberately does not preserve
cost: inserting an expression can evaluate it more often than storing its value.

The open pair `λy.x` and `λy.((λz.z) x)` exercises extension beneath a binder.
`binding_equal` uses `lam_congr`; `binding_substitution_equal` uses
`subst_congr` to close x with zero. `bound_context_weak` then uses `twice_congr`
and `weak_iff` to pass the resulting function through `f (f 0)`.
`bound_context_strong` rejects strong equality of those same clients.
`binding_comparison` separately instantiates the substitution comparison with
x denoting seven. `invoke_identity_comparison` exercises `application` with a
function supplied as an argument. Thus the examples use the public comparison
and compatibility theorems, including their environment hypotheses.

Two constants have different Bool presentation tags but the same numeral.
`inspect` is a proposed syntax observer outside the language.
`no_uniform_inspector` proves it cannot factor through mathematical meaning:
the same zero would have to produce both Bool values. This pinpoints failure
of semantic compatibility, rather than claiming a formal dinaturality failure
for a GSOS law we have not constructed. Adding this observer would invalidate
the chosen equality contract.

## Adoption and remaining ownership

Adopt the explicit function-input relation and the environment-extension,
application and substitution comparison pattern for the next higher-order
client. It isolates the input variance obligation and preserves an independent
meaning. The bounded module requires no shared-interface migration; ordinary
and indexed composition, exact parser `Decision` fibers and noncommutative
weighted meanings retain their existing contracts.

Do not yet replace `IndexedCompositional` with a presheaf or GSOS interface.
The mathematical benefit of a general rule-format theorem would be shared
congruence proofs across languages. Its missing implementation work includes
binding/substitution presheaves, mixed-variance relation liftings, the actual
rule-format laws and source existence hypotheses. Its migration must recover
the ordinary/indexed laws and witness/weight examples before changing their
clients. The present experiment establishes no benefit from imposing those
structures on first-order clients.

[#235](https://github.com/VladimirMarko/conaled/issues/235), coordinated with
#36/#200, retains the architecture decision: select an actual further
higher-order client before generalizing this bounded interface. It also owns
the remaining weak-domain and full-abstraction questions; this result does not
close them. An extension with divergence or effects needs new observations and
comparison evidence. #279 owns independent author trials; no usability result
is inferred from the implementer's successful Lean encoding. Mathematical fit,
Lean encoding effort, and author usability remain separate evidence.
