# Metatheory contracts for extending a language

Assessment for [#254](https://github.com/VladimirMarko/conaled/issues/254),
2026-10-30, against local baseline `5e49a5d`. The smallest useful next adaptation
is the primitive-extension experiment in #259. The current library can reuse
its interpretation and relational proofs without adopting a universal rule
framework. Generic metatheories remain useful where their hypotheses match a
particular fragment; this note identifies those hypotheses and their limits.

## What an extension is required to preserve

Adding rules monotonically preserves old derivations when their syntax and
rules remain included. That fact is different from preserving a theorem *about*
all derivations or programs, whose quantifier now ranges over new cases.
For an inclusion `T → T⁺`, distinguish:

| Claim | Required evidence |
| --- | --- |
| Old proofs still exist | An embedding of judgments and derivations that preserves old rules. |
| Old meanings are retained | A restriction of each selected extended model to the old model, with an interpretation comparison. |
| Old-language conservativity | Reflection of the selected old judgments along the inclusion; soundness alone is insufficient. |
| An interpretation extends | Meanings for the new operations and proofs of their equations and preservation obligations. |
| Substitution remains admissible | The extension satisfies the structural hypotheses of the applicable rule framework. |
| Canonicity or normalization remains valid | A theorem covering the extended calculus, including its new constants, reductions and equalities. |
| Inference remains decidable | An algorithm with the required decidable premises and a specification for the extended fragment. |

For example, in a natural-number calculus, adjoining an opaque constant
`c : Nat` with no computation rule leaves old derivations intact but introduces
a closed normal form that is not a numeral. This is a paper counterexample to
*numeral* canonicity, not to consistency or normalization. Adding an equation
between two distinct old constants likewise defeats equality conservativity
unless the old theory already proved it. The extension's obligation must name
which of these properties it promises.

## Generic structural frameworks

The following source results are mathematical results in the cited papers,
not formalizations added to this repository. Numbering refers to the specified
versions. Recommendations are this assessment's conclusions.

## Jacobs: structure for context change

The [book's author-hosted contents](https://www.cs.ru.nl/B.Jacobs/CLT/bookinfo.html) locate fibrations/splittings in §§1.1,1.4, indexed categories in §1.10, first-order internal language in §4.4, term models in §10.3, and comprehension/closed comprehension in §§10.4–10.5. The full book was not retrieved, so do not attribute a numbered book theorem to this investigation.

For checked mathematical details use Jacobs's primary [1991 thesis](https://ncatlab.org/nlab/files/JacobsCategoricalTypeTheory.pdf), also [listed by the author](https://www.cs.ru.nl/~bart/PAPERS/). Definition 4.1.1 specifies comprehension through a functor into the arrow category, with a fibred codomain projection and cartesian arrows sent to pullback squares. Proposition 4.1.8 characterizes it by representation of sections after reindexing. Definition 4.3.1 adds fullness, unit, dependent products and strong sums, with a terminal base object; morphisms preserve this structure. Example 4.3.2 distinguishes the codomain construction (closed exactly for an LCCC) from the constant construction (closed exactly for a CCC). For Proposition 4.3.6’s change of base along a fibration (Construction 4.1.11(ii)), also require a terminal object in the new base to satisfy Definition 4.3.1; a fibration alone does not supply one. A morphism of closed comprehension categories must preserve the specified terminal structure. This separates dependency from the stronger choice that every base arrow represents a type. The book and thesis are different sources; retain thesis numbering explicitly.

**Assessment for this repository:** use comprehension and substitution stability as design vocabulary. These results do not establish normalization, conservative axiom extension, or algorithmic elaboration for our interfaces.

## Uemura: initiality and internal languages

[Version3](https://arxiv.org/pdf/1904.04097v3), Definitions 4.1–4.5: a type theory is a small category with finite limits and designated exponentiable arrows closed under identities, composition and pullback. A model has a small base category with terminal object and a functor to its discrete fibrations preserving finite limits, designated maps and pushforwards along them. Definition 4.14 also constrains model morphisms; arbitrary interpretation functions are insufficient.

Theorem 6.10 constructs a bi-initial model. Definition 7.1 takes a theory over T to be a finite-limit-preserving functor T→Set; Definition 7.4 gives a model's internal language. Theorem 7.20 supplies its left biadjoint. Proposition 7.25 makes the unit an isomorphism, while Theorem 7.31 restricts the resulting biequivalence to democratic models. Section7.2 constructs T[K], adjoining a T-theory; Proposition 7.17 gives its universal property. This is not a claim that arbitrary new axioms preserve old models or decidable conversion.

**Assessment for this repository:** first prove that a proposed language/model fits the designated-map structure. Bi-initiality means uniqueness up to the specified coherent isomorphism, not equality of all implementations. The construction offers a route to an internal language without choosing a universal AST for the repository.

## Bauer–Haselwarter–Lumsdaine: rule fitness conditions

[Version1](https://arxiv.org/html/2009.05539), Definition 5.12: acceptable theories are tight, presuppositive, substitutive and congruous. Tightness includes one symbol rule per symbol; substitutivity requires empty conclusion contexts; congruity supplies congruence rules. Theorem 5.15 needs weak presuppositivity for derivable presuppositions. Theorem 5.22 eliminates substitution for substitutive, congruous theories; §5.4 distinguishes strict scope systems from the residual trivial renamings needed in general scope systems. Corollary 5.24 and Theorem 5.27 give uniqueness of typing and inversion for acceptable theories. Definition 6.20 adds well-presentedness; Theorem 6.32 addresses well-founded replacement.

**Assessment for this repository:** preservation under adding rules requires re-establishing the applicable conditions for the extended presentation. These theorems reconstruct the object part of derivations, leaving equational evidence to other methods; they do not solve conversion or inference. This is a reusable rule-validation layer, not yet an initial-model/internal-language theorem for our own presentation. Avoid conflating acceptable with consistent or normalizing.

## Haselwarter–Bauer: a directly usable extension discipline

[Version1](https://arxiv.org/html/2112.00539v1), Definition 2.18 requires each rule's metavariable context and boundary to be derivable from earlier rules in a well-founded order. Definition 2.20 further requires exactly one symbol rule per symbol. Immediately after it, the paper constructs standard extensions by adding a fresh symbol with a finitary object boundary, or a finitary equality rule. Thus this is an explicit extension recipe, with validity of the new boundary as an obligation.

Result3.6 in §3.1.1 gives substitution admissibility for raw theories; Theorem 3.18 presuppositivity additionally assumes well-formed variable/metavariable contexts. Theorems3.24 and 3.26 require standard theories for inversion and uniqueness of typing. Sections4–6 translate between explicit contexts and annotated variables; assumption sets retain dependencies otherwise lost by equality reflection. Introduction §1 limits the class to distinct type/term syntaxes, four judgement forms and intuitionistic contexts; linear/cohesive contexts and cubical special intervals are explicit counterexamples.

**Assessment for this repository:** this supports optional rule checking in an appropriate fragment. It cannot be the universal setting interface, and finitary equality rules alone do not ensure conservativity or decidable equality.

## MTT: parameter changes versus extra principles

[MTT2021](https://lmcs.episciences.org/7713/pdf), §2 parameterizes syntax by a small 2-category of modes, modalities and transformations. Section5.3 uses strict model homomorphisms. Theorem 6.8 gives closed-term canonicity through Corollary 6.7, with the extra empty-context lock equation `·.μ = ·` assumed in §6.2. Section9.3 explicitly warns that adding its guarded-recursion axioms takes the instance outside the canonicity theorem. This warning is useful even though the paper's abstract states mode independence.

[Normalization version4](https://arxiv.org/html/2301.11842v4), §2 fixes a strict 2-category. Theorems 31–32 construct normalization for terms/types; Theorem 34 and Corollary 35 identify normal forms with equality classes. Corollary 37 requires a decidable mode theory for decidable type checking; §1.1 explicitly identifies equality of 1- and 2-cells as a necessary obstacle. Corollary 38 removes the earlier empty-context lock equation for Boolean canonicity. Section7 extends the proof to crisp identity induction, rather than treating that principle as a free mode parameter. Theorem 40 exhibits an intensional model where the relevant identity comparison is not invertible.

**Assessment for this repository:** modal signatures can vary inside the theorem; new term equations, recursion principles or modalities outside the specified semantics require fresh proof work. This answers the extension question beyond #221's consumer example.

## Effect and resource extensions

Levy's [CBPV+stacks model, Definition 5.2 and Proposition 8.4](https://pblevy.github.io/papers/ctcs02journal.pdf)
uses a strong adjunction with the specified products, coproducts and
exponentials. Proposition 8.4 relates its theories and models using morphisms
that preserve chosen structure strictly. A theory's congruence must contain the
CBPV equations and be closed under substitution, dismantling and concatenation
(§8.2). Adding an effect therefore needs an interpretation of its operations
and equations in such a model; an arbitrary pair of monads is insufficient.
The strict choices in that correspondence also differ from this repository's
chosen-pullback comparisons. CBPV is a useful candidate for an effectful
fragment, not a reason to turn every existing mathematical interpretation into
an evaluation-order calculus.

Hyland–Plotkin–Power's [*Combining effects*, §3 Theorem 5;
§4 Definition 5 and Theorem 8](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/hpp06.pdf)
distinguishes sum from tensor of countable Lawvere theories. A sum combines the
two structures on a carrier; a tensor additionally requires their operations
to commute. Theorem 8, for a target category with countable products, identifies
tensor models with models of one theory in models of the other. Separate model
proofs thus leave the interaction equations unproved. These are results for the
specified algebraic theories, not all effects or arbitrary monads.

For a small **worked interaction test**, let `put₀` and `put₁` overwrite the same
Boolean state. Both are valid state operations individually. Interpreting the
cross-commutation equation required by a tensor would require
`put₀ ∘ put₁ = put₁ ∘ put₀`. The left side ends in zero and the right side in one.
The same-cell interpretation fails that equation. On a product of two cells,
operations on different coordinates commute. The missing law depends on the
chosen interpretation and observations; it is not made true by composing two
proof records. This is a paper calculation, not a new formal result here.

Atkey's [QTT, §2.1.1, Lemma 2.5, Definition 3.2 and
Theorem 3.7](https://bentnib.org/quantitative-type-theory.pdf) requires a usage
semiring that is positive and has the zero-product property. Substitution scales
and adds resource contexts, with matching erased contexts and the lemma's
zero-usage side condition. Soundness uses an `R`-quantitative category with
families and the structures interpreting its type formers. The output usage is
restricted to zero or one. §2.3 exhibits failure of substitution in the earlier
system allowing arbitrary output usages. A usage annotation is therefore a
change to structural rules, not metadata added to ordinary substitution.
Theorem 3.7 supplies interpretation soundness, not unrestricted inference or a
normalization theorem. A local resource extension should specify its graded
substitution first and retain the erased interpretation; no QTT implementation
is justified merely by having existing numerical cost bounds.

## Worked contract: extend primitives while preserving old clients

This is a proposed specialization of existing checked results, not newly
checked Lean code. Fix the existing `Ty`, contexts and term constructors in
[Compiler](../../Compiler.lean). Let `P` and `Q` be primitive families indexed
by input/output type. Define `P⁺ a b = P a b ⊕ Q a b` and an embedding `i` that
recurses over terms and replaces `.prim p t` by `.prim (.inl p) (i t)`.
The extension changes neither binding nor type formation.

For a model `M⁺` of `P⁺`, restrict its primitive field to the left summand to
obtain `M`. All other fields and the object interpretation are identical. The
intended old-term equation is

```text
compile M⁺ (i t) = compile M t.
```

An induction on `t` uses only these definitions and congruence of the underlying
operations. This equality is about interpretations, not equality reflection
between equational theories. It needs no equations for the new primitives.
A separate syntax retraction or conservative-model argument would be needed
for a claim that no new old-language equations become provable.

Now fix `F`, semantic equivalences `E,H`, `MapLaws F E H`, target
`CategoryCongr`, target `ModelCongr`, and an old
`STLCNaturality.Preserves F H M N`. Extend both models with meanings for `Q`.
The **only additional preservation field**, with these fixed structural
operations, is

```text
∀ q : Q a b, H.Rel (F.map (M⁺.primitive (.inr q)))
                       (N⁺.primitive (.inr q)).
```

Case analysis on `P ⊕ Q` supplies `Preserves` for the extension. Existing
[`naturality`](../../SquareKit/STLCNaturality.lean) then covers every extended
term. `preserves_comp` and `naturality_comp` compose this evidence with a further
interpretation without another syntax induction. Old clients retain their
original assumptions by using the restricted models, even when no compatible
new target primitive exists. This is the bounded experiment already owned by
[#259](https://github.com/VladimirMarko/conaled/issues/259).

A concrete relational specialization makes the failure observable. Represent a
natural number by its parity `r : Fin 2`, with `R(r,n)` meaning `r.val = n % 2`.
Take the original primitive family to contain zero, addition and multiplication
with their corresponding parity implementations. Each respects `R`. Adding
successor succeeds: its implementation toggles parity. In contrast, add
`z : Nat → Nat`, with `z(0)=1` and `z(n+1)=0`. A parity implementation `ẑ`
would have to satisfy

```text
R(0,0) and R(0,2)
R(ẑ(0),z(0)) and R(ẑ(0),z(2))
hence ẑ(0).val = 1 and ẑ(0).val = 0.
```

No such implementation exists. The obligation is precisely
[`STLCRelations.Primitives.correct`](../../SquareKit/STLCRelations.lean), whose
relation lifts through products, matching sum tags and functions quantified
over related inputs. We are not asserting a quotient functor on all functions:
arbitrary natural-number functions need not respect parity. The old compiler
and old-client proofs remain valid; only the attempted extension of that
relational target fails. Recovering `z` needs a richer representation, a weaker
observation contract, or exclusion of `z` from this target's supported fragment.

## Worked contract: add dependent products to a change of base

The existing dependent fragment already distinguishes split substitution from
ordinary pullback substitution. Its
[`ordinary_term_substitution`](../../SquareKit/Internal/DependentSheafComparison.lean)
retains a comparison isomorphism. Extending such an interpretation with a
new dependent product cannot erase that comparison.

Here is the intended categorical contract, with all endpoints fixed:

```text
A′ --g′--> A
 | f′      | f
 v         v
B′ --g---> B

f ∘ g′ = g ∘ f′, and the square is a pullback.
f* ⊣ Πf,   f′* ⊣ Πf′.
g* Πf(X) ≅ Πf′ g′*(X), naturally in X in C/A.
```

Assume the ambient category has the required pullbacks and the two displayed
right adjunctions. The comparison is the mate of the pullback comparison;
compatibility with evaluation and currying, rather than a bare objectwise
bijection, is the useful extension law.
[`DependentBaseChange.WithAdjunction`](../../SquareKit/DependentBaseChange.lean)
already supplies `iso`, `evaluation` and `curry_baseChange` under these
hypotheses. [`FamilyCoherence`](../../SquareKit/FamilyCoherence.lean) supplies
identity, composition and associativity comparisons for chosen pullbacks.
An adapter to an extended source interpreter must still connect these laws to
its actual term, substitution and conversion judgments. Those structures do
not yet constitute a generic dependent-language extension generator.

**Failure without the pullback hypothesis:** in sets let `B′=B=A=1`,
`A′=∅`, `f=g=id`, and let `f′,g′` be the unique maps. The square commutes but is
not a pullback. For the empty family `X` over `A`, `g*Πf(X)` has empty fibre,
whereas `Πf′g′*(X)` has singleton fibre (an empty product). They cannot be
isomorphic. Every slice here has the required dependent products; having those
products individually does not supply the omitted base-change condition.
This counterexample is a paper derivation, not a new checked declaration.

## Local reuse, author obligations and recommendation

| Existing interface or assessment | Reuse and remaining work |
| --- | --- |
| [STLCNaturality](../../SquareKit/STLCNaturality.lean) and [STLCRelations](../../SquareKit/STLCRelations.lean) | Reuse operation compatibility, congruence and composition. Add only signature embedding/restriction and concrete extension evidence in #259. The type grammar remains fixed. |
| [Dependent](../../Dependent.lean), [dependent function laws](../../SquareKit/Internal/DependentFunctionLaws.lean), [sheaf interpretation](../../SquareKit/Internal/DependentFunctionSheafSoundness.lean) | Reuse typed substitution, conversion transports and the supported function laws. A generic signature/rule interpreter and its initiality theorem are absent. |
| [Elaboration contracts, #147](../../Applications/Elaboration/Elaborator.lean) | `Elaborates` separates resolution, semantic fidelity, obligation equivalence and target typing. `elaborate_complete` covers its typed annotated fragment and overload policy. A new semantic operation does not extend that algorithm or prove inference decidable. |
| [Correspondence atlas](logic-correspondence-atlas.md), [transport assessment](correspondence-contracts-and-integration.md), [Harper assessment](harper-methods-and-adaptation.md) | Reuse the distinction between validity, logical relations, computation and identity. Generic substitution results do not supply representation independence or a model of stronger identity. |
| [Codata assessment](codata-elaboration-termination-contracts.md) and [modal consumer assessment](multimodal-reactive-assessment.md) | Keep recursion and observation contracts separate from admissible structural rules. No new productivity or guarded-recursion claim follows from this survey. |
| [Preservation inventory](preservation-contract-inventory.md) | Retain witnesses, indexed typing, coherence, joint distributions and chosen observations. One truth-valued relation does not replace all these contracts. #235 remains the owner of shared-interface evolution. |

**Recommendation:** implement #259's signature-extension experiment first.
Use its existing naturality and logical-relation theorems to expose one new
primitive obligation and reject an incompatible target. Retain ordinary Lean
clients and their direct interfaces. Defer importing an entire generic
metatheory until a second syntax extension repeats enough formation and
substitution work to justify it. This is an adoption decision for the present
library, not a rejection of the more general mathematics.

For a future dependent extension, use the dependent-product contract above as
the comparison test before building new infrastructure. Uemura's model/internal
language discipline and Jacobs's comprehension structure are useful design
references; the general-rule frameworks are candidates for deriving structural
lemmas when their context discipline fits. MTT needs actual repeated modal
clients; CBPV needs a chosen effectful fragment; QTT needs a resource-sensitive
substitution problem. None should become a universal prerequisite for a
construction that only uses products.

Author-facing declarations could present a new operation with its type and
laws, infer the unchanged structural package, and ask only for its meaning and
preservation square in each target. Dependent notation could hide routine
pullback transports while retaining the comparison theorem in the checked
elaboration. Missing obligations must identify the failed operation or
comparison, such as the two incompatible values forced on `ẑ(0)`. This is a
proposed interface, not a completed author trial or automatic requirement
minimizer. #116 retains surface design and #109 recursion compilation.

This assessment adds no Lean declarations, kernel axioms or tooling. Its new
worked calculations are mathematical specifications for experiments; existing
checked capabilities are identified by linked declarations. No normalization,
canonicity, inference, reflection or witness-erasure guarantee is inferred from
interpretation preservation alone.
