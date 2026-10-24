# Contracts for interpretation routes and internal settings

Semantic design for [#118](https://github.com/VladimirMarko/conaled/issues/118),
2026-10-24. This develops the [initial research](composable-internal-languages-and-relativization.md)
into worked contracts. The examples below are mathematical specifications with
proof arguments, **not new Lean results**. Existing checked results are identified
separately. Continue the embedded language; no importer, replacement calculus,
or mandatory compilation chain is proposed.

## Two operations and a comparison between them

A **transport route** consists of a translation of specified source judgments,
a map of their semantic interpretations, and a comparison connecting the two.
An **internal setting construction** takes a presentation expressed in a base
language and constructs a setting over that base, with a generic model and a
universal property. Its parameters admit substitution within the language.
Supplying an external Lean `Model` argument does not provide that operation.

Keep these interfaces separate. A route records its supported judgments,
assumptions, size bounds, translation, semantic map, substitution law and
comparison. Reflection is additional evidence. An internal construction records
admissible presentation data, formation and substitution rules, its external
interpretation, and a change-of-base comparison. Neither requires a universal
syntax shared by every setting. A route may translate a connective to a justified
encoding instead of demanding that the semantic map preserve it directly.

The worked contracts use a regular fragment for transport and a finite geometric
presentation for construction. Their unequal requirements are intentional: the
current regular fragment lacks the disjunction needed by this presentation.
They are examples in a branching family, not limits on richer dependent or
higher-identity routes.

## Transport of the current graph judgment

Use the actual signature of [`Graph`](../../SquareKit/Internal/Graph.lean):
three sorts `a,b,c`, arrows `f:a→b`, `g:b→c`, and context `Γ=[a,c]`.
The two source judgments are

```text
Γ | ∃y:b. (y=f(x) ∧ z=g(y)) ⊢ z=g(f(x))
Γ | z=g(f(x)) ⊢ ∃y:b. (y=f(x) ∧ z=g(y)).
```

`Graph.forward` and `Graph.backward` already derive them. The reverse derivation
uses the term `f(x)` as witness. It assumes neither inhabited carriers nor a
principle selecting witnesses from arbitrary existential statements.

For the general proposed contract let C,D be regular categories, H:C→D a
regular functor (finite-limit and regular-epimorphism preserving), and M a
model of this signature in C. Interpret contexts as finite products, terms as
arrows, equations as equalizers, conjunctions as intersections and existential
quantifiers as images along context projections. Relation symbols, when used,
are designated subobjects. Define HM by applying H to carriers, arrows and
relation subobjects. The syntax translation τ is the identity on this signature
and its derivations; the model changes.

Write `KΓ : H⟦Γ⟧M ≅ ⟦Γ⟧HM` for the finite-product comparison and `K_s` for the
carrier comparison (identity with this choice of HM). The term contract is

```text
K_s ∘ H⟦t⟧M = ⟦τt⟧HM ∘ KΓ.
```

The formula contract is equality **in the subobject poset**, after transport
along KΓ:

```text
(KΓ)₊ (H⟦p⟧M) = ⟦τp⟧HM.
```

This does not assert equality of chosen mono representatives. An implementation
using representatives supplies an isomorphism over the common context. The
proof argument is induction on formulas: finite limits handle equality and
conjunction; preservation of regular epi/mono factorizations handles images.
Consequently both graph sequents remain valid. Concretely, their two subobjects
are equal to the graph of `g∘f`. This is a proposed general regular-category
contract; the repository's current soundness theorems cover its concrete Set
and sheaf interpretations, not arbitrary regular categories.

For a substitution `σ:Δ→Γ`, the required compatibility is

```text
τ(t[σ]) = (τt)[τσ]             τ(p[σ]) = (τp)[τσ]
KΓ ∘ H⟦σ⟧M = ⟦τσ⟧HM ∘ KΔ
⟦p[σ]⟧M = ⟦σ⟧M* ⟦p⟧M.
```

The last equation and its transported version must agree via the pullback
comparison of H. This makes the square usable under binders. In particular,
Frobenius uses the same image/pullback contract:
`Q ∩ ∃π P = ∃π(π*Q ∩ P)`. Reusing this law is preferable to re-proving witness
bookkeeping at each application. See the checked substitution and Frobenius
comparisons in the capability map below.

### A concrete route and two branches

Take C=Set×Set, D=Set, H=π₀, with all chosen operations componentwise. A model
is a pair `(M₀,M₁)`. Translation retains the same graph proof; H selects its
interpretation in M₀. Contexts, substitution, intersections and images are
componentwise, so the comparison above reduces to equality with these choices.
For example choose both models' carriers to be the natural numbers, with
`f₀(n)=n+1, g₀(n)=2n` and `f₁(n)=0, g₁(n)=n`. The same derivation gives graph
composition for both pairs; π₀ yields `z=2(x+1)`, π₁ yields `z=0`. No proof is
rewritten to obtain either interpretation.

There are also two routes to Set through the swap functor S:C→C:
`π₀` and `π₁∘S`. They agree on objects, arrows, predicates and substitutions.
This is a small, explicit comparison of paths, not just an assertion that
arrows can be chained. With arbitrary product choices the agreement is carried
by coherent natural isomorphisms instead of demanding definitional equality.

## A parameterized internal setting

Fix a Grothendieck topos E and a context object X. A predicate `x:X ⊢ r(x)` is
interpreted by a mono `U↪X`. Work internally in the slice B=E/X. Define a finite
geometric presentation Σ(r) with two propositional generators p,q and sequents

```text
⊤ ⊢ p ∨ q       p ∧ q ⊢ ⊥       p ⊢ r.
```

These sequents specify a choice of a left point, permitted only where r holds,
or a right point, which is always permitted. They do not assert `r∨¬r`.
In Set with X={0,1}, U={0}, the fibre has two points at 0 and one at 1.
For a general topos, U need not be complemented; the definition still makes
sense. The presentation therefore varies with an internal predicate, rather
than naming a fixed external category.

Proposed bounded formation and interpretation rules:

| Rule | Required interpretation |
|---|---|
| From `X context` and `r predicate on X`, form `Σ(r) presentation over X`. | The finite generator/relation data above in B. This rule is a new capability, not current `FormulaCore` syntax. |
| Extend the setting by a generic model of Σ(r). | The relative setting `B[Σ(r)]`, with its projection to B and its generic predicates p,q. |
| Substitute `σ:Y→X` into the presentation. | Replace U by `Y×X U↪Y`; retain the three sequents. |
| Interpret a model after changing to a setting D over B. | For a geometric morphism h:D→B, models are complementary subobjects P,Q of 1D, with P≤h*U. |
| Instantiate the generic model. | A model gives a geometric morphism `D→B[Σ(r)]` over B, unique up to the classifier's equivalence of model categories. |

Here U denotes its subterminal object in B in the last two rows. There is an
explicit classifier: put `A=U ⊔ X`, as an object over X. Then

```text
B[Σ(r)] ≃ B/A ≃ E/A,       with projection E/A → E/X.
```

The proof argument is elementary and fixes the intended denotation. In D, a
model partitions the terminal object as `P ⊔ Q ≅ 1D`; its left part maps to h*U
and its right part to 1D. This is precisely a section of `h*(U⊔1B)`. Conversely,
pulling back the coproduct injections along such a section recovers P,Q and
the factorization of P through h*U. Sections of h*A classify geometric
morphisms D→B/A over B. The generic section is the diagonal of A; its inverse
images of the two summands supply the generic p,q. Disjoint, pullback-stable
coproducts and finite limits justify the partition/section correspondence.
The slice-topos universal property supplies the final classification step.

This example needs finite limits, disjoint universal finite coproducts and
subobjects for the explicit construction, and topos structure for the stated
classifier interpretation. It needs no power-object preservation by h*, choice,
excluded middle, arbitrary disjunction or internal universe of all toposes.
It is a discrete localic example. It does not construct a non-discrete locale
or the classifier of an arbitrary internal site.

### What the primary sources establish

Vickers's [*Generalized point-free spaces, pointwise*, §§8.1–8.3](https://arxiv.org/pdf/2206.01113)
uses internal GRD presentations and sites to describe relative geometric
theories. Site data include objects, arrows and coverage; geometric formulation
of the site condition adds chosen structure. The classifier is recovered by a
bipullback of a model-reduction map, retaining an isomorphism to the fixed base
model. A presentation is not determined uniquely by its locale. Boundedness
concerns relative toposes; it is not a claim that every type theory has such a
classifier. These results motivate the interface above. The finite Σ(r)
construction and its explicit verification are our worked specialization.

The relevant referenced development is Vickers's
[*Arithmetic universes and classifying toposes*, Theorems 30–31](https://sjvickers.github.io/AUClTop.pdf).
For its context extensions and strict base models, Theorem 30 identifies the
pseudopullback of a relative classifier with the classifier of the transported
model, including the generic model. Theorem 31 packages this through local
representability. The ambient elementary toposes have natural numbers objects;
its structured presentations have their own admissibility conditions. This
supports a change-of-base contract, not unrestricted preservation of every
logical operation by every functor. The finite slice example avoids needing
the general classifier construction in the first implementation experiment.

## The mixed square

Let f:F→E be a geometric morphism. Its inverse-image functor f*:E→F preserves
finite limits and colimits. Set X′=f*X, U′=f*U and A′=U′⊔X′. The comparison
`c:f*A≅A′` is the canonical coproduct isomorphism over X′. The required square
of **geometric morphisms** is

```text
F/A′  ───────────────→  E/A
 │                        │
 ▼                        ▼
F/X′  ───────────────→  E/X.
```

The [Stacks Project, §7.30](https://stacks.math.columbia.edu/tag/04GY) and
[§7.31](https://stacks.math.columbia.edu/tag/04IT) supply slice topoi and their
induced geometric morphisms. The square here is a pseudopullback by the
section-classifying property just described: cones over its bottom and right
maps specify exactly a section of the pulled-back A, including the compatible
transformations. It is not a strict equality of categories. Its upper map is
the map on slices induced by f*, after identifying f*A with A′ using c.
Thus pulling back the already-constructed relative setting E/A along the
bottom map yields the setting constructed from Σ(f*r). This is the promised
comparison between changing base before construction and afterwards. The
generic model is preserved: the partition by summands of A pulls back to the
partition by summands of A′. Checking only equivalence of bare categories
would omit this required identification of the interpretation.

There is also a smaller square internal to E for parameter substitution
`σ:Y→X`. Put Uσ=Y×X U and Aσ=Uσ⊔Y. Pullback stability of coproducts gives
`Y×X A≅Aσ`, hence the same square with E/Aσ, E/A, E/Y and E/X. This is
substitution of presentation data, distinguished from changing the ambient
topos. Both operations must be supported.

The computational contract for reusing graph or Frobenius proofs inside the
constructed setting is now specific: interpret their carrier and predicate
data in E/A, use the upper inverse image (which is a regular functor), and
compare with their interpretation in F/A′ using the preceding transport
contract. This joins the two constructions on an actual common fragment.
It neither forces every proof through this fragment nor supplies a reflection
map back to E/A.

### Coherence, size and information retained

For identity base change, c is the unit comparison. For composable changes
`G --g→ F --f→ E`, require the comparison for `(f∘g)*A` to equal the composite
of g* applied to c_f, c_g and the inverse-image compositor. The equality is
between arrows after their domains have been identified. For Σ(r), checking
it on both coproduct injections proves it by coproduct uniqueness. The induced
slice equivalences must respect projection and generic section; their unit
and associativity diagrams then follow from those universal properties.
Repeat this check for substitution and its interaction with base change.
For general presentations, these become pseudonaturality and coherence
obligations, not assumptions discharged by declaring a record.

Fix an ambient universe of sets for the small site presenting E, and a larger
universe for its category of sheaves. X,U,A are objects of E; forming these
finite coproducts and slices does not require a new universe per step. A
category of *all* such E, internal sites with arbitrary size, or an object
collecting all stages is a different size claim. An implementation must record
object and hom universes separately and bound presentation data. Internal
objects of E are not interchangeable with an arbitrary externally large
Lean category. This finite example imposes no equality between a universe and
its own collection of semantic models.

Collapsing construction into the route interface would lose the admissibility
and substitution of Σ(r), the generic model, and its classification property.
Collapsing routes into construction would lose useful noninvertible transports,
encodings and comparisons between already-existing settings. Treating every
comparison as a proposition about points would additionally lose the generic
model's isomorphism and the dependent coherence data.

## Preservation, reflection and intentional failures

The projection π₀ in the transport example preserves the whole regular
fragment but does not reflect arbitrary equations. Take arrows
`u,v:(1,1)→(1,{0,1})` with identical first components and second components
selecting 0 and 1. Then π₀u=π₀v while u≠v. Returning that equality to Set×Set
is unsound. Equations can be reflected by a faithful functor; reflection of
all specified sequents needs its own theorem. A syntactic conservativity claim
about τ is separate again. The pair (π₀,π₁) detects equality jointly; this is
an example of why keeping branches can recover information lost by one route.

For a missing-preservation example, let G be the two-element group and take
the fixed-point functor `(-)^G:G-Set→Set`. It preserves finite limits. The
regular G-set G has no fixed points, while the terminal G-set has one. The
surjection G→1 is a regular epimorphism, but its image under this functor is
`∅→1`. Thus `∃x:G. x=x` is internally true before transport and false after it.
The failed obligation is image preservation, exactly the existential case of
the transport contract. Finite-limit preservation alone would not suffice.
These are mathematical counterexamples, not checked negative Lean fixtures.

A new encoding may justify a different route: retain local witnesses with
descent information instead of pretending that this fixed-point functor
preserves existence. That needs a new interpretation and soundness proof.
For higher identity, use groupoid/higher models and maps retaining the required
identity witnesses and coherence. Equality of subobjects in our regular
example does not license replacing such identities by Lean `Prop` equality,
or quotienting them to sets. Likewise `RelSquare` only preserves its stated
relation; its Prop witness construction is not an arbitrary higher-identity
interface. Each branch states exactly what it forgets and reflects.

## Four composition claims with different obligations

| Claim | Status and acceptance obligation |
|---|---|
| A particular finite route | The componentwise graph and swap routes above have explicit comparisons. Existing `Squares.compose` and `vertical` already prove bounded pasting laws. Each new edge still needs its own contract. |
| All finite paths in a fixed family | Once identities, composition and coherence are supplied, induction on paths gives uniform finite composition. Specify the family and comparison composition; a list of individually working examples is insufficient. Existing ordinary category laws cover their own operations, not the proposed full family of internal constructions. |
| Closure under further internal construction | Finite iteration of this slice example stays among Grothendieck toposes with admissible predicate data. General relative constructions need a closure theorem for the chosen presentations, base changes and size bounds. Vickers supplies a geometric setting, not a theorem for arbitrary dependent theories. |
| An infinite tower object | Requires a specified diagram, direction and intended universal property, plus existence and preservation of its limit or other chosen construction. No such object or theorem is specified or established here. Uniform finite iteration is insufficient. |

Our finite slice claim has a direct reason: a slice of a Grothendieck topos is
again such a topos; for A over X and B over A, `(E/A)/B≃E/B`. This flattens a
particular finite tower while retaining the projections B→A→X. Discarding those
projections would erase its dependence structure. The argument does not prove
closure of arbitrary internal type theories, nor a limit theorem for an
unbounded tower.

The host Lean can describe these presentations, judgments and bounded
interpretations without claiming a truth predicate for all its own theorems.
Nothing above reflects validity in every model back into unrestricted Lean
provability, or gives an interpretation of all Lean universes inside one of
themselves. [#114](https://github.com/VladimirMarko/conaled/issues/114) owns the
precise target-fragment and metatheory obligations. A future return route using
reflection must name that fragment and its assumptions; more finite layers do
not establish unrestricted self-soundness.

## Current capabilities and implementation gaps

Source inspection at commit `6b1aa30`; no new build was run for this design note.

| Current interface | Reuse and gap |
|---|---|
| [`Logic`](../../SquareKit/Internal/Logic.lean): `FormulaCore`, `Derives`, `formula_subst`, `sound`; [`Graph`](../../SquareKit/Internal/Graph.lean), [`Frobenius`](../../SquareKit/Internal/Frobenius.lean) | Reuse syntax, derivations and Set substitution. Missing general regular-functor model transport. Σ(r) additionally needs truth, falsehood and disjunction, absent from this syntax. |
| [`SheafSoundness`](../../SquareKit/Internal/SheafSoundness.lean): `sound`, `frobenius_valid`, `frobenius_semantic_comparison` | Checked interpretation uses local images, sheaf carriers and sheaf relations. Reuse its separation of source soundness from semantic comparison; no general geometric-morphism transport is supplied. |
| [`Internal.Squares`](../../SquareKit/Internal/Squares.lean): `vertical_comparison`, `horizontal_comparison` | Already compares interpreted graph composition to existing square pasting. Extend this seam for the bounded transport example instead of duplicating square algebra. |
| [`Category`](../../SquareKit/Category.lean), [`RelationalCategory`](../../SquareKit/RelationalCategory.lean): `CategoryLaws`, `graphMap_laws`, `witnessMap_laws`, `graphWitness_laws` | Operations and equivalence-relative laws already compose. Reuse these where types fit; hom equivalence alone does not encode a general pseudonatural classifier comparison. |
| [`Squares`](../../Squares.lean): `compose`, `vertical`; [`Relations`](../../SquareKit/Relations.lean): `witnessSquare`; [`RelationComposition`](../../SquareKit/RelationComposition.lean): `transportRelations` | Exact, relational and witness comparisons have different contracts. Their Set-level carriers cannot be silently identified with arbitrary toposes or higher witness types. |
| [`ContextualModel`](../../SquareKit/Internal/PathTransport/ContextualModel.lean), [`GroupoidSoundness`](../../SquareKit/Internal/PathTransport/GroupoidSoundness.lean) | Retain dependent telescopes and groupoid identity for richer branches. They do not currently present internal sites, relative classifiers or the mixed square. |

## Bounded follow-up experiments

These scopes are independent of Agda import and of #107/#108's reserved repair
and fresh-theorem retest. They are proposed issue scopes, not claims delivered
by this documentation change.

1. **Checked branching graph transport.** Formalize the paired Set-model
   specialization, its two projections and swap comparison, including
   substitution under the existing existential binder. Reuse the graph
   derivations and current square/map laws. Check the non-reflecting projection
   example. Acceptance requires one derivation used through both paths with
   an explicit comparison, not two hand-written native graph proofs. This tests
   the route interface without building general regular-category semantics.
2. **Checked parameterized finite setting.** Represent Σ(r)'s finite presentation
   as data, and its models as complementary predicates with the left predicate
   below r. Prove the partition/section correspondence for the Set-family
   specialization `A_x = {proof of r(x)} ⊔ 1`, uniformly in X and r. Prove
   substitution and its identity/composition laws. Compare r=true, r=false and
   r(x)=(x=0) on a two-element X. Do not label this a general topos classifier:
   the categorical classifier property remains a separate obligation. Avoid
   introducing Boolean decidability as a hidden hypothesis of the interface.
3. **Checked mixed substitution square.** Using experiment 2, compare forming
   A before and after pullback along σ, preserve the model/section comparison,
   and prove coherence for two substitutions. Include the componentwise base
   change Set×Set→Set, then interpret the graph fragment over the resulting
   families using experiment 1. Acceptance requires both paths and generic
   model data, not merely a bijection between final carriers. General
   geometric-morphism pseudopullbacks remain out of scope.

Experiments 1 and 2 can proceed independently; experiment 3 depends on both.
Their denotations are given above before implementation. If their interfaces
cannot express either the internal presentation or the generic-model comparison,
record the missing capability and revise the interface. Success justifies a
further issue for a non-discrete example; it does not justify a universal
language or an infinite-tower implementation.
