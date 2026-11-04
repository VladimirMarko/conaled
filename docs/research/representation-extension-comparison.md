# Representation extensions by products and quotients

For [#287](https://github.com/VladimirMarko/conaled/issues/287), adopt a bounded
extension certificate for explicit product and quotient representation sorts.
The constructions below expand every model in the frozen set-model class,
recover old interpretations, and compose. They retain dependent sections only
with coherent descent data. They supply neither natural representative choice
nor recovery of arbitrary proof objects.

The [fixture](representation-extension-comparison/fixture.md) was committed in
`2f164de` before this comparison. It fixes classical many-sorted first-order
logic, nonempty sorts A and B, an equivalence relation R on A, an unrestricted
predicate P on A, all set models, and homomorphisms preserving R and P. Old
observations include every old formula with its assignment. Arbitrary
homomorphisms do not preserve all those observations; the comparisons used for
recovery are isomorphisms. This is a paper construction and derivation, not a
Lean implementation or an author-effectiveness trial.

## Source results and the local baseline

Barrett–Halvorson's [*Morita Equivalence*, §§4.1–4.2, Theorems 4.1–4.3](https://arxiv.org/html/1506.04675)
provide explicit new-sort definitions, expansion up to isomorphism,
conservativity, and formula translation using codes. Their nonempty-sort
convention matters for admissibility. New constants and functions require
existence and uniqueness; subsorts require inhabitation; quotients require an
equivalence relation. Codes for quotient variables are not representative
selectors. Below we instantiate the product and quotient cases and prove the
map laws for our chosen homomorphisms directly. We do not import a categorical
theorem with a different morphism class.

Current local interfaces already distinguish several narrower guarantees:

| Existing source | Reuse and boundary for this fixture |
| --- | --- |
| [STLCSignature](../../SquareKit/STLCSignature.lean), `map`, `restrict`, `compile_map`, `map_comp` | Primitive relabeling commutes with interpretation and composes, but its `Ty` grammar is fixed. It is not an implementation of this many-sorted quotient extension. |
| [ObservationExtension](../../SquareKit/ObservationExtension.lean), `Compatible`, `descend`, `descend_mk`, `no_factor` | Exact-valued functions descend through a setoid precisely with equality preservation. A distinguishing related pair obstructs every factor. These operations directly cover the constant-fiber case below. |
| [Indexed composition](indexed-constructor-observer-laws.md) and [IndexedCompositional](../../SquareKit/IndexedCompositional.lean) | Dependent result comparisons need stated index transport and interaction laws. The implementation does not automatically supply the descent datum used below. |
| [Observation extension evidence](observation-extension-contracts.md) | Selected parser witnesses and private FIFO layout already exhibit failed descent. Retain those stronger observations and existing client proofs. |
| [Extension metatheory](language-extension-metatheory.md) | #262 owns admissible semantic type interpretations; the inspected checkout has no completed #262 artifact supplying an all-model expansion theorem. #278 owns constructor/observer interactions and extension order. |

The direct route therefore consists of explicit set constructions, using the
existing quotient descent API where its contract fits. It does not pretend
that the current compiler already encodes the fixture's entire first-order
syntax. Both routes below use exactly the frozen models and observations.

## Product: defining axioms, expansion and maps

Let T₁ extend T by C, πA:C→A and πB:C→B, with the single axiom

```text
∀ a:A b:B, ∃! z:C, πA(z)=a ∧ πB(z)=b.
```

Existence gives every pair; uniqueness says two C-elements with the same
projections are equal. No old axiom beyond nonempty A and B is needed. For
any M, define E₁M by C=Aᴹ×Bᴹ and the ordinary projections, leaving A, B, R, P
unchanged. The witness for (a,b) is the pair (a,b); equality of both coordinates
proves uniqueness. Nonemptiness of A and B gives nonemptiness of C without a
family of choices. The reduct U₁ simply forgets C and its projections, so
U₁E₁M=M, literally as set structures.

For any other T₁-expansion N of M, define

```text
αC : Cᴺ → Aᴹ×Bᴹ,       z ↦ (πAᴺ(z),πBᴺ(z)).
```

The axiom proves αC bijective: existence proves surjectivity and uniqueness
proves injectivity. Its inverse sends each pair to its unique element, using
unique specification, not arbitrary choice. Together with identities on old
sorts this is an isomorphism N→E₁M commuting with projections. Every such
isomorphism must have this C-component, so the comparison over M is unique.

For an old homomorphism f:M→M′, define E₁f on C by
`(a,b) ↦ (fA(a),fB(b))`. Projection squares commute by evaluation. R and P are
preserved by f on the unchanged A. Identity and composition hold coordinatewise.
A homomorphism between arbitrary expansions has its C-component forced by
these same projection squares. Thus U₁ is full and faithful and E₁ gives an
inverse up to the displayed natural isomorphism. Naturality follows by taking
both coordinates of αC′∘hC and (hA×hB)∘αC.

## Quotient: defining axioms, expansion and maps

Let T₂ extend T₁ by Q and q:A→Q, with

```text
∀ a a':A, q(a)=q(a') ↔ R(a,a').
∀ z:Q, ∃ a:A, q(a)=z.
```

The equivalence laws for R are the admissibility obligation, already axioms of
T and hence of T₁. They are necessary: any relation defined by equality of q
images is reflexive, symmetric and transitive. Surjectivity prohibits unrelated
extra Q-elements. Unlike adding P(c), these axioms constrain only the new
representation once R is known to be an equivalence relation.

For any T₁-model N, define E₂N by Q=Aᴺ/Rᴺ, the set of equivalence classes,
and q(a)=[a]. The equivalence laws give `[a]=[a′]` iff R(a,a′): one direction
uses membership and reflexivity; the other uses symmetry and transitivity to
show equality of classes. Every class has a member by definition, so q is
surjective. Since A is nonempty, Q is nonempty. Keep C and all old symbols
unchanged; U₂E₂N=N.

For an arbitrary T₂-model L, the comparison to E₂U₂L is

```text
βQ : Qᴸ → Aᴸ/Rᴸ,       qᴸ(a) ↦ [a].
```

Surjectivity of qᴸ covers every input. If qᴸ(a)=qᴸ(a′), the kernel axiom gives
R(a,a′), so the prescription is single-valued. Its inverse `[a] ↦ qᴸ(a)` is
well-defined by the other implication of that axiom. Both composites are the
identity. Together with identities on the T₁ sorts, β is an isomorphism over
U₂L. Commutation with q forces every possible comparison to have this value;
no representative selector was used.

For f:N→N′ define E₂f by `[a] ↦ [fA(a)]`. Forward preservation of R proves
well-definedness, including when f identifies previously unrelated elements.
The q-square commutes. Identity and composition follow by evaluating on [a],
which covers Q. Any map between arbitrary quotient expansions is forced on
q(a), so the reduct is again full and faithful. The equation
`βQ′(hQ(q(a)))=[hA(a)]=(E₂U₂h)(βQ(q(a)))` proves naturality. This argument is
specific to the atomic R in the fixture; a general first-order defining
formula need not be preserved by our homomorphisms.

The direct route builds these carriers and proves these equations for M. If
its construction is parameterized by arbitrary M as here, it too proves the
all-model claim. The certificate route records the syntactic defining axioms
and the discharged admissibility obligations once, making this reusable class
of constructions explicit. The distinction is quantification and packaged
evidence, not a mathematical limitation of direct set construction.

## Composition and recovery of old interpretations

Set E=E₂E₁ and U=U₁U₂. The resulting model has C=A×B and Q=A/R. On a morphism
its new components are `(a,b) ↦ (fA(a),fB(b))` and `[a] ↦ [fA(a)]`. Both
identity and composition laws were proved above; UEM=M and UEf=f.

For a general T₂-model L, compose β:L→E₂U₂L with E₂ applied to
α:U₂L→E₁U₁U₂L. The result is

```text
δL : L → E₂E₁U₁U₂L,
δA=id, δB=id, δC(z)=(πA(z),πB(z)), δQ(q(a))=[a].
```

Each component is bijective and respects every symbol, and naturality follows
from the two established squares. This is the required comparison for a
noncanonical expansion. Merely saying that both extensions admit models would
not specify how the selected interpretations match. In a formulation whose
reducts agree only up to isomorphism, the old comparison must instead be the
composite `U₁(ε₂) ; ε₁`, with its naturality; one may not replace it by a
judgmental equality.

For every old formula φ and old assignment ρ, satisfaction in EM equals
satisfaction in M. The proof is structural induction: old atomic predicates
and equality have unchanged interpretations; Boolean connectives use the
inductive hypotheses; quantifiers range over exactly the same old carriers.
For L, the same induction uses δ's old components, which are identities here.
Consequently for old Γ and φ,

```text
T₂ ∪ Γ ⊨ φ    iff    T ∪ Γ ⊨ φ.
```

For reflection, any old countermodel M,ρ expands to EM with the same Γ and
counterexample to φ. For preservation, the reduct of every T₂-model satisfies
T. Universal closure handles contexts. Soundness and completeness of the fixed
classical first-order calculus then give old derivability conservativity.
This argument establishes existence of an old derivation; it does not compute
an inverse on proof trees or recover a selected derivation identically.

For example, the valid extended observation `q(a)=q(a′)` translates to R(a,a′),
while equality of two C-elements translates to equality of their two
coordinates. A Q-variable can be represented by a code `q(a)=z`; surjectivity
permits quantifier translation through such codes. Distinct a can encode the
same z. Neither formula translation nor semantic completeness can turn this
coding relation into a natural selector.

The two sorts in this fixture depend only on old A and B, so reversing their
order gives the same canonical carriers and an identity comparison of the
final signatures. This calculation proves no commutation result for arbitrary
extensions whose operations interact. Those obligations remain with #278.

## Dependent witness descent with explicit fiber comparisons

The following is an additional set-theoretic construction, external to the
first-order signature. Let E(a) be sets, possibly empty, and for every related
pair let θaa′:E(a)→E(a′) be a bijection. Require

```text
θaa = id;    θa′a″ ∘ θaa′ = θaa″ whenever R(a,a′) and R(a′,a″).
```

There is one θ for a related pair, independent of any proof presentation of R.
This is descent along a thin equivalence-relation groupoid; it cannot encode
arbitrary higher identity or nontrivial loop actions. The laws imply θa′a is
the inverse of θaa′.

Form D as the quotient of pairs (a,e), e∈E(a), by
`(a,e) ∼ (a′,e′)` iff R(a,a′) and θaa′(e)=e′. Identity, inverses and composition
of θ prove this is an equivalence relation. The map `[(a,e)] ↦ [a]` is
well-defined. Define F(z) to be its fiber over z∈Q. For each a there is a
canonical map

```text
ιa : E(a) → F([a]),     e ↦ [(a,e)].
```

It is injective: equality of these classes implies θaa(e)=e′, hence e=e′. It
is surjective: a class [(a′,e′)] over [a] has R(a′,a), and is the image of
θa′a(e′). The same equivalence relation proves this preimage independent of its
presentation. Thus ιa is a bijection, and
`ιa′ ∘ θaa′ = ιa` in the common fiber whenever R(a,a′).

A chosen section w(a)∈E(a) descends exactly when
`θaa′(w(a))=w(a′)` for every R(a,a′). Under that condition define
`w̄([a])=[(a,w(a))]`. The condition proves well-definedness and w̄ lands in
F([a]). Its pullback satisfies `ιa(w(a))=w̄([a])`, so the original selected value
is recovered through the specified fiber bijection. Conversely, any descended
section satisfying those equations yields equivariance by injectivity of ιa′.
This is selected-value recovery relative to descent data, not automatic proof
object recovery from a first-order Morita theorem. No choice of representatives
is needed anywhere in this construction.

A concrete dependent case uses A={0,1,2}, R with classes {0,1} and {2}, and
singleton B. Let E(0)={(0,0),(0,1)}, E(1)={(1,0),(1,1)}, and E(2)={(2,0)}.
For related a,a′ put θaa′(a,i)=(a′,i). The laws follow by substitution.
The section w(a)=(a,0) is equivariant. F has a two-element fiber over {0,1}
and a singleton fiber over {2}; w̄ selects the class of index 0 in each. It
retains the chosen index and recovers the tagged original through ιa⁻¹. This
case has varying fiber cardinality, not just a renamed constant observer.

For the negative case, use the frozen A={0,1}, universal R, E(a)={0,1}, and
θaa′=id. The section w(0)=0, w(1)=1 fails equivariance. If w̄ existed with the
pullback equations, equality [0]=[1] would force 0=1. The ordinary operation
`r(a)=a` fails factorization Q→A for the same reason. This is precisely the
constant-fiber obligation expressed by local `Compatible` and `no_factor`.
Both failures concern the specified identity transport. Changing the descent
data or retaining more observations would change the witness contract.

## Symmetry rules out natural selection, not all selection

In the frozen two-point model, q:A→Q has singleton codomain. There are two
set-theoretic sections of q, selecting 0 or 1; no choice axiom is needed for
this finite fact. Let σ swap 0 and 1. It preserves universal R and empty P,
so is an admitted automorphism, and its induced Q-map is the identity.

A selector natural under the chosen automorphisms would satisfy
`σ ∘ s = s ∘ Qσ = s`. Evaluating at the sole class gives σ(s(*))=s(*).
Neither element is fixed by σ, a contradiction. Thus no natural family of
selectors on the admitted models exists, and even an equivariant selector in
this model is impossible. A noncanonical selector still exists. The quotient
expansion's unique comparison over A therefore supplies no natural inverse
Q→A: q loses representatives, whereas β compares two quotient representations.

## A constant with P(c) fails the expansion obligation

Let Tbad=T∪{c:A, P(c)}. For every Tbad-model N and every old formula φ,
`N ⊨ φ` iff `Ubad N ⊨ φ`, by the same structural induction used above.
This satisfaction-under-reduct equation only concerns models N that exist.
It does not imply that a prescribed old M is a reduct of one.

The frozen model has A={0,1}, B={*}, universal R and P=∅. It satisfies T.
Every interpretation of c belongs to A, and none satisfies P(c), so it has no
Tbad-expansion. Indeed Tbad proves the old sentence ∃x:A,P(x), which T does
not entail. In a selected model with P={0}, interpreting c=0 works. With
P=A there are two expansions over the old structure, and no isomorphism
fixing A can change c from 0 to 1. Thus selected success proves neither
all-model existence nor uniqueness over the base.

Here the all-model existence obligation would need T⊨∃x P(x), which fails;
a definitional constant determined by P would require T⊨∃!x P(x), which also
fails. Product admissibility needs nonempty factors, already fixed. Quotient
admissibility needs the R equivalence laws, already supplied. These precise
obligations distinguish the valid representation extensions from a new old-sort
constraint. Such additional assumptions may be useful, but must have a weaker
extension contract.

## What the two author routes require

| Task on the frozen fragment | Direct construction | Representation-extension certificate |
| --- | --- | --- |
| One selected model | Build A×B and A/R, projections, q and their laws for that model. | Instantiate the defining-sort recipes and the selected model. |
| Every admitted model | Parameterize those constructions over arbitrary M and prove they stay in the fixed class. | Supply T's equivalence proofs and nonempty-sort convention; reuse the demonstrated recipes for all M. |
| Maps and old observations | Define product/quotient maps, prove squares and induction on old formulas. Existing primitive restriction equations are useful precedents, not a full proof. | Include model class, morphism class, expansion/reduct laws and natural comparison as certificate fields justified by these recipes. |
| Chosen dependent witnesses | Supply E, coherent θ, equivariant w and the fiber comparisons. | Supply exactly the same data. First-order definitional axioms do not remove this obligation. |
| Old derivations | Preserve existing local proofs under their original premises; a general syntax claim needs its own calculus theorem. | Use all-model expansion plus soundness/completeness for old consequence reflection. No selected proof-tree inverse follows. |

For reuse, keep three layers separate: a defining-sort recipe and its
admissibility proof; a model expansion with reduct/comparison laws for the
stated morphisms; and any observation or dependent-witness compatibility
package. The first two form the recommended bounded extension certificate.
The third is explicit client evidence. The derivations above populate these
layers for this fixture; an abstract record with unfilled expansion fields
would not answer the comparison.

A model builder outside Set must establish the required products and effective
quotients in that target and the comparison laws. For instance, a target
category lacking effective quotients is not covered by our set construction.
Moving to its completion changes the target; it does not expand a model inside
the original category. Authors adding a non-invariant observer must retain a
finer representation or discharge a changed contract, as #267 already shows.

No existing client needs migration for this paper result. A future Lean
implementation should reuse `Setoid`, `Quotient.lift`, and existing compatibility
results, then add the many-sorted theory/reduct layer only for a concrete
consumer. STLCSignature's fixed type grammar would require a distinct type
interpretation adapter under #262; it should not be silently stretched into
this first-order syntax. Dependent sections additionally need coherent family
transport. No universal grammar, global type lattice, or new kernel axiom is
justified here.

## Dependent Morita and coherence: applicability limits

Tsementzis's [*A Syntactic Characterization of Morita Equivalence*, Theorem 4.7
and Corollaries 4.8–4.9, PDF pp.22–23](https://arxiv.org/pdf/1507.02302)
relate syntactic Morita equivalence of coherent theories to classifying-topos
equivalence and model equivalence natural in Grothendieck toposes. Our product
and quotient axioms can be written as coherent sequents, adding inhabitation
sequents to represent our nonempty-sort convention. This offers a broader
semantic route for that coherent presentation. It does not transport the
fixture's arbitrary classical observations into every topos, or prove retention
of proof-relevant dependent sections. We have established the Set case directly.

Isaev's [*Morita Equivalences between Algebraic Dependent Type Theories*,
Definition 2.4 and Proposition 2.5, PDF p.8](https://arxiv.org/pdf/1804.05045v2)
distinguish the unit of a free/forgetful adjunction being a weak equivalence at
the initial model (syntactic), every cofibrant model (Morita), and every model
(strict Morita). The Quillen characterization assumes semi-model theories.
Even the all-model weak-equivalence condition is not our literal same-reduct
set expansion condition. None of these names alone certifies preservation of
chosen proof objects.

Kapulkin–Li's [*Extensional concepts in intensional type theory, revisited*,
Definitions 1.10–1.11, Theorem 7.3 and §8, PDF pp.5–6,34](https://arxiv.org/pdf/2310.05706v2)
prove a Morita comparison from ITT with UIP to extensional type theory. The
setup includes Id, Σ and Π with function extensionality, stable UIP on the
intensional side, equality reflection on the extensional side, and strict
structure/substitution preservation by model maps. The unit conclusion is for
cofibrant models, not every model; its lifting is up to the specified weak
equivalence. Section 8 reports use of choice in §§5–6. Our set quotient proof
needs none of that choice for its canonical maps. This theorem does not
justify imposing UIP or judgmental equality reflection on existing
higher-identity consumers.

Bocquet's [*Towards coherence theorems for equational extensions of type
theories*, Conjecture 6.3, Theorems 6.6 and 8.1, PDF pp.29,35](https://arxiv.org/pdf/2304.10343)
provides a conditional non-UIP alternative for SOGATs with homotopy relations
and selected homotopies to become strict equations. Theorem 6.6 requires the
first comparison to be a weak equivalence and the generated higher congruence
to be relatively merely 0-truncated. Theorem 8.1 establishes the second factor's
trivial-fibration property under its truncation hypothesis. Conjecture 6.3
proposes the first comparison under external univalence and cofibrancy; the
paper's introduction reports no concrete applications. We have not supplied
a dependent client, these structures, or those hypotheses. Consequently this
is an applicability boundary, not a strictification result for the repository.

## Adoption decision and validation boundary

Mathematically, the bounded certificate succeeds for every frozen model and
morphism. Direct construction succeeds on the identical fragment when given
the same universal quantification and laws. The certificate makes admission
and comparison obligations reusable and exposes the P(c) failure before any
selected-model success can be mistaken for conservativity. Its extra theory
layer earns no claim of better author productivity from this paper comparison.

Lean encoding remains prospective: existing quotient and observation interfaces
cover part of it, but no all-model first-order extension implementation or
measured author trial was performed. Validation for these Markdown artifacts
is local-link and whitespace checking plus independent mathematical/spec review;
no build or proof audit is claimed. All new mathematics is presented as paper
derivations with explicit positive and negative instances.

[#235](https://github.com/VladimirMarko/conaled/issues/235) owns any future
certificate implementation and repeatable author comparison.
[#107](https://github.com/VladimirMarko/conaled/issues/107), coordinated with
#235, retains dependent coherence. A new D1 investigation needs a named client
with actual repeated coherence obligations and discharged applicability
conditions, including its permitted identity contract. The present result
supplies no such client and opens no new D1 task. #262 and #278 retain their
existing scopes; [#260](https://github.com/VladimirMarko/conaled/issues/260)
remains conditional. The comparison ends with this bounded certificate and
these explicit exclusions, without selecting a universal foundation.
