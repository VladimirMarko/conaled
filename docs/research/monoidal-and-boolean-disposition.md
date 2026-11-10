# Tensor factoring and the Boolean proposals

Issue [#454](https://github.com/VladimirMarko/conaled/issues/454) resolves the
factoring proposal in Felix `Raw.agda:49–137` and the commented Boolean families
at revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`.

## Tensor boundary

[TensorOperations](../../SquareKit/TensorOperations.lean) separates tensor
objects/arrows, structural comparisons, and braiding data. The records are raw:
their names do not promise a monoidal category. Inverse equations, naturality,
pentagon, triangle and hexagon equations are not silently added.
[TensorLaws](../../SquareKit/TensorLaws.lean) separately gives semantic
congruence, identity and composition laws for the tensor bifunctor.

| Felix operation | Sufficient raw data |
| --- | --- |
| tensor, first, second, twice | tensor on objects and arrows, category operations |
| left/right unit elimination and insertion | selected unit comparisons |
| left/right associators | selected associator comparison |
| const left/right and pairing two constants | tensor and inverse unit comparison |
| inAssoc left/right, including primed versions | associators, composition, and first/second where used |
| swap and inSwap | braiding, composition |
| transpose and inTranspose | associators, tensor, braiding, composition |
| discard, projections, diagonal, arbitrary pairing | extra cartesian operations |
| initial arrow, injections, arbitrary copairing, jam | extra cocartesian operations |

For middle-four transpose, a monoidal expression follows the object sequence

```text
(ab)(cd) → a(b(cd)) → a((bc)d) → a((cb)d) → a(c(bd)) → (ac)(bd).
```

The middle step tensors the braiding of `b,c` with identities; the others use
associators and their inverses. Equality with Felix's projection-based formula
requires cartesian laws. Raw category/product operations alone do not identify
two differently built arrow expressions. #450 retains the projection formula
and its semantic equations. The disposition is to retain that API, expose the
weaker operations it actually shares, and use lawful monoidal coherence where
needed. This task does not replace the existing transpose formula with a raw
equality claim or introduce an unfinished raw coherence hierarchy.

`ofProducts` recovers the cartesian tensor, unitors, associators and swap from
#450's operations. The first/second/twice and constant-operation recovery
lemmas are generic, not restricted to functions. `TensorLaws.ofProducts`
recovers bifunctor laws under the existing semantic cartesian hypotheses.

## Mathlib comparison and a noncartesian consumer

The inspected pinned Mathlib modules are
`CategoryTheory/Monoidal/Category.lean`, `Monoidal/Braided/Basic.lean`, and
`Monoidal/Discrete.lean`. Mathlib's `MonoidalCategory` already supplies lawful
category operations, isomorphism-valued structural maps, tensor naturality,
pentagon and triangle. `BraidedCategory` adds natural braidings and hexagons;
symmetry is additional structure. This is stronger than raw selected arrows
with a separately chosen semantic relation.

The `ofMonoidal`/`ofBraided` adapters forget exactly to the raw operations.
`TensorLaws.ofMonoidal` checks recovery of the semantic bifunctor laws with
equality. Ordinary lawful clients should continue to use Mathlib's coherence
API. Raw clients can use the smaller records without proving laws irrelevant
to their operation definitions. No existing category/product client imports a
Boolean package, and no existing library definition is replaced.

[The resource example](../../Examples/TensorOperations.lean) uses Mathlib's
lawful additive monoidal structure on `Discrete Nat`. Tensor adds resource
counts. The checked consumer combines two and three resources and applies
`first`; there is no arrow from one resource to the tensor unit, or from one
to two resources. Thus this tensor is not cartesian: a monoidal unit does not
supply discarding, and tensor does not supply copying. Function examples recover
ordinary product tensor, constant insertion and swap through the new adapters.

## Boolean source inventory

These are commented proposals, not active records or proofs to port:

| Source | Proposal |
| --- | --- |
| `Prop.agda:31–41` | `Logicᴾ` closure witnesses for false, true, not, conjunction, disjunction, xor and conditional |
| `Construct/Product.agda:52–68` | Boolean object pair and componentwise seven operations |
| `Construct/Product.agda:122–130` | componentwise `f∘cond` law |
| `Construct/Product.agda:198–248` | projection Boolean comparisons, strong comparison equations, and preservation of the seven operations |
| `Construct/Comma/Raw.agda:179–352` | Boolean connector, seven square constructions and conditional naturality used to close the conditional square |
| `Instances/Identity.agda:28–30,46–54` | identity Boolean comparison, inverse equations and operation preservation |

The operation types, using a selected terminal object `I`, product `×` and
selected Boolean object `B`, are:

```text
false,true : I → B
not        : B → B
and,or,xor : B×B → B
cond_A     : B×(A×A) → A       for every object A.
```

None of these types imposes a Boolean truth table. In particular the source's
commented product law is conditional naturality, not a full Boolean algebra
presentation. The exact naturality obligation is

```text
f ∘ cond_A ≈ cond_D ∘ (id_B ⊗ (f ⊗ f)),    for f : A → D.
```

The checked `badConditional` example shows this cannot be inferred from an
arbitrary operation of conditional's type. `conditional_natural` checks the
intended ordinary Boolean conditional. Additional truth-table or Boolean
algebra equations must be named explicitly if a later client requests them;
there is no active upstream theorem asserting them here.

## Exact preservation and closure obligations

Let a raw interpretation `F : C → D` have semantic category preservation.
Choose comparisons from interpreted structure to target structure:

```text
e : F I_C ↔ I_D
m_A,A' : F(A×A') ↔ F A × F A'
b : F B_C ↔ B_D.
```

Use `hom` for the displayed direction and `inv` for its reverse. With target
composition and tensor, operation preservation is precisely:

```text
F(false_C) ≈ b.inv ∘ false_D ∘ e.hom
F(true_C)  ≈ b.inv ∘ true_D  ∘ e.hom
F(not_C)   ≈ b.inv ∘ not_D ∘ b.hom
F(op_C)    ≈ b.inv ∘ op_D ∘ (b.hom ⊗ b.hom) ∘ m_B,B.hom
             for op = and, or, xor
F(cond_A)  ≈ cond_FA ∘ (b.hom ⊗ m_A,A.hom) ∘ m_B,A×A.hom.
```

Equivalent primed equations moving comparisons to the other side require the
corresponding inverse equations and category congruence/laws. They cannot be
obtained merely by naming an arrow `inv`.

For morphism restriction `M f : Type w`, admissibility requires a retained
witness of `M false`, `M true`, `M not`, each of the three binary operations,
and `M cond_A` for every admitted object `A`. Category/cartesian closure is
needed separately where the restricted category uses those operations. The
forgetful map ignores these witnesses for semantic equivalence, as in #452;
closure cannot be inferred from the existence of the underlying operations.
A restriction to identity arrows, for example, does not admit an ordinary
negation map unless that map is itself an identity.

For product categories, select `(B₁,B₂)` and pair all seven operations. Their
semantic equations and conditional naturality hold componentwise when each
factor has them. Projection comparisons are identities; their preservation
follows from the category unit and product identity equations. No condition on
one factor can supply a missing operation or law in the other.

For comma categories `F : C → K ← D : G`, choose the Boolean object with
connector `G.b.inv ∘ F.b.hom`. Its product connector is the existing comma
product connector formed using the product comparisons. The constant/unary/
binary Boolean squares close from the two operation-preservation equations,
target category/cartesian congruence and laws, and strong unit/product/Boolean
comparisons. The conditional square additionally needs the target's
`f∘cond` equation for the object's connector `F A → G A'`. This is the exact
extra obligation visible in the commented proof. Without it, arbitrary
selected conditional operations do not define a comma arrow. Source Boolean
truth tables are not a substitute for that target naturality equation.

For identity interpretations, select identity comparisons. The equations
above reduce by category unit laws and tensor identity laws; conditional's
nested product comparison also reduces using those laws. No Boolean truth
table is needed for these identity preservation equations.

This is a mathematical disposition of all four commented families: an optional
algebraic operation signature with explicit closure/preservation and conditional
naturality. It is not evidence of existing checked generic Boolean instances.
No missing truth-table theorem is claimed or deferred under an invented source
contract. The active source has no such Boolean package. Implementing an
optional package for a future concrete client can use these exact obligations
without changing ordinary category/product imports.

## Statement review and validation

The tensor records expose only the operations used; semantic bifunctor laws
remain separate. The noncartesian example prevents accidental use of a terminal
unit or diagonal. Product recovery consumes existing raw definitions and law
proofs. The conditional control distinguishes a type-correct operation from the
naturality needed by comma construction. The Boolean disposition records
mathematical arguments and source coverage, not checked generic Boolean proofs.

Focused tensor modules and consumers pass. Full integrated build, exhaustive
proof audit and independent Standards/Spec review remain pending. This result
does not by itself complete #8.
