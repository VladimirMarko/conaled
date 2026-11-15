# Composed proof reuse through interfaces and theory views

For [#294](https://github.com/VladimirMarko/conaled/issues/294), keep native
interfaces for the worked algebraic client and investigate a small publication
adapter. The two routes below preserve the same selected solution through two
successive interpretations. Explicit theories add named dependency boundaries
and reusable view composition; they do not remove model-law proofs. The example
does not justify replacing the library with a theory-network framework. A
foundation-indexed theory network remains an eligible replacement architecture
when clients need to publish arguments across different object logics.

This is a **paper result**. The [fixture](theory-network-comparison/fixture.md)
was frozen in commit `11f4f652a8c40be578743c482f761377ec0e44c7` before route
adaptation. Local source inspection uses
`2525b12052e4c85c57f9050dbf18f7a36ba2ef19`, Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No Lean declaration, MMT file,
extractor or author-effectiveness measurement is delivered here. Existing
checked claims cited below were inspected in source, not rebuilt for this
report. This comparison continues [#286](proof-requirement-comparison.md)
with publication, composition, model reducts and a principle-sensitive extension.
Primary texts were inspected on 2026-11-04.

## Frozen argument and semantic contract

The base theory T has a carrier M, product `m`, unit e, and chosen elements a,u.
Its laws are

```text
assoc : ∀x y z. m(m(x,y),z) = m(x,m(y,z))
left  : ∀x. m(e,x) = x
right : ∀x. m(x,e) = x
r     : m(a,u) = e
```

The selected solution term is `s(x) := m(u,x)`. Its certificate is the following
single derivation D, universally closed in x:

```text
m(a,m(u,x)) = m(m(a,u),x)    symmetry of assoc(a,u,x)
            = m(e,x)         congruence of r under λv.m(v,x)
            = x              left(x)
```

Write `W(x)=(s(x),D(x))` for data together with its equation. This is a
metalevel dependent pair, or a native subtype value in a prospective Lean
client. The paper object fragment can publish the open term s and its proof
D separately: it does not need an object-language dependent sum. Its observable
first component is exactly `m(u,x)`; a mere existential sentence would lose
this selection. Equality is extensional set equality. No identity between
proof objects, equality reflection or recovery from a lossy representation is
required. The family is indexed by x; there is no variable dependent carrier.

T⁺ adds exactly one principle:

```text
C_a : ∀y z. m(a,y) = m(a,z) → y=z.
```

It does not add global cancellation or an inverse operation. Define the proof k
of `m(a,m(u,a))=m(a,e)` by this chain:

```text
m(a,m(u,a)) = m(m(a,u),a) = m(e,a) = a = m(a,e).
```

The steps are symmetry of associativity, congruence of r, left unit, and
symmetry of right unit. Then `E := C_a (m(u,a)) e k` proves `m(u,a)=e`.
For any `h:m(a,y)=x`, the term
`U(x,y,h) := C_a y (m(u,x)) (trans h (sym D(x)))`
proves `y=m(u,x)`. This derives uniqueness of the selected solution rather than
assuming it in the interface. T includes a right-unit law unused by D but used
by E; no minimality claim is made for T.

## Native interfaces: assignment, reuse and composition

Native notation below describes ordinary records and functions, not new Lean
syntax. Let `Base` package the data/laws of T, and let `CancelAt A` be C_a for
`A:Base`. The functions `selected A x`, `twoSided A c`, and
`uniqueSolution A c x y h` use D, E and U respectively. A Lean implementation
should reuse `Monoid`, `Group` and their existing laws, adding only the chosen
elements, right-inverse evidence and local cancellation evidence. Requiring a
`LeftCancelMonoid` for T⁺ would strengthen the frozen contract.

Let G be the theory/interface of a group H with a distinguished element g.
Its primitive laws are associativity, both unit laws and both inverse laws
`z*inv(z)=1` and `inv(z)*z=1`. Define the native interpretation builder
`fromGroup(H,g):Base` with these assignments:

| T declaration | Assignment in G | Evidence |
|---|---|---|
| M | H | Group carrier |
| m | group product `*` | Binary operation |
| e | 1 | Unit |
| a | g | Distinguished element |
| u | inv(g) | Chosen group inverse, retained as data |
| assoc, left, right | group associativity, left unit, right unit | Same universally quantified equations |
| r | right inverse at g | `g*inv(g)=1` |

`groupCancel(g)` supplies C_a. For `h:g*y=g*z`, multiply both sides on the
left by inv(g), reassociate, replace `inv(g)*g` by 1, then apply left unit:

```text
y = 1*y = (inv(g)*g)*y = inv(g)*(g*y)
  = inv(g)*(g*z) = (inv(g)*g)*z = 1*z = z.
```

This proof uses no cancellation premise. It is the assignment to C_a, reusable
for every T⁺ client interpreted through G.

For the second interpretation, let J be the integer library with a parameter
`n:ℤ`, standard addition, zero and negation. Define `integerGroup(n)`:

| G declaration | Assignment in J | Law evidence |
|---|---|---|
| H, product, unit | ℤ, +, 0 | Typed integer operations |
| inv, g | negation, n | `-z` and the supplied n |
| associativity, left/right unit | additive associativity, `0+z=z`, `z+0=z` | Integer additive-group laws |
| right/left inverse | `z+(-z)=0`, `(-z)+z=0` | Integer additive-inverse laws |

These arithmetic laws are the explicit library boundary. They may be discharged
once by the standard integer additive-group instance; neither integer induction
nor a proof of that instance is transported as part of D. J means the intended
standard-integer interpretation, not an assertion that a first-order axiom set
categorically characterizes ℤ. This report supplies no new proof of integer
arithmetic.

The composite builder is `fromGroup(integerGroup(n))`. Its Base fields are
`(ℤ,+,0,n,-n,add_assoc,zero_add,add_zero,add_neg_cancel n)` in mathematical
notation. Its C_a proof is precisely the groupCancel body with these replacements:

```text
y = 0+y = ((-n)+n)+y = (-n)+(n+y)
  = (-n)+(n+z) = ((-n)+n)+z = 0+z = z.
```

Native reuse is application of the one polymorphic D/E/U to these packages.
For D the first application yields

```text
g*(inv(g)*x) = (g*inv(g))*x = 1*x = x.
```

Applying the integer builder yields

```text
n+((-n)+x) = (n+(-n))+x = 0+x = x,
W_J(x) = ((-n)+x, this chain).
```

For E the translated chain is
`n+((-n)+n)=(n+(-n))+n=0+n=n=n+0`; applying the displayed
integer cancellation proof gives `(-n)+n=0`. U uses that same cancellation
proof on `n+y=x=n+((-n)+x)` and returns `y=(-n)+x`.
At n=2,x=5 the selected component is 3 and its certificate is `2+3=5`.
A new integer proof of E could use the inverse law directly, but the matched
route above translates the frozen argument instead.

Identity on a native interface is the builder returning the supplied package.
Composition is ordinary composition of builders. Thus
`id ∘ F=F`, `F ∘ id=F`, and `(F ∘ G) ∘ H=F ∘ (G ∘ H)` hold pointwise,
and evaluating the composite builder gives exactly the fields above. These
are interpretations of interfaces, contravariant on models. They are **not**
a homomorphism from every concrete group H to ℤ. No such homomorphism is
needed for this reuse. Two independently constructed packages need not have
identical proof fields; the contract compares their operation data and
selected elements, with certificates of the same equations.

## Presented theories and total views

Use a common paper metalanguage F: typed terms, binding and capture-avoiding
substitution, intuitionistic equality reasoning, implication and universal
quantification. Equality has reflexivity, symmetry, transitivity and
congruence. The intended models below use ordinary extensional equality.
F supplies syntax/rules, not monoid laws. An integer library over F supplies
J's arithmetic; a natural-function library supplies the countermodel below.
Their construction is model work outside the reusable argument.

Publish T's ordered declarations M,m,e,a,u,assoc,left,right,r, followed by the
**definitions** s and D. Publish T⁺ by including T and adding C_a, then definitions
k,E,U. Publish G with the primitive declarations and laws listed above, and J
with its integer library and n. Let `i:T→T⁺` be the inclusion, assigning every
old primitive to its namesake and each definition to its unchanged body.
The views are `φ:T→G`, `φ⁺:T⁺→G` and `ψ:G→J`.

The two native tables are also the complete primitive assignment tables for
φ and ψ. φ⁺ agrees with φ on T and assigns C_a to groupCancel's displayed
proof. Defined declarations are translated by substitution into their bodies:

| Defined declaration | Image under φ or φ⁺ | Image under ψ∘φ or ψ∘φ⁺ |
|---|---|---|
| s(x) | `inv(g)*x` | `(-n)+x` |
| D(x) | Three-step group chain above | Three-step integer chain above |
| k | `g*(inv(g)*g)=(g*inv(g))*g=1*g=g=g*1` | `n+((-n)+n)=(n+(-n))+n=0+n=n=n+0` |
| E | `groupCancel(g) (inv(g)*g) 1 kφ` | Integer cancellation on k's image |
| U(x,y,h) | `groupCancel(g) y (inv(g)*x) (h · Dφ(x)⁻¹)` | Integer cancellation on `h · DJ(x)⁻¹` |

Here `·` composes equalities and superscript `⁻¹` reverses an equality;
these are proof notation, not extra algebra operations. Both routes therefore
translate the same derivation and selected term, not merely the same theorem
statement. There is no view assignment saying “assume the final theorem.”

For a declaration `c:τ=δ`, an assignment must have translated type `τ[v]`
and agree with `δ[v]` when a definition is present. For example C_a's target
type is `∀y z:H. g*y=g*z→y=z`, checked by the explicit group calculation.
D's target type is `∀x:H. g*(inv(g)*x)=x`, checked by its three translated
steps. The selected term has target type H for every x:H. All primitive
assignments are present. Each view uses the identity on F, including all
its typing, equality and binding rules; imported integer operations stay in J.
No change of logic is concealed in that identity clause.

In this fragment composition is simultaneous substitution:
`(ψ∘φ)(c)=φ(c)[ψ]`. For u this is `inv(g)[ψ]=-n`; for r it is the integer
right-inverse proof at n. On a compound term apply substitutions recursively,
renaming bound variables to avoid capture. Induction on variables, constants,
application and binders gives `t[id]=t` and
`t[ψ∘φ]=(t[φ])[ψ]`; the same recursion on rule constructors proves it for D.
Associativity follows by a third substitution with fresh binders. These
paper laws hold up to alpha-renaming and the specified definitional reductions,
not arbitrary equality of independently chosen proof terms.

The extension square commutes: `φ⁺∘i=φ` on every T declaration. Hence its
composite with ψ also commutes. Restricting the T⁺ argument package to s,D
recovers exactly the published T package. A client requiring only W can import
T; a client needing E/U imports T⁺. This is the publication boundary absent
from a list of operation-name replacements.

## Model reducts and the institution boundary

For a concrete pointed group B=(H,*,1,inv,g), the reduct `Rφ(B)` is
`(H,*,1,g,inv(g))` with the Base laws. `Rφ⁺(B)` adds the proved local
cancellation law. For the standard integer model J_n, `Rψ(J_n)` is the
pointed additive group `(ℤ,+,0,-,n)`. Consequently

```text
R(ψ∘φ)(J_n) = Rφ(Rψ(J_n)) = (ℤ,+,0,n,-n),
Ri(Rφ⁺(B)) = Rφ(B),       Rid(B)=B.
```

Reduct composition is in this reverse order for **both** routes. At the native
level these are the builder equations already calculated. At the theory level
they follow by interpreting substituted declarations. A group homomorphism
h preserving the distinguished g preserves inv(g), and hence a,u and m after
reduct: applying h to both inverse equations shows h(inv(g)) is the inverse
of h(g), and inverse uniqueness identifies it. Thus Rφ acts on arrows by the
same function h; identity and composite homomorphisms remain identities and
composites. For the intended J_n models we can use the discrete category of
integer parameters; Rψ sends its identities to group identities. This suffices
for the displayed family and makes no claim about every model of arithmetic.

The primary institution source is Goguen–Burstall,
[*Institutions: Abstract Model Theory for Specification and Programming*][ins],
JACM 39(1), pp. 95–146. The ticket's [author-hosted PDF][ins-original] has
corrupted text extraction; the readable published copy resolves access.
Definition 1, pp. 101–102, supplies signatures, covariant sentences,
contravariant models and the satisfaction equation
`B ⊨ Sen(v)(P) iff Mod(v)(B) ⊨ P`. Section 2.2, pp. 104–105, restricts reducts
to theory models when translated axioms hold. Definition 32, p. 125, describes
institution morphisms with natural sentence/model transformations and a
satisfaction condition. Definition 34 and Proposition 35, p. 126, additionally
require the model transformation to be surjective on objects for their
semantic-consequence equivalence. We do not apply that theorem to proof terms.

There is an extra issue in this fixture: u maps to the **term** inv(g), not a
primitive constant. Ordinary first-order signature renaming alone does not
express this assignment. One can either add a defined constant `uG=inv(g)` to
G and use renaming followed by definitional expansion, or construct an
institution allowing term-valued interpretations. This report uses the first
route for a satisfaction-law reading; adding uG has a unique interpretation
in every G-model and changes no chosen data. Extend ψ by the forced assignment
`uG↦-n`, which satisfies the translated defining equation.

The needed satisfaction instance can also be checked directly. Induction on
terms proves
`eval_B(t[v],ρ)=eval_Rv(B)(t,ρ)` for the same carrier and valuation. Constants
use the tables; product uses the corresponding target operation; variables use
ρ. Equality follows by comparing the two values. Universal closure and
implication follow by quantifying over the same carrier and comparing their
truth conditions. This establishes the law for the equations and Horn
sentences used here, including C_a; it supplies no theorem about unrelated
logical constructors. Restriction along i preserves T's laws because T⁺
contains them. Composition of evaluations follows from term substitution.

Truth of `∀x.∃y. a*y=x` does not record which y was selected. In the function
countermodel below, even x equal to the constant-zero function admits two
different solutions. The pair W is preserved because the term calculation
retains s, and its equation is preserved because D is translated. The
institution satisfaction relation alone contains neither this selection nor a
map of proof objects. No reflection or recovery theorem is inferred from it.

## Failed extension with a successful base view

Take N with carrier `ℕ→ℕ`, multiplication `f*g=f∘g`, e=id, a=pred
(truncated predecessor), and u=succ. Associativity and both unit laws hold
pointwise. For every k, `pred(succ(k))=k`; extensionality gives `a*u=e`.
These discharge **all** T declarations. Its selected solution for x:ℕ→ℕ is
`W_N(x)=(succ∘x,D_N(x))`, whose equation at k is
`pred(succ(x(k)))=x(k)`. The selected function, not just its existence, remains
available.

Let y be constant zero and z constant one. Then `pred∘y=pred∘z` is the
constant-zero function, while `y(0)=0≠1=z(0)`. Hence C_a is false.
Also `(u*a)(0)=succ(pred(0))=1`, whereas `e(0)=0`, so E's conclusion fails.
This refutes any total extension view with these assignments, rather than
merely a particular tactic's ability to find one. It also shows nonuniqueness
of solutions to `a*w=y`: both y and z solve it; W selects z.

The native constructor accepts Base(N) and has no possible `CancelAt` argument.
The presented route has a total `ν:T→N` but cannot complete `ν⁺:T⁺→N`.
Leaving C_a unassigned, filtering it, or retaining E with an unproved leaf
would produce an uncertified partial view. Publishing s,D in T remains valid.
The extension inclusion is not conservative for the old vocabulary: E is an
old-language equation false in this T-model and derivable in T⁺. No automatic
model expansion or conservativity follows from the existence of i.

## MMT source hypotheses and encoding audit

Rabe–Kohlhase, [*A Scalable Module System*][mmt], preprint dated 17 December
2012, §7.2, printed pp. 60–64, is the source for the following conditions.
Definition 30 requires normalization-respecting equality, equivalence,
congruence, context conversion, and typing/equality preservation by flat
assignments satisfying declaration types and definitions, including
meta-theories. Definition 32 makes totality recursive on the metamorphism;
undefined constants cannot be filtered, while defined constants may expand.
Theorem 34 assumes a fixed regular foundation. Parts 3–5 give associative
composition, units, closure of totality and iterated application; part 7 gives
typing/equality preservation for well-formed total morphisms. Part 2's
composition congruence requires total second morphisms. Theorem 48, §8.2,
pp. 72–73, establishes regularity for the paper's LF foundation. These results
do not establish adequacy of our object encoding or arbitrary logic migration.

The tables and substitution induction above establish the bounded paper
comparison directly. They are not a checked MMT graph. In particular F is a
specified paper calculus, not an implementation for which this report has proved
all Definition 30 clauses. Applying Theorem 34 to an executable version needs
that missing foundation check or a suitable existing regular foundation.

A plausible LF encoding uses `sort:type`, `tm:sort→type`, `prop:type`,
`pf:prop→type`, `eq_A:tm A→tm A→prop`, and constants for the universal,
implication and equality rules. M is a constant of type sort; product is
`tm M→tm M→tm M`; a law is a constant of its pf type. Keep object equality
as a proposition with proofs, distinct from LF definitional equality.
Publish s as an LF function `tm M→tm M`, and D as its equation proof family.
W is the external pair of these, so no unprovided LF Σ constructor or
elimination from mere existential truth is needed.

Harper–Honsell–Plotkin, [*A Framework for Defining Logics*][lf], inspected
37-page author manuscript, §1 pp. 1–2 and §2 p. 3, defines adequacy through a
compositional bijection with canonical LF forms: substitution must commute
with encoding. Its framework equality is distinct from equality in an encoded
logic. The source's adequacy methodology applies to a supplied representation;
it does not certify the candidate declarations just sketched.

The audit for this candidate is therefore:

| Obligation | Evidence here | Remaining work before an LF/MMT claim |
|---|---|---|
| Sorts, terms, law types and declaration order | Explicit tables; M precedes operations and laws | Encode and check all declarations and imports |
| Rules and discharge conditions | D/E/U list equality rules; U discharges h; universal variables are fresh | Give exact LF rule constants and context grammar |
| Substitution and composition | Structural paper induction, including binders | Prove encoding commutes with substitution |
| No extra encoded terms/proofs | No such assertion used | Prove canonical-form decoding and inverse encoding, at the chosen proof equivalence |
| Selected data | s is an open term; pair projection observes s | Verify LF representation/readback preserves s and parameter x |
| Arithmetic and function models | Standard extensional interpretations; explicit law boundary | Verify imported logic/model interfaces and function extensionality obligations |
| Foundation regularity | Source theorem for its LF foundation only | Match that foundation or verify the chosen implementation's conditions |

Using native Lean equality in an LF object-logic encoding without this audit
would not establish adequacy. Nor does a signature that merely postulates the
final transport theorem discharge any of these obligations. The unimplemented
encoding remains a research cost, not a mathematical rejection of the network.

## Changed logic: a supported fragment and a rejected total translation

Consider publishing T/T⁺ in classical first-order reasoning with equality, then
reusing D/E/U in intuitionistic reasoning with equality. Translate carriers,
operations, terms, equality, `∀` and `→` identically. For the selected fragment,
the required rule translations are explicit:

| Source rule actually used | Intuitionistic target meaning/evidence |
|---|---|
| Reflexivity, symmetry, transitivity, operation congruence | Corresponding equality rules with the same terms |
| Universal elimination | Substitute a well-typed term for the quantified variable |
| Universal introduction | Abstract a fresh variable absent from undischarged assumptions |
| Implication elimination/introduction | Apply a proof to its premise; discharge h in U |
| Selected term s and its certificate | Translate s homomorphically and replay D; no existential elimination |

Replace every rule node in D/E/U by that row's target rule. All theory law
leaves map to the same target assumptions or the group/integer proofs already
displayed. Induction on this finite derivation gives the target judgment.
In particular the integer result remains the data `(-n)+x` with the same
equation, while the function model still rejects C_a. This is a paper proof
translation for the used fragment, not a claim that classical and intuitionistic
models have the same truth relation for every formula.

A total identity translation of the full classical meta-theory fails. Add a
fresh proposition P and the classical rule asserting `P∨¬P`. In the two-world
Kripke frame `w0≤w1`, force P only at w1. At w0 neither P nor ¬P is forced,
so their disjunction is not forced. Interpret the selected integer algebra
constantly at both worlds; its equations and cancellation remain valid. The
algebra assignments therefore cannot supply that missing logical rule.
One must publish the argument in its intuitionistic fragment, supply a suitable
restricted principle, or change the translation and prove its rule/meaning
contract. Negative translations and their witness recovery are not established
here. A fixed-foundation MMT theorem cannot replace that evidence.

Changing equality is also substantive. If function equality in N were replaced
by agreement only at zero, id and constant zero would be equal, but composing
each on the right with succ would give values 1 and 0 at zero. Product
congruence would fail. Thus the identical rule translation is rejected for that
proposed observation equality; the label “equality” does not supply its laws.

## Reuse, costs and competing organization

The following is an obligation inventory, not elapsed time or an author score.

| Work | Native interfaces | Presented theories with total views |
|---|---|---|
| Publish one reusable argument | Choose Base/CancelAt boundaries; define D/E/U once | Choose T/T⁺ boundaries; store s and derivations once |
| Add the group interpretation | Supply data/laws and groupCancel once | Same assignments and proofs, plus named total views |
| Add integer interpretation | Reuse integer group instance; instantiate n | Assign all group declarations to integer library evidence |
| Two-step reuse | Compose interpretation builders and apply generic theorem | Compose views and apply substituted derivation |
| Selected witness | Keep subtype/data value and its projection | Publish open term s alongside D; preserve readback |
| Missing principle | Cannot construct CancelAt | Cannot complete C_a assignment; base view remains usable |
| Logic migration | Restricted proof replay or a separate interpretation | Total meta-view plus adequate rule/term encoding |
| Infrastructure | Existing Lean structures and specialization | Naming, theory imports, assignments, equality checking, trusted replay and encoding adequacy |

The base model laws, groupCancel and the integer instance are model-builder
work discharged once per interpretation. Authors of later T⁺ arguments may
reuse the same package/view. Each newly required principle still needs a
statement, a proof that the model supplies it, and a decision about whether it
belongs in the common theory or a separate extension. Neither route discovers
requirements or proves unused imported axioms automatically. A large imported
theory can impose avoidable obligations; T and T⁺ demonstrate one useful split.

The paper comparison shows no extra mathematical generality for the network
on this fixed-logic client: native polymorphism already supplies its proofs and
composition. A publication adapter could make the declaration boundary and
assignment coverage inspectable while emitting ordinary checked Lean calls.
That is a prospective tooling benefit; this work measures no reduction in
repeated author effort. Naming, conversion and diagnostic costs remain unknown
until implementation and the separate frozen author trial.

A stronger alternative would organize the library as a **network indexed by
object logic**, with theories, derived declarations and interpretations as the
primary public artifacts. Lean modules would become one realization and replay
target. That changes today's assumption that native Lean interfaces organize
all reusable proofs. It could publish the same object argument to multiple
foundations, provided each connection supplies term/rule meanings, adequacy
and selected-data comparisons. No universal AST, global subtyping or new
kernel axiom is required by this proposal. A family of adequate encodings and
explicit bridges is eligible even if it cannot translate directly into today's
generated syntax. Its unresolved central cost is certifying those bridges and
recovering existing capabilities, not the extra spelling of a view declaration.

Two current results provide different comparison evidence at the inspected
revision:

- [#277's equation bridge](equation-composition-bridge.md),
  [`compile_transpose` and `observations`](../../SquareKit/EquationComposition.lean),
  turns a binding-free equation table into a finite indexed rule. Transposition
  preserves the full rule, while `observations` still needs compatibility with
  the independent algebra and a leaf morphism. This is checked presentation
  change plus semantic lifting, not theorem transport for arbitrary theories.
  The vector counterexample to an output depending only on a child's head
  prevents treating its restricted rule format as a universal publication IR.
- [#284's guarded construction](modular-guarded-streams.md),
  [`solve_fixed`, `unique` and `map_solution`](../../SquareKit/GuardedStreams.lean),
  constructs a solution by coordinate recursion, proves uniqueness from
  guardedness and transports through a local square. It does not assume the
  complete solution theorem as a model field. The modulo-two application loses
  information and does not reflect equality. A theory network must preserve
  these hypotheses and constructed selected solutions; merely declaring a
  constant called `solve` would not recover them.

Neither is encoded in this fixture. Recovery of their indexed observations,
selected parser evidence and guarded solution contracts is a future adoption
obligation. Their present encoding does not exclude a different organization.
The broader [foundation comparison](external-language-foundations.md) remains
relevant; this report does not reassess categorical doctrines, realizability,
higher identity, dependent substitution or arbitrary recursive theories.

## Decision and scoped continuation

**Adopt** the explicit T/T⁺ requirement split and selected-term-plus-certificate
contract as documentation for this comparison. **Keep** the native route for
this client. **Investigate** a small publication adapter under
[#290](https://github.com/VladimirMarko/conaled/issues/290), coordinated with
[#235](https://github.com/VladimirMarko/conaled/issues/235). **Defer** adoption
of a repository-wide theory network pending a client that needs cross-logic
publication and evidence that its adequacy/recovery costs are justified.
**Reject** partial-axiom transport and equality changes lacking congruence for
the frozen contract. None of these decisions rejects the replacement
architecture on the basis of current Lean encoding convenience.

A justified next formalization is bounded to the frozen client:

1. Reuse Mathlib monoids/groups, represent chosen a,u and their right-inverse
   equation, and use `Function.Injective (fun y => a*y)` for C_a. Define the
   selected solution as data, prove D/E/U, and provide group/integer builders.
2. Define a small declaration/assignment representation for this finite
   algebraic fragment, or an adapter generating native checked declarations.
   Check assignment coverage, translated law types and definition bodies.
   Prove identity/composition and agreement with native specialization for s,D
   through the two views. Do not declare arbitrary theorem transport as a field.
3. Check n=2,x=5, the function countermodel and base-only reuse. A candidate
   must fail if it drops C_a or changes the selected component, and must retain
   the original T assumptions without importing global cancellation.
4. If an LF/MMT realization is chosen, close the encoding-audit table above
   before claiming its general transport theorem. If only native generated
   calls are chosen, state that narrower scope and defer cross-logic claims.
   Follow the repository's example/statement-review and full build/audit rules
   for all new Lean claims, then independent Standards and Spec review.

#290 owns that bounded proposal and selection of a real publication consumer;
#235 owns any shared-interface expansion and recovery assessment with #36.
The separate [#293 trial](https://github.com/VladimirMarko/conaled/issues/293)
owns author observations; it is not evidence supplied by this paper. No new
implementation or theory-network rollout is authorized by these recommendations.

For this documentation-only delivery, validation checks relative links, the
frozen fixture's unchanged bytes and `git diff --check`; independent review
checks the paper derivations and source hypotheses. No build or proof-audit
result is claimed for the new mathematics.

The candidate incorporates integration tip
`90980ba02aee0d878fc0946b787c25def70937f5`, which is its review base.
The documentation check ran through `direnv exec . python3`: all seven
relative links resolve, the fixture matches its freeze commit byte for byte,
and authored prose contains no em dashes. The staged diff passes whitespace
checking. Independent review is coordinated by the parent implementation loop.

[mmt]: https://www.kwarc.info/people/frabe/Research/mmt.pdf
[ins]: https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf
[ins-original]: https://cseweb.ucsd.edu/~goguen/pps/ins.pdf
[lf]: https://era.ed.ac.uk/bitstreams/f02739c7-c52e-4764-9229-a1fcb46daad6/download
