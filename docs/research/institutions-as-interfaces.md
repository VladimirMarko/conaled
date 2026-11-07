# Institutions, proof meanings and computation interfaces

For [#340](https://github.com/VladimirMarko/conaled/issues/340), investigate an
institution-style organization of specifications and interpretations throughout
the library, with proof and witness data retained. The evidence supports a
common organization with distinct capabilities for satisfaction, proof
translation, dependent interpretation and computation. It does not yet justify
requiring one combined record at every interface.

This is a paper assessment, including new worked derivations, not a Lean
implementation. Source inspection uses `b8731310f05efdac29f994706fbc1f32eb77de20`;
primary sources were read on 2026-11-07. Existing checked clients below were
inspected, not rebuilt. The assessment extends the
[theory-network comparison](theory-network-comparison.md): its same-logic
algebraic view is insufficient for the change-of-logic question here.

## The literature includes proof-sensitive institutions

Ordinary institutions specify signatures, sentences, models and satisfaction,
with sentence translation covariant and model reduction contravariant. Their
satisfaction condition compares truth in a target model with truth in its
reduct. Goguen and Burstall's Definition 1 gives that contract; their Section 2
uses it to organize theories independently of a particular logic.
[Institutions: Abstract Model Theory for Specification and Programming][ins].

The relevant alternatives already go beyond proposition-valued satisfaction.
Rabe, Mossakowski, de Paiva, Schröder and Goguen define preorder-enriched proof
categories and comorphisms in Definitions 2.4 and 2.6. Proofs are arrows;
reduction is an ordering on arrows. Definition 4.1 constructs these institutions
from categorical logics, and Proposition 4.15 transports categorical theory
maps to institution comorphisms. Satisfaction still records inhabitation,
while the proof category retains additional data. Their scope is categorical
propositional logic, including linear logic, not arbitrary dependent calculi
or higher identities. [An Institutional View on Categorical Logic][catlog].

Rabe's *A Logical Framework Combining Model and Proof Theory*, Sections 3–5,
provides a further candidate combining abstract institution-style logic with
LF representations of syntax, judgments, proofs and model theory. Encoding
adequacy remains a separate obligation. This is a reason to evaluate existing
frameworks before inventing a universal interface locally.
[A Logical Framework Combining Model and Proof Theory][combined].

MMT supplies another organization through theories and assignments. Its
composition and typing-preservation results require the regular-foundation
hypotheses in Section 7.2; they do not certify a new object encoding. Rabe's
later comparison, Examples 5.7 and 5.10, exhibits choices and compatibility
obstructions when combining logics. A universal construction needs the chosen
connections; it cannot choose the intended combination for us.
[A Scalable Module System][mmt],
[How to Identify, Translate, and Combine Logics?][howto].

The calculations below are this assessment's bounded designs and arguments.
They are not applications claiming that these papers already prove correctness
of conaled's representations.

## The two sides of a translation

Fix institutions I and J. Use the comorphism orientation of Definition 2.6
above, explicitly avoiding the opposing conventions sometimes called
institution morphisms. A connection F has:

```text
ΦF : Sign I → Sign J                         signature functor
αF : Sen I Σ → Sen J (ΦF Σ)                   sentence translation
βF : Mod J (ΦF Σ) → Mod I Σ                   model reduct functor
SatJ(M, αF φ) ↔ SatI(βF M, φ)                 satisfaction comparison
```

The last line is the comparison between these paths, with domain
`Mod J (ΦF Σ) × Sen I Σ`:

```text
                 (M, φ)
              /          \
      (M, αF φ)          (βF M, φ)
           |                 |
        SatJ                SatI
           \                 /
              propositions
```

The arrows to propositions are satisfaction evaluations, not model morphisms.
Within each institution, signature substitution must commute with α and β.
For `s : Σ → Σ'`, these equations are
`αΣ' (SenI s φ) = SenJ (Φ s) (αΣ φ)` and
`βΣ (ModJ (Φ s) M) = ModI s (βΣ' M)`, or specified coherent isomorphisms
in a weaker presentation. The underlying functors supply identity/composition
on signature maps and model arrows. Satisfaction need not be preserved by
arbitrary model homomorphisms; an arbitrary first-order homomorphism, for
example, need not preserve negation. No unrestricted evidence bifunctor on all
model arrows is implicit here.

For G from J to K, the composite is

```text
ΦGF = ΦG ∘ ΦF
αGF = αG ∘ αF
βGF = βF ∘ βG
SatK(N, αG(αF φ)) ↔ SatJ(βG N, αF φ) ↔ SatI(βF(βG N), φ).
```

The identity uses identity functors and reflexive comparisons. Associativity
follows from functor composition and composition of comparisons. If reductions
are identified only by isomorphism, their associators and unit comparisons
must satisfy coherence; replacing those obligations by literal equality would
exclude intended models. These are satisfaction laws, not a decoder for target
proofs.

To retain selected data, additionally fix an evidence family `E_I(M, φ)` and
an evaluation of source proofs into it. A candidate *additional capability* is

```text
eF(M,φ) : E_I(βF M,φ) ≃ E_J(M,αF φ)
PF      : ProofI(Γ ⊢ φ) → ProofJ(αF Γ ⊢ αF φ)
eF(evalI d) = evalJ(PF d), with the environment comparison understood.
```

For the diagram take closed proofs first, so no environment is suppressed:

```text
ProofI(⊢ φ)          -- PF -->       ProofJ(⊢ αF φ)
    | eval in βF M                       | eval in M
    v                                    v
E_I(βF M,φ)          -- eF -->        E_J(M,αF φ)
```

An equivalence is appropriate for exact reinterpretation; one-way maps or
relations fit other contracts. A one-way evidence map gives one direction of
inhabitation preservation, not the satisfaction iff by itself. In this report
`≃` is an equivalence of the selected evidence spaces, not equality of
representations. For higher evidence, replace equality in the compatibility
law by the specified comparison and retain its coherence. The ordinary
satisfaction relation is recovered as `Nonempty E` only for clients whose
satisfaction has that definition.

With strict matching indices, define
`eGF(N,φ) = eG(N,αF φ) ∘ eF(βG N,φ)` and `PGF = PG ∘ PF`.
The compatibility calculation is

```text
eG(eF(evalI d)) = eG(evalJ(PF d)) = evalK(PG(PF d)).
```

Identity evidence maps and proof maps give the unit law; threefold function
composition gives associativity. These laws compare selected meanings. They do
not identify arbitrary raw proof trees. More general indexed comparisons must
insert the named index transports before composing.

## A change of logic with a failed reverse connection

Use two independently specified paper calculi. L is the multiplicative
intuitionistic linear fragment with formulas
`p | I | A ⊗ B | A ⊸ B`. Its term judgments use contexts of distinct variables.
Exchange is permitted. Variables use their one-variable context; tensor
introduction and application split contexts into disjoint parts; abstraction
discharges one variable; tensor elimination consumes its scrutinee once and
introduces both components once; the unit introduction has empty context and
unit elimination consumes one unit. There is no weakening or contraction.
Equality is the usual beta/eta equality for these constructors together with
the context exchanges. This specifies the resource boundary independently of
our rule engine.

C is the simply typed lambda calculus with formulas
`p | 1 | A × B | A → B`, shared-context pairing and application, projections,
unit, abstraction and variables. Variables may be unused or repeated. Equality
is beta/eta for products, unit and functions. L models are symmetric monoidal
closed categories with chosen structure and a valuation of atoms. C models are
cartesian closed categories with chosen structure and a valuation. Restrict
model maps to functors preserving that chosen structure strictly for this
paper fixture. This restriction makes the comparisons below literal; general
strong comparison maps need coherence. Small categories or a fixed universe
can be used throughout. Set below can be taken in the next universe.

Define F on formulas by `I ↦ 1`, `⊗ ↦ ×`, `⊸ ↦ →`, and atoms identically.
On terms use identity on variables, ordinary pairing/application/abstraction,
translate tensor elimination to product elimination, and unit elimination to
unit elimination with the unused unit allowed. The disjoint source contexts
embed into the shared target context. Translation of each source typing rule
is therefore a target derivation. Recursion on terms proves capture-avoiding
substitution commutes with F, using fresh bound variables; beta/eta images are
target beta/eta equations. This establishes forward typing and equality
preservation on paper. It is a change of admissible reasoning and formula
constructors, not a same-signature `RuleInterpretation` instance.

The reduct βF regards a cartesian closed category as symmetric monoidal closed,
with tensor its chosen product, unit its terminal object and internal hom its
exponential. It retains underlying arrows and their selected values. On model
maps it retains the same functor. Formula induction identifies the interpreted
objects, and rule induction identifies the interpreted arrows. Define
`E_L(M,A) = Hom_M(I,⟦A⟧)` and `E_C(N,B) = Hom_N(1,⟦B⟧)`.
The identity on the resulting hom-set supplies eF and hence the satisfaction
iff. There is no claim that every L model arises as a reduct.

The selected client is the linear proof

```text
swap = λz. let (x,y) = z in (y,x)
     : (A ⊗ B) ⊸ (B ⊗ A).
```

It translates to `λz.(snd z,fst z)`. Interpret C in Set with
`A = Fin 2`, `B = Fin 3`. At `(1,2)` the selected output is `(2,1)`, and a
second swap returns `(1,2)`. The result is a particular function, not the truth
that a swap exists. The second stage here is semantic realization in a model,
not another claimed change of logic. As a second institution connection take G from C to C with
`ΦG Σ = Σ × Unit`, signature maps `s × id`, and atom translation
`p ↦ (p,())`. Then αG recursively tags formulas and proofs and βG
precomposes valuations by this inclusion, retaining underlying categories
and model functors. These definitions commute with every signature map.
Writing X and Y for the tagged A and B, a Set model with `X=Fin 2,Y=Fin 3`
gives exactly the same function through βFβG. This exercises the two-step
comorphism formula with an actual change of logic in its first step.

The reverse connection fails for contraction. C derives
`λx.(x,x) : A → A × A`. In the symmetric monoidal closed poset
`(ℤ, ≤, +, 0)`, let `A` denote `-1`; tensor is addition and internal hom is
`a ⊸ b = b-a`. Closure holds because `x+a ≤ b` iff `x ≤ b-a`.
An arrow `A → A⊗A` would require `-1 ≤ -2`, which is false. Every linear
rule above is sound: tensor uses monotonicity of addition, abstraction uses
this closure equivalence, and elimination uses composition and its adjunction.
Thus no formula-preserving reverse proof translator can send this contraction
proof to L. The same model need not expand to a cartesian closed model.
This is a semantic obstruction, not failed proof search. The source paper's
linear example motivates the categorical choice; this specific integer
countermodel and the term calculation are our worked controls.

Neither forward truth nor forward proof translation reflects equality. Set
interpretation may identify distinct source functions at a particular finite
valuation. For example, identity and swap on `A ⊗ A` agree when A is
interpreted as a singleton, but disagree in Set at `(0,1)` when `A = Fin 2`. Reflection would require additional evidence
about the whole model class or a faithful interpretation. Reconstructing a
source proof from a target proof is a fourth, separate requirement and is
already obstructed by contraction for unrestricted target proofs.

## Combining computation and satisfaction

For a fixed evidence comparison, let `R_I(βF M,φ)` and `R_J(M,αF φ)` be
representation types with decoders into the evidence spaces above. A
computation interface adds a translation cF and this square:

```text
R_I(βF M,φ)          -- cF -->        R_J(M,αF φ)
    | decodeI                            | decodeJ
    v                                    v
E_I(βF M,φ)          -- eF -->        E_J(M,αF φ)
```

The additional law is `decodeJ(cF r) = eF(decodeI r)`. It connects a chosen
implementation to the same evidence comparison that interprets proofs. It
must not be silently inferred from satisfaction. Conversely, a correct
computation square does not supply syntax, models or a logic translation.
For successive stages the law follows by pasting:

```text
decodeK(cG(cF r)) = eG(decodeJ(cF r))
                 = eG(eF(decodeI r))
                 = eGF(decodeI r).
```

Identity is identity on representations and evidence. This is the ordinary
square calculation with indices; its associativity uses the same composition
as the proof diagram. A combined interface bundles F, PF, eF, cF and the two
compatibilities. Separate interfaces can share eF and derive the identical
pasting theorem. Merely bundling them removes no obligation. Its potential
benefit is preventing a proof translator and compiler from silently using
different meanings, and exposing composition once at their common boundary.

For relational interpretations use a relation `Q(r,e)` and a preservation
map `Q(r,e) → Q'(c r,eF e)`, or an appropriately indexed relation on both
meanings. Relational composition retains intermediate witnesses if the client
observes them. Neither a total decoder nor an inverse is required. This agrees
with [ADR 0002](../adr/0002-relations-and-synchronization.md); forcing a decoder
would lose its interval and signal interpretations.

## Three existing clients discriminate between the alternatives

### Type-valued languages and selected parses

Elliott's pinned `Language.lagda` defines `Lang = A* → Set ℓ`; union keeps a
tagged choice, and concatenation retains the split and component witnesses.
[Language.lagda][lang]. Locally,
[`Witnesses.lean`](../../Applications/Languages/Witnesses.lean) defines
`Language α = List α → Type u`, while
[`Parser.lean`](../../Applications/Languages/Parser.lean) implements decisions
for the represented parser syntax. A successful decision chooses one parse;
it is not an enumeration of all parses or an executable realization of every
possible type-valued language.

For a language P, word w and parser p, the evidence is P w and the executable
observation is `Decision (P w)`. A language equivalence e acts on the entire
decision, transporting success by its forward map and refutation using its
backward map. Arbitrary one-way witness maps are insufficient for this
refutation branch. For this computation the bottom corners of the square are
`Decision (P w)` and `Decision (Q w)`, with the equivalence induced by e.
They are not P w and Q w: a rejecting parser has no value in P w to decode.
The type-valued language remains its specification; the decision result
contains either selected evidence or a refutation. This derived comparison
connects the executable observation to that specification. The checked
[`ExactRewrites.lean`](../../Applications/Languages/ExactRewrites.lean)
`Decision.map_trans`, `parse_transport_trans` and `contextual_transport_trans`
retain the selected decision through two transports. For a hypothetical
ambiguous empty-word language `P [] = Unit ⊕ Unit`, the two successful parses
`inl ()` and `inr ()` have identical `Nonempty` and Boolean observations.
No decoder from that one success observation can recover both original tags:
its value would have to equal both distinct injections. An institution of
inhabitation remains useful for recognition, but does not meet this contract.

Construction and observation still supply the induction principle. In
[`IndexedCompositional.lean`](../../Applications/Languages/IndexedCompositional.lean),
local `sourceCompatible`/`targetCompatible` laws and the leaf morphism feed
`recovered`, retaining full finite-depth parser observations in arbitrary
constructor terms. A satisfaction interface does not derive these local laws
or the recursion over constructors by itself. An enriched framework could
organize this as interpretation of a freely generated indexed syntax and
its observation algebra. It must recover `recovered` and the two-transport
law from those local inputs, without taking `recovered` as a field.

### Sparse polynomial computation with independent meaning

[`Polynomial.lean`](../../Applications/Convolution/Polynomial.lean) realizes
word-indexed series by finite association lists, allowing duplicates and
zeros. Its independent meaning is the series of summed coefficients.
`denote_mul` proves multiplication preservation; `denote_normalize` proves
normalization preservation; `normalizedMulSquare` pastes them. Over natural
coefficients `languageMulSquare` additionally forgets coefficients to support.
These are source-inspected checked declarations, not new experiments.

A hypothetical list with two entries `(w,1),(w,2)` and the normalized list
`(w,3)` have the same series, while their representations differ. Product laws
belong to series equality. A combined institution/computation account can use
equational sentences about series and proof interpretations together with this
realization. It must retain the entire coefficient function when that is the
contract; nonzero support cannot recover the coefficient 3. Support is an
appropriate distinct observation with its own theorem, not a replacement
meaning for multiplication.

Here the square's denotation space is the series carrier, not the proof type
of an equation about series. One can derive a property comparison: for a
predicate q on series, `q (denote (normalize p)) ↔ q (denote p)` follows from
`denote_normalize`. This does not require q to be decidable. To organize such
properties as an institution still requires its signature/sentence structure.
The computation comparison and its induced satisfaction claims should be
connected without identifying value types with equation-proof types.

The square framework already derives normalization after multiplication. A
new institution wrapper earns reuse only if it also derives a needed
specification translation or model restriction, or makes the same law
transport available across a change of logic. Representing the theorem as a
satisfaction field alone adds packaging here.

### Dependent proof and selected section

The checked
[`CompositionalSpecifications.lean`](../../Examples/CompositionalSpecifications.lean)
retains the section `n ↦ n : Fin(n+2)` through primitive/stable/eta specification
views, then reindexes by doubling. `decoded_twice` recovers the selected
`6 : Fin 8` at input 3. The zero section has the same inhabited fibers and
would fail the selected-value contract. This test is same-signature; it does
not establish the cross-logic result above for dependent types.

For a dependent extension of the proposed interface, judgments include
contexts Γ, types A over Γ, terms t and substitutions σ. Translation must
map all four, including `F(A[σ]) ≅ (FA)[Fσ]` and the corresponding typed term
comparison. A witness comparison for t must commute with reindexing under
that type comparison. For two substitutions σ,τ, its sequential comparison
must agree with the comparison for σ∘τ after the specified associativity
transports. Otherwise the two paths can return elements in different fibers,
or different selected elements in the same fiber. The displayed `6 : Fin 8`
checks a nonconstant fiber and nonzero selection; it cannot by itself certify
all higher coherence. Higher identity witnesses remain a further adoption
obligation, shared with [#342](https://github.com/VladimirMarko/conaled/issues/342).

This extra structure is not supplied by an ordinary satisfaction iff or by the
propositional categorical-logic construction in the cited paper. An indexed
proof category or comprehension structure, with coherent interpretation maps,
is a candidate extension. A formalization must derive term/substitution
transport from its local constructors, as #339 does for its narrower rules.
It must not ask the client for the final `decoded_twice` theorem as a field.

## What existing machinery derives

Pinned Felix `MakeLawful.agda` derives category and Cartesian laws using local
homomorphism preservation and the equivalence induced by the meaning map.
It does not require literal source-arrow equality.
[MakeLawful.agda][felix]. Locally,
[`CategoryMap.lean`](../../SquareKit/CategoryMap.lean) separates operations,
equivalence and laws: `inducedLaws`, `transportLaws` and `comp_laws` derive
congruence/law transport and composition under their stated assumptions.
Reflection is needed for an independently chosen source equivalence; for the
induced equivalence it is immediate. This remains useful inside categorical
proof interpretations. It does not supply an institution's signatures,
sentence functor, model reduct or dependent substitution.

[`GuardedRuleInterpretation.lean`](../../SquareKit/GuardedRuleInterpretation.lean)
derives transport of arbitrary derivations from primitive rule certificates.
Its model reduct retains the algebra, so its satisfaction theorem is reflexive.
It supplies no changing-signature or changing-logic translation, and no theorem
identifying the raw transported proof trees. Its noncomputable implementation
is a separate executable-translator follow-up recorded on #339/#290.

[`Squares.lean`](../../Squares.lean) supplies exact horizontal and vertical
pasting, including a comparison between the middle arrows;
[`Relations.lean`](../../SquareKit/Relations.lean) supplies relational
preservation and witness-space bridges. Their reusable composition is already
the computation part of the calculation above. Existing contextual parser
transport supplies stronger witness information than ordinary satisfaction.
The shared additional work is making syntactic interpretation, evidence
interpretation and dependent reindexing use compatible indices and meanings.

| Candidate organization | What it derives from its local inputs | Cost or missing information |
|---|---|---|
| Ordinary institutions throughout | Signature/theory translation and reduct composition; satisfaction comparison pasting | Selected parses, proof data, executable maps and substitution coherence need additional contracts |
| One combined satisfaction/proof/computation interface | The two compatibility diagrams paste over the same evidence comparison | May require executable structure for non-executable specifications; bundling alone derives no primitive laws |
| Separate capabilities with a shared indexed evidence comparison | Same pasting, optional executable/relational realizations, selected observations retained | Index coherence must be supplied or generated once; risks duplicated comparisons if their common boundary is not enforced |
| Categorical or LF-based logic organization | Potential generic proof translation and model interpretation from presentation assignments | Adequacy and framework hypotheses; propositional sources do not settle arbitrary dependent/higher cases |

## Recommendation and bounded next formalization

**Adopt** the distinction between a logic connection, its evidence comparison
and a computational realization as the contract for the next experiment.
**Investigate** institutions with proof and dependent evidence as an organizing
interface across the library, including construction and observation.
**Defer** mandatory repository-wide use or replacement of the current squares.
**Reject** a proposition-only satisfaction record as a sufficient interface for
all three tested clients: the parse-tag and dependent-section controls refute
that sufficiency. This does not reject institutions, their proof-sensitive
extensions, or a future architecture organized around them.

The present preference is separate capabilities sharing one comparison,
with a combined package available when a consumer needs all of them. This
preference rests on non-executable meanings, witness-sensitive observations and
the existing reuse of square composition. There is no measured productivity
comparison and no demonstrated universal dependent interface. A better
framework may replace the current organization if it derives more of the
needed structure without discarding these contracts. No immediate adapter to
today's guarded engine is an entry requirement.

The justified next formalization, owned by #290/#235 and coordinated with
#36/#200, is one bounded comparison, not a universal framework rollout:

1. Specify the linear and cartesian fragments above independently, preferably
   reusing an adequate existing presentation. Derive translation on types,
   terms, substitutions and beta/eta from primitive assignments. Check swap,
   two-step renaming, the integer countermodel and rejection of contraction.
2. Implement the proof/evidence comparison and computation pasting twice:
   separate capabilities and a combined interface. Reuse native squares where
   they fit. Neither route may take whole-client correctness as an input.
   Compare recurring obligations, not just record field counts.
3. Specialize to parser transport and recover the exact selected decision
   through two equivalences and a constructor context. Include the ambiguous
   tag counterexample and the negative-decision branch. Retain finite-depth
   bounds and do not claim an executable parser for arbitrary P.
4. Specialize to the dependent selected-section client, deriving two-substitution
   coherence and recovering `6 : Fin 8`. If the candidate framework cannot
   express that contract, record the missing structure rather than truncating
   the evidence. Compare with #342's metatheory findings before extending to
   higher witnesses. #341 owns enforcing the semantic-client boundary, not
   recovering evidence from lossy observations.
5. Record one-time model/encoding work separately from repeated authoring and
   repair effort. Agent productivity is sufficient for the MVP. Formal changes
   need statement review, checked specializations, full applicable build/audit
   and independent Standards/Spec review.

This assessment answers the research question at paper scope. The bounded
formalization remains proposed work under the named owners; neither its
implementation nor ubiquitous adoption is claimed complete. For this report,
validation consists of local-link checking and whitespace checking, with
independent content review owned by the enclosing orchestration.

[ins]: https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf
[catlog]: https://kwarc.info/people/frabe/Research/GMPRS_catlog_07.pdf
[combined]: https://kwarc.info/frabe/Research/rabe_combining_10.pdf
[mmt]: https://www.kwarc.info/people/frabe/Research/mmt.pdf
[howto]: https://kwarc.info/people/frabe/Research/rabe_howto_14.pdf
[lang]: https://raw.githubusercontent.com/conal/paper-2021-language-derivatives/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4/Language.lagda
[felix]: https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda
