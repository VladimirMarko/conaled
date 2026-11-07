# Progressive evidence and computation capabilities

Bounded formalization for [#343](https://github.com/VladimirMarko/conaled/issues/343),
following the [#340 assessment](institutions-as-interfaces.md). The checked
experiment connects independently defined linear and cartesian proof syntax,
selected parser decisions, and a dependent section to a shared evidence map.
It adds no mandatory interface to existing clients.

## Outcome and scope

Use separate capabilities sharing typed interpretation data, and combine them
when a consumer needs both proof translation and computation. The combined
package derives the same composition as its separate constituents. Its benefit
is that both constituents must use the same meaning map. Merely putting two
independently correct squares in a product does not establish that agreement.
The checked `incompatible_meanings` example rejects such a combination.

Existing relational squares provide a useful common local preservation
interface. They specialize to exact computation and to satisfaction
preservation, but forgetting selected evidence to satisfaction loses information.
The Boolean example gives identical satisfaction squares for distinct evidence
maps. This obstructs recovering the selected comparison from that forgetful
view; it does not rule out a richer common abstraction.

The implementation is a family of chosen-signature connection capabilities,
not a complete port of institutions with signature categories and categories of
models. Atom renaming, its formula identity/composition laws, and two-stage
connection composition are checked. Nontrivial model morphisms, their
naturality, and a general signature-category package are not implemented here.
Those are further requirements for institutional metatheorems, rather than
implicit claims of `Connection`. The bounded comparison can already test the
shared-meaning contract without them. [#290](https://github.com/VladimirMarko/conaled/issues/290)
retains that architectural adoption decision; #344 and #348 own the adjacent
dependent-framework and richer-boundary work.

## Corners, arrows and capabilities

[`Capabilities.lean`](../../SquareKit/Institutions/Capabilities.lean) separates:

- `Setting`: sentences, models, and a type of evidence for each model/sentence.
- `Connection`: a forward sentence map, backward model reduct, and forward
  evidence map at the resulting indices.
- `Connection.Reflects`: optional inhabitation reflection. Together with the
  evidence map this derives the satisfaction iff. It is not proof reconstruction.
- `Proofs` and `ProofMap`: selected syntactic proofs, their interpretation, a
  proof translation, and its semantic compatibility.
- `Realization` and `RealizationMap`: representation carriers, decoders,
  representation transport, and its compatibility with that same evidence map.
- `RelRealization` and `RelRealizationMap`: relations instead of selected
  decoders, with no choice of one meaning from a relation.
- `Compatible`: proof and realization capabilities indexed by one connection.

For `f : Connection A B`, a target model `m` and source sentence `p`, the
common lower arrow is

```text
A.Evidence (f.reduct m) p  ── f.evidence m p ──▶ B.Evidence m (f.sentence p).
```

A proof map places source and target proof types above it, with interpretation
as the downward arrows. A realization map places representation types above
it, with decoders as downward arrows. The corresponding square is obtained by
`RealizationMap.square`. Its composition uses `Squares.compose`, not a new
proof of the square-pasting calculation. `ofSquares` accepts existing squares
only with compatibility of their lower arrows. Relational realizations have
the same adapter and a composition theorem using the existing relational
contract. This respects ADR 0002's many-valued meanings.

For `g : Connection B C`, `g.comp f` translates sentences by `g ∘ f`, reduces
models by `f.reduct ∘ g.reduct`, and composes evidence maps at those indices.
The direction change is explicit in the definition. It establishes neither an
adjunction nor an inverse compiler. Composition is associative; identity laws
hold for connections, proof maps and realization maps. Forgetting either field
of a compatible package commutes with composition. Exact and relational square
adapters preserve composition.

`Connection.ofMap` accepts a plain map of meanings with no model class, proof
syntax or evaluator supplied by the caller. Unit indices are inserted inside
the specialization. `RealizationMap.ofSquare` similarly embeds an existing
ordinary square and recovers it exactly. A family reindexing client supplies
only a family and substitution. A parser supplies no proof language or model
category. Executability is never a condition for a semantic denotation to
participate. In particular, a function-valued model interpretation is not
claimed to be an executable decision procedure for its equations.

## Independently specified reasoning and model restriction

[`LinearCartesian.lean`](../../SquareKit/Institutions/LinearCartesian.lean)
defines separate formula and proof datatypes. Linear formulas have atoms,
unit, tensor and internal hom. Cartesian formulas have atoms, terminal object,
product and function type. Linear arrows have composition, tensor,
symmetry, associator and inverse, unit maps, curry and uncurry. Cartesian arrows
instead have shared-domain pairing, projections and terminal maps, alongside
composition and closure. Thus contraction is a target construction and is not
a source primitive.

This is a categorical combinator presentation. An input object represents its
context, and substitution is composition. `translate_substitution` checks the
translation of that operation. `closedSwap` curries the context arrow to the
closed function. There is no separately claimed adequacy theorem relating
these datatypes to a named-variable lambda calculus or its capture-avoiding
substitution implementation.

The source equation fragment contains category laws, congruence, closed
beta/eta and curry naturality, tensor functor laws, symmetry naturality and
involution, and inverse associator/unit equations. The target equation
specification is equality of the independently defined function interpretations
at every valuation. `translate_equation` proves the whole source equation
induction. This is sound preservation of the stated fragment; it is not a
completeness theorem for symmetric monoidal closed coherence, or reflection
of target equations. Additional coherence generators could be added with
primitive model checks; no universal completeness result is inferred from
this finite presentation.

[`LinearModels.lean`](../../SquareKit/Institutions/LinearModels.lean) separates
primitive semantic operations from their local laws. Recursive interpretation
of proofs and soundness of arbitrary equation derivations follow from them.
The actual source model class contains both function and resource models:

- `cartesianModel v` interprets tensor as product and hom as function type.
  The model reduct constructs this source model from a target type valuation.
  Its evidence map is identity on the resulting function space.
- `resourceModel v` interprets an arrow from A to B as a lifted proof that
  `resource A ≤ resource B`; tensor adds resources, unit is zero, and hom
  subtracts the input resource from the output resource. Every primitive
  operation and every local law is checked for this model.

At the valuation assigning the atom `-1`, contraction would require
`-1 ≤ -2`. `no_reverse_contraction` derives its impossibility using the generic
source model interpretation. Target contraction evaluates to `(7,7)` at 7.
This is a model obstruction, not a failed attempt at proof search.

The first translation assigns each linear primitive a cartesian proof and
extends recursively over arbitrary proofs. Its interpretation theorem compares
that translation with independent source evaluation, then with the generic
model interpretation. The second translation tags each atom `a` as `(a,())`.
Its model reduct precomposes a valuation; its evidence comparison is conjugation
by recursively constructed formula equivalences. `rename_meaning` is another
primitive-constructor induction. It also yields target equation preservation.

The composed proof and computation capabilities retain the selected swap on
`Fin 2 × Fin 3`: `(1,2)` becomes `(2,1)`, and a second swap returns `(1,2)`.
Both the open context arrow and its closed curried form are tested. These
results use the composed compatibility theorem, not an unrelated direct
calculation. Satisfaction reflection holds at each target model's reduct;
it does not assert that every source model is such a reduct. The resource
countermodel explains why that distinction matters.

## Parser and dependent clients

[`IndexedClients.lean`](../../SquareKit/Institutions/IndexedClients.lean) keeps
`Language = List α → Type`. Its observation evidence is a selected `Decision`,
including refutation. A language isomorphism acts on both branches; the
backward map is used to transport refutations. The universe lift used to place
symbolic syntax and observations in an existing square is a representation
adapter, not truncation.

`parserMap` derives its compatibility by induction over the observed word.
`parser_pasting` uses the generic realization composition and existing
`Decision.map_trans`. `parser_context` uses the existing `recovered` theorem,
whose constructor/observer induction derives all-term behavior from local
compatibility. The new interface does not take that final result as a field.
Examples retain the left tag of an ambiguous empty-word parse through two
swaps and retain the rejection of a nonempty word. A constructor-context
example uses the same selected decision. `parser_contextual_fusion` feeds the
capability-derived local transport law into the existing contextual induction;
the pre-existing context with star, concatenation and depth restriction is
checked through that result. Finite trie
observations still require the word-length bound; there is no parser for every
arbitrary type-valued language.

For dependent families, `reindexConnection` uses substitution as model reduct
and identity at the reindexed fiber as evidence map. `section_comp` and
`section_reindex_twice` derive the corresponding selected-section composition.
The client reuses #339's independently established `selected_value` and
`decoded_twice`: decoding the transported source derivation agrees with the
capability's twice-reindexed section, which returns exactly `6 : Fin 8`.
It neither replaces that section by zero nor merely asserts inhabited fibers.

This dependent specialization has strict reindexing of native families.
Arbitrary weak comprehension comparisons, dependent changes of logic and
higher identity coherence are not consequences of it. In those cases the
fiber comparisons and their coherence must be retained, not truncated to
inhabitation. #344/#348 and the new adjoint work under #351 address distinct
parts of those remaining requirements.

## Comparison and recurring obligations

| Organization | Setup | Recurring work and result |
|---|---|---|
| Native client | Existing square, parser induction or dependent substitution API | Keeps the shortest route when there is no changing proof/model interpretation. |
| Separate capabilities | Sentence/reduct/evidence indices; primitive proof assignments and local semantic checks | Generic composition, adapters and selected-section transport are reused; clients request only the capabilities they need. |
| Compatible wrapper | The same connection and the already constructed proof/realization maps | No new mathematical obligations; prevents choosing different evidence maps and derives joint composition. |
| Common relational square | A relation and maps preserving it | Existing relational composition applies. Satisfaction specialization forgets selected evidence and cannot recover it; full institution indexing must remain elsewhere. |

The repeated mathematical work remains the primitive interpretation checks.
Neither a wrapper nor ordinary satisfaction can discharge them automatically.
The shared interface does remove the need to repeat the two-stage compatibility
calculation or invent a new proof that proof and compiler meanings agree.
These are source-level obligation comparisons, not measured productivity data.
Agent productivity remains sufficient for the MVP, but no speedup is claimed.

MakeLawful and local `RawMap.inducedLaws`/`transportLaws` already organize laws
under an induced or reflected equivalence. They do not supply changing formula
constructors or selected parser decisions. This experiment keeps those
foundations intact and uses the existing square and parser composition where
applicable. It does not claim a new general replacement for category law
transport. The law record for the bounded linear constructor algebra specifies
its equation fragment, and its congruence/soundness theorem is an induction
specific to that fragment.

The #349 audit also identifies existing uses of `AdjointComparison`. If future
indexed connections change a chosen right adjoint to the same left adjoint,
its curry/uncurry/mate compatibility should be reused. This experiment does not
claim an adjunction between the sentence map and model reduct, or infer that
an arbitrary mate is invertible.

## Statement review and validation

Checked claims are in the four library modules and
[`InstitutionCapabilities.lean`](../../Examples/InstitutionCapabilities.lean).
Statement review checked the following boundaries:

- Connection composition orders the contravariant reduct correctly and uses
  the intermediate evidence fiber. Identity and associativity observe maps,
  not an erased existential statement.
- Model interpretation is derived from primitive operations. Equation soundness
  uses justified local laws in both concrete models. The contraction premise
  is impossible in the resource model, while source swap and target contraction
  are inhabited and computed in the positive controls.
- Translation equality is target semantic equality at all type valuations.
  It neither reflects equality nor reconstructs arbitrary target proofs.
- Exact realization adapters demand the same lower arrow. The two separately
  lawful Boolean squares fail that compatibility. The relational client
  admits both Boolean values and never selects a decoder.
- Parser decisions and dependent sections remain data. Refutation transport
  uses both directions of an isomorphism; the dependent result checks a
  nonconstant fiber and a nonzero selected value.
- The common satisfaction view has a precise information-loss example. This
  establishes no impossibility result for proof-sensitive institutions.

Focused validation uses `lake build Examples.InstitutionCapabilities`.
The enclosing implementation workflow owns exact-candidate full build, exhaustive
axiom audit and independent Standards/Spec review. No new axioms, admitted goals,
global decidable equality, universal AST or wholesale client migration are added.

## Sources and attribution

The mathematical institutional motivation is from Goguen and Burstall,
[*Institutions: Abstract Model Theory for Specification and Programming*](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf),
Definition 1, and Rabe, Mossakowski, de Paiva, Schröder and Goguen,
[*An Institutional View on Categorical Logic*](https://kwarc.info/people/frabe/Research/GMPRS_catlog_07.pdf),
Definitions 2.1, 2.4, 2.6 and 4.1. The latter supplies a proof-sensitive
institutional account; this experiment is not a Lean port of its general
construction. Those sources were re-opened for this implementation.

The independent combinator datatypes, resource countermodel and capability
specializations here are new checked constructions motivated by #340's worked
fixture. Existing square and constructor/observer results retain their original
provenance. Felix's pinned
[`MakeLawful.agda`](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
was inspected for the law-transport comparison. Parser meanings follow the
source and local implementation recorded in the #340 report. This document
separates those source results, the new checked fragment, and the remaining
architectural inference that broader use might reduce repeated obligations.
