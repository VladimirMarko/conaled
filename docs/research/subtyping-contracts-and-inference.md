# Choosing subtyping contracts and optional inference

Assessment for [#258](https://github.com/VladimirMarko/conaled/issues/258),
2026-10-30. **Adapt explicit evidence and variance first; investigate implicit
subsumption only within a checked fragment; defer global subtyping.** Dolan's
algebra supports a useful combination of guarantees, but it is one specified
algebra. Subsequent work extends different parts of the design and exposes
which equations and inference claims do not survive unchanged.

This note reads beyond the thesis: Dolan–Mycroft's MLsub paper and
Yallop–Dolan's First-Class Subtypes are included, alongside later work on
modal effects, memory management and data-race freedom. Algebraic-inference
follow-ups by other authors are identified separately. Source results below are not local formalizations. The shared worked
examples and adoption recommendations are this project's assessment.

## Dolan's thesis

[Dolan, Algebraic Subtyping
(2016)](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf):
§§1.3–1.4 define the open-world motivation; Chapter 3 constructs the algebra, with
type variables as indeterminates rather than quantification over a fixed ground
universe. Section 5.1's inferable polar syntax permits joins/bottom positively,
meets/top negatively, booleans, functions and records. Recursive binders are guarded
by function/record constructors and covariant in their bound variable. Theorems 59 and
65 establish failure completeness and success soundness of biunification. Proposition
66 gives a principal **typing scheme**, including its free-term-variable assumptions,
under a polar environment. Corollary 67 separately gives a positive principal **type**
for a closed typable expression. Chapter 8 decides scheme subsumption using automata,
independently of generating principal types. Theorems 27–28 establish
progress/preservation for the core language. Section 10.2.3 explicitly records the
arrow-intersection equation discussed below; §§11.1.1–11.1.2 leave GADTs and
first-class polymorphism as future work. These claims concern the specified algebra,
not arbitrary axioms or dependent refinements.

## Dolan and Mycroft's MLsub paper

[Accepted POPL 2017
paper](https://api.repository.cam.ac.uk/server/api/core/bitstreams/d50b4d1a-a688-46eb-bb4f-9f4e204d0f60/content),
§1.1 scopes the formal language to pure booleans, records, functions and let. Section
3 treats contextual typing schemes; §4 constructs principal inference with
input/output polarity. Theorems 8–9 cover biunification success and failure; §5.3,
Theorem 10 connects equality of same-polarity types to equality of regular languages.
Mutable references and deciding scheme subsumption are explicitly deferred to the
thesis, despite being implemented extensions. The paper's introduction gives exactly
`select p v d = if p v then v else d` with type `(α → bool) → α → β → (α ⊔ β)`.
Section 1.1 points to separate contravariant write and covariant read parameters for
references, not blanket covariance of mutable cells. The dissertation is Dolan's;
the POPL paper is joint work with Mycroft. The following systems have different
authors.

## Parreaux's Simple-sub

[ICFP 2020
paper](https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content),
§3 presents a mutable bound-propagation algorithm, with recursive types (§3.4.1) and
let-polymorphism/recursive definitions (§3.5). Section 5 explicitly restricts the
metatheory to the **non-let-polymorphic** version and gives proof sketches, saying
complete proofs lie outside the paper. Theorems 1–2 (§5.3) state soundness and
principal-scheme completeness against the minimal declarative system of Figure 10;
Lemmas 4–5 concern constraining termination/completeness. Section 5.1 warns that
constructor-merging rules needed for subsumption and simplification exceed that
minimal relation. Section 3.3 tracks polarity during coalescing to generate covariant
recursive variables; §5.1 guards recursive subtyping assumptions beneath
function/record constructors. Differential implementation testing (§6) supplements
these arguments; it is not a mechanized semantic proof. Suitable as a small
algorithmic reference once the target relation is selected, with the let-polymorphic
proof obligation retained.

## Chau and Parreaux's MLstruct / Boolean-Algebraic Subtyping

[2024 technical report extending the 2022
work](https://lptk.github.io/files/boolean-algebraic-subtyping.pdf): §§2–3 provide
unrestricted type-level union, intersection and complement, equi-recursion, structural
records, single-inheritance tags and tag-based matching; polymorphism remains
ML-style. Section 3 defines a generic Boolean-algebraic framework, but the concrete
constructor rules matter: the report explicitly permits equations unavailable in
classical set interpretations. Theorem 4.1 proves constructor-shape soundness under
consistent bounds. Theorems 6.2–6.3 prove program progress/preservation; Theorems
7.4,7.6,7.7 separately give inference soundness, constraining termination, and
principal inference completeness. The latter compares universally closed outputs using
subsumption; it does not claim all semantic subset constraints are decidable.
Inference uses normalization of Boolean constraints and guarded recursive assumptions.
Unrestricted connectives do not mean arbitrary new constructor rules are sound. This
is a broader algorithmic fragment than MLsub, purchased with explicit nonstandard
algebraic laws.

## Chau and Parreaux's MLstruct+ semantic account

[POPL 2026, DOI 10.1145/3776689](https://doi.org/10.1145/3776689): §2.5 specifies the
algebra and guarded assumptions; §3.2, Definition 3.2 gives consistency through
top-level substitutions and guarded context entailment. Section 4.5, Lemma 4.12
obtains constructor-shape inversion using five characteristic Boolean homomorphisms;
the surrounding Theorem 4.1 handles consistent contexts. Section 5.2, Lemma 5.2
characterizes subtyping by those homomorphisms; §5.3.1 derives a decision procedure.
Section 5.3 and Lemma 5.11 establish **co-NP-hardness**, already without recursive
types, via propositional tautology. The author landing-page abstract says NP-hard, but
the published text says co-NP-hard; use the latter. Record removal is encoded in the
type algebra, so record extension adds a term form/rule without changing subtyping.
This is a semantic proof about the chosen algebra and constructor separation, not
identification of its types with ordinary sets of program values. It does not newly
prove complete dependent or impredicative inference. The conclusion leaves
simplification of MLstruct's inference proofs for future work.

## SuperF: first-class polymorphism changes the contract

[Parreaux, Boruch-Gruszecki, Fan and Chau, technical
report](https://lptk.github.io/files/superf-tech-report.pdf), §3 defines multi-bounded
F{≤}; Theorem 3.5 translates declaratively typable terms to System Fcc. Section 4.5,
Theorems 4.5 and 4.7 prove inference/constraining soundness. Section 4 and Appendix
D.1 use recursion detection to obtain termination, with an explicitly incomplete
heuristic. Section 2.4 restricts user annotations to System F types without bounds;
inferred polymorphism is positive and generalized at lambdas. Section 5's
implementation supports recursive definitions beyond the displayed core. Do not claim
complete inference or a universal principal-type result.

Section 2.4, footnote 9 (printed 48:9) gives the exact incompatibility:

`∀α. α → α ≤ (Int → Int) ∧ (Str → Str)`

but retaining MLsub's equation

`(A → B) ∧ (C → D) = (A ∨ C) → (B ∧ D)`

would assign identity `(Int ∨ Str) → (Int ∧ Str)`. Applying it to an integer cannot
produce both an integer and string. The paper explicitly calls that simplifying
assumption unsound with first-class polymorphism. This is a failed extension of a
particular algebra, not a failure of ordinary function variance.

## Evidence, inclusion and dependent transport

Yallop–Dolan's [*First-Class Subtypes*, §2.3, Figures 2–5,
§3.3](https://arxiv.org/pdf/1905.06546) gives positive-context, negative-context
and Church-style encodings of subtype witnesses, with conversions between
implementations of the interface. Its `lift` ranges over *every* positive
context; the paper argues that coercion must pass values through unchanged,
rather than traverse a data structure. This is stronger than having an arbitrary
function `A → B`. Modular implicits supply higher-kinded quantification with
variance information. The mutable lazy-cell example (§1) separates private
representation variance from a covariant public interface; it does not make
unrestricted mutable references covariant. This is a library-evidence lead,
not a general dependent inference theorem or a license to erase arbitrary
semantic maps.

Castagna's [semantic-subtyping account, §3 Definition 1 and
§§4.1–4.4](https://arxiv.org/pdf/2111.03354) interprets subtyping as inclusion
in a specified semantic domain. Its recursive type trees must be regular and
contractive; its algebra includes union, intersection, negation, products and
arrows. The unrestricted typing presentation is not effectively implementable;
the later sections choose restricted annotation/inference disciplines.
§4.2.5 explicitly separates the monomorphic value interpretation from the
polymorphic treatment. For our purposes, choosing Boolean type syntax does not
establish a faithful interpretation in every internal logic. Semantic inclusion
also concerns a common domain of values, not inclusion of arbitrary mathematical
function graphs with different domains.

Luo–Soloviev–Xue's [coercive-subtyping account, Definition 2.2;
Theorems 3.6–3.10](https://www.cs.rhul.ac.uk/~zhaohui/Subtyping12.pdf) treats
coercion insertion as abbreviation. Its coherence condition includes well-typed
coercions, no strict self-coercion, and equality in the underlying theory of
parallel coercions. Basic judgments are generated without coercive application;
Example 2.1 explains why allowing rules whose premises become newly applicable
can defeat the earlier formulation. For the specified UTT/MLTT setting and
coherent judgments, Theorem 3.9 proves conservativity of the marked star-calculus;
Theorem 3.10 relates it to the implicit presentation. These hypotheses matter:
existence of two functions with the right endpoints does not provide coherence,
and equality of coercions is stronger than choosing one by priority.

Najmaei–van der Weide–Ahrens–North's [CCTT v2, Theorem 3.10,
§3.6, Theorems 4.13 and 4.26](https://arxiv.org/html/2503.10868v2) gives
structural soundness in comprehension categories without assuming fullness or
splitness. Type morphisms retain witnesses. Functorial dependent products and
sums require additional model structure; §4's dependent function rule reindexes
the codomain along the contravariant domain morphism. This is a soundness
framework for explicit dependent maps, not automatic coherent subsumption,
set inclusion or decidable inference. It matches the need to retain substitution
comparisons in our dependent interfaces.

Laurent–Lennon-Bertrand–Maillard's [definitional-functoriality v2,
§4, Corollary 5.7 and Theorem 5.8](https://arxiv.org/pdf/2310.14929v2)
adds identity/composition equations for maps to conversion. The mechanized
fragment has empty and natural-number types, dependent products/sums, lists and
a single universe. §4 establishes normalization, canonicity and decidable
checking for that fragment. The later coercive/subsumptive comparison provides
elaboration and definitional coherence; §5.2 explicitly says that part was not
mechanized. Record coercions and the specified structural subtyping rules are
part of that later system. The paper does not prove that arbitrary refinement
entailment becomes decidable; §6 makes such extensions conditional on the
chosen fragment. This is a potential object-language design, not a change to
Lean's kernel or a consequence of proving ordinary map laws propositionally.

## The same examples under different contracts

The following are worked mathematical specifications, not new Lean declarations
or claims that every reviewed solver accepts them. `≤` denotes the selected
subtype judgment; maps and predicates are written explicitly when different.

### Function variance and loss of injectivity

Given `i : A′ → A` and `j : B → B′`, define
`lift(i,j)(f) = j ∘ f ∘ i : A′ → B′`. Identity and composition give the usual
contravariant/covariant action. Designated coercions need this action to preserve
the designation and its semantic laws. Semantic subtyping obtains the analogous
rule from its common-domain arrow interpretation. A refinement presentation
instead proves that admitted arguments and returned results satisfy their
predicates. In a dependent setting, the result family must be reindexed along
`i` before a codomain map can be supplied. Definitional functoriality can make
selected composition equalities automatic only in its specified calculus.

Even when `i` and `j` are injective, `lift(i,j)` need not be. Let `A′={false}`,
`A=Bool`, and `B=B′=Bool`; take `j=id`. The constant-false function and identity
on `Bool` agree after restriction to `A′`, but differ at `true`. Thus a semantics
requiring every subtype map to be monic cannot also admit all these function
lifts as subtype maps. #257 must retain this negative case; changing the
observation to equality only on `A′` changes the contract explicitly.

### Selecting a value or its default

For `select p v d = if p v then v else d`, let `p : A → Bool`, `v : A`, `d : B`.
A common-domain union gives result `A ∨ B`; the default need not be accepted by
`p`. Explicit coercions instead require chosen maps `a : A → J`, `b : B → J`
and return `if p v then a(v) else b(d)`. A tagged sum is one possible `J`, but
its tags retain branch information that an overlapping set union may forget.
A *least* upper bound requires a universal property beyond these two maps.

For predicates `P,Q` on a common carrier `X`, the result predicate is `P ∨ Q`.
For witness-bearing restrictions, injections into a sum retain the selected
witness; replacing that sum by a proposition-valued union may discard it.
A comprehension category does not supply joins just because it has type
morphisms. Definitional map laws likewise do not create the required join.
These are different answers to the same selection example, not interchangeable
spellings of one universally available type.

### Record width

A structural view may forget `y` from `{x:A,y:B}` to obtain `{x:A}`. Semantic
inclusion supports this when both types classify the same record values by
required fields. A coercive representation may implement an actual projection
or rearrangement, so it needs a preservation equation and cannot promise zero
runtime work without representation evidence. A refinement can express field
presence only after a record carrier and field semantics have been chosen.
Dependent records require reindexing later fields when earlier data changes;
plain width rules do not justify arbitrary dependent projection. Comprehension
morphisms can retain that map, and the definitional-functoriality paper treats
its specified record calculus, not every dependent record representation.

### Read and write bounds

A stateful interface `Cell(W,R)` accepts writes in `W` and returns reads in `R`.
With the same state behavior and chosen subtype maps, using one such interface
in place of another requires

```text
Cell(W₁,R₁) ≤ Cell(W₂,R₂) when W₂ ≤ W₁ and R₁ ≤ R₂.
```

The implementation must also preserve its state invariant: admitted writes
must leave future reads valid. In a common carrier, an actual cell storing
`S` can supply this interface if `W ⊆ S ⊆ R`. For one invariant parameter used
for both reads and writes, the two variance directions demand both subtype
inequalities; ordinary references do not become covariant. Coercions implement
pre/post-processing, refinements express the invariant, and dependent type
morphisms express indexed obligations. None by itself proves aliasing or effect
soundness. Map composition laws do not supply those state laws.

### Restricted data and `Fin`

For `m ≤ n`, the usual `Fin m → Fin n` preserves the underlying natural number
and transports its bound proof. A refinement interpretation uses implication
`k<m ⇒ k<n` in a fixed context. A witness-bearing family instead needs a map on
its evidence; projection from `Σ x, W(x)` loses information when `W(x)` has
multiple distinguishable inhabitants. A subobject interpretation must justify
that loss or restrict to proof-irrelevant witnesses.

With symbolic `m,n`, an arithmetic proof is required. With arbitrary dependent
predicates, entailment can be as hard as the ambient mathematics. ML-style
algebraic constraint solving does not supply it. Comprehension/type morphisms
record the transported family and substitution comparisons; definitional map
laws remove selected composition bookkeeping but do not prove `m ≤ n`. No
reviewed theorem combines arbitrary such constraints with complete algebraic
inference and the project's higher-identity interpretations.

### Two coercion paths

Suppose declared coercions give `A → B → D` and `A → C → D`. Implicit insertion
needs the two composites to agree under the promised observation/equality.
For a concrete failure, use distinct type names represented by `Bool`, with
identity on every edge except the `C → D` edge, interpreted by negation. At
`false`, the first path returns `false`, the second `true`. Both are valid
functions. They are not a coherent implicit coercion diamond.

Literal inclusions of sets into a common domain commute automatically; these
arbitrary functions are not such inclusions. Predicate implication can forget
proof choice only under the selected proof-irrelevance contract. In a category
of type morphisms both paths may remain visible and distinct. Functor laws
normalize identity and composition, but cannot identify independent primitive
maps that disagree. A priority rule can select one path; that is a resolution
policy, not derivation-independent semantics.

## Observational equality and the video proposal

Altenkirch–McBride–Swierstra's [*Observational Equality, Now!*,
§3 Lemma 1 and §4 Lemmas 2–4/Corollary 5](https://people.cs.nott.ac.uk/psztxa/publ/obseqnow.pdf)
studies equality, computational coercion between equal types, and a separate
proof language. Lemma 1 gives a strong-normalization proof sketch by simulation;
Lemma 2 separates canonicity of normal forms from consistency. Consistency is
then obtained through the extensional interpretation. §4.1 supplies equality
laws, including proof irrelevance. These results are for that calculus, not an
MLsub extension. Its equality/transport discipline is worth studying, but a
proof-irrelevant equality cannot simply replace path-sensitive identity in a
setting that retains nontrivial paths. Any comparison must state what it forgets.

The earlier [video assessment](language-design-and-type-systems.md#the-supplied-video)
used downloaded audio and a local transcript, with explicit transcription limits.
The separation of semantics, typing and solving at 10:04 supports testing a
small algebra against a model before implementing inference. The read/write
proposal at 19:54 has the variance obligations above. The dependent/observational
proposal at 21:20 is a lead: none of the reviewed theorems establishes its
combination with algebraic principal inference. The `Fin` example cannot be
settled by Boolean connectives alone. No new claims about unseen slide formulas
or the unidentified McBride talk are made here.

## Dolan's later work beyond algebraic subtyping

The following are Dolan-authored or coauthored leads, assessed at the cited sections
rather than as complete theorem audits. They address effectful and resource-sensitive
language extensions, not just improvements to MLsub.

Tang, White, Dolan, Hillerström, Lindley and Lorenzen's [*Modal Effect Types*
(2025)](https://www.pure.ed.ac.uk/ws/portalfiles/portal/514998748/TangEtalPACMPL2025ModalEffectTypes.pdf)
uses modalities to track changes of effect context. Theorems 4.3–4.4 establish progress
and subject reduction for Met, giving effect safety. Lemma 5.2 preserves typing for a
well-scoped row-effect encoding restricted to the lexically closest effect variable.
Section 7's bidirectional elaboration inserts boxes/unboxes; polymorphic inference is
explicitly beyond the paper's scope. This provides a concrete modal/elaboration
comparison, not evidence that algebraic subtype inference already composes with effects.

Lorenzen, White, Dolan, Eisenberg and Lindley's [*Oxidizing OCaml with Modal Memory
Management* (2024)](https://richarde.dev/papers/2024/modes-3/modes.pdf) separates
locality, uniqueness and affinity. Lemma 3.1 requires context addition to be defined for
substitution, preventing incompatible unique uses. Section 3.7 generates mode
inequalities for inference; Lemmas 4.1–4.2 prove progress/preservation with store and
frame invariants. Its reusable lesson is that substitution and sharing require explicit
context laws. Its memory guarantees concern this operational model.

Georges and coauthors, including Dolan, [*Data Race Freedom à la Mode*
(2025)](https://plv.mpi-sws.org/drfcaml/paper.pdf), is especially relevant to extension
stability. Theorems 5.1–5.3 connect rule compatibility, semantic typing and data-race
freedom through an Iris model formalized in Rocq. Section 6 says existing compatibility
proofs depend on the semantic-type conditions of Definition 5.1, rather than a fixed
type syntax. New types require interpretations satisfying those conditions and
compatibility proofs for new rules. This supports the Capsule API despite its unsafe
casts; the core theorem alone does not justify those casts. Lemma 5.4 separately
establishes semantic preservation of context locks.

Dolan's [*Rethinking the Value Restriction*
(ML2024)](https://icfp24.sigplan.org/details/mlworkshop-2024-papers/3/Rethinking-the-Value-Restriction)
is currently an abstract-level lead here: the workshop abstract proposes reformulating
ML with references and value restriction after identifying failed standard assumptions.
No detailed theorem assessment is claimed. It belongs in follow-up work on mutation,
generalization and preservation under language extension.

## Adoption and author effort

| Choice | Recommendation and expected author work |
| --- | --- |
| Explicit designated evidence | **Adapt through #257.** Authors choose maps, laws and observations. Function adaptation needs a domain map and a codomain map; a dependent restriction additionally needs evidence transport. Identity/composition wrappers can be shared without hiding unequal paths. |
| Optional subsumption in a selected fragment | **Investigate conditionally through #260.** Authors may omit structural coercions and intermediate upper-bound annotations after the fragment's semantics and coherence are checked. A solver must return evidence or expose residual obligations, rather than treating success as an axiom. |
| Global implicit subtyping across settings | **Defer.** There is no single interpretation here validating every Boolean lattice, recursive-type, equality, resource and dependent-context law reviewed above. Requiring it would narrow admissible settings and hide incompatible coercion paths. |

These are predicted obligations, not measurements from an author trial. On the
selection example, the direct route supplies a common result type and two maps;
a successful assisted route could infer the upper bound and insert certified
maps. On `Fin m → Fin n`, assistance may discharge a chosen arithmetic fragment
but must leave an explicit `m ≤ n` obligation outside it. On the diamond,
assistance must report ambiguity or request a named route; silently selecting a
path must be documented as policy and cannot claim coherence.

Use the same examples for #257's direct/assisted trial. Record supplied
annotations, explicit witnesses, coercions inserted, failed obligations and
whether the generated term has the same declared observation. Runtime traversal
or representation changes must be counted separately from source concision.
The existing [elaboration contract](../../Applications/Elaboration/Elaborator.lean)
separates resolution, semantic fidelity, obligations and target typing, but its
current two-type fragment is not an implementation of this subtype experiment.

## A bounded optional inference experiment

The proposed first scope for [#260](https://github.com/VladimirMarko/conaled/issues/260)
is a nondependent structural fragment with atoms, products, arrows and explicit
join/meet bounds. Exclude negation, recursive types, impredicative polymorphism,
mutable effects and arbitrary refinement predicates initially. This is a reduced
experiment informed by algebraic subtyping, not a claim to implement MLsub,
Simple-sub or SuperF in full. #257's evidence/variance experiment must establish
the reusable interpretation interface before activation.

Its **declarative target contract** must specify:

1. A type preorder with designated joins/meets, their universal bounds and the
   exact equations used by the solver, including whether distributivity is
   required. If types are quotiented by equations, interpretations must respect
   that quotient; merely computing a syntax normal form is insufficient.
2. A carrier interpretation and coercion for each subtype derivation, preserving
   identity/composition and the chosen semantic equivalence. Parallel derivations
   must agree for any implicit conversion claimed coherent.
3. Product covariance and function pre/postcomposition with the stated variance.
   Do **not** add MLsub's arrow-intersection equation to an arbitrary function
   interpretation; the SuperF example is a required rejection test.
4. Join introduction/elimination and meet use with interpretation equations.
   A tagged sum can realize explicit branch injection but is not automatically
   an idempotent semantic union. Ordinary functions between arbitrary types do
   not themselves supply a thin subtype category or the required lattice.

These are obligations to construct and test, not postulates to add to Lean. The
present library has [composable model preservation](../../SquareKit/STLCNaturality.lean),
[logical relations](../../SquareKit/STLCRelations.lean),
[relational requirement transport](../../SquareKit/RelationTransport.lean) and
[dependent base change](../../SquareKit/DependentBaseChange.lean); it does not
already provide this type algebra with coherent joins. A target failing those
laws excludes the corresponding inference fragment while remaining a valid
setting for other constructions. This missing target is why this assessment
alone does not unblock #260.

After constructing such a target, implement constraint generation and a bounded
solver that emits checkable derivations. First prove successful results satisfy
the declarative judgment and preserve meaning. Treat termination, completeness
and principal results as separate deliverables, with the grammar and annotation
policy in their statements. Do not import any reviewed paper's completeness
claim merely because its worklist algorithm looks similar.

Retain positive tests for higher-order variance, the `select` join and record
width when records are added. Test extension by a fresh base type while
preserving old derivations and meanings. Negative tests must include the
incoherent diamond, missing join laws, the incompatible arrow-intersection
law, and a dependent `Fin` constraint reported as outside the fragment. Read/write
cells remain a subsequent effect/invariant test, not an accepted consequence of
having positive and negative type variables.

This sequencing preserves the option to stop at explicit evidence if assistance
adds no useful author benefit. #258 resolves the adoption comparison; #257 owns
checked variance/evidence, #260 the conditional elaborator, #116 surface design,
and #235 the compatibility of interpretations. No additional broad implementation
issue is needed. This research adds no Lean declarations and reproduces no
external compiler or proof artifact; source results, paper examples and local
proposals are distinguished above.
