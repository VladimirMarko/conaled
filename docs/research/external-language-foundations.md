# External foundations for a setting-parameterized language

Research date: 2026-11-04. This is the foundations part of
[#235's external comparison](https://github.com/VladimirMarko/conaled/issues/235#issuecomment-6530272680),
read against [the language ambition](../language-direction.md#selecting-research-by-semantic-requirements).
The discovery question is: what can make mathematical assumptions, meanings and
admissible arguments parameters of a language? Selection began with that question,
before comparison with the repository's preservation interfaces. The approaches
below can change the architecture, rather than merely supply additional clients.

“Source result” identifies the reviewed literature's claim. “Proposed comparison”
identifies our experiment or inference. None of these comparisons has been run as
an author trial or implemented here. Paper derivations, explicit translations and
countermodels are valid first outcomes; a small Lean example is not an admission
condition. The [computational comparison](external-computational-semantics.md) covers other
semantic commitments; the [synthesis](external-language-comparison.md) records
local fit and proposed follow-up priorities.

This completed first-pass note is retained evidence for
[#280's completed assessment](external-discovery-assessment.md), which selects
#286/#287 and records deferred comparisons under #235. This first-pass note's
proposed comparisons remain evidence, not completed experiments.

## Current coverage

The [#350 coverage map](semantic-traditions-coverage.md) reconciles these
first-pass leads with completed #295–#301 and #337–#342 results. #343/#344 own
current institution and generic-calculus experiments; #351/#352 own the distinct
adjoint quantifier and mode-based compiler successors. Local-universes and
modal/higher variants retain explicit applicability conditions there.


## Institutions: change the logic while retaining theory structure

**Source result.** Goguen and Burstall's institution consists of signatures,
sentences, models and satisfaction, with sentence translation covariant and model
reduct contravariant. For a signature map `σ : Σ → Σ'`, its satisfaction condition
is `M' ⊨ Sen(σ)(φ)` iff `Mod(σ)(M') ⊨ φ`. This preserves truth under change of
notation. The original paper develops theory composition and conditions for
cross-institution theorem proving. Bare satisfaction supplies no selected proof
or existential witness. These are the basic definition and abstract-level scope
in [Goguen and Burstall, *Institutions*](https://cseweb.ucsd.edu/~goguen/pps/ins.pdf),
JACM 39(1), 1992, pp. 95–146; the
[author's account](https://www-cse.ucsd.edu/~goguen/projs/inst.html) also describes
the variance explicitly. The earlier
[1986 report on charters and parchments](https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/)
explicitly adds sentence morphisms to represent proofs. That extension is
evidence that truth and proof transport are distinct requirements, not a license
to infer witness preservation from satisfaction.

**Proposed comparison.** Describe a parameterized mathematical module with one
equational instance and one witness-bearing logical instance. Specify signature
gluing, model reducts and sentence translations first. Then ask what extra data
transports an actual witness through two changes of setting. Count separately
the obligations for a module author and for the implementer of a new logic.
Reject any comparison that silently substitutes existence of a target proof for
transport of the source proof's data. An institution-based outer module layer
could subsume bespoke management of requirements while leaving richer internal
semantics necessary. A useful negative result would identify the exact
proof-enriched structure the outer layer lacks. Neither composable signature maps
nor theory colimits alone establish preservation of computational content.

Access limitation: the author PDF's extracted text is corrupt. This assessment
uses its abstract and the linked primary institutional records for broad claims;
it does not assert the hypotheses of a particular institution-morphism theorem.

## Logical frameworks and MMT: requirements as presented theories

**Source result.** Harper, Honsell and Plotkin represent judgments by types of
proofs in LF, a dependent typed lambda calculus. This handles binding and
hypothetical judgments and reduces checking represented proofs to type checking.
The claim is about the representation of logics, not automatic semantic adequacy
of every encoding. See the abstract of
[*A Framework for Defining Logics*](https://era.ed.ac.uk/items/d9cebf2b-52bd-4532-b848-7d0402f32cf5/full),
JACM 40(1), 1993, pp. 143–184.

Rabe and Kohlhase's MMT separates theory/module structure from foundation-specific
typing and equality. Views assign meanings to declarations; theory morphisms
compose. A foundation supplies typing and equality judgments (Definition 24),
and regularity supplies compatibility conditions (Definition 30). Structural
well-formedness deliberately omits some semantic checks, so it cannot certify
the correctness of a translation. See
[*A Scalable Module System*](https://www.kwarc.info/people/frabe/Research/mmt.pdf),
author preprint dated 2012-12-17, especially §§6–7, Definitions 24, 30 and 37;
published in Information and Computation 230 (2013), pp. 1–54. Page numbers in
the longer author preprint differ from the journal pagination.

**Proposed comparison.** Present a construction's requirements as a small theory,
instantiate it twice, then extend the theory with one extra principle. Require
the same proof expression to translate along a composite view. List the
declaration assignments and proof obligations required of the instance author,
including the foundation's equality. Run a second case where the new principle
is unavailable: the diagnostic must identify that principle rather than demand
unrelated structure. This could replace an expanding inventory of handcrafted
capability records with theory presentation and translation. It might also move
bookkeeping into a framework without improving the author's mathematical
interface. Compare both possibilities, and require an adequacy argument for the
selected LF encoding before treating framework proof checking as object-logic
soundness. The cited abstract does not establish such an encoding for our tasks.

## Adjoint categorical logic: quantify without erasing the semantic choice

**Source result.** Lawvere describes cartesian closed structure and quantification
through adjunctions. In the 2006 commentary, slices `C/X` carry proof bundles,
whereas their poset reflections record existence of deductions. For a locally
cartesian closed category with finite coproducts, substitution and its adjoints
express quantification; passage from proof bundles to propositions loses data.
The commentary distinguishes this from passage to ordinary subobjects in a
topos and discusses the additional role of choice. See
[*Adjointness in Foundations*](https://tac.mta.ca/tac/reprints/articles/16/tr16.pdf),
1969 article reprinted with author commentary in TAC Reprints 16 (2006), revised
2006-10-30, commentary pp. 1–2 and §3. This gives a semantic reason to distinguish
quantifiers whose values are propositions from constructions whose values retain
witnesses. It does not supply one preservation theorem for all doctrines.

**Proposed comparison.** Write the same argument twice, once producing a dependent
pair and once asserting its existence. Specify the context category, the fibers,
reindexing, and which adjoints each derivation uses. Give a change of setting and
ask which comparison maps are invertible and which merely provide implications.
Test substitution of the quantified argument explicitly, including the required
Beck–Chevalley square; do not assume that preserving the underlying category
preserves the adjunctions. The author should state “dependent sum” or
“existential proposition” without rebuilding the semantic distinction.

This comparison can fail an architecture that gives every existential statement
the same witness-erasing interpretation or every preservation map a symmetric
equality contract. It can also fail an overly demanding categorical interface
that asks an author for universal quantifiers in a construction using only
finite products. Those are alternative design risks to test, not defects
established about current code. A successful paper result identifies the weakest
explicitly justified structure for this argument and leaves requirement inference
as a separate question.

## Local universes: absorb substitution coherence at the model boundary

**Source result.** Lumsdaine and Warren's Theorem 3.4.1 takes a **full comprehension
category** satisfying condition `(LF)`. Definition 3.1.3 requires finite products
and dependent exponentials for specified display maps and product projections.
Weakly stable constructors then give strictly stable constructors in the split
replacement `C!`. The theorem lists sums, products, identity types, zero, unit
and W-types, with W-types relative to a stable class of products. Types in the
replacement use a local family plus a map selecting it; substitution composes
that map. Section 4.1 explains limits on extending the pattern, particularly
rules concluding type equalities. See
[*The local universes model*](https://arxiv.org/pdf/1411.1736v2),
arXiv:1411.1736v2, April 2015, §§3.1, 3.4 and 4.1. This is coherence under stated
hypotheses, not a theorem that every semantic structure can be strictified while
preserving arbitrary additional laws.

**Proposed comparison.** Choose a semantic model with substitution naturally
preserving a dependent constructor only up to comparison isomorphism. On paper,
interpret a dependent argument after two substitutions. Compare direct repeated
coherence proofs with one construction of a split model followed by ordinary
use. Keep identity types and their eliminators in the comparison; replacing
them with proof-irrelevant host equality would answer a different question.
Then add a proposed type equality rule and identify whether it lies outside
the lifting result. Record separately model-builder work, construction-author
work and the assumptions introduced by `(LF)`.

The architectural possibility is to replace repeated coherence management with
a reusable semantic completion. The failure condition is equally concrete: the
required model or extension may not satisfy the theorem. Even when it does, the
cited result alone does not give a functorial transport construction for every
weak map between models. That additional composition question belongs in the
comparison before adopting completion as a common boundary.

## Relational abstraction: reusable arguments across representations

**Source result.** Reynolds's abstraction theorem relates interpretations of a
typed term under related environments, with relations lifted through its type.
The general type-definition theorem permits higher-order exported operations;
when the abstract type does not occur in the result type, its identity-relation
case yields representation independence. For domains and recursion, §5 requires
complete relations, containing bottom and closed under directed suprema. Thus
adding fixed points changes the admissible relations. See
[*Types, Abstraction and Parametric Polymorphism*](https://www.cs.cmu.edu/~crary/819-f09/Reynolds83.pdf),
Information Processing 83 (1983), pp. 513–523, §§3–5, especially the theorem on
p. 517. The search index exposes that theorem and the domain discussion; the
scanned PDF has no extractable text. This assessment does not use the later
polymorphic discussion as a construction of unrestricted set-theoretic System F
semantics.

**Proposed comparison.** Specify a module whose exported operation accepts a
callback involving its abstract representation. Relate two implementations
without requiring a function between their carriers. Compare a single generic
client argument with explicit preservation proofs for each client. Add a third
implementation, then demand a statement of how the two representation relations
compose and whether their higher-order liftings support the desired conclusion.
Do not silently assume that relation lifting preserves relational composition.
Finally add recursion and ask which relations remain admissible.

This can challenge a design that handles only forward representation maps or
first-order operation compatibility. It can also expose the cost of making an
author supply logical relations at every function type. The intended successful
interface exposes the abstract module and its compatibility obligations while
deriving routine relational reasoning. A relational conclusion does not itself
preserve a chosen proof object, run time, or allocation: add each observation
explicitly if that is the task. This experiment concerns higher-order reuse,
not a claim that parametricity alone provides all changes of mathematical logic.

## Multimodal dependent type theory: settings change the context rules

**Source result.** Gratzer, Kavvos, Nuyts and Birkedal parameterize MTT by a small
strict 2-category of modes, modalities and transformations. Context locks govern
variable access. Its generalized algebraic presentation supplies initial syntax
and strict model morphisms; §5.3 explicitly requires preservation on the nose.
Dependent right adjoints provide models (§7), while §10 investigates internal
adjunctions and crisp induction. The canonicity argument in §6 assumes locks
preserve the empty context; the abstract's broad description must be read with
this restriction. See
[*Multimodal Dependent Type Theory*](https://arxiv.org/pdf/2011.15021v2),
arXiv:2011.15021v2, 2021-06-01, §§2, 4–7 and 10. Changing a mode theory supplies
modal interaction laws, but this result does not establish unrestricted
preservation under arbitrary weak model maps or arbitrary added axioms.

**Proposed comparison.** State one dependent construction using a variable that
must be crisp and another using an ordinary variable. Run the derivations with
two composable modalities and a specified 2-cell. Require the invalid variable
access to fail for a mathematical reason visible to the author. Compare a
mode-indexed judgment interface with adding modal operations to a fixed ordinary
context. Ask which laws must be supplied once by the mode-theory author and
which annotations remain in each proof. This tests whether the setting parameter
reaches the judgment structure, rather than just the interpretation of terms.

MTT is a candidate for replacing that part of the architecture. Its strictness
requirements and restricted canonicity argument are costs to compare, and a
desired weak interpretation may need additional mathematics. Neither a plausible
modal API nor successful elaboration proves that the intended model validates
its context restrictions. The discriminating artifact is a valid derivation,
an invalid counterpart, and the semantic account explaining their difference.

## Cubical identity: changes of setting must preserve higher evidence

**Source result.** Cohen, Coquand, Huber and Mörtberg give a dependent theory with
dimension names, restrictions, path types, composition and glueing, interpreted
in cubical sets. Univalence is derivable. Section 9 distinguishes path types from
an identity-type extension with the usual judgmental computation rule, and
describes selected higher inductive types. See
[*Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol069-types2015/LIPIcs.TYPES.2015.5/LIPIcs.TYPES.2015.5.pdf),
TYPES 2015 proceedings, published 2018, §§3–9, DOI
10.4230/LIPIcs.TYPES.2015.5. Its composition operation and cubical semantics are
specific structure. Derivability of univalence here does not show that arbitrary
models or ordinary proof-irrelevant equality can provide the same evidence.

**Proposed comparison.** Specify a dependent construction transported along an
equivalence of types, then along a second equivalence. Retain the resulting path
data and ask for the comparison between sequential and composite transport.
Add one higher path and track its boundary. The paper task must name which
equalities are judgmental, which are paths, and which carry still higher
evidence. Compare this with a contract reporting only equality of final values.
Failure to state the higher comparison is a useful result even before any
encoding work.

This could require a richer internal language and preservation layer. It does
not require changing Lean's kernel: an interpreted language can distinguish its
own identity structure. Whether such an interpretation gives an acceptable
author interface is unresolved. Model-builder obligations include cubical
structure and its laws; ordinary authors should use the justified equality
principles. A proposal must say where that division is implemented and how
existing set-level specializations are recovered without imposing higher
structure on clients that do not need it.

## Comparison boundaries and remaining discovery

The seven approaches occupy different boundaries: theory organization,
representation of judgments, interpretation of logical operations, substitution
coherence, representation abstraction, modal contexts and identity evidence.
They should not be ranked as interchangeable solutions. The proposed tasks
identify where combinations or replacements deserve investigation, without
concluding that one universal intermediate language exists.

For every task, record the exact argument, semantic assumptions, composite
interpretation, equality and witness contract, extension obligation, and author
actions. A paper comparison can reject an unsuitable contract; an implemented
comparison adds host-language and usability evidence. Keep those conclusions
separate. No local implementation limitation is established by this document.

This pass leaves realizability and tripos-to-topos constructions, categorical
abstract interpretation, enriched and quantitative doctrines, game semantics,
linear/noncommutative logical frameworks, displayed models, and general
type-theory metatheorems without substantive assessment. These are omitted
research directions, not rejected candidates. The effects/resource companion
may cover parts of this list, but omission here must not count against them.
The present selection favors foundations for dependent arguments and so retains
that bias. Follow-up discovery should ask which omitted tradition changes a
specific failed task before comparing more algorithms inside a familiar one.

The primary sources establish bounded mathematical results. They do not measure
this project's author effort, maintenance cost, or Lean encoding quality. Those
questions remain for the coordinated comparison under #235, #36, #200 and #8.
