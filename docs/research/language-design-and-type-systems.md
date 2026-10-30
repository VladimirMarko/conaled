# Language design and type systems for compositional denotational programming

Research assessment, 2026-10-30, against conaled
`aa35d5a86b60dabd04dc5936f3d0817561fd7d60`.

The best fit is a language whose mathematical requirements and interpretation
maps are explicit, with inference algorithms attached to specified fragments.
The literature offers substantial support for this direction: categorical
internal languages, general metatheories, modular logical relations, algebraic
effects, multimodal type theory, and algebraic subtyping. None requires us to
adopt one fixed operational calculus as the meaning of all programs.

This is a broad, selective review, not an exhaustive bibliography or an adopted
architecture. It evaluates the owner's concern about **denotational** semantics
and extension stability, Elliott's language-derivative duality, Harper and the
correspondence workstream, and Dolan's subtyping programme. Recommendations below
are project judgments. Proposed mathematical experiments are not new checked
Lean claims. The [language direction](../language-direction.md) and
[embedded-language constraints](language-architecture-research.md) remain in force.

## What should survive an extension

The concern about brittle guarantees is justified, but several different kinds
of extension need separate contracts. Here is the distinction we should demand
from a proposed system, rather than treating compositionality as one property.

| Change | What can survive | What needs a separate argument |
|---|---|---|
| Add axioms while retaining judgments and inference rules | Every old derivation is still a derivation | Consistency and conservativity; which old models admit the extra axioms |
| Add primitive operations | A theorem parameterized by primitive preservation can be instantiated again | Semantics and preservation for the new primitives; whether new observations reveal previously hidden representations |
| Add type or term constructors | Old syntax may embed, with its old meaning | Substitution, equality, inference, normalization and logical relations for the enlarged calculus |
| Add reductions or definitional equalities | Existing derivations may embed under an explicit translation | Termination, confluence, decidable conversion, and preservation of distinctions |
| Change the mathematical setting | Arguments using preserved operations and principles can transport | Preservation of quantifiers, equality, witnesses and coherence; reflection is additional |
| Combine effects | Theories can describe interactions compositionally | Which interaction equations are intended and which interpretations satisfy them |

These distinctions are a synthesis of the judgment discipline in
[Harper's PFPL](https://www.cs.cmu.edu/~rwh/pfpl/), the explicit theory classes in
[Bauer, Haselwarter and Lumsdaine](https://arxiv.org/abs/2009.05539), and the
model/satisfaction viewpoint of
[Goguen and Burstall](https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/).
They are also visible in our existing
[preservation contracts](preservation-contract-inventory.md).

For a concrete mathematical example, adjoining an opaque constant `c : Nat`
without a computation rule leaves old proofs usable, but defeats the statement
that *every* closed natural-number term reduces to a numeral. It need not defeat
normalization: `c` can itself be a normal form. Adding unrestricted fixed points
has a different effect, permitting divergence. Adding an inconsistent axiom
preserves old derivations too, but destroys their use as evidence of consistency.
These are illustrative distinctions, not failures observed in this repository.

Model restriction is equally relevant to denotational designs. If theory `T'`
extends `T`, a `T'` model forgets to a `T` model, but a `T` model need not expand
to a `T'` model. Stronger assumptions can therefore reduce the settings in which
an argument applies. Requiring every model to expand would be a strong sufficient
condition for semantic conservativity, not something supplied merely by adding
axioms. Institutions make signatures, sentences, models and satisfaction explicit;
they do not provide executable proof transport or computational witnesses for free.

**Our design test:** state each reusable result relative to the operations,
laws, observations and structural rules it needs, then state separately which
extensions preserve those requirements. Denotational semantics itself does not
make extension stability automatic. Operational semantics remains useful for
adequacy, execution, productivity and cost claims that denotation alone cannot
establish.

## Harper and the correspondence work already in place

The current [Curry–Howard implementation](curry-howard-implementation.md) covers
an intuitionistic atom/truth/conjunction/implication fragment. In
[SquareKit/CurryHoward.lean](../../SquareKit/CurryHoward.lean), `Proof` retains a
compiler term and an admissibility certificate; `Program` shares that
representation. The round trips are identity functions, not a newly proved
bijection between independent calculi. `cut_compiles`, `cut_meaning` and
`detour_meaning` connect substitution and proof detours to compilation and
meaning. This is a useful bridge, with a deliberately limited scope.

[STLCNaturality](../../SquareKit/STLCNaturality.lean) already provides
`naturality`, `preserves_comp` and `naturality_comp`: local operation-preservation
obligations extend through the existing syntax and compose across model maps.
[RelationTransport](../../SquareKit/RelationTransport.lean) supplies a Galois
connection between possible-output images and universal input requirements.
Neither makes all logical principles transport automatically. The former still
has a fixed source grammar; the latter expresses partial correctness and permits
vacuous requirements when there is no related output.

Harper's work is relevant in three different roles:

- [PFPL](https://www.cs.cmu.edu/~rwh/pfpl/) supplies the discipline of defining
  judgments and their metatheory. Consult the relevant fragments and errata;
  adopting its presentation does not choose the project's semantic universe.
- [Harper, Honsell and Plotkin's LF](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf)
  represents object judgments and derivations using dependent types. Its adequacy
  question is essential: does the encoding represent precisely the intended
  proofs and substitution? Merely type-checking an encoding is insufficient.
- [Sterling and Harper's Logical Relations as Types](https://arxiv.org/abs/2010.08599v3)
  treats proof-relevant, phase-sensitive representation independence for modules.
  This addresses the owner's compositionality concern directly: a client theorem
  should not depend on private representations that it cannot observe.

The [existing Harper assessment](harper-methods-and-adaptation.md) already
compares LF, typed compilation, module phases, logical relations, calf/Decalf,
abstraction maps and potentials, cubical computation and gluing. The
[shared FIFO client](abstract-fifo-client.md) and
[modular cost contract](modular-fifo-costs.md) record bounded implemented
adaptations. The new question is how extending a language preserves those client
boundaries, not whether to repeat the same representation-independence proof.

Curry–Howard provides a connection between a specified logic and a specified
term calculus. It does not imply that every programming feature is a harmless
logical axiom. General recursion, effects, control, proof erasure and inspection
of representations change the relevant correspondence. The
[logic atlas](logic-correspondence-atlas.md) is the existing comparison across
linear, temporal, modal, dependent and other fragments. Keep its distinctions
between soundness, adequacy, equivalence and extraction.

## Literature families and their fit

The families overlap. A language can be dependent, graded, modal and effectful;
their metatheorems do not automatically combine. The recommendations concern
which mathematical methods to investigate, not wholesale adoption of a language.

| Family and primary reading | Useful structure and result | Fit and limiting assumption |
|---|---|---|
| Categorical logic and internal languages: [Jacobs, chapters 1–5 and 10–11](https://www.cs.ru.nl/B.Jacobs/CLT/bookinfo.html) | Fibrations organize context change, predicates, quantification and type dependency; comprehension connects predicates/types with extended contexts. | Foundational reading for our setting parameter. Select the structure needed by a fragment rather than requiring every setting to be a topos or locally cartesian closed. |
| General semantic metatheory: [Uemura, v3](https://arxiv.org/abs/1904.04097v3) | Within the paper's abstract notion of theory, bi-initial models and internal languages relate theories and models, including dependent and cubical examples. | Strong match for meaning-first language design. It does not promise automatic normalization or type inference for arbitrary extensions. |
| General syntactic metatheory: [Bauer–Haselwarter–Lumsdaine](https://arxiv.org/abs/2009.05539), [Haselwarter–Bauer](https://arxiv.org/abs/2112.00539v1) | Explicit classes of admissible rule presentations support generic weakening, substitution and other structural metatheorems. | Direct answer to repeated fragile metatheory. Check the presentation conditions for each extension; these results are not generic canonicity theorems. |
| Institutions and theory morphisms: [Goguen–Burstall](https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/) | Abstract signatures, models and satisfaction support logic-independent specification and changes of vocabulary. | Useful organizational contract for #200/#235. Satisfaction alone can discard proof identity, computational witnesses and cost. |
| Domain semantics and recursion: [Winskel's denotational semantics notes](https://www.cl.cam.ac.uk/~gw104/dens.pdf) | Orders, continuity and least fixed points give compositional meanings to recursion and partial computation. | Necessary comparison for recursive execution. Total-function semantics cannot simply acquire arbitrary fixed points; expose order/continuity and adequacy assumptions. |
| Call-by-push-value: [Levy's account](https://pblevy.github.io/cbpv.html), [adjunction models](https://pblevy.github.io/papers/ctcs02journal.pdf) | Distinguishes values, computations and thunks; factors call-by-value and call-by-name through an adjunction-based semantics. | Candidate effectful fragment or intermediate language. Its usefulness is compatible with denotational semantics; it need not become the universal syntax for geometry or proofs. |
| Algebraic effects and handlers: [Plotkin–Pretnar](https://arxiv.org/abs/1312.1399v2), [Hyland–Plotkin–Power](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/hpp06.pdf) | Operations and equations specify effects; handlers interpret a theory via models/homomorphisms. Sum and tensor describe different effect combinations. | Close fit to operations/laws/interpretation separation. Combining two effects requires choosing their interaction; arbitrary handlers need not respect every equation. |
| Multimodal dependent type theory: [Gratzer–Kavvos–Nuyts–Birkedal](https://lmcs.episciences.org/7713), [Gratzer normalization, v4](https://arxiv.org/abs/2301.11842v4) | Parameterizes modes/modalities and proves generic metatheory. Conversion/type-checking decidability is reduced to deciding the relevant modal equality. | A concrete counterexample to the idea that all type-system metatheory is tied to one fixed setting. Arbitrary added axioms are not changes of mode theory covered by the theorem. Compare with our existing modal/guarded consumers before adopting. |
| Linear, affine and quantitative dependency: [Atkey](https://bentnib.org/quantitative-type-theory.pdf) | Tracks variable usage with a quantitative dependent semantics. | Relevant to resource-sensitive proofs and erasure; a usage discipline is distinct from measured runtime cost. It cannot inherit unrestricted contraction without changing its contract. |
| Higher identity and cubical computation: [HoTT book](https://homotopytypetheory.org/book/), [Huber canonicity](https://arxiv.org/abs/1607.04156) | Higher paths preserve identity structure; cubical rules support computational treatment of univalence in a specified theory. | Needed comparison for settings with nontrivial identity. A groupoid model, an axiom of univalence and a cubical computational theory are different commitments. |
| Coalgebra and data/codata: [Rutten](https://ir.cwi.nl/pub/4802) and the derivative sources below | Observation, bisimulation, final semantics and changes between constructor/destructor organization. | Direct consumer in language derivatives and reactive systems. A finite observation theorem is not an unbounded productivity theorem. |
| Bidirectional elaboration: [Dunfield–Krishnaswami](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/) | Separates checking against an expected type from synthesizing a type, accommodating features that preclude complete inference. | Promising author interface around rich semantic fragments. Treat elaboration as a checked route with explicit remaining obligations, not the definition of which mathematics exists. |
| Morphisms between dependent types: [Najmaei–van der Weide–Ahrens–North, v2, §§3–4](https://arxiv.org/html/2503.10868v2) | Reflects morphisms in comprehension categories into syntax with dependent products, sums and identities; gives soundness and discusses coercive subtyping. | Especially relevant bridge between variance/subtyping and our semantic direction. The result is not an MLsub-style principal-inference algorithm. |

These sources supplement the [existing atlas](logic-correspondence-atlas.md),
which also covers session/process correspondences, proof search, temporal logic,
and staging. They are not mutually exclusive alternatives to it. Refinement,
semantic subtyping, coercive subtyping and algebraic subtyping are compared below.

## Elliott section 4.3 and the missing generalization

### What the cited duality says

Elliott §4.3 transposes the equations indexed by language constructors and observations (`nullable`, `derivative`). Symbolic parsing makes constructors data and observations functions; automatic parsing makes observations codata fields and constructors functions. Figures 6 and 8 contain the same equations grouped differently. This does **not** assert that the carrier of all tries is isomorphic to regular-expression syntax. The paper explicitly cites Ostermann–Jabs (2018). Its initial unsized trie concatenation bypasses termination checking; Figure 9 replaces that with sized tries. [Elliott, §§4.2–4.3](https://conal.net/papers/language-derivatives/paper.pdf)

Ostermann and Jabs formalize a calculus with GADTs and generalized algebraic codata, obtaining inverse transformations that preserve types and operational semantics. Their matrix representation explains the exchange of constructor-oriented and destructor-oriented decomposition. These are scoped metatheorems about their calculus, providing a precise starting point rather than a universal duality theorem for arbitrary languages. [Ostermann and Jabs, 2018](https://ps.informatik.uni-tuebingen.de/publications/ostermann18dualizing.pdf)

Binder, Jabs, Skupin and Ostermann develop symmetric data/codata language support and automatic changes between functional and object-oriented decomposition. This connects the derivative example to the expression problem and author-facing module organization. [Decomposition Diversity with Symmetric Data and Codata, 2020](https://ps.informatik.uni-tuebingen.de/publications/ostermann20decompositiondiversity.pdf)

### Verified local capabilities and actual gaps

The assessment follows code, not only ADR status:

- [Applications/Languages/Witnesses.lean](../../Applications/Languages/Witnesses.lean) defines `Language α := List α → Type u`, `derivative`, `derivativeWord`, explicit `Iso` with inverse laws, and witness-preserving concatenation/star isomorphisms. In particular `derivativeStarIso` retains `List (P [])` before the first consuming parse. `nullableStarIso` retains every list of empty parses.
- [Applications/Languages/Parser.lean](../../Applications/Languages/Parser.lean) has the indexed symbolic grammar, including union, intersection, scalar evidence, concatenation, star and transport. `Parser.nullable`, `Parser.derive` and `Parser.parse` implement the symbolic half. Its parser returns a witness or refutation, selecting one witness rather than enumerating all parses. Star selects the empty list for its nullable evidence.
- [Applications/Languages/Machines.lean](../../Applications/Languages/Machines.lean) has **Boolean** `Machine`, its two-field `Correct` contract, `run_correct`, a regex instance, a product-state intersection, bounded inductive `Trie α n`, finite unfolding and sufficiently-deep lookup correctness. Its snapshot builds a trie from symbolic derivative states. It does not independently implement all automatic operations over proof-relevant tries.
- [Applications/Languages/ParserBridge.lean](../../Applications/Languages/ParserBridge.lean) bridges witness inhabitation to Boolean recognition. [Applications/Convolution/](../../Applications/Convolution/) provides arbitrary semiring coefficients and word convolution. These are available specialization tests.
- The inspected language modules do not contain a general equation-matrix representation, verified transposition, an indexed proof-relevant automatic parser family, or generic distributive-law framework deriving both implementations.

[ADR 0004](../adr/0004-convolution-and-languages.md) accurately records the bounded automatic representation but is not evidence that the duality itself was formalized. Its termination-override discussion should be read alongside the paper's sized repair and the existing [codata research](codata-elaboration-termination-contracts.md), which already distinguishes finite observations, finality and productive execution. Extending the current representation need not contradict the ADR; replacing its bounded route would require explaining recovery of its existing guarantees.

### Precise proposed formalization, not established local theorems

Start with a semantic theorem independent of regex syntax. For types `A` and `O`, take `B X = O × (A → X)`. In sets (or ordinary Lean types with extensional function equality), the function space `L = List A → O` has structure

```
out f = (f [], fun a w => f (a :: w)).
```

For every coalgebra `c : S → B S`, define `run s [] = (c s).1` and `run s (a :: w) = run ((c s).2 a) w`. Structural induction on `w` proves it is the unique map satisfying `out ∘ run = B(run) ∘ c`. This gives a concrete final-coalgebra theorem without native coinductive definitions. It generalizes the existing Boolean run contract to arbitrary observations; no semiring, decidable equality, or finite-state hypothesis is needed. Computable finite observations additionally need executable `c` and `s`. The theorem does not promise memoization.

For algebraic operations and derivative equations, choose a binding-free signature functor `Σ`, its free term monad `T`, and a natural rule family

```
ρ_X : Σ (X × B X) → B (T X).
```

The original `X` arguments matter: the residual of concatenation refers to the unchanged right operand as well as derivatives. A narrower `Σ(B X) → B(Σ X)` interface need not express that rule or nested derivative expressions. Under the appropriate abstract-GSOS/distributive-law hypotheses, syntax and behavior fit one compositional construction. Turi and Plotkin develop precisely a parameterized connection between syntax, behavior, distributive laws and denotational interpretation; the word “operational” in its title should not exclude it from a denotational research program. [Turi and Plotkin, 1997](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf)

The proposed experiment should instantiate those hypotheses and prove the resulting interpretation laws, not assume arbitrary equation tables define productive operations. For Boolean languages first, compare the existing symbolic derivative interpreter with directly defined finite automatic operations using extensional observation equality. Prove agreement on every finite word. Separately prove truncation compatibility for all depths, so a family of snapshots actually describes one behavior.

Next retain semantic indices: a finite witness trie `WTrie P n` has root `Decision (P [])` and children `WTrie (derivative P a) (n-1)`. Define constructor combinators through the existing `Iso` lemmas and prove their finite-observation contracts. This is a proposed indexed extension; `B X = O × (A → X)` alone does not express the changing witness index. An indexed signature/coalgebra formulation and coherence of transport need their own work. Equality of the witness selected by two parsers is stronger than equal inhabitation; either preserve the same selection equations or state the weaker contract explicitly.

Suitable checked examples would be:

1. Boolean union/intersection: recover current recognition and product machines.
2. Semiring-weighted concatenation: recover the existing noncommutative derivative order `Dₐ(f*g) = scale (f []) (Dₐ g) + (Dₐ f)*g`. Do not silently add commutative multiplication.
3. Proof-relevant nullable star: take `P` recognizing the empty word with one witness. `Star P []` has a distinct witness for each finite list length; Boolean erasure collapses them all. A generic interface must preserve this distinction when requested.
4. An extension by one operation, with its new observation equations and preservation obligation. Show old equations and proofs survive through the signature inclusion. This tests modular extension concretely.

Weighted star over arbitrary semirings is not an automatic consequence: arbitrarily many empty factors can require infinite summation or extra closure structure. The word convolution theorem only uses finitely many binary splits. Likewise, arbitrary monoids do not inherit the list constructor decomposition or finite decomposition property. Generalize those pieces separately, exposing the relevant hypotheses.

A separate, longer experiment could formalize equation-matrix transposition in a small indexed calculus following Ostermann–Jabs. It should be scoped as a syntax/representation transformation theorem. The coalgebraic agreement theorem above establishes semantic agreement but does not itself establish such a source transformation or imply all inductive and coinductive carriers are isomorphic.

### Implication for the literature review

This case supports three distinct connections: proof-relevant parsing to Curry–Howard; constructor/destructor organization to data/codata and the expression problem; compositional derivative equations to distributive laws and bialgebraic semantics. Each has explicit assumptions and existing formal work. The useful research question is which of those assumptions the project's settings can supply, and which preservation maps retain them. It is not necessary to adopt a whole operational calculus to use its general compositionality theorem.

## Subtyping and variance

### What Dolan establishes

Dolan's *Algebraic Subtyping* dissertation (2016) develops ML-style polymorphism with subtyping, principal type inference and decidable subsumption through biunification. Its open-world concern is directly relevant: adding types should not invalidate formerly valid typings. Chapter 1 illustrates how reasoning by exhaustion over the currently available type constructors can fail under extension; its algebraic approach avoids making that closed-world assumption. This extensibility claim has a specified scope. It is not a theorem that arbitrary new axioms, reduction rules, dependent type formers or semantic interpretations preserve every metatheorem. Read the introduction's extension example, the type algebra, and Chapters 5–8 before treating its inference machinery as a general language foundation. [Dolan, dissertation](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf).

The shorter Dolan–Mycroft MLsub paper makes the benefit concrete. For `select p v d = if p v then v else d`, ordinary ML forces `v` and `d` to share a type. MLsub permits `(α → Bool) → α → β → (α ∨ β)`: only `v` is passed to `p`. The system distinguishes input and output types and simplifies principal types using the algebra of regular languages. This is a connection worth investigating alongside language derivatives, but a shared use of regular languages does not establish that the two constructions have the same duality. [Dolan and Mycroft, MLsub](https://api.repository.cam.ac.uk/server/api/core/bitstreams/d50b4d1a-a688-46eb-bb4f-9f4e204d0f60/content).

Thus “solves subtyping” is too broad. It solves a difficult combination of properties for a particular language and algebra, with useful ideas for other designs. Our research question should be which algebraic assumptions and preservation results survive the intended interpretations.

### Followups and their limits

| Source | Contribution | Consequence for conaled |
|---|---|---|
| [Yallop and Dolan, *First-Class Subtypes*](https://arxiv.org/pdf/1905.06546) (2019) | Encodes subtype witnesses as library values in OCaml and relates several encodings. A covariant lazy interface implemented using mutable storage motivates separating exposed variance from representation variance. | Especially close to our goals: investigate evidence and its composition before requiring pervasive implicit subsumption. This is followup work coauthored by Dolan. |
| [Parreaux, *The Simple Essence of Algebraic Subtyping*](https://cse.hkust.edu.hk/~parreaux/publication/icfp20/) (2020) | Simple-sub offers a simpler inference implementation and syntactic account; differential testing found bugs in the MLsub implementation. | Useful implementation and testing reference. A compact algorithm is not itself a replacement for semantic contracts. This is Parreaux's work, not Dolan's. |
| [Chau and Parreaux, *Boolean-Algebraic Subtyping* technical report](https://lptk.github.io/files/boolean-algebraic-subtyping.pdf), extending MLstruct (2022) | Extends the line with unrestricted union, intersection and negation types and principal ML-style inference. Its algebraic presentation permits rules that do not hold in a classical set-theoretic interpretation. | Treat Boolean structure and constructor rules as explicit assumptions. Do not silently identify these type connectives with every setting's internal logical connectives. |
| [Parreaux, Boruch-Gruszecki, Fan and Chau, *When Subtyping Constraints Liberate*](https://lptk.github.io/files/superf-tech-report.pdf) (2024) | SuperF supports first-class polymorphism using multiple subtype bounds. Termination uses a heuristic that rejects some valid programs; user annotations are restricted to System F syntax. | A useful candidate for elaboration experiments, with explicit completeness and annotation limits. It is not evidence that unrestricted inference is solved. |

SuperF supplies an unusually concrete extension failure. Its §2.4, footnote 9 (printed p. 48:9), explains that MLsub's treatment of an intersection of arrows as an arrow from the union of inputs to the intersection of outputs cannot simply be retained with first-class polymorphism. A polymorphic identity inhabits both `Int → Int` and `String → String`; it cannot generally return an inhabitant of `Int ∧ String` on either kind of input. The restriction is a property of the chosen algebra and typing discipline, and the paper states the failure rather than hiding it. [SuperF technical report](https://lptk.github.io/files/superf-tech-report.pdf).

A newer followup, *The Simple Essence of Boolean-Algebraic Subtyping: Semantic Soundness for Algebraic Union, Intersection, Negation, and Equi-recursive Types*, explicitly studies semantic soundness for this line, including MLstruct+. Its indexed publisher text was accessible, but direct DOI access was later blocked. It should be included in a deeper soundness review rather than assuming the older MLstruct account is the final word. [Publisher record](https://doi.org/10.1145/3776689).

### Variance does not force a global subtype relation

These distinctions are a proposed design decomposition for conaled:

- **Variance** describes how a construction acts on maps or ordering evidence. Given `i : A' → A` and `j : B → B'`, function space maps `f : A → B` to `j ∘ f ∘ i : A' → B'`. This already expresses contravariance in inputs and covariance in outputs, with no implicit subtype judgment.
- **Subtype evidence** can be a designated class of maps with identity, composition and constructor-lifting laws. If the language inserts these maps implicitly, different derivations need a coherence contract. Arbitrary maps should not all become invisible conversions.
- **Predicate restriction** selects elements satisfying a proposition. A dependent pair `Σ a : A, P a` may retain witness information; replacing it with a proof-irrelevant subset or a subobject requires further assumptions. In a higher setting, silently erasing witnesses may change the intended mathematics.
- **Refinement entailment** asks whether one predicate implies another. Arbitrary mathematical predicates do not inherit MLsub's decidable constraint solving merely by being called subtypes.
- **Conversion and equality** need their own treatment: a forgetful map is not an isomorphism, and neither automatically supplies the language's judgmental equality.

These choices are consistent with the repository's requirement to expose the structure a construction uses and preserve equality and witness distinctions. They suggest testing variance independently from the decision to offer global implicit subtyping.

A subtle warning: the induced map on function spaces above need not be injective, even when `i` and `j` are injective. Restricting functions to a smaller domain can identify functions that differed outside it. Therefore “all subtype coercions are monomorphisms” and “all function domains are contravariant under those coercions” need not be simultaneously valid in a chosen semantics. This is a mathematical design check, not a claimed defect of Dolan's system.

The [subtyping-contract comparison](subtyping-contracts-and-inference.md) follows
these leads at theorem level, compares common examples across interpretations,
and specifies the conditions for an optional inference experiment.

### The McBride lead

The remembered Agda talk remains unidentified. A verified nearby primary source is McBride's [*universe hierarchies*](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/) (2015), linking [slides from a 2011 talk](https://personal.cis.strath.ac.uk/conor.mcbride/Crude.pdf). It explains why treating subtyping as literal inclusion of set-theoretic function graphs motivates invariant domains: restricting a function's domain changes the graph. It then discusses contravariance and reusing constructions across universe-level settings that preserve their constraints. This is unusually close to conaled's direction. The post is a proposal, not a completed metatheory or documentation of current Agda behavior.

McBride's [2022 answer about Π/Σ variance](https://proofassistants.stackexchange.com/questions/1152/whats-the-benefit-of-having-pi-and-sigma-types-with-an-invariant-parameter) gives another direct lead: mandatory lambda annotations complicate subsumption, while checking lambdas bidirectionally avoids that particular obstacle. This answer does not identify the remembered talk. Neither source should be substituted silently for it.

### Proposed bounded investigation

**Recommendation:** keep subtyping optional at the foundational level while testing a small, explicit algebra of evidence. Decide surface subsumption from checked applications and author effort. This permits reuse of Dolan's insights without requiring every mathematical setting to validate MLsub's particular type algebra.

A useful experiment would have the following acceptance questions:

1. Can one variance argument specialize to ordinary maps, predicate implication in a fixed context, and a designated coercion interpretation, with assumptions stated separately?
2. Can a restricted-data example preserve its witness information through interpretation and substitution? Compare explicit evidence with inferred coercions on the same task.
3. Can an MLsub-like nondependent fragment elaborate into that semantic interface while preserving its interpretation? Record which joins, meets, recursive-type principles and arrow laws the target must supply.
4. Does adding a base type preserve old derivations and their meanings? Separately test an added principle, a new type former and a stronger equality rule; these are different extension questions.
5. Can a deliberately incompatible interpretation produce a precise missing obligation instead of changing the theorem silently? The function-restriction example above is a small test of an overstrong coercion contract.

A positive result would justify a fragment and identify its transport conditions. It would not decide full dependent subtyping, universal inference or an entire language architecture.

### The supplied video

James Faure's [Programming languages all secretly want one thing](https://www.youtube.com/watch?v=OenHweMNVeY)
was published on 2026-10-29. Its most relevant parts are:

- [10:04–13:38](https://www.youtube.com/watch?v=OenHweMNVeY&t=604s):
  extensible type lattices and the separation of semantics, typing specification
  and inference algorithm. This supports investigating Dolan's algebra before
  selecting an implementation.
- [19:54–21:20](https://www.youtube.com/watch?v=OenHweMNVeY&t=1194s):
  extensions and separate read/write bounds for mutable collections, a concrete
  variance example worth testing.
- [21:20–24:06](https://www.youtube.com/watch?v=OenHweMNVeY&t=1280s):
  dependent types and observational equality. Faure identifies the difficulty of
  context-dependent `Fin` subtyping and excludes arbitrary term equations from
  his inference ambition. Treat the proposed combination as a research lead,
  not an established dependent extension of MLsub.
- [24:06 onward](https://www.youtube.com/watch?v=OenHweMNVeY&t=1446s):
  record layouts and ABI design. These implementation proposals need separate
  representation and performance evidence.

The observational-equality lead connects to
[Altenkirch–McBride–Swierstra, Observational Equality, Now!](https://people.cs.nott.ac.uk/psztxa/publ/obseqnow.pdf),
which studies computational transport and extensional propositional equality.
Its compatibility with algebraic subtyping and our higher-identity settings
requires a separate investigation.

### Source access and attribution

The web reader initially failed to fetch the video. `yt-dlp` subsequently
retrieved its metadata and full audio; caption requests returned HTTP 429.
The audio was transcribed locally with whisper.cpp 1.8.4 and the `base.en`
model, then the transcript was inspected. This is machine transcription, not
publisher captions; mathematical notation and technical names can be mistranscribed,
and on-screen formulas were not inspected. The timestamped synopsis above
reports the spoken discussion; theorem claims rely on the primary papers.

The supplied thesis was read through PDF extraction. The Cambridge MLsub
preprint URL returned 403; its university repository copy supplied the primary
text. The exact McBride talk remains unidentified. Audio, metadata and the
transcript are research intermediates outside the repository; no Lean or
inference implementation was added.

### Alternative subtyping contracts to compare

| Approach | Meaning of the relation | Recommendation |
|---|---|---|
| Semantic subtyping, [Frisch–Castagna–Benzaken](https://www.irif.fr/~gc/papers/lics02.pdf) and [Castagna's later account](https://arxiv.org/abs/2111.03354) | Inclusion of type denotations in a specified set-theoretic model, with Boolean type operations. | Compare with Dolan's open-world algebra. A model-based definition is attractive, but its complement and function-space laws must not be imposed on every internal setting. |
| Coercive subtyping, [Luo–Soloviev–Xue](https://www.cs.rhul.ac.uk/~zhaohui/Subtyping12.pdf) | Implicit application abbreviates designated coherent coercions. The paper proves a conservative/definitional extension result under its specified framework and conditions. | Strong candidate for a dependent surface language. Coherence is part of the theorem's assumptions and construction, not a property of arbitrary user-supplied maps. |
| Definitional functoriality, [Laurent–Lennon-Bertrand–Maillard, v2](https://arxiv.org/abs/2310.14929v2) | Makes map identity/composition laws definitional and uses them to justify structural coercive subtyping and its relation to implicit subsumption. | Investigate as an object-language design. Its mechanized decidable-checking result is scoped to the dependent system with list functor laws; it does not authorize changing Lean's kernel equality. |
| Refinement inference, [Rondon–Kawaguchi–Jhala, Liquid Types](https://patrickrondon.com/research/papers/liquid-types-pldi08.pdf) | Predicate abstraction supports inference of logical refinements within a selected inference/logic discipline. | Useful optional automation for ordinary verification clients. Keep arbitrary predicates available through explicit proof obligations rather than claiming their entailment is decidable. |

The first two rows are especially useful controls for an MLsub experiment:
compare the same restricted-data and higher-order examples under set inclusion,
explicit coercions and algebraic constraints. The comprehension-category theory
in the broader survey supplies another comparison where type morphisms are
first-class. Similar notation does not establish equivalent semantics.

## Recommended reading and experiments

Read in the order of the questions we need to answer:

1. **What is the derivative duality?** Elliott §4.3, Ostermann–Jabs, then
   Turi–Plotkin. Recover the current parser as a specialization, and distinguish
   equation transposition from final-coalgebra semantics.
2. **What is a language parameterized by its setting?** Jacobs on fibrations and
   comprehension, Uemura on general semantics, and Bauer–Haselwarter–Lumsdaine on
   general rule presentations. Use the current internal-language and
   `STLCNaturality` interfaces as comparison cases.
3. **Which abstractions survive a new client or operation?** PFPL's judgment
   discipline, LF adequacy and Logical Relations as Types, alongside the existing
   FIFO/cost examples. Test extension boundaries rather than recreating those
   examples unchanged.
4. **Which meaning of subtyping serves authors?** Dolan's thesis and MLsub,
   First-Class Subtypes, coercive and semantic subtyping, then Simple-sub and
   SuperF. Compare dependent morphisms and definitional functoriality before
   selecting an inference architecture.
5. **Which computational structures should remain explicit?** CBPV and algebraic
   effects for effectful execution; MTT and its normalization result for modal
   setting changes; quantitative type theory for usage. Bring in domain and
   cubical semantics for the recursion and identity contracts actually needed.

The following are proposed follow-up scopes, not newly accepted tasks or a
required sequential implementation plan. GitHub Issues remain the owners of
acceptance criteria. Existing coordination points are
[#8](https://github.com/VladimirMarko/conaled/issues/8),
[#36](https://github.com/VladimirMarko/conaled/issues/36),
[#200](https://github.com/VladimirMarko/conaled/issues/200) and
[#235](https://github.com/VladimirMarko/conaled/issues/235).

| Proposed investigation | Evidence that would justify proceeding | Boundary that must remain visible |
|---|---|---|
| Derivative semantics and transposition | Arbitrary-observation run/finality theorem; symbolic/automatic agreement; Boolean, weighted and witness specializations; explicit signature-extension example | Generic GSOS hypotheses and indexed witnesses are additional work; no claim that regex syntax equals all behavior |
| Variance and subtype evidence | One construction used with maps, predicates and designated coercions; composition and substitution laws; explicit/inferred author comparison | Coherence, witness erasure, non-monic restriction and required arrow algebra |
| Extension preservation | Extend an existing fragment by a primitive or base type and recover old interpretation/client laws; include a failing extension with a precise unmet obligation | Separate old-proof embedding, semantic conservativity, canonicity, normalization and inference completeness |
| Optional algebraic inference | An MLsub-like nondependent fragment elaborates into a checked meaning-preserving interpretation, with representative join/meet examples | The target's laws, polymorphism restriction, annotation burden and unsupported dependent cases |

A useful extension test should include both success and failure. For example,
adding a primitive that preserves a representation relation should preserve a
shared client's proof. Adding an operation that exposes the private
representation should fail that relation obligation. Similarly, a new mode
within a framework's parameters and a new global axiom are different tests.
Record author effort, hidden casts and diagnostic quality alongside the proofs,
as required by the [language direction](../language-direction.md).

The current recommendation is to investigate **variance, coherent evidence,
generic extension metatheory and semantic interpretation first**. A particular
subtyping solver can then become one realization of a stated contract. There
is insufficient evidence to make global implicit subtyping, a universal type
lattice, or a single modal calculus mandatory for the language.

The [extension-metatheory assessment](language-extension-metatheory.md) now
compares the generic structural results at theorem level and gives primitive
and dependent-product extension contracts, including failed interpretations.
It recommends #259 as the first bounded formal experiment.

## Evidence and remaining limits

The focused derivative and Dolan assessments use paper text and local source
inspection. The broader map combines primary paper abstracts, introductions,
selected sections and author-maintained bibliographies; it is a reading and
fit assessment, not an independent reconstruction of all cited metatheorems.
The new MLstruct+ semantic-soundness paper deserves a full theorem-level review
before selecting its algebra. The supplied video was assessed through local
machine transcription, with the limits recorded above. The exact McBride talk
remains unidentified; no claims are attributed to that remembered talk.

Local source inspection does not replace the repository's build and proof audit.
This change adds research documentation only; it adds no Lean declarations,
changes no axioms and runs no external research artifact. Formal follow-ups
must use checked specializations, statement review and the applicable build/audit.
No GitHub issue was created or changed by this review.
