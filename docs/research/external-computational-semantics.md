# External comparison: computational semantics and reusable reasoning

Research date: 2026-11-04. This is discovery evidence for
[#235](https://github.com/VladimirMarko/conaled/issues/235), starting from
[the language ambition](../language-direction.md#selecting-research-by-semantic-requirements):
make the mathematical setting a first-class parameter of programming and proof.
The question is which semantic structures let authors reuse arguments, and what
information those structures require them to retain. Existing compiler support,
citation counts and ease of encoding in Lean are not selection criteria here.

Six traditions below were selected for different potential failure modes:
effect equations, recursion, pattern semantics, ownership, interaction and usage.
The source claims are restricted to named fragments. Paragraphs labelled
**Design inference** and the proposed tests are our analysis, not results claimed
by the cited authors. This comparison does not select a replacement architecture. The
[foundations companion](external-language-foundations.md) investigates changes
of logic and dependent setting; the [synthesis](external-language-comparison.md)
records local fit and proposed follow-up priorities.

## Algebraic effects and call-by-push-value

Plotkin and Pretnar's *Handling Algebraic Effects*, LMCS 9(4:23), 2013,
§§2, 4–7, treats operations together with an effect theory. Computations receive
free-model semantics; a correct handler supplies a model of the equations and
handling uses its induced homomorphism. The distinction between a syntactically
well-formed handler and a correct handler matters: equation preservation is an
obligation. Their §6 studies its decidability under specified restrictions; §7
only sketches the addition of recursion. The introduction explicitly excludes
continuations from the listed algebraic effects. These are denotational contracts,
not consequences of selecting an interpreter.
[Source PDF](https://lmcs.episciences.org/705/pdf).

Levy's *Adjunction Models for Call-by-Push-Value with Stacks*, TAC 14, 2005,
§§4–8, gives a separate candidate for the surrounding language. Values,
computations and stacks have distinct judgments; the model uses an indexed
adjunction and universal properties for the supported type constructors.
The equational theory is closed under substitution and stack composition
(Lemma 7.3), and §8 relates theories and models. §6 includes storage,
continuations and game models. Although stack-machine execution motivates the
presentation, these models supply meaning independently of running that machine.
The author's linked manuscript has a 2003 copyright header; section references
here refer to that PDF, not an assumed identical pagination in the journal.
[Author manuscript](https://pblevy.github.io/papers/ctcs02journal.pdf).

**Design inference.** This pair could replace a single undifferentiated category
of expressions with a language separating values from computations, while
making effects and their equations requirements of reusable code. Authors would
write operation clauses and prove only the equations needed by their handler.
Transport must respect the chosen value/computation distinction, substitution,
and effect equations. Merely preserving returned values cannot establish that
two effectful programs are equal. Combining handlers needs a stated interaction
contract; their existence individually does not justify swapping their order.
Proof-relevant results would require a specified data interpretation beyond
an equation between computations.

**Paper-only test.** Give choice the semilattice equations, then try a handler
that returns an ordered list of alternatives. For distinct `a` and `b`,
`[a,b]` differs from `[b,a]`; the handler must fail the commutativity obligation.
Try again with an ordered-choice theory. Compare how directly each candidate
language explains the failure and scopes the valid proof. A universal effect
interface that silently accepts both has lost a semantic distinction.

## Domain semantics and recursive constructions

Smyth and Plotkin, *The Category-Theoretic Solution of Recursive Domain
Equations*, SIAM Journal on Computing 11(4), 1982, pp. 761–783, §§2–4, develop
solutions through ordered categories and embedding/projection structure.
Theorem 2 relates the relevant limits and colimits; Theorem 3 uses local
continuity to obtain continuity on embeddings. This supplies conditions for
mixed-variance recursive domain constructions, rather than treating every
type expression as an ordinary covariant functor. §4 gives concrete categories.
The linked source is the joint 1982 paper, not Smyth's similarly titled 1976
technical report.
[Author-hosted journal PDF](https://homepages.inf.ed.ac.uk/gdp/publications/Category_Theoretic_Solution.pdf).

For term recursion, the Cambridge *Denotational Semantics* notes, 2008 edition
(Fiore; copyright Pitts, Winskel and Fiore), §§2, 4, 6–8, distinguish least fixed
points of continuous functions, admissible predicates for Scott induction,
compositional interpretation, and its relation to evaluation. §8 discusses
failure of full abstraction for the basic domain model of PCF. Thus existence
of a mathematical denotation and adequacy for execution do not automatically
identify denotational equality with contextual equivalence.
[Course source](https://www.cl.cam.ac.uk/teaching/0809/DenotSem/notes.pdf).

**Design inference.** A recursion-aware foundation could subsume finite
interpretation contracts when computations or types are recursively defined.
Authors must identify the order, continuity and induction conditions used in
their argument. A transport route needs preservation of the chosen limits or
fixed points, not only of the nonrecursive operations. If an invariant uses
Scott induction, the admissibility evidence belongs to the reusable proof's
requirements. Equality of finite observations needs a separate justification
before being promoted to equality of infinite objects. This family offers a
denotational account without making a machine the definition of meaning, but
does not itself supply higher identity or dependent witnesses.

**Paper-only test.** Ask for the fusion equation `h (fix f) = fix g` from
`h ∘ f = g ∘ h`. On the two-element chain, take `f = g = id` and `h` constantly
top. Commutation holds, but the two sides are top and bottom. The missing
strictness condition is visible before implementation. Then add continuity
and strictness and derive fusion through the approximation chain. Compare
whether each proposal exposes these obligations where recursion is introduced.

## Matching logic and equational specifications

Roșu's *Matching Logic*, LMCS 13(4:28), 2017, §2.3, interprets patterns as sets
of matching elements. Symbols denote functions into powersets; ordinary total
functions are a special case. Negation is complement, conjunction intersection,
and existential quantification union over valuations. §§5–7 distinguish
definedness, equality, functionality and algebraic/first-order specializations;
§9 treats separation logic. These set-theoretic interpretations do not require
an execution relation. Program reachability, when used, is an additional
semantic subject, not identical to satisfaction of a pattern. This entry concerns
the 2017 many-sorted first-order presentation, not every later system called
matching logic.
[Journal PDF](https://lmcs.episciences.org/4153/pdf).

**Design inference.** Patterns could replace a rigid separation between terms
and predicates in a specification layer. Authors could state partial and
relational operations without prematurely choosing total functions. However,
ordinary equality reasoning requires the appropriate definedness/functionality
conditions. A set of satisfying valuations records which witnesses work; it
does not distinguish different proofs of the same membership or supply higher
identity structure. A claim to subsume proof-relevant internal reasoning must
explain that additional interpretation. Transport of the whole Boolean logic
also requires more than operation preservation.

**Paper-only test.** For the noninjective map from `{a,b}` to `{*}`, the direct
images of `{a}` and its complement `{b}` are both `{*}`. Hence direct image
does not commute with complement. Ask each proposal to transport a proof using
negation, and demand that it identify whether inverse image, stronger map
conditions, or a positive fragment is needed. Separately compare a partial
operation's empty result with a Boolean false result. A design that confuses
them cannot safely reuse equational proofs. These tests concern model maps;
neither an SMT interface nor rewriting performance settles them.

## Separation logic and resource semantics

Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*,
LICS 2002, §§2–4, gives heap assertions whose separating conjunction requires
disjoint pieces. The frame rule extends a local Hoare specification with an
unaffected resource assertion, with a side condition on modified variables.
Its soundness uses properties of the command semantics; conjunction alone
cannot rule out aliasing. Assertions have a mathematical heap interpretation,
but the specified commands and their safety/partial-correctness behavior are
operationally grounded in this presentation.
[Author PDF](https://www.cs.cmu.edu/~jcr/seplogic.pdf).

Jung et al., *Iris from the Ground Up*, JFP 28(e20), 2018, §§2.1, 4–7,
separates a base logic from its derived program logic. Resource algebras and
their step-indexed counterparts account for ownership and valid updates;
ordered families of equivalences support the recursive model. §7.3's weakest
precondition is parameterized by a programming language and its reduction
relation; §7.4 establishes the corresponding adequacy result. Language
parameterization is therefore not independence from operational assumptions.
[Author-hosted journal PDF](https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf).

**Design inference.** Resource assertions and local reasoning could replace
a correctness layer based only on input/output relations where interference
and ownership matter. The language author must supply resource composition,
validity and permitted updates; a program-proof author supplies invariants and
resource splits. Preserving resource composition is insufficient if a
translation loses validity or the update protocol. The resource model might
complement independent denotational program specifications, with adequacy
connecting them to execution. Neither cited presentation establishes that any
base-language mathematical proof transports across arbitrary internal settings.

**Paper-only test.** Compare updating `x` while framing `y ↦ v`, first with
disjoint addresses and then with `x = y`. Require the framework to reject the
second precondition rather than prove an unchanged framed value. Then replace
physical ownership by an abstract exclusive token and repeat the local proof.
Record whether the shared proof uses heap addresses or only the resource laws.
Do not convert ownership evidence into an ordinary duplicable proposition.

## Games and interaction semantics

Abramsky, Jagadeesan and Malacaria, *Full Abstraction for PCF*,
Information and Computation 163, 2000, has an author-deposited version
arXiv:1311.6125v2, dated January 2014. In that version, §§2–4 construct games
and history-free strategies, an intensional model, and an extensional quotient.
Theorem 4.15 states full abstraction for PCF. Strategy composition accounts
for interaction through an intermediate interface; the quotient uses an
intrinsic observational preorder. These are different equalities, and the
full-abstraction theorem concerns the stated language and observations.
[Versioned author deposit](https://arxiv.org/pdf/1311.6125v2).

Levy's Definition 6.7 and Remark 6.8 give a separate comparison point: game models with
different bracketing restrictions fit his adjunction treatment. This is evidence
that a shared semantic organization can accommodate distinct interaction
disciplines, not permission to erase the restrictions.
[CBPV manuscript](https://pblevy.github.io/papers/ctcs02journal.pdf).

**Design inference.** Interaction could become the primitive semantic interface
for higher-order programs, replacing a foundation that observes only final
values. Authors would specify legal interactions and the strategy conditions
their reasoning needs. Transport must preserve those conditions and composition,
and state whether it preserves raw strategies or only an observational quotient.
If strategy data is the desired witness, passing to the quotient loses it.
No cited theorem licenses extension of PCF's full-abstraction result to arbitrary
effects, dependent types, or a larger set of observers.

**Paper-only test.** Compare `λf. f 0` with
`λf. ifzero (f 0) then f 0 else f 0`, using PCF's strict conditional and
`f : Nat → Nat`. First justify their observational equivalence for pure PCF,
including divergence, then compare the interaction strategies. Finally add a
call-count observation and ask whether the earlier equality still holds.
Require either a compatibility proof or a withdrawal of the old equality under
the new observation contract. A candidate passes by identifying which claim
survives; it need not force every observation into one equality. This is also a
test of whether constructor/observer syntax commits prematurely to a particular
control discipline.

## Quantitative dependent type theory

Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018,
§2.1.1, requires a positive semiring with the zero-product property for usage
accounting. Context addition combines use; multiplication accounts for nested
use. Usage zero permits information in types without computational use.
§2.3 repairs a substitution failure in the earlier formulation; §§3–4 give
quantitative categories with families and realizability models. The exact
fragment includes dependent function and tensor types, booleans and a universe
presentation, not arbitrary graded dependent syntax. Its models give a
semantic account of usage; a grade alone is not a runtime-cost theorem.
[Author PDF](https://bentnib.org/quantitative-type-theory.pdf).

**Design inference.** This could replace unrestricted structural rules with
an explicit usage parameter while retaining dependent reasoning. Proof authors
must distinguish type dependence from computational use; model authors must
supply the quantitative structure supporting substitution. A setting change
would need to account for the usage algebra, type interpretation and any
realizer contract together. Erasing annotations without a theorem could retain
extensional output while losing the promised resource behavior. Conversely,
making erased variables disappear from all judgments would destroy meaningful
dependent types. Adoption need not commit all fragments to resource accounting.

**Paper-only test.** Type a construction whose result type depends on a
usage-zero parameter. Substitute an expression for it, checking both dependency
and usage, then attempt to return that parameter as runtime data. The first
task should remain legal under the stated rules and the last should expose an
additional use. Repeat with a proposed change of grading semiring and require
an explicit substitution-preservation argument. Do not infer that every
semiring homomorphism automatically yields a model morphism.

## Comparison and remaining discovery

The common comparison task should be an argument plus its setting change,
not a benchmark program alone. Record four artifacts for each test: the
author's statement, the semantic requirements, the proposed interpretation
map, and the rejected variant showing why an assumption is necessary. Count
author-supplied definitions and proofs separately from representation
bookkeeping. Paper derivations can expose a missing law before any Lean
prototype exists; none of the tests above is claimed machine-checked here.

| Tradition | Potential architectural change | Evidence that would discriminate |
|---|---|---|
| Effects/CBPV | Separate values, computations and handlers | Equation-respecting handling across different models |
| Domains | Add recursion and approximation to interpretation | Fixed-point transport with necessary hypotheses exposed |
| Matching logic | Use patterns for terms and assertions | Preserve the selected logical fragment across model maps |
| Resources | Make ownership part of correctness | Reuse local reasoning beyond one concrete heap model |
| Games | Interpret higher-order behavior through interaction | Separate strategy witnesses from observational equality |
| Quantitative types | Parameterize structural use of variables | Preserve dependent substitution and erasure contracts |

These proposals need not compete for one universal layer. Effects and recursion
can interact, and resource or interaction models can instantiate a surrounding
language. Establishing such combinations requires laws connecting the structures;
the table does not establish them. Integration must also recover the repository's
existing distinctions between relations and dependent transport
([ADR 0002](../adr/0002-relations-and-synchronization.md)) and recognition and
parse witnesses ([ADR 0004](../adr/0004-convolution-and-languages.md)). Those
are later migration constraints, not the discovery filter used above.

This bounded comparison omits a substantive treatment of probabilistic and
measure-theoretic semantics, abstract interpretation and refinement calculi,
concurrency via event structures, differential and analytic semantics, and
rewriting logic as a distinct tradition. Matching logic does not stand in for
all rewriting semantics; QTT does not stand in for all graded effects or
coeffects. Institutions, fibrations, parametricity and multimodal dependent
frameworks belong to the companion discovery work. Further comparisons should
select omitted families by the obligations they expose, especially probability,
continuous behavior and concurrency, before choosing algorithms or tools.

Sources were checked through the linked primary PDFs, with definitions and
section boundaries inspected. No current-library compatibility theorem, author
usability trial, comprehensive bibliography, or completeness result for the
union of these fragments has been established. The next decision should select
contrasting tests and state what evidence would change that selection.
