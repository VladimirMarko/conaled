# Mathematical suppression: recoverable views, abstraction, and discovery

Research note, 2026-11-14. This investigates a possible `conaled` feature;
it does not select an implementation or introduce a new library abstraction.
“Suppression” is used here as the user's umbrella term for omitting expression
details. The sources formalize several different operations under names such
as elaboration, coercive subtyping, coherence, anti-unification, and abstract
interpretation. This search did not establish a single standard theory with
exactly the requested scope.

The strongest starting hypothesis is **a family of views with explicit
contracts**. Some omissions recover the original expression from context;
some preserve only chosen observations; others suggest an analogy that still
needs proof. Keeping these contracts separate allows useful aggressive
simplification without treating every common simplified shape as a theorem.
A syntax-only restriction would exclude useful existing mathematics, while an
unrestricted semantic abstraction would permit vacuous connections.

## Benefits and dangers for reasoning

An expression can spend most of its visible space specifying carriers,
instances, indices, transports, or administrative operations. Omitting those
details can expose repeated operations and dependencies. This is a plausible
mechanism for reducing bookkeeping and finding a reusable construction, but
it is not a universal productivity result.

There is direct human evidence that presentation affects algebraic reasoning.
Landy and Goldstone manipulated visual grouping in algebraic validity tasks;
accuracy depended on whether grouping agreed with operator precedence.
Their experiments concern spatial layout, not a suppression feature. They
support testing the visible structure of notation rather than assuming
semantically equivalent presentations are cognitively interchangeable.
[Landy and Goldstone, *How Abstract Is Symbolic Thought?*, 2007](https://pubmed.ncbi.nlm.nih.gov/17576149/).

Gentner's structure-mapping account explains analogy by preserving relational
systems while setting aside many object attributes. It supplies a specific
hypothesis about the user's proposed benefit: retaining how objects interact
can expose a common construction across different domains. It does not make
the transferred inference deductively valid. This is a theoretical account
of analogy, not a controlled evaluation of Lean notation.
[Gentner, *Structure-Mapping*, 1983](https://groups.psych.northwestern.edu/gentner/papers/Gentner83.2b.pdf).

The associated danger is hiding a dependency needed to understand or modify
an expression. Green and Petre's cognitive-dimensions analysis treats hidden
dependencies, visibility, and abstraction as distinct usability concerns.
Applied here, shorter text can lower scanning effort while increasing the
work needed to recover why a term is well-typed. That application is our
inference, not their evaluation of this proposed feature.
[Green and Petre, 1996](https://citeseerx.ist.psu.edu/document?doi=ad745bd2f3147f486f4b447fa80a3d32d75f599a&repid=rep1&type=pdf).

Concrete dangers include:

- **Ambiguous reconstruction:** two hidden operations or instances fit the
  visible expression but compute different results.
- **False generality:** deleting a field, topology, dimension, or law makes an
  argument appear to require less structure than its proof uses.
- **Lost dependency:** independent-looking holes originally shared a variable,
  index, witness, or resource. Copying and discarding are not available in
  every mathematical setting.
- **Unstable context:** the same text elaborates differently after changes to
  expected types, imports, local instances, or notation.
- **Lost construction:** recording only the proposition proved can erase the
  selected witness or argument pattern that motivated reuse.

These are distinct failure modes. A kernel check can reject an ill-typed
reconstruction, but cannot establish that the accepted theorem says what the
author intended, or that the selected discovery result is useful.

## Existing rigorous mechanisms

| Mechanism | What can disappear | What justifies using the result |
| --- | --- | --- |
| Elaboration and implicit arguments | Type arguments, instances, annotations, some coercions | Reconstruction in a context, followed by checking |
| Coercive subtyping | An explicit conversion application | Coherence and definitional-extension results for a specified coercion system |
| Coherence and graphical calculi | Parentheses and structural isomorphisms | A theorem for the particular categorical structure and diagram equivalence |
| Anti-unification | Differing subterms, replaced by shared metavariables | Substitutions recover the inputs; least-generality within a stated fragment |
| Semantic abstraction | Distinctions irrelevant to an observation | A preservation or sound approximation theorem |
| Bidirectional views | Details omitted from an editable presentation | Update laws, often using the retained original source |

### Elaboration and implicit parameters

Lean already reconstructs partially specified expressions using unification,
instance synthesis, coercions, and expected types. The 2015 elaboration paper
is a primary account of these interacting mechanisms, rather than a proof
that any omitted information is inferable.
[de Moura, Avigad, Kong, and Roux, *Elaboration in Dependent Type Theory*](https://arxiv.org/abs/1505.04324).

Lean distinguishes ordinary, strict, and instance implicit parameters.
Ordinary implicits use unification; strict implicits change when inference is
triggered; instance implicits invoke type-class synthesis. Making something
implicit therefore changes an interface's reconstruction policy, rather than
deleting its argument from the fully elaborated application.
[Lean reference, implicit parameters](https://lean-lang.org/doc/reference/latest/Terms/Functions/).

A worked illustration is an explicit application `@id Nat 3` presented as
`id 3`. The argument determines the hidden type. By contrast, presenting an
explicitly typed empty list as `[]` needs an expected element type or further
context. These are explanatory examples, not newly checked repository
fixtures. Bidirectional typing makes the distinction systematic: checking
uses an expected type, while synthesis produces one. The expected type is
part of the information retained by the interface.
[Dunfield and Krishnaswami, *Bidirectional Typing*, 2021](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/).

A proposed contract for a recoverable view is:

```text
viewΓ(e) = v
reconstruct(Γ, expectedType, v) = success e'
e' ≈ e
```

The chosen equivalence `≈` must be stated: syntactic identity, definitional
equality, propositional equality, or equality of a particular observation
are different guarantees. Soundness of successful reconstruction does not
imply success on all views, uniqueness among possible reconstructions, or
preservation after a context change. A deterministic implementation can pick
one answer without proving that all valid answers agree.

### Making every parameter of a type implicit

This can be specified rigorously, but “of a type” needs a policy. A selector
could match the written type, its elaborated expression, definitional equality
to a chosen type, or a user-supplied semantic classification. These selectors
need not agree. Matching all binders of type `Type u`, for example, selects
carriers; it does not thereby select values inhabiting those carriers.
Matching all binders of type `Nat` can conflate lengths with ordinary data.

Consider the hypothetical telescope:

```text
(A : Type u) (n : Nat) (xs : Vector A n) (i : Fin n)
```

Hiding `A` and `n` at a call site can be recoverable from `xs` and `i`. The
binders remain in the elaborated term, and the types of later arguments still
depend on them. Removing those binders from the telescope instead requires
rewriting the dependencies. Hiding every `Nat` parameter also affects a
hypothetical `constant (n : Nat) : Nat`; a result expected merely to have type
`Nat` does not determine which value of `n` was intended.

A candidate experiment should therefore fix:

1. The telescope and environment in which selection occurs, including
   universes and dependent substitution.
2. Whether the transformation changes a declaration, builds a wrapper, or
   changes only a displayed call. These have different caller consequences.
3. Which inference mechanism supplies each omitted argument and what happens
   on failure or ambiguity.
4. A comparison with the original elaborated application, including its
   selected instances and dependent indices.

Changing binder metadata alone is a syntactic operation; deciding which
binders qualify and proving reconstruction can require typing and semantic
information. Lean's `BinderInfo` records the explicit/implicit distinction,
but this does not provide the proposed selector or its correctness theorem.
[Lean API, `Expr` and `BinderInfo`](https://lean-lang.org/doc/api/Lean/Expr.html).

### Coercions and coherence

Luo, Soloviev, and Xue formalize coercive subtyping as abbreviation and prove
conservativity and a definitional-extension result for their specified
system. Their revised account also repairs a gap in an earlier conservativity
argument. The result is evidence that suppressing conversions can have a
rigorous foundation; it is not a guarantee for arbitrary collections of
coercions or for Lean's entire elaborator.
[*Coercive Subtyping: Theory and Implementation*](https://www.cs.rhul.ac.uk/~zhaohui/Subtyping12.pdf).

Placement matters even for familiar arithmetic. Lean's documentation compares
subtracting two naturals after conversion to integers with converting their
natural-number difference. For inputs `4` and `8`, these yield `-4` and `0`.
Hiding the conversions can conceal this distinction. A policy must preserve
the actual operation and conversion placement, not just the apparent `a - b`
shape. [Lean reference, coercion insertion](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-Between-Types/).

Monoidal coherence is another rigorous model: associators and unitors allow
one to omit parenthesization bookkeeping under specified equations.
Strictification provides an equivalent strict presentation, not literal
identity of all original objects. String diagrams retain connectivity and
boundary types while omitting many expression constructors. Their permitted
deformations depend on the structure: planar, braided, symmetric, and traced
settings have different laws. A braid cannot be discarded just because a
symmetric drawing would allow it. Selinger gives the relevant coherence
statements and explicitly flags scope limitations.
[*A Survey of Graphical Languages for Monoidal Categories*](https://www.mscs.dal.ca/~selinger/papers/graphical.pdf).
For an original proof development, Wilson, Ghica, and Zanasi present non-strict
monoidal string diagrams by generators and relations, prove correctness,
and derive strictification and coherence, including canonical isomorphisms.
[*String Diagrams for Strictification and Coherence*, 2024](https://arxiv.org/abs/2201.11738v4).

For `conaled`, these are examples of semantic justification enabling concise
syntax. Point-free composition gives a smaller familiar example:
`fun x => g (f x)` exposes the same function as `g ∘ f`, once the function
interpretation and equality are fixed. Removing the variable name retains
its wiring. Generalizing that translation to other settings requires their
operations and laws, including any needed copying or discarding.

### Anti-unification and structural discovery

Plotkin's least general generalization is a term of which the inputs are
instances, and which is itself an instance of every common generalization.
This gives a principled alternative to arbitrarily deleting details when
looking for common structure.
[Plotkin, *A Further Note on Inductive Generalization*, 1971](https://homepages.inf.ed.ac.uk/gdp/publications/MI6_further_note.pdf).

For a worked first-order example, `f(a,a)` and `f(b,b)` generalize to
`f(X,X)`. Reusing `X` retains the dependency between the positions;
`f(X,Y)` loses it, and a single unconstrained hole loses the whole
construction. The substitutions `X ↦ a` and `X ↦ b` recover the inputs.
This is a structural certificate, not proof that every instance of `f(X,X)`
satisfies an interesting theorem.

Pfenning extends unification and anti-unification to a restricted
higher-order-pattern fragment of the Calculus of Constructions, with
least common anti-instances, when the typed inputs have a common upper bound,
unique up to a specified equivalence. Proof generalization is an intended
application. The paper treats uniqueness of canonical forms for the full
Calculus of Constructions as a working hypothesis. The restriction matters: this is
not an algorithmic completeness theorem for arbitrary Lean expressions,
unrestricted higher-order unification, or every semantic equivalence.
[*Unification and Anti-Unification in the Calculus of Constructions*, 1991](https://www.cs.cmu.edu/~fp/papers/lics91.pdf).

Discovery could return a pattern, the instantiating substitutions, and the
obligations for turning the pattern into a theorem. A common pattern alone
must remain a candidate connection. Dependent typing, binding, shared holes,
and the selected equational theory are part of its correctness question.

### Abstract interpretation and editable views

Abstract interpretation formalizes deliberate information loss using ordered
semantic domains and sound approximation. A Galois connection relates
abstraction and concretization; abstract operations require their own
soundness properties. Coarse domains can be sound but uninformative.
[Cousot and Cousot, *Abstract Interpretation*, 1977](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf).

For an illustrative abstraction, the sign of an integer forgets its
magnitude. Knowing two operands are positive determines a positive sum,
but knowing one is positive and the other negative does not determine the
sum's sign. A set of possible signs is appropriate; inventing a unique
reconstructed integer is not. This differs from omission of an inferable
type argument. A theorem about the abstract result must state the relation
to concrete results and its direction.

If users edit suppressed views, an additional problem appears: how to update
the full expression. Lens research explicitly retains a concrete source
alongside the modified view and imposes update laws. Retained source data
can make updates possible even when the view alone is not invertible.
This is relevant to a future editing feature, not necessary for read-only
views. [Bohannon, Foster, Pierce, and Schmitt, *Resourceful Lenses for Ordered Data*](https://www.cis.upenn.edu/~bcpierce/papers/resourceful.pdf).

## Empty suppression and the order of information

The following is a paper-level candidate formulation, not an implemented
`conaled` theorem or a claim of novelty.

Fix a source set `X` and a set-sized family of views with specified target
sets. A view is a function `q : X → V`. Define

```text
q ≼ r  iff  there exists h : V → W with r = h ∘ q.
```

Thus `q ≼ r` means **q retains at least as much information as r**. Identity
and composition of the factor maps establish reflexivity and transitivity.
If included in the family, the constant view into a singleton is greatest
in this orientation. Quotienting
views by mutual factorization gives a partial order. This does not assert
that an arbitrarily restricted family of admissible views forms a lattice;
closure and universal-property requirements would need separate proofs.

Every view identifies the sources in each fiber: `q(x) = q(y)`. An observation
`o : X → O` can descend to the image of `q` exactly when

```text
q(x) = q(y)  implies  o(x) = o(y).
```

Necessity follows by applying the descended observation to both sides.
Sufficiency defines the result on each fiber by its common observation.
Using the image or quotient avoids demanding arbitrary values outside the
image of `q`; a constructive implementation must still specify how it
represents and eliminates that quotient.

Consequently, if `o` distinguishes two sources, a constant view cannot
preserve `o`. This gives a mathematical guard against vacuity without banning
the constant view from the theory. It can remain a useful extreme case or a
sound abstraction that answers no discriminating question.

Literal deletion of string characters is another order: write `s ≼ t` when
`t` is obtained by deletion from `s`. The empty string is greatest with this
orientation. The deletion relation is not by itself an order of mathematical
meaning: it can destroy grammar and binders. A common deletion of two strings
always exists, so “they have a common suppressed form” conveys nothing if
empty output is allowed. The analogous span through a singleton is equally
uninformative for arbitrary semantic views.

An empty visible string need not mean no information remains. A context,
expected type, source identifier, or reconstruction certificate can retain
the entire answer. Any compression measurement must account for that retained
information and the cost of accessing it.

A proposed discovery policy should require a useful retained observation or
construction and return its certificate. Ranking can then consider preserved
operators, dependencies, proof reuse, ambiguity, and reconstruction cost.
Those are task-dependent selection criteria, not consequences of the
preorder. Banning empty text alone is insufficient: every expression could
instead map to the same visible token.

## Fit with the current `conaled` architecture

The [architectural guidance](../agents/architectural-quality.md) and
[language direction](../language-direction.md) require reusable constructions,
explicit assumptions, separate operations and laws, and checked recovery of
specializations. The current code supplies candidate components, not a
universal suppression interface:

| Existing component inspected | Possible reuse and boundary |
| --- | --- |
| [CoreSyntax](../../SquareKit/Internal/CoreSyntax.lean) | Binding-aware syntax, renaming/substitution laws, and a partial Lean decoder. It preserves universe data and accepts only `.default` binders. It is not an implicit-argument elaborator. |
| [DependentTheoryMaps](../../SquareKit/DependentTheoryMaps.lean) | Operation maps natural in substitution and local certificates for derivation transport. The `SyntaxMap` interface fixes variables and commutes with substitution. Constant erasure cannot fix distinct variables; hole insertion or context projection needs its own contract, not weakened map laws. |
| [Institution capabilities](../../SquareKit/Institutions/Capabilities.lean) | Forward evidence connections, separately requested reflection, proof maps, and exact or relational realizations. These express different preservation claims without asserting automatic recovery. |
| [Relational squares](../../SquareKit/Relations.lean) and [ADR 0002](../adr/0002-relations-and-synchronization.md) | Many-valued meanings can retain a relation instead of choosing a fictional unique decoder. A relation does not repair an invalid dependent substitution. |
| [DiagonalConstruction](../../SquareKit/DiagonalConstruction.lean) | Selected code, representation evidence, witness, and interpretation laws are separate. Its checked maps expose what a forgotten distinction can invalidate. |
| [DiagonalCoverage](../../SquareKit/DiagonalCoverage.lean) | Selected-row extension evidence or restriction to the image can replace blanket surjectivity when transferring representation. |

The [paradox research](paradoxes-and-theorems.md) asks about forgetting
quotation, universe, or self-application restrictions while retaining the
construction. The diagonal fixture makes the distinction concrete:
`d a = h (e a a)` retains the duplicated argument. Hiding the chosen code
while keeping only the fixed-point witness can lose recoverability. Preserving
evaluation on translated inputs does not alone establish representation at
new target inputs. Surjectivity is one sufficient condition;
`DiagonalCoverage.Extension` states a weaker selected-row obligation.
[Checked assessment](diagonal-construction-assessment.md).

Suppression could help discover this shared construction, display it, or
express a certified interpretation. These are separate applications. Erasing
restrictions until a paradoxical expression resembles a valid theorem does
not transport validity into the paradoxical setting. A useful result may
instead identify which proposed interpretation law is impossible.

No architectural change is selected here. First compare native examples with
existing syntax and preservation interfaces. As an experimental adoption criterion, require at least two concrete routes
to reuse a proposed shared abstraction's laws without hiding their assumptions. Do not force an inferential surface view and a lossy semantic
abstraction through the same decoder. If a new interface is needed, its
remaining gaps include reconstruction, coherent ambiguity handling, policy
composition, and a measured discovery procedure; none follows merely from
naming it a square or functor.

## Evidence and experiments for agent users

LLM research gives motivation, not a demonstrated benefit for this feature.
*Lost in the Middle* reports position-sensitive retrieval and question
answering in the tested models and contexts. LLMLingua evaluates prompt
compression on several tasks. Neither establishes that suppressing Lean
parameters improves proof discovery, preserves intended statements, or helps
the agents available to this project.
[Liu et al.](https://arxiv.org/abs/2307.03172),
[Jiang et al.](https://aclanthology.org/2023.emnlp-main.825.pdf).

The agent hypothesis is that a concise structural view can reduce irrelevant
context and expose reusable patterns. The competing hypothesis is that
reconstruction calls, hidden assumptions, or less familiar notation increase
failure and total cost. Human perceptual results cannot decide this comparison.
Machine-readable source identities, selected instances, dependency maps, and
on-demand expansion may matter more than visual brevity.

A bounded experiment should compare these independently:

| Experiment | Positive case | Required negative case |
| --- | --- | --- |
| Recoverable parameter view | Infer carrier and length from a dependent argument | Unconstrained hidden natural parameter; changed local context |
| Coercion or coherence view | Preserve a certified conversion path or structural map | Natural versus integer subtraction; braided versus symmetric equality |
| Structural discovery | Recover `f(X,X)` and both instance substitutions | Reject a claim that unrelated shared holes prove a theorem |
| Observation abstraction | Preserve an explicitly selected observation | Reject constant-view preservation of a distinguishing observation |
| Paradox construction view | Retain duplicated input, selected witness, and local laws | Omitted target inputs invalidate unqualified representation transport |

For each route, retain the full source, policy, environment, reconstruction
result, and failed obligations. Test identity and composition of the proposed
operations at their actual scope, including renaming and capture avoidance
where binding is involved. Review statements before accepting proofs. These
are proposed future checks; this note has added no Lean definitions or tests.

For agent trials, freeze tasks, model/version, toolchain, documentation,
assistance, and resource budget. Compare full expressions, ordinary Lean
notation, and the proposed view using independent authors and held-out tasks.
Measure accepted intended proofs, false proposed connections, unresolved
inference, expansion requests, total tokens including retained context,
wall-clock cost, and reused proofs. Record preparation cost separately.
This follows the repository's [author-trial criteria](../language-direction.md#elegance-author-capability-and-language-constraints).

A useful first deliverable would be a small set of checked examples and
counterexamples under these distinct contracts, followed by an agent trial.
The research supports pursuing that comparison; it does not yet establish
which policy should become a library feature or that a new general framework
will outperform existing Lean notation and `conaled` interfaces.
