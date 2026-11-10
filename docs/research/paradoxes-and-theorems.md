# Paradoxes as sources of theorems

Logical paradoxes often supply constructions that become nonexistence,
undefinability, incompleteness, or fixed-point theorems once their assumptions
are made explicit. This note collects those connections, their hypotheses,
and sources for further investigation. It covers diagonal and self-reference
arguments, including size obstructions relevant to sets, categories, and
surreal numbers. It does not assert a theorem about every kind of paradox.

## Historical starting point

Gödel wrote: “Every epistemological antinomy can likewise be used for a similar
undecidability proof.” See
[On Formally Undecidable Propositions, Meltzer translation](https://gtts.ehu.es/German/Docencia/2021/MTBYC/pdf/Godel.pdf),
p. 40, footnote 14. The surrounding passage connects his incompleteness
argument with Richard's paradox and the liar. The remark concerns
undecidability proofs; it is not a general guarantee that every paradox yields
a powerful theorem.

Three kinds of connection occur below:

- **Nonexistence:** the contradictory construction proves that an object with
  specified properties cannot exist.
- **Adaptation:** replacing a notion such as truth with formal provability
  turns the construction into a different mathematical argument.
- **Abstraction:** identifying the shared construction yields a theorem with
  both limitation and positive fixed-point applications.

A shared proof pattern does not establish that one result historically
inspired another. The sources below distinguish those claims where relevant.

## Diagonalization and Lawvere's fixed-point theorem

Lawvere's [Diagonal Arguments and Cartesian Closed Categories](https://www.its.caltech.edu/~matilde/LawvereDiagonalArgCartesianClosedCats.pdf)
unifies arguments of Cantor, Russell, Gödel, and Tarski. In a cartesian closed
category, a weakly point-surjective map `e : A → Y^A` implies that every
endomorphism of `Y` has a fixed point. Weak point-surjectivity means that each
map `A → Y` is represented by a global element of `A`, at least in its values
on global elements. See §1 for the precise categorical formulation.

The set-based proof exposes the construction. If `e : A → Y^A` is surjective,
then for any `h : Y → Y`, the function `g(a) = h(e(a)(a))` is `e(b)` for some
`b`. Consequently `e(b)(b) = h(e(b)(b))`, giving a fixed point of `h`.

Thus diagonalization produces fixed points when the representation hypothesis
holds, and rules out such representation when `Y` has an endomorphism without
fixed points. Boolean negation supplies the latter case. In categorical
applications, which maps count as morphisms is part of the hypothesis.

## Size obstructions

### Russell's paradox and Cantor's theorem

Russell's paradox asks for the set of all sets that do not contain themselves.
In ZF, if a set `V` contained every set, Separation would give
`R = {x ∈ V | x ∉ x}`. Since `R ∈ V`, we would have `R ∈ R ↔ R ∉ R`.
Thus no universal set exists. This conclusion depends on the comprehension
principles of the setting; it is not a prohibition on every alternative set
theory with a universal set. Lawvere treats the membership-relation version
in §2 of the paper linked above.

The barber story has the same logical shape: a barber shaves exactly those
people who do not shave themselves. If the barber belongs to that population,
the condition contradicts itself when applied to the barber. The conclusion
is that no such barber exists.

**Cantor's theorem** states that no function `f : A → P(A)` is surjective,
where `P(A)` is the power set of `A`. Form `D = {a ∈ A | a ∉ f(a)}`;
`D = f(d)` would imply `d ∈ D ↔ d ∉ D`. The missing subset exists for every
proposed enumeration. This is a shared diagonal construction, rather than a
claim that Cantor historically derived his theorem from Russell.

### Freyd's theorem on small complete categories

**Freyd's theorem:** a small category admitting all small limits is a preorder.
If two distinct arrows `X → Y` existed, a product of copies of `Y` indexed by
all arrows would yield more arrows than the category has. See
[Ruiyuan Chen's notes](https://rynchn.github.io/math/math595-2019fa.pdf),
Theorem 21.27. This applies Cantor's argument to obtain a structural conclusion.

The scope of “small” is shared by the category and its limit indexing diagrams.
The theorem does not assert that a large category with all small limits is a
preorder, or that a small finitely complete category is one.

### Surreal cuts and proper-class size

For any set `S` of surreal numbers, the cut `{S | ∅}` is a surreal greater than
every member of `S`. Hence the surreals form a proper class, and no set of
surreals is cofinal in that class. The cut construction takes sets of options;
applying it to the entire proper class is not allowed. See the construction in
[Schleicher and Stoll, An Introduction to Conway’s Games and Numbers](https://arxiv.org/abs/math/0410026).
This deduction identifies the failed hypothesis in an attempted construction
of a surreal greater than every surreal.

## Truth, provability, and incompleteness

Here `T ⊢ A` means that theory `T` proves sentence `A`, `⌜A⌝` denotes its
Gödel code, and `Prov_T(⌜A⌝)` is the usual arithmetized provability predicate.
`PA` denotes Peano arithmetic and `⊥` denotes falsehood. Hypotheses differ
between the following results; consistency and soundness are not interchangeable.

### The liar: undefinability and first incompleteness

The liar sentence asserts its own falsity. With a truth predicate applying to
all sentences of its own language and satisfying the unrestricted truth
biconditionals, it is equivalent to its own negation.

**Tarski's undefinability theorem:** arithmetical truth in the standard natural
numbers is not arithmetically definable. A purported truth predicate permits
diagonal construction of a sentence equivalent to its own untruth.
[Salehi's research paper](https://arxiv.org/html/2009.00315v2) distinguishes
semantic and syntactic forms and proves connections with diagonal lemmas.

**First incompleteness** uses provability in place of truth. The Gödel sentence
says that it has no proof in `T`. For a consistent effectively axiomatized
extension of PA it is unprovable; the usual original argument needs a stronger
assumption to show its negation unprovable. Rosser's refinement gives
incompleteness from consistency alone. Salehi's paper also derives
Gödel–Rosser incompleteness from syntactic undefinability.

### Curry's paradox, Löb's theorem, and second incompleteness

**Curry's paradox** uses a sentence saying that if it is true, then an arbitrary
sentence `A` holds. A sentence `C` satisfying `C ↔ (C → A)` lets ordinary
implication reasoning derive `A`. Löb uses a sentence with
`L ↔ (Prov_T(⌜L⌝) → A)` instead.

**Löb's theorem:** if `T ⊢ Prov_T(⌜A⌝) → A`, then `T ⊢ A`, for theories
supporting the diagonal lemma and the standard derivability conditions.
The condition is that `T` proves this implication. External confidence in
`T`'s soundness does not suffice.
[Löb's original paper](https://math.umd.edu/~laskow/Pubs/713/Lob.pdf),
pp. 116–117, proves the theorem and gives the corresponding truth-based paradox.

Taking `A = ⊥` gives **second incompleteness**: a consistent effectively
axiomatized extension of PA cannot prove its usual arithmetized consistency
statement `Con(T) = ¬Prov_T(⌜⊥⌝)`. Otherwise Löb would yield `T ⊢ ⊥`.
The original paper also answers Henkin's question: a sentence provably equivalent
to its own provability is provable. Such a sentence is a provability analogue
of the truth-teller; it is not itself a contradiction.

### Surprise examination: another proof of second incompleteness

In the surprise examination paradox, students are promised an exam on an
unexpected day. They rule out the last possible day because, if it were reached
without an exam, its occurrence would be predictable. Repeating that reasoning
backward appears to rule out every day.

[Kritchman and Raz](https://www.wisdom.weizmann.ac.il/~ranraz/publications/Pincompleteness.pdf)
give a proof of second incompleteness using Kolmogorov complexity, Chaitin's
theorem, and an argument resembling this backward elimination. This is a later
proof, not Gödel's original route. The authors also propose a resolution of the
paradox; their theorem does not settle every interpretation of the story.

## Description length: Berry's paradox and Chaitin's theorem

Berry's paradox considers the least positive integer that cannot be described
in fewer than a specified number of words. For a sufficiently large bound,
that description itself appears to use fewer words than the bound allows.
Replacing informal describability with program length makes the limitation
precise.

**Chaitin's incompleteness theorem:** fix a universal machine and a sound
effectively axiomatized extension of PA. There is a bound beyond which the
theory proves no individual lower bound on Kolmogorov complexity. Searching
proofs for a claimed counterexample would itself describe that counterexample
too briefly. Soundness is a sufficient assumption here; sharper formulations
weaken it. [Chaitin's own exposition](https://arxiv.org/html/chao-dyn/9406002)
develops this connection.
