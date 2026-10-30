# What constructor–destructor duality suggests for the language

Discussion and follow-up agenda, 2026-10-30. The owner requested preservation of
both findings and speculations after #256. #268 now supplies the bounded
composition result described below. The remaining proposals are research tasks,
not a selected universal language architecture.

## Evidence and conjecture

| Status | Claim | Boundary |
|---|---|---|
| Checked locally | #256 transposes intrinsically indexed equation bodies, swaps their parameter scopes, and proves both syntax round trips and exact denotational preservation. | Binding-free cells with total primitive interpretations; no arbitrary recursive source transformation. |
| Checked locally | #255 gives finite-word final behavior and exact finite parser/trie observations; #256 recovers its selected union/concat/star observations. | No equivalence between all finite syntax and all codata behaviors, or infinite-productivity/runtime-sharing theorem. |
| Checked locally | #268 derives composite interpretations and compatible substitution from local constructor laws in a finite-arity derivative-template format. | Ordinary type carriers and fixed outputs; fixed-fiber vector specialization, with index-changing/dependent observations owned by #271. |
| Existing literature | Decomposition diversity, bialgebraic semantics, Chu pairings and symmetric proof calculi supply related structures. | Their assumptions differ; no single source identifies all of them with our implementation. |
| Design inference | Constructor/observer interaction equations may support several verified program organizations and more explicit extension obligations. | Requires usable author routes and checked composition beyond the existing cell transformation. |
| Conjectural connection | A compatible account of construction, observation and proof transport may explain several current interfaces together. | Dependent results, witnesses, binders, recursion and changes of setting remain substantive tests, not details to erase. |

The existing [implementation record](constructor-destructor-transposition.md)
contains exact scope, source comparisons and statement review. The files
[EquationTranspose](../../SquareKit/EquationTranspose.lean),
[WordCoalgebra](../../SquareKit/WordCoalgebra.lean) and
[language transposition](../../Applications/Languages/Transposition.lean)
are the local evidence behind the first two rows.

## Program organization as a verified view

An equation such as

```text
observe_d(construct_c(x), y) = e[c,d](x,y)
```

can be organized around constructors or observers. The conjectured language
benefit is that authors could select the organization appropriate to their
current task while preserving the equations and their interpretations. A source
layout would then be a verified view of a supported specification, rather than
an irreversible choice about how to extend it.

This is motivated by [Decomposition Diversity](https://ps.informatik.uni-tuebingen.de/publications/ostermann20decompositiondiversity.pdf),
§§5–7, and the [indexed GADT transformation](https://ps.informatik.uni-tuebingen.de/publications/ostermann18dualizing.pdf),
§§2–4. Their scoping and admissibility requirements matter. Our #256 result
supplies a smaller intrinsic fragment; it does not implement their full source
languages. The direction is multiple useful views where their preservation laws
hold, not a mandatory equation-matrix IR for every fragment.

[#266](https://github.com/VladimirMarko/conaled/issues/266) owns the next concrete
test: complete the remaining parser rows, recover their observations, and compare
matched constructor-oriented and observer-oriented author tasks. This also gives
#8's omitted-row follow-up a scoped owner and informs #116's surface work.

## Observations belong in extension contracts

Adding a constructor requires its interactions with existing observers. Adding
an observer requires its interactions with existing constructors. This explains
local proof obligations, but preserving old cells alone does not settle the
meaning of equality after an observer extension.

For a fixed result comparison, define equivalence relative to a family of
observations. Enlarging that family can distinguish representations previously
identified. Boolean parser recognition and witness-sensitive parsing provide a
local motivation: acceptance agreement alone cannot recover the selected parse.
A new observer descends to an old quotient only if it respects that quotient's
relation. For dependent results, the required transport/comparison must be stated
before even formulating observer agreement.

This is a proposed proof obligation, not a new quotient theorem in this note.
It explains how an old theorem can remain correct under its original contract
while becoming insufficient for a richer one. Adding axioms is a separate change;
no preservation of consistency or arbitrary metatheorems follows from retaining
old equation cells.

[#267](https://github.com/VladimirMarko/conaled/issues/267) owns a checked
restriction theorem, compatible extension, and non-factorization counterexample.
[#262](https://github.com/VladimirMarko/conaled/issues/262) retains the distinct
semantic-type admissibility experiment. Together they should expose which old
assumptions remain valid, rather than silently changing the observations or
weakening an existing client.

## From local equations to composite behavior

Constructors supply algebraic structure; observations supply coalgebraic
structure. Derivative clauses describe their interaction. Concatenation's use of
both operand observations and the original right operand is an especially useful
test of a proposed general law.

[Turi–Plotkin](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
§3 equation (8), §5 Theorem 5.1, Proposition 5.1 and Definition 5.2, investigate
natural rules of shape `Σ(Id × B) ⇒ BT`, with syntax functor `Σ` freely generating
monad `T` and behavior functor `B`. Naturality and the stated categorical
assumptions support compatible semantic liftings. Further distributive-law and
denotational results need their additional hypotheses. This is a route connecting
operational and denotational semantics, not a reason to impose a fixed execution
model on our language.

[#268](https://github.com/VladimirMarko/conaled/issues/268) now supplies a
[bounded composition theorem](compositional-constructor-observer-laws.md).
Derivative templates explicitly distinguish original arguments from successors.
Their naturality is proved; local semantic compatibility yields a morphism for
arbitrary finite terms. Compatible substitution, leaf insertion and flattening
have separate checked laws. Exact embeddings recover the existing weighted
semantics, and pointwise multiplication adds one local compatibility case.
A deliberately incorrect concatenation rule remains natural but fails semantic
compatibility, so naturality alone does not establish the intended meaning.

The independent vector family retains its size index within each fixed fiber.
Index-changing constructors and dependent parser observations need a stronger
setting, owned by [#271](https://github.com/VladimirMarko/conaled/issues/271).
A table of typed handlers or #256's permutation alone does not supply these laws.
The experiment does not implement a general distributive-law framework or infer
compatibility automatically from transposed source cells.

## Pairings, variance and the limits of dual equivalence

A possible broader account starts with a pairing `e : X × Y → R`, interpreting
`X` as representations and `Y` as observations. For another pairing
`e' : X' × Y' → R`, forward representation transport `f : X → X'` and backward
observation transport `g : Y' → Y` can satisfy

```text
e'(f(x), y') = e(x, g(y')).
```

This is the Set specialization of Chu-map compatibility. [Barr's construction](https://www.math.mcgill.ca/barr/ftp/pdffiles/chucon.pdf),
§§2 and 4 and the morphism square preceding Proposition 5.7, supplies the
pairing-based structure and its categorical assumptions. Calling the two sides
representations and observations is our proposed application. It would connect
contravariance to the existing preservation squares if suitable instances fit.

A fixed result object does not directly capture every indexed witness family.
Tagged packaging, fiberwise structure, or another ambient category would require
construction and preservation proofs. Replacing the results with Booleans would
not satisfy the witness-sensitive use case.

Even with a pairing, mapping an object to all its observations need not be
invertible. Distinct objects may agree observationally; some functions on tests
may have no representing object. Separation and representability are questions
to investigate before claiming an equivalence. An exact program-organization
involution does not answer them, and initial syntax and final behavior must not
be identified merely because both appear in the same semantics.

[#269](https://github.com/VladimirMarko/conaled/issues/269) owns a source-backed
fit/mismatch assessment against existing squares, relations and #257's variance
interfaces. It may recommend an additional layer or reject the proposed fit;
it does not prescribe a universal Chu framework.

## Symmetric proof syntax and evaluation order

The Curry–Howard question is whether producers and their uses should both have
explicit status in the proof language. A symmetric presentation might connect
proof composition with constructor/observer interaction while retaining direct
natural-deduction clients.

[Binder et al.](https://arxiv.org/html/2211.13004v1), §§2.3–2.5 and 4–6, distinguish
data/codata polarity from evaluation order in a sequent-calculus presentation.
Transposition preserves evaluation order; shifts handle changes of strategy.
The eta laws have strategy-specific conditions, and core transposition requires
local matches on the transformed type to be lifted first. These qualifications
prevent inferring unrestricted eta equality from the data/codata analogy.

[#270](https://github.com/VladimirMarko/conaled/issues/270) owns a bounded design
assessment using the existing #203 Curry–Howard and #212 session examples,
coordinated with #116's surfaces and #145's codata findings. Any change in logic,
structural rules, control principles, equality or evaluation assumptions must be
explicit. A consumer is not automatically a constructive refutation. No decision
to replace the current calculus follows from this research direction.

## Priority and ownership

The first mathematical priority is explicit extension and composition laws:
#267 and #268, coordinated with #262. #266 can develop independently from the
existing checked syntax. #269 and #270 are bounded assessments whose negative
findings would be useful; they need not block local source-view improvements.
There is no artificial hard dependency among these investigations. #268 selected
a restricted template law; its indexed continuation #271 retains a design gate.

#235 owns cross-cutting applicability and recovery of existing specializations;
#36 owns internal-language and surface integration; #200 owns correspondence
research; #8 owns the categorical compilation side. Acceptance criteria live in
the linked issues. The checked #268 result is bounded as above; the remaining
agenda does not follow from it without further evidence.
