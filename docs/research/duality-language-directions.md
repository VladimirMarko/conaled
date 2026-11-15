# Construction and observation

Discussion and follow-up agenda, 2026-10-30. The owner requested preservation of
both findings and speculations after #256. The checked results and bounded
assessments below refine that agenda. They do not select a universal language
architecture.

The project owner adopted **Construction and observation** as the workstream
name on 2026-10-30. Duality remains a central research direction within it.
The scope includes verified presentations, compatibility under composition
and substitution, and the obligations imposed by extension. The historical
filename remains stable so existing links continue to resolve.

## Evidence and conjecture

| Status | Claim | Boundary |
|---|---|---|
| Checked locally | #256 transposes intrinsically indexed equation bodies, swaps their parameter scopes, and proves both syntax round trips and exact denotational preservation. | Binding-free cells with total primitive interpretations; no arbitrary recursive source transformation. |
| Checked locally | #255 gives finite-word final behavior and exact finite parser/trie observations; #256 recovers its selected union/concat/star observations. | No equivalence between all finite syntax and all codata behaviors, or infinite-productivity/runtime-sharing theorem. |
| Checked locally | #268 derives composite interpretations and compatible substitution from local constructor laws in a finite-arity derivative-template format. | Ordinary type carriers and fixed outputs; fixed-fiber vector specialization, with index-changing/dependent observations owned by #271. |
| Checked locally | #271 derives composite preservation and compatible substitution for finite terms over fixed indexed families. | Index-changing vectors and exact parser/trie operations; #274 adds coherent restriction and full finite composition. |
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

The [#266 implementation record](constructor-destructor-transposition.md)
completes the remaining parser rows and recovers their exact observations.
Its vector example adds a constructor row and an observer column while retaining
old cells through both view changes. The matched author comparison records the
required wrappers and diagnostics; it does not claim an independent usability
trial. These results discharge #8's omitted-row follow-up and inform #116's
surface work.

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

The [#267 extension contract](observation-extension-contracts.md) proves
restriction, compatible extension and quotient descent, with a non-factorization
counterexample. An old theorem remains correct under its original contract;
restriction also lets refined hypotheses reuse it. A new observer requires its
own compatibility proof to respect the old equivalence. Adding axioms is a
separate change; retaining old equation cells does not establish consistency.

[#262](https://github.com/VladimirMarko/conaled/issues/262) retains the distinct
semantic-type admissibility experiment. The #267 parser and FIFO examples state
which old assumptions remain valid and distinguish observer refinement from
compatibility with the old quotient.

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

The #268 vector family retains its size index within each fixed fiber.
The [#271 indexed continuation](indexed-constructor-observer-laws.md) adds
index-changing constructors and observations over a fixed family. Its vector
cons/head/tail case and native parser/trie union-and-transport case use the same
local-to-composite theorem. Exact `Decision (P word)` results survive bounded
word observations, including distinct selected nullable-star witnesses.
An explicit singleton-index bridge recovers #268's ordinary contract.

The indexed theorem does not infer compatibility from transposed source cells
or cover arbitrary changes of index base. [#274](https://github.com/VladimirMarko/conaled/issues/274)
adds coherent depth restriction for retained operands, plus scale, intersection,
concatenation and star templates. Both native interpretations satisfy the local
laws; the same theorem now recovers exact observations and whole finite tries
for arbitrary composite terms. A table of handlers or #256's permutation alone
does not supply these composition laws.

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

The [#269 pairing assessment](pairing-observation-transport.md) compares Chu
maps with existing squares, relations and #257's variance interfaces. Its parser
and vector cases support reuse of exact squares with explicit query transport;
changed result fibers still need dependent comparison. It recommends no universal
Chu framework for these clients and leaves broader applicability under #235.

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

The [#270 assessment](symmetric-producer-consumer-assessment.md) compares
bounded producer/consumer syntax with the existing #203 Curry–Howard and #212
session examples. Its vector and exact parser-witness cases separate polarity,
evaluation order and structural rules. Transposition can leave the polar default
strategy assignment while preserving evaluation order. The assessment retains
direct clients and finds no basis for replacing the current calculus.

## Demand, retention and cleanup

The [#273 assessment](demand-retention-cleanup-assessment.md) tests the proposed
connection against demand, heap liveness, resource reasoning and reversible
computation. An unused divergent thunk, retained storage, recomputation and
reversible scratch expose different obligations. Root sets, execution order,
ownership and retained history affect the resource claims. The examples support
keeping these theories separate with explicit connections; they establish no
construction/observation duality or thermodynamic law.

## Priority and ownership

The checked local results are #266's source views, #267's extension contracts,
#268's ordinary composition laws, #271's indexed continuation and #274's full
finite parser composition. The #269, #270 and #273 assessments retain narrower interfaces or separate theories where
their examples do not justify a universal framework. These conclusions do not
rank all possible language designs or settle the wider conjectures above.

The [bialgebraic adoption assessment](bialgebraic-semantics-adoption.md),
[#275](https://github.com/VladimirMarko/conaled/issues/275), led to completed
experiments: exact contextual rewrites (#276), the equation-view bridge (#277),
constructor/observer interaction (#278), and independent author trials (#279).
The later #281–#285 results add whole-client workspace comparisons, retained
parser snapshots, exact transport-spine normalization, guarded recursive streams,
and a higher-order comparison with independent function meaning.

The [cross-workstream assessment](construction-observation-research-assessment.md)
records their source-level evidence, limits and consequences for the new
[research programmes](language-research-agenda.md). Reuse the accepted results
when testing theory extension (#288), dependent coherence (#289), and theory
publication/transport (#290). The finite indexed laws do not settle the latter
two programmes, and semantic equivalence alone does not imply runtime sharing.

#262 remains the distinct semantic-type admissibility experiment; #263 owns
generic memoization integration beyond the retained parser instance; #109 owns
source recursion and compilation beyond the guarded-stream construction. #235
owns cross-cutting applicability and recovery of existing specializations; #36
owns internal-language and surface integration; #200 owns correspondence research;
#8 owns categorical compilation. Acceptance criteria and live status belong to
the issues. Completed studies are evidence, not queued work.
