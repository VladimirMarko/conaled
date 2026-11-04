# Bialgebraic semantics: adoption assessment

Reviewed 2026-11-04 against the implemented #268/#271 contracts and the shared
language direction. This is a research assessment, not a new formalization or
an architecture decision. The four papers below were read in their full primary
texts, including the cited assumptions and limitations.

## Recommendation

Adopt bialgebraic compatibility as a reusable semantic method, and develop its
quotient, recursion and higher-order consequences where the project needs them.
The existing finite indexed construction should become a checked specialization
of a broader account if that account supports the additional clients. Do not
make a particular operational observation functor the definition of all project
meaning. A syntax-independent carrier can still distinguish implementation
steps that our mathematical denotation should forget.

There are three different commitments to assess:

| Commitment | Recommendation | Evidence needed next |
| --- | --- | --- |
| Separate syntax, observations and compatible interpretation; derive composite laws | Adopt and retain | Already checked for #268/#271; preserve native interfaces and exact witnesses. |
| Generalize reusable theorem machinery to quotients, productive definitions and higher-order behavior | Develop through the experiments below | Each new theorem must recover a concrete native semantic contract; existing finite interfaces may need revision. |
| Use the entire Turi–Plotkin framework, or the higher-order successor, as the language's universal foundation | Keep open pending discriminating comparisons | Higher-order binding, intended equality, recursion and changes of setting must fit without weakening established contracts. Encoding difficulty alone is not a reason to reject it. |

## Higher-order compositionality

[Goncharov, Milius, Schröder, Tsampas and Urbat, *Higher-order bialgebraic
semantics*, v5](https://arxiv.org/pdf/2405.16708v5), Assumptions 4.2 and
Theorem 4.14, use a category with finite limits and colimits, a variable object,
a signature with free algebras, and a behavior bifunctor `B : Cᵒᵖ × C → C`.
The rule is dinatural in its input-state argument and natural in its successor
argument. Congruence additionally requires a regular category, preservation of
reflexive coequalizers by the signature, preservation of monomorphisms by B,
and a final coalgebra for `B(μΣ,−)`. The paper develops combinatory and binding
examples. Its central examples concern strong applicative behavior; ordinary
covariant state maps do not express function input variance. These are source
results, not properties established for our modules.

**Project experiment.** Implement a small typed combinatory language with
application and one ground type, followed by an open-term binding example.
Specify its ordinary function-valued mathematical interpretation separately.
Derive a congruence theorem from the higher-order rule format and compare it
with the direct semantic contextual-equivalence proof. Include beta-equivalent
terms with different numbers of reduction steps as a deliberate discrimination
case. State which relation is congruent and which relation the project wants.

This would add something #271 cannot express: accepting a program as an
observation input, rather than accepting a request from a fixed request type.
Binding further needs context extension and substitution. Reindexing #271's
fixed families alone does not discharge either obligation. The likely reusable
interface includes a mixed-variance behavior layer and explicit input/output
comparison laws. Its success criterion is an application proof that shares this
machinery without embedding every ordinary client into a higher-order language.

## Higher-order denotational models and adequacy

[Goncharov, Peressotti, Tsampas, Urbat and Volpe, *Towards a Higher-Order
Bialgebraic Denotational Semantics*, v2](https://arxiv.org/pdf/2602.18295v2):
Definition 3.2 makes `Z → B(Z,Z)` locally final when it is final for `B(Z,−)`.
Theorem 3.9 extends such a domain to a compatible algebra under relative
flatness. Theorem 3.11 gives adequacy for every compatible bialgebra, assuming
the required final coalgebras: denotational equality implies behavioral
equality. Theorem 4.13 constructs locally final domains in stable M-categories
with a terminal object, chain limits, contravariant local contractiveness,
covariant local non-expansiveness, an inhabited specified hom-set, and
convergent final sequences. Uniqueness additionally requires inhabited
hom-sets. Section 6 leaves the converse needed for full abstraction and weak
behavioral semantics open. Relative flatness typically excludes unrestricted
Y recursion (Remark 3.8).

**Project experiment.** Use the same typed fragment as above. Start with its
independent extensional function interpretation D and the paper's behavior
domain Z, and construct an explicit relation or map between them. Test whether
`D(p) = D(q)` implies the desired observation agreement, whether the converse
holds, and whether the comparison commutes with application. A step-sensitive Z
will distinguish some terms D identifies. That outcome should select a weaker
observation contract or a different comparison theorem; it should not redefine
D to make the test pass. The exact maps and equality directions are acceptance
criteria, not an assumed isomorphism.

The reusable opportunity is broader than constructing Z: a compatibility theorem
can connect an independently supplied algebra to behavior. For a sufficiently
expressive fragment, this could replace repeated adequacy proofs. Constructing
Z alone does not prove agreement with Conal-style mathematical meaning. Our
existing `Compatible` obligation plays the same protective role at a smaller
scale: the natural wrong-cons rule is rejected because it computes the wrong
head. Adequacy relative to the behavior generated by that wrong rule would not
repair its meaning.

A substantial redesign is worth considering if the typed experiment shares
interpretation, binding and congruence proofs that our present interfaces
cannot share. It must retain the exact parser result fibers and the weighted
noncommutative example. The higher-order construction is not a ready-made
replacement for semantic-type admissibility or arbitrary changes of base.

## Equations and quotients

[Bonsangue, Hansen, Kurz and Rot, *Presenting Distributive Laws*,
v2](https://arxiv.org/pdf/1503.02447v2), Theorem 4.3, characterizes descent of a
distributive law `T F ⇒ F T` to an equational quotient monad: it descends
uniquely precisely when the law preserves the generating equations after
quotienting. Assumption 2.2 supplies algebra coequalizers and preservation of
regular epimorphisms by the relevant forgetful/composite functors. Propositions
4.10 and 4.12 extend the result to copointed functors and comonads. Preservation
is a behavioral obligation, not merely a syntax quotient construction.

**Project experiment.** First prove a context-closed rewrite using #268's
weighted addition associativity, then verify its compatibility with transitions
and substitution. Separately choose an indexed parser equation with an explicit
witness comparison. Reject a Boolean-valid simplification that changes the
selected witness, such as identifying left and right nullable alternatives.
The fixed-output weighted quotient and the parser's dependent transport are
separate cases: a theorem on Set cannot silently identify their witness fibers.

This gives a principled route from free terms to normalized representations.
A quotient theorem may be worthwhile after the context-rewrite proof exposes
repeated obligations. It does not select a canonical representative, establish
termination of rewriting, or prove that normalization reduces runtime. The
existing `bind_morphism` already covers behavior-preserving substitutions;
quotient descent adds a reusable representation of all admitted equations.

## Recursive definitions and productivity

[Milius, Moss and Schwencke, *Abstract GSOS Rules and a Modular Treatment of
Recursive Definitions*, v2](https://arxiv.org/pdf/1307.2538v2), Assumption 2.1,
requires binary products/coproducts, a terminal behavior coalgebra, and free
algebras for the operation functor. Theorems 3.5–3.6 extend completely iterative
algebra structure, including a sandwiched form. Theorem 4.8 establishes
modularity for guarded recursive program schemes; Theorems 5.14 and 5.23 give
unique solutions for the stated GSOS-relative schemes and their sandwiched
extension. The hypotheses allow defined operations to participate in subsequent
admissible definitions. They do not assert uniqueness for arbitrary recursion.

**Project experiment, coordinated with #109.** Begin with streams whose
independent meaning is `Nat → R` and the existing local pointwise operations.
Define one guarded recursive stream operation, prove its unique solution, then
use that operation in another admissible recursive definition. Compare with
the direct mathematical sequence at every coordinate. Include an unguarded
self-equation admitting multiple solutions to show why the hypothesis is
needed. Generalize only after identifying the repeated proof obligations.

For the parser line, a separate later application would connect coherent finite
snapshots to an infinite observation object and show that each finite query
agrees with the current parser. #274's depth restriction is useful preparation,
but does not by itself supply that object or the recursive-scheme theorem.
Guarded semantic productivity and runtime memoization are separate properties.

## What could improve execution

The research exposes concrete engineering candidates, with different proof
obligations:

- Coherent depth restriction can justify reusing a deeper snapshot for a
  shallower query. A representation with sharing would still be needed to
  avoid recomputing or copying it. This is a candidate for #263, not a measured
  speedup from #274.
- Equation-preserving normalization can merge equivalent derivative states.
  Exact-witness observers restrict which merges are legal; Boolean language
  equivalence alone is insufficient. A finite-state bound and performance
  comparison remain additional work.
- Productive recursive interpretation can define unbounded observations while
  preserving every finite query. It does not establish bounded memory or time.

No new parser algorithm or benchmark improvement was established by the four
papers' application assessment. Their immediate contribution is a way to state
and reuse the correctness contracts for these experiments.

## Follow-up ownership and research boundary

The approved higher-order assessment should own the first two experiments
and an explicit comparison with execution-independent meaning. The approved
contextual rewrite issue should own the quotient experiment. Add the recursive
scheme experiment under #109 rather than leave the fourth paper as a reading
item. #274 remains the next concrete parser extension. Author trials should
compare these shared interfaces with direct proofs after the examples exist.

One targeted additional reading follows from the observed equality mismatch:
the higher-order paper's reference 58, *Weak similarity in higher-order
operational semantics* (Urbat et al., 2023). Its cited role is weak congruence
via lax higher-order bialgebras; it should be read before assuming that the
2026 denotational construction automatically extends to weak observations.
This paper was identified through the reviewed source but has not been fully
assessed here. A competing denotational account remains necessary for the
larger architecture comparison; this investigation is a focused lineage study,
not a ranking of all semantic traditions.

## Selected experiment specifications for #275

The following are **unimplemented specifications**, not checked examples.
They make the success and failure obligations concrete enough for successor
issues to accept or reject the proposed generalizations.

| Experiment | Positive comparison obligation | Essential-assumption failure | Owner |
| --- | --- | --- | --- |
| Higher-order congruence | For typed identity and application, relate the operational result to independent function evaluation; show replacing a related argument inside application preserves the chosen observations. Record the relation at function types, including its contravariant argument obligation. | Add two ground constants with the same behavior and a proposed observer that returns different Boolean results by inspecting their syntax tags. Its apparent rule must fail the required uniformity/compatibility check; otherwise the purported congruence theorem is too strong. | #275 hands formal implementation to a scoped successor under #235/#36. |
| Locally final denotation | For the typed fragment, construct `erase : Z → D` where possible, or an explicitly typed logical relation if a total map is unjustified; prove `erase(denoteZ t) = denoteD t` and application compatibility. Prove the chosen adequacy direction separately. | Compare a ground constant with its identity redex. The intended extensional denotation agrees; step-sensitive behavior distinguishes them. Also show why adding `Y f → f (Y f)` fails the proposed relative-flatness rank assignment. | Same higher-order successor, with #235 retaining the weak-observation gap. |
| Quotient/rewrite compatibility | Weighted addition associativity preserves coefficients at every word and transitions modulo the generated equations. The context theorem must cover substitution below other constructors. | Boolean simplification of two selected nullable alternatives loses witness identity; reject that equation for the exact observation contract. | #276. |
| Modular recursive interpretation | Define `ones = 1 :: ones`, then define prefix sums of that stream using the admitted addition operation. Compare with independent sequences `ones(n)=1` and `sums(n)=n+1`, and prove uniqueness plus reuse in the subsequent definition. | `x = x` has distinct constant-stream solutions; the admissibility checker must reject it rather than claim uniqueness. | #109, coordinated with #235. |

For the first experiment, the extra syntax-inspecting observer is deliberately
outside the admissible rule format. The task is to identify the exact failed
naturality/dinaturality or semantic-compatibility equation, rather than assume
all source-language extensions preserve congruence.

The current migration baseline consists of `Rule.layer_natural`,
`Rule.Compatible`, `Rule.fold_morphism`, `bind_morphism`, `join_morphism`,
`map_morphism` and `Behavior.observe_morphism` in
`SquareKit/IndexedCompositional.lean`, plus the ordinary recovery in
`SquareKit/IndexedCompositionalOrdinary.lean`. A new categorical interface must
recover their fixed-family results and keep the current selected
`Decision (P word)` examples. #277 owns source-view integration, #278 owns
constructor/observer extension composition, and #279 owns author comparisons.
These tasks should use the additional structure only when their examples need
it. No operational cost or effect equivalence is inferred from the present
finite-path morphism theorem.
