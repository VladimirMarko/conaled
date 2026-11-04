# Construction and observation: conclusions and further research

Assessment after #266–#273, 2026-11-04. The owner approved the five scoped follow-ups below. Their creation does not
select a universal framework. The subsequent [adoption assessment](bialgebraic-semantics-adoption.md)
examines all four prioritized papers and their remaining semantic obligations.

## What the checked work establishes

Local constructor compatibility can discharge the repeated whole-term induction
needed for semantic preservation. The ordinary theorem covers weighted language
operations; the indexed theorem covers index-changing vectors and native
parser/trie union and witness transport. Both preserve their independently
specified meanings. The indexed case retains exact `Decision (P word)` results,
including distinct selected nullable-star witnesses. Finite constructor terms
and their finite observations are the scope; this is not arbitrary recursion.
See the [ordinary contract](compositional-constructor-observer-laws.md) and
[indexed contract](indexed-constructor-observer-laws.md).

The [source-view experiment](constructor-destructor-transposition.md) permits
constructor-oriented and observer-oriented presentations of supported equations.
Its syntax preservation does not itself establish the semantic compatibility
needed by the composition theorem. Connecting those two checked interfaces is
still work. The [observation-extension contract](observation-extension-contracts.md)
separately explains when new observations respect old equivalence. Restricting
richer hypotheses preserves reuse of old theorems under their old assumptions.

The [pairing](pairing-observation-transport.md),
[symmetric-syntax](symmetric-producer-consumer-assessment.md), and
[demand/cleanup](demand-retention-cleanup-assessment.md) assessments identify
useful connections and different obligations. Their bounded cases do not justify
a universal Chu framework, replacement proof calculus or resource duality.
These outcomes leave broader applicability open. Existing direct interfaces
remain usable; the examples do not establish independent author effectiveness.

## What #274 would add

**Completion update, 2026-11-04:** #274 supplies the cut constructor, coherent
restriction, and local compatibility for scale, intersection, concatenation and
star. The existing all-term theorem now recovers exact decisions and whole
finite tries for arbitrary composite expressions. Checked cases retain nullable
star choices, including a nonstandard selected empty witness that a resetting
rule would lose. See the [implementation record](indexed-constructor-observer-laws.md).
The following proposal records the gap that motivated this work.

[#274](https://github.com/VladimirMarko/conaled/issues/274) would recover existing
native parser/trie combinators through the shared indexed theorem, including
scale, intersection, concatenation and star. Concatenation exposes the key gap:
its derivative retains the original right operand. A finite trie at depth n+1
must then be available at depth n without consuming a letter from that operand.
Retaining a child keeps its depth; taking its successor consumes a letter.
Neither expresses that restriction.

The proposed cut operation reduces observation depth while preserving all
remaining observations. Its local compatibility and repeated-restriction
coherence would let the harder native combinators fit the shared rule format.
The acceptance case retains selected parse witnesses, including nullable star's
empty-factor information, and recovers arbitrary finite composites through the
shared theorem. This would strengthen evidence that the reusable interface
handles the project's existing mathematics and reduce per-composite proof work.
It would not add a new parsing capability, infinite productivity or a performance
guarantee. #263 separately owns memoization with demonstrated reuse.

## How Turi–Plotkin helped

The [original paper](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf)
supplied the concrete rule shape `Σ(X × B X) → B(T X)`: a constructor sees both
its operands and their one-step behaviors and produces behavior with syntax as
successor states. Retaining X explains the original operand in concatenation.
Its lifting perspective motivated the separate substitution, leaf and flattening
laws in #268; multi-sorted settings informed #271.

Our Lean development proves a bounded concrete construction. It does not
formalize the paper's full distributive-law, adequacy or full-abstraction theory.
The paper's canonical semantics also does not certify agreement with an
independently intended mathematical meaning. Our compatible-algebra obligation
supplies that connection: a natural rule with the wrong arithmetic can still
fail it. This distinction lets the operationally presented mathematics support
the project's denotational priority.

## Recommended direct successors

1. **Goncharov, Peressotti, Tsampas, Urbat and Volpe, Towards a Higher-Order Bialgebraic Denotational Semantics (ICFP 2026).** [Current version](https://arxiv.org/abs/2602.18295), [paper](https://arxiv.org/pdf/2602.18295). This is the closest strategic match. It constructs denotational domains independently of syntax using locally final coalgebras: `Z → B(Z,Z)` must be final for `B(Z,-)`. A relative-flatness restriction permits the induced bialgebra (theorem 3.9); theorem 3.11 proves adequacy, meaning denotational equality implies behavioral equality. Its examples include strong applicative bisimilarity. Domain existence uses additional machinery, including metric-enriched categories and guarded models (theorem 4.13). This does not automatically prove full abstraction or identify the domain with an independently chosen mathematical meaning. Investigate that comparison on a small example before architectural adoption. Priority: first strategic investigation.

2. **Milius, Moss and Schwencke, Abstract GSOS Rules and a Modular Treatment of Recursive Definitions (2013).** [Published article](https://lmcs.episciences.org/1180), [paper](https://arxiv.org/pdf/1307.2538), theorem 5.14 and section 6.4. Abstract GSOS supplies operations on a terminal coalgebra; completely iterative algebra structure gives unique solutions to the paper's specified recursive schemes. Newly defined operations can be reused in subsequent such schemes. This directly extends the Turi–Plotkin program beyond finite terms. It does not justify arbitrary unguarded equations or runtime resource bounds. Priority: immediate reading, with any implementation owned by existing #109. A stream or language example and a rejected unguarded counterpart would expose the assumptions.

3. **Bonsangue, Hansen, Kurz and Rot, Presenting Distributive Laws (2015).** [Paper](https://arxiv.org/pdf/1503.02447), theorem 4.3 and proposition 4.10. For an equational quotient of a monad, preservation of the equations is equivalent to existence of the corresponding quotient distributive law. The copointed extension covers abstract GSOS, including language concatenation; context-free languages provide an application. This suggests a precise test for syntax simplification while retaining observations. A Boolean-valid parser equation may fail for exact selected witnesses. Proposed experiment: an accepted rewrite and a witness-sensitive rejection, compared with what the current concrete morphism API already proves. Priority: immediate bounded experiment if rewriting or quotienting is needed.

4. **Goncharov, Milius, Schröder, Tsampas and Urbat, Higher-order bialgebraic semantics (JFP 2026).** [Current version](https://arxiv.org/abs/2405.16708), [paper](https://arxiv.org/pdf/2405.16708). This extends the earlier *Towards a Higher-Order Mathematical Operational Semantics*. Pointed higher-order GSOS uses dinaturality and mixed-variance behavior. The compositionality result (theorem 4.14) and lambda-calculus examples address higher-order behavior beyond first-order GSOS; categorical preservation hypotheses matter. It is the prerequisite for the new denotational paper. #271's intrinsically sorted finite terms do not establish this higher-order result. Its strong applicative-bisimilarity contract does not alone identify the project's desired denotational equality or supply dependent types.

5. **Pous and Rot, Companions, Codensity and Causality (2019).** [Paper](https://arxiv.org/pdf/1712.08526); the arXiv landing page reverses the final two title words. It connects final distributive laws, causality and sound up-to-context reasoning. Theorem 9.10 concerns polynomial behavior functors on Set and causal algebras on their final coalgebra. Theorem 9.5 states additional continuity and polynomial hypotheses. Union, concatenation and star of languages occur as causal contexts. This may shorten behavioral-equivalence proofs and help assess finite observation depth. It does not automatically solve #274's indexed witness-preserving restriction. Priority: when a concrete proof demonstrates a need beyond the existing fold/morphism results.

6. **Urbat, Tsampas, Goncharov, Milius and Schröder, Weak Similarity in Higher-Order Mathematical Operational Semantics (2023).** [Paper](https://arxiv.org/pdf/2302.08200), theorem VIII.6. This extends higher-order GSOS to weak similarity using relation liftings and a categorical Howe argument. The weakened operational model must form a lax bialgebra; simply hiding transitions does not establish congruence. It includes applicative similarity for the lambda calculus. Read when implementation steps need abstraction, after choosing the observations and stating their relationship to independent denotation. Priority: later, unless the higher-order experiment requires weak evaluation observations.

All six are direct continuations of the bialgebraic/abstract-GSOS research program. For background, Bartels's [Generalised coinduction](https://ir.cwi.nl/pub/4375) (report 2000, journal 2003) and [2004 thesis](https://ir.cwi.nl/pub/17104/Thesis_F_Bartels) explain generalized coiteration and up-to-context proofs through distributive laws. The main validity theorem has categorical hypotheses, including countable coproducts. These are useful prerequisites, not separate implementation commitments.

The Gambino–Kock and Gambino–Hyland polynomial-family papers already used by #271 are adjacent foundations: they help express indexed or dependent structure but do not supply native parser compatibility. Modular SOS is another adjacent modularity approach; it should not be conflated with the bialgebraic theorem.

## Proposed follow-up issues

The approved scopes are tracked in #275–#279. Priorities reflect the present
project questions, not a ranking of the entire literature.

1. **Assess higher-order bialgebraic denotational semantics against independent
   mathematical meanings.** [#275](https://github.com/VladimirMarko/conaled/issues/275) Under #235/#36, map the 2026 papers' assumptions to a
   bounded higher-order example. Construct or identify its semantic domain,
   state the comparison with the intended mathematical interpretation, and
   distinguish adequacy, congruence and full abstraction. Include a failed
   assumption case and assess what current indexed interfaces can recover.
   Deliver research and a selected experiment before committing to a full
   framework. This is the strongest strategic research lead.
2. **Retain exact observations through equations and contextual rewrites.** [#276](https://github.com/VladimirMarko/conaled/issues/276)
   Under #235, use the 2015 quotient-law criterion to select one useful valid
   equation and one Boolean-valid but selected-witness-invalid transformation.
   Prove replacement in arbitrary supported constructor contexts. Compare the
   existing concrete morphism route with a quotient presentation; adopt extra
   categorical infrastructure only if it discharges a real missing obligation.
3. **Connect verified equation views to compositional semantic rules.** [#277](https://github.com/VladimirMarko/conaled/issues/277) Under
   #36, choose a common fragment of #266 and #271. Translate supported cells
   to the rule format, preserve their interpretation through transposition,
   and apply the shared fold theorem after local compatibility is supplied.
   Exercise a mixed term and expose unsupported cells. This must not claim
   that transposition establishes compatibility or that all primitives fit.
4. **Compose constructor and observer extensions with explicit cross-obligations.** [#278](https://github.com/VladimirMarko/conaled/issues/278)
   Under #235, combine #267's observation contract with #271's composition law.
   Test one new constructor and one new observer, state their interaction
   obligations, preserve old observations through the old-syntax embedding,
   and demonstrate a failed compatibility case. New semantic types remain
   #262's scope; this proposed task concerns composition of operation and
   observation extensions.
5. **Run independent author trials for the new construction/observation APIs.** [#279](https://github.com/VladimirMarko/conaled/issues/279)
   A bounded child of #235, coordinated with #117's methodology, should compare
   direct and shared routes for the same extension tasks. Use authors who did
   not implement the interfaces; record wrappers, casts, diagnostics, assistance
   and retained theorem contracts. This can use current Lean interfaces without
   waiting for #117's alternative-surface experiment or #116's surface design.

Run #274 alongside the first literature assessment. The equation-view bridge
and an independent author trial test whether the existing results form a usable
interface. Select the equation/quotient experiment around an actual rewrite;
keep modular recursion with #109, memoization/reuse with #263, and semantic-type
admissibility with #262. None of those existing scopes needs a duplicate umbrella
issue. General higher-order state, weak equivalence and arbitrary changes of
index base remain possible research directions rather than automatic additions.

## Implemented follow-ups

The bounded implementations from #276–#279 and #281–#285 keep independent
meaning and exact observations as their acceptance contracts. Their research
records distinguish the checked claims from broader adoption questions.

| Issue | Result and boundary |
| --- | --- |
| [#276](https://github.com/VladimirMarko/conaled/issues/276) | [Exact contextual rewrites](exact-observational-rewrites.md) preserve selected witnesses through arbitrary supported finite contexts. Boolean recognition alone still cannot justify witness-changing rewrites. |
| [#277](https://github.com/VladimirMarko/conaled/issues/277) | [Equation-view compilation](equation-composition-bridge.md) supplies rules for a stated common fragment. Transposition preserves the rule; local semantic compatibility remains a separate obligation. |
| [#278](https://github.com/VladimirMarko/conaled/issues/278) | [Constructor/observer composition](constructor-observer-composition.md) combines a vector constructor and observer through a common meaning and explicit cross-obligations. It does not establish arbitrary extension-order commutation. |
| [#279](https://github.com/VladimirMarko/conaled/issues/279) | [Independent author trials](construction-observation-author-trials.md) checked direct and shared routes against a frozen protocol. The trial record reports assistance, failed attempts and configuration limits; it does not establish human usability or a causal productivity advantage. |
| [#281](https://github.com/VladimirMarko/conaled/issues/281) | [Whole-client schedules](whole-client-workspace.md) compare retention and recomputation, including cleanup and a surrounding computation. Work/space results concern the specified schedules, not optimal implementations. |
| [#282](https://github.com/VladimirMarko/conaled/issues/282) | [Retained snapshots](retained-parser-snapshots.md) reuse stored derivatives with exact lookup and depth restriction. Explicit workloads include construction costs and an adverse case; the result is a bounded client for #263. |
| [#283](https://github.com/VladimirMarko/conaled/issues/283) | [Transport normalization](derivative-transport-normalization.md) reduces redundant outer wrappers while preserving exact parse decisions. Logical derivative-call savings can exceed packing costs on the stated workload; short and already simple states can lose. |
| [#284](https://github.com/VladimirMarko/conaled/issues/284) | [Modular guarded streams](modular-guarded-streams.md) have unique solutions, and a later definition reuses an earlier solution. The coordinate construction rejects an unguarded equation and does not implement the paper's full categorical framework. |
| [#285](https://github.com/VladimirMarko/conaled/issues/285) | [Higher-order comparison](higher-order-extensional-comparison.md) connects a typed behavioral model with independently specified function meaning. Equal mathematical results can have different beta-step counts; forgetting those counts requires its own comparison proof. |

These results support continued use of local compatibility and explicit
comparison theorems. They do not select a universal syntax or turn logical
cost models into runtime measurements. The completed [#286](https://github.com/VladimirMarko/conaled/issues/286)
and [#287](https://github.com/VladimirMarko/conaled/issues/287) paper assessments
preserve that direction: assumption extraction and representation expansion
have specific additional obligations, without replacing the existing direct
interfaces.
