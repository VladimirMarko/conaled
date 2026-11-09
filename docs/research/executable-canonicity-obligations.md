# Canonicity obligations for executable fragments

[#395](https://github.com/VladimirMarko/conaled/issues/395) recommends a bounded
canonicity interface for the omega-free part of the existing weak machine.
The embedded total fragment already has a checked operational return theorem.
Reuse that bridge: the proposed additions are a structural admission/coverage
API, substitution closure, and packaging with uniqueness and sufficient fuel,
plus an opaque-stuck control. Keep the existing partial language and its
divergence results available unchanged.

This is a research deliverable, not a new Lean development. Local declarations
were inspected at `28f8643141055dc194b22f59c210fb4b089e7062` on 2026-11-09.
The report was refreshed onto accepted `f67e7fe`; the audited machine and
total-fragment bridge are unchanged there. Statements labelled **checked** refer to existing integrated Lean declarations;
**proposed** statements and the opaque-extension counterexample below have not
been formalized here. The historical Harper discussion is background, not the
source of the literature claims.

## What must a canonicity claim specify?

For this work, an operational ground-data claim has the shape

```text
for every admitted closed t : ground,
there is a numeral n such that the selected evaluator reaches lit n.
```

A usable specification must name the admitted terms, primitive declarations,
closure conditions, canonical forms, reduction strategy, and relation between
the evaluator and reduction. For a fuelled evaluator, it should assert a
sufficient finite bound and success at every larger fuel, not promise success
at an arbitrary fuel. The numeral is unique when determinism and canonical
terminal forms justify uniqueness.

These are different obligations:

| Property | What it establishes | What it leaves open |
| --- | --- | --- |
| Typing | A term belongs to the selected syntax/judgment boundary. | Whether it computes. |
| Semantic soundness | Derivable judgments hold under the stated interpretation. | Whether source reduction reaches a constructor. |
| Progress | A closed term is a value or can step. | An infinite sequence of steps. |
| Termination | The selected execution eventually stops. | Whether its terminal term is a numeral or a stuck neutral. |
| Operational canonicity | Every admitted closed ground term reaches the specified data form. | Normal forms for arbitrary open terms or all reduction strategies. |
| Judgmental canonicity | A closed data term is judgmentally equal to a canonical datum. | An algorithm implementing that equality unless separately established. |
| Value-plus-identity recovery | A canonical datum and a witness relating it to the source are obtained. | Reduction of the unchanged source to that datum. |
| Open normalization | Terms with free variables have the specified normal forms. | Decidable judgmental equality without the required soundness, completeness, and comparison algorithm. |

These distinctions are proposed contract vocabulary for the audited interfaces,
not a new universal equality hierarchy. In particular, a theorem about one
strategy does not establish strong normalization of every reduction sequence.
An object identity witness is not a Lean equality proof by default, and neither
is automatically a source reduction trace.

## Primary theorem boundaries

### Huber: natural numbers in name-only contexts

Huber's *Canonicity for Cubical Type Theory*, arXiv:1607.04156v2 (2017),
Corollary 4.21, concerns the specified CCHM-style dependent calculus. If a
natural-number term is derivable in a context containing only interval names,
it is judgmentally equal to exactly one numeral. Empty context is included;
arbitrary term assumptions and arbitrary additional constants are not.

The calculus includes dependent functions and pairs, natural numbers, paths,
systems, composition, Glue, and its universe. Section 2 specifies typed,
deterministic weak-head reduction contained in judgmental equality. The
computability proof supplies effective numeral recovery; it is not merely
interpretation into cubical sets. Reduction need not commute literally with
name substitution, so coherence under substitution is part of the argument.
Theorem 4.3 and Lemma 4.11 support the canonicity corollary. Section 5 sketches
particular circle and propositional-truncation extensions with additional
rules. This is not a theorem for arbitrary HITs, arbitrary extensions, or a
complete normalization/type-checking algorithm. See [the pinned paper,
§§1–5](https://arxiv.org/html/1607.04156v2).

### Angiuli–Harper–Wilson: computational Boolean membership

Angiuli, Harper, and Wilson's *Computational Higher Type Theory I: Abstract
Cubical Realizability*, arXiv:1604.08873v2 (2016), Theorem 38, says that Boolean
membership with empty term context and empty dimension context entails
execution to `true` or `false`. Determinacy makes the value unique.

Section 3.2 gives deterministic weak-head operational rules; no-transition
alone does not mean value for arbitrary raw expressions. Definitions 11, 13,
and 15 build evaluation and coherent dimension substitution into semantic
membership. Thus its canonicity statement uses a computational meaning
explanation, not an arbitrary set-valued sound model. The theory includes
functions, products, booleans, the circle, and the specific Boolean-negation
identification. It does not supply full univalence, dependent type families,
or an internal universe theorem. The introduction reserves broader dependent
and identification-type machinery for later work. At nonzero dimension,
Boolean canonical forms include suitable composition forms; Theorem 38's
zero-dimensional restriction matters. See [the pinned paper, §§1, 3–5 and
Theorem 38, printed p.36](https://arxiv.org/pdf/1604.08873v2).

### Applicability decision

Neither theorem applies directly to the local languages below. Their syntax,
primitive interfaces, equality judgments, and evaluation rules differ. A
transfer needs an actual translation and a theorem connecting source execution
to the translated execution, or an independent computability argument for the
local rules. A translation preserving only typing or denotation is insufficient.
This is an inference about applicability, not a claimed obstruction to building
such a connection.

## Audit of current executable and internal fragments

### The selected operational fragment: weak higher-order execution

The inspected files are
[`WeakHigherOrder.lean`](../../SquareKit/WeakHigherOrder.lean),
[`WeakMachine/Substitution.lean`](../../SquareKit/WeakMachine/Substitution.lean),
[`WeakMachine/Execution.lean`](../../SquareKit/WeakMachine/Execution.lean), and
[`WeakMachine/Adequacy.lean`](../../SquareKit/WeakMachine/Adequacy.lean).

The types are `ground` and arrows. Terms are intrinsically typed variables,
natural literals, lambdas, applications, and `omega` at any type. `Term [] a`
is closed because its term-variable context is empty; there are no dimension
variables, external signature constants, or general primitive declarations in
this syntax. Ground canonical forms are `.lit n`. At arrow type, weak values
are lambdas; their bodies need not terminate.

**Checked:** `next` implements left-to-right call-by-value substitution
execution, and `step_iff` connects it to the independent `Step` relation.
`next_none` characterizes closed values, `no_stuck` rules out closed stuck terms,
and `deterministic` establishes step uniqueness. `execute` is a terminating
fuelled host function returning a terminal value or a timeout residual.
At zero fuel it still recognizes a value. A timeout is not proof of divergence.
`execute_sound`, `execute_complete`, and `execute_sufficient` connect the
fuelled evaluator to finite reduction, including all sufficiently large fuels.

**Checked:** `closed_fundamental`, `return_agreement`, `divergence_agreement`,
`return_denotation`, and `divergence_denotation` connect actual transitions to
the independently specified partial computation and denotation. These are
stronger than an isolated denotational soundness statement. They nevertheless
allow `omega`: `next .omega = some .omega`, `Step.loop`, and `self_infinite`
give an actual infinite execution. `terminal_not_infinite` excludes a finite
terminal value for it. The whole fragment therefore does not have operational
ground canonicity. It has progress and an explicit divergence case.

**Proposed restriction:** `NoOmega t` is structural: variables/literals are
admitted, a lambda requires its body admitted, an application requires both
parts admitted, and `omega` is rejected. No source constructor changes are
needed. This is deliberately stronger than “this particular closed term
returns”: a lambda containing `omega` is a weak value but fails `NoOmega`.
The restriction supports a compositional total-function claim at arrow types.
No existing `NoOmega` theorem is being reported as implemented.

### Existing total higher-order evaluation

[`HigherOrderComparison.lean`](../../SquareKit/HigherOrderComparison.lean)
has variables, tagged natural literals, lambdas, and applications without
`omega`. Its structurally defined `run` returns a beta-count/value pair, with
host functions representing arrow values. `comparison` and `weak_eq_denote`
are **checked** semantic agreements. At closed ground type its result is a
host natural number; this is an existing executable route.

The cross-file bridge is also **checked**. In
[`WeakHigherOrder.lean`](../../SquareKit/WeakHigherOrder.lean), `embed` maps this
total syntax into the partial syntax, explicitly discarding literal tags.
`TotalRel` relates total and partial values; at arrows it requires related
inputs to yield a finite `done` computation with related result and the total
computation's latent cost. `TotalEnv` supplies the environment hypothesis.
`recovery` constructs that result by induction, and `recovery_ground` and
`recovery_meaning` specialize it to closed ground terms.

Crucially, [`Examples/WeakMachine.lean`](../../Examples/WeakMachine.lean)'s
`recovered` already proves, for every closed total ground term `t`, a finite
machine reduction from `embed t` to the literal denoting `t`. It composes
`recovery_meaning` with `return_denotation`. Thus canonicity on the embedded
image is already supported operationally, not merely by host evaluation.
`terminal_unique` and `execute_sufficient` can package uniqueness and sufficient
fuel from that existing return result. No new totality relation or duplicate
fundamental theorem is needed for this image.

What is not supplied by these declarations is a structural `NoOmega`
characterization of the image, its closure API, or an executable extraction of
a fuel bound. A proposed back-translation can choose a fixed literal tag and
prove `embed (back t h) = t` for `h : NoOmega t`. The reverse composition need
not recover the original tags. This assesses the actual remaining reuse work;
there is still no general open-term normal-form reifier in these files.

### Sufficient admission is not necessary termination

`NoOmega` would be an optional sufficient condition for the selected total
interface, not a restriction on all library expressions, settings, or source
specifications. It is not intended to characterize every terminating program.
The partial language already admits values whose function bodies diverge:
`Examples.WeakMachine` checks that `loopingFunction` is terminal at zero fuel
and proves that invoking it diverges.

Even a closed ground result can return with syntactic `omega` present. Under
the current call-by-value rules, the schematic term `(λf. 0) (λx. omega)` takes
one beta step to zero: the argument lambda is already a value and its body is
not forced. This is a direct derivation from existing `Step.beta` and
`Value.lam`, not a newly added named Lean theorem. A structural `NoOmega` test
would reject it. In contrast, existing `discardLoop = (λx. 0) omega` has the
checked `discard_infinite` proof because call-by-value evaluates its argument.

The user's `fst ((), undefined)` example raises the same demand question for
a lazy pair interface: if projection demands only the first component, a
partial second component need not prevent that observation. The current machine
has neither pairs nor call-by-need rules, so it should not be presented as an
implementation of that example. A future lazy/pair fragment must state its own
value, demand, and reduction contracts. Neither strict evaluation of every
field nor whole-program termination follows from specifying the meaning of a
pair. Observation-specific definedness and total-fragment admission can coexist.

### The bounded cubical interpretation is semantic evidence

[#321](https://github.com/VladimirMarko/conaled/issues/321) is closed for its
constructed bounded interpretation. Its current scope is recorded in
[`cubical-model-construction.md`](cubical-model-construction.md): a
universe-free, provider-annotated fragment, with further universe/Glue/HIT and
geometry coverage outside its advertised boundary.

Concrete inspected declarations include
[`Naturals.lean`](../../SquareKit/Internal/Cubical/Naturals.lean),
[`NaturalsAlgebra.lean`](../../SquareKit/Internal/Cubical/Judgments/NaturalsAlgebra.lean),
[`NaturalsTheory.lean`](../../SquareKit/Internal/Cubical/Judgments/NaturalsTheory.lean),
and [`Conversion.lean`](../../SquareKit/Internal/Cubical/Conversion.lean).
`natFamily` is a constant family of lifted host naturals, and `natRecValue`
constructs dependent recursion fiber by fiber. These are **checked** mathematical
constructions. `Naturals.interpret` validates a derivation under a valuation
and satisfaction of its assumptions. Its model and algebra are explicitly
noncomputable. Semantic family conversion uses equality transport of sections.

None of these declarations specifies a source small-step evaluator that reduces
every closed source numeral expression. The word `eval` in an algebraic
interpretation is not such a theorem. A model's natural-number component may
supply a natural at a semantic environment without establishing a source
reduction trace or a computable syntax-level extraction algorithm. Existing
provider arguments and assumptions must also be accounted for when defining
“closed.” This is a missing operational interface, not a claim that the model
is unsound or that Lean cannot host the desired proof.

The independent
[`ReferenceCalculus.lean`](../../SquareKit/Internal/DependentJudgments/ReferenceCalculus.lean)
also admits explicit typed declarations and equations through `Declaration`.
Its `termDecl` rule checks the type boundary of an admitted declaration; it
does not furnish a computation rule for that declared term. An empty object
context is therefore not enough to guarantee computation when the declaration
policy can still introduce opaque data. This observation concerns declaration
policy, not a claim that this calculus already has the proposed machine syntax.

### #214 and #307 supply narrower reusable results

[#214](https://github.com/VladimirMarko/conaled/issues/214) selected arithmetic
staging, not normalization by evaluation. In
[`ArithmeticStaging.lean`](../../SquareKit/ArithmeticStaging.lean), `quote`,
`specialize_correct`, substitution compatibility, and `compile_correct` give
**checked** phase-respecting specialization and compilation. Quoting an evaluated
integer does not prove normalization or decidable equality for arbitrary
higher-order/dependent syntax. The completed route should remain available.

[#307's execution report](guarded-stream-execution.md) supplies **checked**
finite-prefix correctness and delivery under explicit primitive realization
and availability contracts. Streams are not finite canonical data: their
relevant guarantee is each requested finite observation. Its causal-but-not-
indexed operation control is useful precedent for stating exactly what a
semantic operation must supply to become executable. Do not make stream
productivity depend on a claim that a whole infinite stream terminates.

## Opaque stuck-term control

The following is a **paper-level counterexample specification**, not a newly
checked Lean result and not an existing `WeakMachine` constructor.

Start with the omega-free typed language and add a closed ground constant
`κ`. Preserve all ordinary typing and beta rules. Declare only literals and
lambdas to be values. Add no reduction rule for `κ`. Extend the ordinary
function model by interpreting `κ` as zero.

Then `κ` is well typed and closed, its model value is zero, and the model can
still validate the ordinary beta equations. Yet the specified evaluator has
no next step for `κ`, and `κ` is not a literal or a value. It is stuck, rather
than divergent. The proposed ground-canonicity conclusion fails even though
semantic meaning is supplied. An equation proving its meaning equals zero
does not add an operational rule.

The counterexample concerns `κ` itself, or an execution that reaches and demands
it. Its mere occurrence in a larger term does not imply stuckness. For example,
`(λf. 0) (λx. κ)` returns zero under the same call-by-value strategy because the
argument lambda is a value and its body is never evaluated. A demanded `κ`
would instead block execution. This paper-level control therefore follows the
demand distinction above; it does not require rejecting every expression that
contains an opaque constant.

| Control | Closed? | Can step? | Ground numeral/value? | Outcome |
| --- | --- | --- | --- | --- |
| Current `.lit 0` | Yes | No | Yes | Terminal canonical data. |
| Current `.omega` | Yes | Yes, to itself | No | Infinite execution, not stuck. |
| Proposed `κ` | Yes | No | No | Stuck under the specified extension. |
| Open variable | No | Not in isolation | Neutral | Outside closed-canonicity hypotheses. |
| Fuel timeout on a reducible term | Yes | Possibly | Not yet established | Budget exhaustion; not a divergence or stuckness proof. |

This control must be implemented as an opt-in test language or explicit
signature policy in a follow-up, not as a new host axiom. Repair choices are
precise: exclude `κ` from the executable fragment, require an implementation
with a terminating canonical-result proof, or extend the operational rules and
prove their compatibility. Declaring every opaque term a “value” would instead
weaken the intended numeral contract and is not the proposed repair. Under
#396, a separate value-plus-identity extraction result could also be useful;
it would retain its different advertised guarantee.

## Bounded construction plan

**Recommended next implementation:** expose the existing embedded-image
ground-canonicity result through a structural omega-free admission interface,
with a checked opaque-extension rejection. No full cubical theory, new kernel
axiom, audit exception, or ordinary-client migration is needed.

1. Define structural `NoOmega` on existing `WeakHigherOrder.Term`. Prove
   `NoOmega (embed t)` by induction. Construct a back-translation for admitted
   terms into `HigherOrderComparison.Term`, choosing one fixed literal tag;
   prove `embed (back t h) = t`. These proposed coverage results identify the
   admission predicate with the embedded image without equating distinct tags.
2. Prove renaming/substitution closure under admitted substitutions, including
   binder lifting, and preservation by existing machine steps. Reuse existing
   substitution machinery and check compatibility of `embed`/back-translation
   with it. These are proposed closure/coverage laws, not new totality axioms.
3. Apply existing `recovery`/`TotalRel` and `Examples.WeakMachine.recovered` to
   the back-translated term, then rewrite by the coverage equation. This gives
   a source reduction to the numeral independently denoted by the total term.
   Use `terminal_unique` for uniqueness and `execute_sufficient` for every
   sufficiently large fuel. Do not construct a second logical relation unless
   an additional consumer exposes a specific obligation this route cannot meet.
4. Package the consumer result: admitted closed ground terms have a unique
   numeral, finite reduction, and sufficient evaluator bound. Exercise nested
   beta reduction under binders, duplicated arguments, zero fuel on values,
   insufficient fuel on a returning term, and `omega` exclusion. Include a
   returning term with an unforced omega-bearing lambda to demonstrate that
   the predicate is conservative. The semantic beta count and machine steps
   have different contracts; no count equality is required. If bound existence
   is proved only in `Prop`, do not call it an extracted executable bound;
   executable extraction requires computational proof data or a separately
   justified algorithm.
5. Implement the `κ` control in a separate test extension. Prove its typing,
   semantic assignment, no-step fact, and non-value fact. Demonstrate that a
   primitive operational-realization policy rejects it until a real evaluator
   clause is supplied. Do not modify the current machine's `no_stuck` contract.
6. Recover existing direct APIs and examples unchanged. Add statement review,
   runtime tests for the selected evaluator interface, the required full
   compilation/proof audit, and independent reviews. Report the admission and
   closure policy, strategy, fuel behavior, and unsupported extensions.

The existing image theorem may first be exposed through a small public facade;
that packaging need not wait for the structural coverage proof. Conversely,
canonicity for the image does not establish all proposed `NoOmega` laws or
classify every returning partial term. No new embedding is needed: the
implemented embedding and recovery are the starting point.

For a later cubical experiment, first freeze a rule and declaration slice
from #321 with an independently specified source reduction relation, canonical
Nat forms, and executable primitive/provider conditions. Construct the
computability argument for that slice and its substitution behavior. Only
then enlarge it to the particular cubical operations required by a consumer.
The current algebraic soundness theorem is reusable as semantic evidence; it
is not the missing computational relation. This separate milestone is not a
blocker for the weak-machine theorem.

## Coordination and decisions

| Owner | Concrete handoff | Dependency policy |
| --- | --- | --- |
| [#36](https://github.com/VladimirMarko/conaled/issues/36), [#235](https://github.com/VladimirMarko/conaled/issues/235) | Schedule structural coverage and public packaging of existing embedded-image canonicity, plus the opaque control; retain the full partial machine. | No blanket wait for cubical foundation work. |
| [#321](https://github.com/VladimirMarko/conaled/issues/321) and its future coverage owners | Reuse constructed semantics; name a future operational rule slice and provider policy separately. | The closed bounded model ticket is not reopened or relabelled as a canonicity proof. |
| [#214](https://github.com/VladimirMarko/conaled/issues/214) | Reuse staging/quotation where useful. | Its accepted staging deliverable is not missing NbE work. |
| [#396](https://github.com/VladimirMarko/conaled/issues/396) | Compare an opaque term with value-plus-identity recovery, retaining the witness and source-execution distinction. | A different useful guarantee, not a prerequisite for machine canonicity. |
| [#398](https://github.com/VladimirMarko/conaled/issues/398) | Reuse the closedness/canonical-form distinction; own open neutrals, dependent/cubical normalization and equality completeness. | Closed ground evaluation does not settle its open-term question. |

The architectural conclusion is to make computational guarantees selectable
and explicit for each fragment. Sound interpretations remain useful even when
a setting does not support a total evaluator. Executable compilation clients
need the stronger local contract, while higher-identity proof clients may need
witness-preserving interpretation or extraction. These interfaces should share
proved bridges where available, without requiring all settings to satisfy one
universal normalization or decidable-equality contract.
