# Computational meaning explanations and independent denotation

Research for [#400](https://github.com/VladimirMarko/conaled/issues/400).
Inspected on 2026-11-09 at `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
The recommendation is to retain independent denotation and test an optional
behavioral membership interface on a partial higher-order client. This report
adds a matched methodology comparison to
[#407's compiler assessment](algebra-and-program-specification.md); the counted
stack experiment proposed there is already implemented by #409.

## What a meaning explanation supplies

**Literature.** The [RedPRL paper](https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf),
Figure 1 and §§2–3, distinguishes raw syntax/dynamics, semantic judgments over
programs, and rules used to establish those judgments. Types are explained by
partial equivalence relations on values; program membership requires evaluation
to a related value. Open judgments respect equal closing substitutions. The
refinement calculus is a means of proving these judgments, not their definition.
Its Boolean canonicity theorem concerns semantic membership in that system.

[Computational Higher Type Theory I, v2](https://arxiv.org/abs/1604.08873v2)
extends the explanation to dimension-indexed programs, requiring compatibility
with dimension substitutions and Kan operations. Its simple theory includes
a circle and a particular Boolean-negation line; it is not the later full
univalent universe construction. Thus plain evaluation plus a PER is not yet
a model of the cubical fragment used by conaled.

An operational semantics alone says how expressions step. It need not classify
which programs count as members of a type. A syntactic calculus inductively
presents derivable judgments. A meaning explanation supplies what those
judgments mean and why rules are valid. Mixing these three prevents identifying
whether a failed proof is a missing rule, an invalid program, or a missing
semantic theorem.

## Same task: return a function without running its body

Use the existing partial weak language. The client receives `λx. omega`, returns
that function through a higher-order identity, then optionally applies it to a
numeral. The intended contract distinguishes returning a function value from
termination of every application. This is a proposed comparison task with
existing checked behavior, not a claim that RedPRL admits this lambda at its
ordinary total function type.

| Obligation | Computational membership route | Independent denotation route |
| --- | --- | --- |
| Explain functions | A function type specifies behavior on related members; ordinary total membership rejects a function diverging on an admitted argument | Interpret into a domain of partial functions and state which applications return |
| Return the function | Need a type/specification permitting partial bodies, or a different value observation | Existing partial relation can retain a lambda value whose body diverges |
| Execute its application | Prove return membership, or specify divergence/partial correctness separately | Use operational adequacy for the partial denotation; no totality conclusion from typing |
| Reuse under substitution | Prove functionality for related closing substitutions, plus dimensions if cubical | Prove the relevant environment relation and interpretation/substitution laws |
| Admit another model | Validate all adopted semantic principles, not only the printed type constructors | Supply the selected operations/laws, then realization evidence only for requested execution observations |

**Local source evidence.** [CountedStack](../../Examples/CountedStack.lean)
contains `retained_partial_function`, `applied_loop` and `no_totality`, reusing
the existing partial semantics and machine adequacy. Its
[implementation record](counted-stack-contracts.md) explains that no decoder
for arbitrary host functions is required. The
[canonicity module](../../SquareKit/WeakMachine/Canonicity.lean) supplies an
optional sufficient total-fragment predicate. Its conservative rejection of
unforced omega is not an intrinsic limitation of the partial language.
[OpaqueControl](../../SquareKit/WeakMachine/OpaqueControl.lean) independently
shows that assigning zero as a meaning does not establish a return.

[Adequacy](../../SquareKit/WeakMachine/Adequacy.lean) already defines
`Behavior`, `Related`, `ClosingRelated`, `fundamental` and
`related_application`. Its behavior relation includes a finite return or a
finite path to a self-loop for the supported partial syntax. Thus a proposed
behavioral predicate and related-environment closure would mostly rename
existing machinery. No fresh wrapper or theorem is justified by this example.

For a total comparison, replace the input by `λx. x`. Both routes should prove
that the caller returns a function and its application returns the supplied
numeral. The computational route needs the function membership and substitution
argument; the denotational route uses the existing related-input theorem and
adequacy. Equal task and observations are essential: comparing total membership
with partial denotational typing would charge one route for a stronger claim.

## Principles, model scope and author costs

The computation-first route can validate equations by quantified behavior of
closed programs, but such equations need not be decidable syntactic conversion.
The denotational route permits independent mathematical interpretations when
their operations satisfy the selected laws. Neither route automatically
supplies all geometric models, a compiler, or an algorithm deciding equality.
The [cooltt discussion](https://github.com/RedPRL/cooltt/discussions/186)
records the authors' concern about model applicability and repeated equality
obligations, motivating typed normalization and elaboration. That experience
is not a measured comparison of these conaled clients.

**Assessment.** For conaled, building a fresh PER universe would duplicate
substantial functionality before proving any author benefit. A behavioral
predicate over the existing partial realization could instead expose exactly
which demand requires totality. Setup would comprise the observation relation
and its substitution theorem; repeated work would comprise argument evidence
and the requested return or divergence certificate. Existing direct compiler
clients should incur none of that setup. No time/token productivity comparison
has been measured here, and proof length alone would not establish one.

The [language direction](../language-direction.md) prefers compositional meaning
independent of a chosen execution mechanism. Treating operational membership
as the only meaning for every backend would conflict with that preference and
restrict admissible settings without evidence of a corresponding benefit.
Using it as a realization of an independently specified contract is compatible.
No ADR change follows from this investigation.

## Experiment and rejection criteria

Defer a standalone interface implementation: #409 already proves the basic
partial-client behavior, and no repeated author failure is established here.
If a consumer needs reusable admission specifications, the bounded experiment
under #235/#200 is to compare direct partial
adequacy proofs with an optional behavioral predicate for the two higher-order
clients above, with identical observations. Reuse the existing syntax,
application relation, return/divergence bridge and #410 demand controls. Reuse
the existing closure under related environments, and show why membership at a
total function specification rejects the diverging body while the partial
specification admits returning it. Add one composed caller to test reuse.

Record setup, per-client obligations, repairs and agent resources separately.
Reject the added interface if it only stores the final desired theorem or
requires another syntax induction per caller. Retain the direct route in that
outcome. This is distinct from #409's unit-cost finite first-order experiment
and from #398/#399's conversion algorithms. A full computational foundation,
a cubical PER model and claims of general productivity are deferred.

This documentation change adds no formal declarations. Local claims above are
inspection of existing checked-source statements; acceptance for a later
implementation requires statement review, checked examples and the README
build/proof audit. Literature theorems have not been formalized here.
