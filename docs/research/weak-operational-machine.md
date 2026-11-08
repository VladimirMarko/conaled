# Syntactic execution for the weak higher-order fragment

Issue [#308](https://github.com/VladimirMarko/conaled/issues/308) connects the
existing typed call-by-value fragment to a substitution-based small-step
evaluator. The executable evaluator operates on source terms, not on the
`Comp` result of `WeakHigherOrder.run`. Both earlier APIs remain available.

## Operational interface

`SquareKit/WeakMachine/Execution.lean` defines closed syntactic values,
`Step`, executable `next`, finite `Steps` and infinite transition sequences.
Literals and lambdas are terminal. Application evaluates its function first,
then its argument, then substitutes that value into the lambda body. Omega
steps to itself at every type. Evaluation does not enter a lambda body early.
The relational transition and `next` agree; closed well-typed terms either are
values or have a successor. Terminal values cannot step, and deterministic
transitions give unique terminal outcomes. Stuck means nonvalue with no next
transition and is impossible for these configurations. These statements do
not cover open or malformed raw terms.

Configurations carry their type in `Term [] a`, and every transition preserves
that index. The substitution lemmas in `Substitution.lean` establish syntax
equalities for renaming, substitution composition and closing beneath binders.
They are not obtained by identifying denotationally equal syntax.

There are no closure-management or stack-administration transitions here.
One source transition is a beta contraction or the active omega step, possibly
lifted through application positions. Computing that transition still traverses
syntax and may copy a substituted term. Source-step fuel is not a hardware
cost or an allocation bound.

`execute` inspects terminality even with zero fuel. A successor consumes one
unit; timeout retains the current residual term. `execute_sound` connects
successful runs to finite source transitions, and `execute_sufficient` supplies
a bound above which every fuel budget succeeds for a finite terminal path. Timeout has no
divergence interpretation. A returning identity application times out at zero
fuel, just as omega does.

## Adequacy through related inputs

`Adequacy.lean` first relates syntactic execution to the existing behavioral
model. A returning computation has a finite path to a syntactic value related
to its semantic value. A spinning computation has a finite path to a syntactic
configuration with an actual self-loop. This second clause retains the finite
prefix that `Comp.spin` collapses.

At ground type the value relation identifies the literal numeral. At function
type it identifies a syntactic lambda and requires its beta-instantiated body
to behave correctly for every **related syntactic and semantic input**. It
does not assert that every host function is definable. `related_application`
is the reusable higher-order application result; the identity example applies
it at arbitrary types, including function inputs.

The fundamental theorem inducts on the original source term with an arbitrary
related closing substitution and semantic environment. The lambda case uses
the syntactic beta/lift equation to extend the substitution beneath a binder.
Application composes function, argument and body paths in call-by-value order.
A divergent endpoint is propagated through the active position using the
same transition rules. The proof does not induct on reduced syntax size or
assume that substitution shrinks a term.

A finite path to a self-loop constructs an infinite execution. Determinism and
terminal irreducibility make any finite terminal path incompatible with an
infinite execution. Together with the fundamental theorem these establish both
directions of return agreement at closed ground type and divergence agreement
at every closed type. Composing with `observed_return` and
`observed_divergence` gives agreement with the independent partial denotation.
No unrestricted silent-stuttering simulation is used as a divergence argument.

The bridge preserves weak observations, not a theorem equating the behavioral
model's finite counts with all implementation costs. Literal zero and identity
applied to zero have the same return observation but different source reduction
lengths. No equality of their strong counted behavior is inferred.

## Applications and boundaries

`Examples/WeakMachine.lean` covers literals, a returning redex, explicit omega
execution, a lambda whose invocation diverges, and the call-by-value control
`(lambda x. 0) omega`. Function-first and argument-before-body transitions are
checked separately. The existing `closeSeven` example returns seven through a
binder, preserving the outer variable rather than capturing the inner
argument. The #285 total embedding is recovered through the existing semantic
comparison without changing its interface.

`context_returns` and `context_divergence` transport the supported finite
contexts to machine observations. Their premise remains open denotational
equality, and they use the existing `Context` constructors. They do not prove
full abstraction, completeness of contextual equality, arbitrary-context
preorders, or unconditional beta equivalence. The existing value-substitution
hypotheses remain in place; the operational beta rule requires a syntactic
value.

The executable assertions are in `scripts/WeakMachineTest.lean`; run them with
`direnv exec . lake env lean --run scripts/WeakMachineTest.lean` after building
`Examples.WeakMachine`. Repeated timeout tests are runtime checks of the bounded
runner. Separate infinite-path proofs establish divergence. Formal modules and
examples enter the normal build and exhaustive axiom audit. Immutable candidate
receipts and independent reviews belong to the enclosing orchestration.

Adopt this operational bridge for the existing fragment while retaining its
native model and denotation. The author-facing obligation for a new primitive
is an independent transition specification and a related-input fundamental
case, including a finite divergent endpoint argument when needed. General
recursion, effects or nondeterminism would require revisiting that argument;
this fragment's finite path to active omega must not be assumed for them.
There is no demonstrated need here for a new general preservation interface,
a CEK stack, or a categorical weak-GSOS layer. Those broader choices remain
with #235/#36/#200 when a consumer supplies the missing obligation.

Executing source terms does not execute a translation of source derivations.
The executable proof-translation residual under #339 is unchanged. This work
imports no machine-adequacy theorem from the weak-similarity literature and
makes no claim about its call-by-name instances or categorical hypotheses.
