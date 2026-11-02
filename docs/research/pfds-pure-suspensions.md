# Pure recursive suspension forcing

This is the incomplete implementation record for local10019, required by the
complete book/thesis union. The source is the recursive-forcing remark in
[thesis AppendixA](https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf),
printedp135. The unrestricted [suspension foundation](pfds-suspensions.md)
retains effectful reentry. No blackhole rule is inserted into that machine.

## Current representation and execution

The effect predicates use the existing core expressions and patterns. They
exclude mutable reference expressions, reference patterns and generative
exception names. Functions, finite data, recursive bindings, suspension forms,
ordered matching and fixed exceptions remain available. Effect purity is
separate from permitted recursive RHS shapes, binder distinctness, nonempty
matches, identifier classification and typing.

Finite pure values contain explicit suspension meanings. A recursive group
descriptor contains its source function/delay right-hand sides and the earlier
environment; it contains none of its newly created members. Each member
retains the same descriptor, and repeated unrolling supplies the same body
environment. This avoids cyclic Lean values and makes recursive function/
suspension dependencies explicit.

The auxiliary machine uses `Progress.Machine`, `Evaluates` and `search`, with
the existing resource adapters. It has no memoization or raw memory addresses.
A suspended-pattern entry records its exact body, capture and group descriptor,
then executes the body through explicit local transitions. Primitive meanings
are parameters; no raw-to-pure primitive compatibility law is assumed silently.
Excluded effects have explicit faults. Its counts describe these auxiliary
transitions, not source allocation cost or host running time.

The separate all-outcome continuation decomposition extends the existing raw
machine laws without changing its transition. It distinguishes an isolated
body fault from a normal delivered boundary whose caller later faults. Both
retain exact transition counts. This avoids assuming type safety merely to
decompose a finite execution.

The immutable world reuses `Durability.Heap` and `Extends`. A represented raw
address retains the same finite body meaning through heap growth and cache
writes. Original recursive creation templates have a separate representation;
the public unrolling theorem relates actual `Rec` to group members without
requiring their suspension cells to remain unforced. The representation and
its mutual-recursion/returned-closure clients pass focused checks.

Actual recursive creation now constructs a prospective world extension from
its receipt. New thunk captures are pending until SRec closes them; a separate
pending-group predicate records that phase without supplying body results.
Distinct binding names ensure every allocated delayed member is an effective
SRec target. Closing yields represented expanded captures and retains all old
occupied cells. The connected mutual group and a duplicate-name counterexample
pass focused checks.

Primitive compatibility quantifies over every represented input and immutable
world. Fault and result classes remain explicit. Identity, integer and Boolean
adapters satisfy the law; memory validity and hereditary source-code restrictions
are separate. In particular, representation alone does not prevent a primitive
from returning a closure containing an excluded effect. The separate hereditary
domain now checks stored code, captures, selected primitive tokens and finite
group descriptors, including nested permitted recursive RHS shapes and distinct
recursive names. Its usable basis preservation and connected fault/recursive
clients pass focused checks. It does not require full source typing.

The pure continuation and recurrence modules also pass their focused clients.
A positive actual prefix returning to the identical isolated input with caller
frames appended precludes every finite result, including faults. The cyclic
function/suspension example has a checked fifteen-transition recurring prefix
and an eight-transition source entry. The universal nontermination result uses
those exact prefixes and evaluation-count uniqueness, rather than inferring
divergence from a failed bounded search.

Cache-cell validity and its clients also pass focused checks. Unforced thunks
need represented effective captures; cached values need an actual finite pure
body evaluation. Fresh delay, world extension and justified memoization retain
that invariant. A cyclic thunk is valid without a termination witness and cannot
justify any cached value for its known nonterminating pure body.

The history invariant records an actual executed pure prefix for each pending
raw memoize-frame occurrence. It permits duplicate active addresses. Completing
a body prefix constructs its finite certificate; reentering the same meaning
creates a strictly positive recurrence. Control and frame representation keep
the raw and pure continuations aligned without asserting a simulation by
definition. Their connected before/after reentry states pass focused checks.

The local actual delay/force/cache correspondence now passes its full clients.
Delay allocates without evaluating even a known nonterminating body. Uncached
entry starts a new history and advances older ones. A cache hit replays the
stored certificate through the caller's still-unmatched inner pattern. Normal
memoization derives its certificate from the past prefix and writes before
matching resumes. Exceptional exit skips that pending frame's successful
cache write and retains the memory reached so far, including any successful
write by an inner evaluation. These local results preserve the unrestricted
raw transition and its body/cache events.

## Actual execution and self-reentry

Runtime code-domain preservation, world-domain composition and ordinary-step
correspondence now pass their modules and connected clients. Actual recursive
creation consumes its checked raw prefix and one auxiliary step; no body-result
premise is needed. The complete finite correspondence composes these laws with
delay, uncached entry, cached replay, memoization and exceptional return. It
returns an actual pure evaluation and represented final raw state. Its induction
decreases the remaining raw transition count; cached replay uses the already
constructed body certificate. An admitted malformed application still yields
the same expected-function fault. No type-safety assumption is added.

The separate body-entry correspondence handles every actually observed raw
body event without assuming that the enclosing run terminates. Intermediate
recursive-creation states are covered by their proved absence of body events.
At an observed entry, it constructs the related pure configuration and its
per-occurrence active histories. The positive pure recurrence for an already
active address excludes pure completion. Finite correspondence then excludes
every finite raw outcome, including runtime faults and exceptions. Thus the
finite-run absence of an active same-address entry is a conclusion, never an
invariant premise or a replacement transition rule.

The source-facing client starts the mutual function/suspension cycle in an
empty raw heap. Its independent actual prefix reaches the second body entry
after29 transitions, with the original memoize frame still pending at index3.
It consumes the general source theorem to rule out all finite outcomes and
derive failed bounded search for every fuel. It does not posit an active pure
history or infer divergence from testing finitely many budgets.

## Successful cache consequences and their limits

Value-cell persistence now passes its general raw-machine laws and clients.
Given bounded input memory, an actual step preserves the fact that an address
contains some value. The existing configuration-bounded invariant lifts this
through arbitrary finite runs and unfinished or completed observations. A later
suspended match at that address therefore takes the actual cache-hit transition;
there is no new body-entry event for that address. This conclusion does not
require purity or termination of the surrounding computation.

The payload is allowed to change. The checked assignment example changes7 to8;
the existing effectful reentrant program retains its two cache writes. The
checked `Exceptions.raised_body_can_repeat` case in
[SuspensionValuePersistence](../../Examples/SuspensionValuePersistence.lean)
raises without changing its initial thunk, so that particular body can be
attempted again with the same result. In unrestricted execution, the checked
`outer_exception_preserves_inner` and `outer_exception_then_hit` cases in
[SuspensionMachine](../../Examples/SuspensionMachine.lean) retain an inner
successful cache when the outer body raises. No general at-most-one cache-write
trace theorem is claimed. Equal pure meanings at distinct newly allocated
addresses likewise do not identify their storage.

The checked connected literal source program creates and evaluates a suspension,
then returns its address. Its actual raw and pure executions each take15 steps.
Finite correspondence supplies the final represented memory, and result inversion
recovers the exact original empty capture and meaning. A later force uses that
recovered stored certificate, with raw3 versus pure5 steps and unchanged cached
memory.

The connected cached recursive-closure client also passes. It reuses the existing
returningClosure source: a suspended function captures its own suspension, then
uses that back reference after the function is cached. Actual recursive creation
recovers the address meaning; finite correspondence of the residual source run
derives the final cache representation. The actual raw53/pure51 executions return7.
A later application to false reaches the back-reference force after18 transitions,
then consumes the recovered cache certificate under its four caller frames.
Raw hit1 versus pure replay3 followed by the same17-step suffix gives raw36/pure38.
The raw memory is retained exactly. The source's one-body/one-write/one-hit counts
are concrete facts about this client, not a general trace bound.

## Remaining acceptance

These are focused-checked development results. Full isolated-candidate build,
exhaustive audit, independent Standards/Spec review and immediate final
verification remain required. Source and auxiliary event traces and costs are
different. The existing exception, allocation and effectful reentry distinctions
remain part of the contract.
