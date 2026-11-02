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
matching resumes; exceptional exit leaves the thunk uncached. These local
results preserve the unrestricted raw transition and its body/cache events.

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

## Remaining acceptance and cache work

These are focused-checked development results. Full isolated-candidate build,
exhaustive audit, independent Standards/Spec review and immediate final
verification remain required. Source and auxiliary event traces and costs are
different. Successful cache persistence/reuse consequences and a connected
source-program-to-later-cache-hit client remain to complete. Repeated exceptions,
fresh allocation identities and unrestricted effectful reentry must retain
their distinct behavior; no unconditional single-write claim is justified.
