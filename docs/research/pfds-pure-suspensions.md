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
from returning a closure containing an excluded effect. A primitive-preservation
law for the eventual code domain remains necessary.

The pure continuation and recurrence modules also pass their focused clients.
A positive actual prefix returning to the identical isolated input with caller
frames appended precludes every finite result, including faults. The cyclic
function/suspension example has a checked fifteen-transition recurring prefix
and an eight-transition source entry. The universal nontermination result uses
those exact prefixes and evaluation-count uniqueness, rather than inferring
divergence from a failed bounded search.

## Remaining proof obligation

All these development results remain unaccepted until the complete candidate
passes its integrated build, exhaustive audit and independent reviews. They
do not yet prove pure nonreentrancy for the raw machine. Cache-cell validity is
under focused development: unforced thunks need represented captures, whereas
cached values need an actual finite pure-body evaluation. The execution bridge
must construct those certificates from earlier raw body execution. It must not
assume all unforced thunks terminate, or use nonreentrancy to justify the
certificates.

Every actual nested body entry must map to a proper nested pure body execution.
Exact pure input/count uniqueness can then contradict active self-reentry.
Equality of final values alone does not supply that occurrence argument.
Source and auxiliary event traces and costs remain different; successful
cache/write-count consequences need separate proofs.

The representative checked clients include mutual function/suspension recursion,
repeated forcing without a cache, a finite cyclic prefix and a suspension that
returns a closure referring back to itself. The separate recurrence argument
supplies the negative result for the cyclic example. Full isolated-candidate validation, exhaustive proof audit,
final verification and independent Standards/Spec review remain required.
