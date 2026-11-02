# Pure recursive suspension forcing

This is the incomplete implementation record for local10019, required by the
complete book/thesis union. The source is the recursive-forcing remark in
[thesis AppendixA](https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf),
printedp135. The unrestricted [suspension foundation](pfds-suspensions.md)
retains effectful reentry. No blackhole rule is inserted into that machine.

## Current representation and execution drafts

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

## Remaining proof obligation

These initial modules and clients are still under focused development and are
unaccepted. They do not prove pure nonreentrancy. The necessary bridge must
assign stable pure meanings to actual suspension addresses, justify recursive
creation/closing, and construct each cached-value evaluation certificate from
the earlier actual body execution. It must not assume all unforced thunks
terminate, or use nonreentrancy to justify those certificates.

Every actual nested body entry must map to a proper nested pure body execution.
Exact pure input/count uniqueness can then contradict active self-reentry.
Equality of final values alone does not supply that occurrence argument.
Source and auxiliary event traces and costs remain different; successful
cache/write-count consequences need separate proofs.

The representative draft clients include mutual function/suspension recursion,
repeated forcing without a cache, a finite cyclic prefix and a suspension that
returns a closure referring back to itself. No finite prefix is presented as a
divergence proof. Full isolated-candidate validation, exhaustive proof audit,
final verification and independent Standards/Spec review remain required.
