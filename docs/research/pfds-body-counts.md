# Counting actual suspension-body entries

The suspension observer retains the actual transition events in order. The
`eventCount` additive map selects occurrences of one event, and `bodyEntries a`
selects body entries at physical address `a`. These observations compose over
the existing measured workload and its actual intermediate state. An absorbing
finished suffix adds no events.

## The two ways a completed body can be reused

A body-entry transition pushes its actual memoize frame. While that frame is
pending, `FreshEntries` excludes reentering its address. A successful return
writes a value cell; bounded-memory preservation then keeps a value cell at
that address, which makes a later force use the cache.

An exception can instead unwind the memoize frame and leave the thunk unforced.
A surrounding handler can then retry it. The source model retains this
behavior. A finite pure program that returns normally can still enter one
body twice and make zero successful cache writes.

`UnwindsMemoize a config` identifies the precise exceptional exit: the current
control is a raised packet and the exposed continuation is a memoize frame for
`a`. The pending-retention theorem classifies every actual continuing step at
an existing pending address as retaining it, writing it, or performing that
unwind. It uses the public continuation laws and permits duplicate pending
addresses in arbitrary raw configurations.

`NoMemoizeUnwind parameters config a` excludes that structural exit at every
actual unfinished prefix of the selected run. A handler inside the body can
catch an exception before the memoize frame is exposed, so this condition
permits locally handled exceptions. The condition concerns the selected
address; other addresses remain unrestricted.

## Conditional bounds on the same trace

`bodyEntries_observe_le_one` derives the pointwise bound from `ConfigBounded`,
the existing `FreshEntries` predicate and `NoMemoizeUnwind` at the selected
address. The budget may stop while a body is pending or extend beyond an answer.
The raw theorem uses no initial pending-address uniqueness or termination
premise. Its proof preserves the disjunction that the address has a pending
frame or a value cell; each alternative precludes another fresh body entry.

The finite pure source specialization derives boundedness and fresh entries
from the existing representation, admissibility, primitive-compatibility and
finite-evaluation results. It retains the extra no-unwind condition explicitly.
The connected source cases include successful repeated forcing, two distinct
allocations of identical bodies, a handler inside a body and a handler outside
that retries an uncached exception.

## From entry events to distinct debit identities

Projecting the same ordered trace to its body addresses preserves physical
identity. If the derived count bound holds at every address, that projected
list has no duplicates, and its length equals its finite support cardinality.

The persistent realization interpreter can label each body event with its
singleton address and every other event with empty support. With zero unshared
charge, it charges the number of distinct body addresses. The nonrepetition
theorem identifies that charge with the actual number of body-entry events
under the explicit conditions above. The retry case retains projected length
two and distinct support one, exposing the missing condition directly.

This selected metric charges one for each body-entry event and zero for each
other event. The full observer still records every other transition. Work
inside bodies, primitive-operation costs and algorithm-specific debit
assignments require their own correspondence and bounds. The complete
persistent source/work obligations remain open alongside those algorithms.
