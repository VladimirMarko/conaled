# Selected bridge route: forward histories for active force occurrences

Local10019 remains open. This is the selected implementation design, not a
proved raw-to-pure execution theorem. The pure evaluator, continuation split
and recurrence obstruction are focused-checked. Representation, Creation,
Compatibility and Memory supply separate ingredients; their own validation
records determine their checked status. Root owns the complete bridge, source
domain, frame/control representation, acceptance gates and checkpoints.

## Decision and induction measure

Use a forward simulation carrying one actual pure prefix witness for each
active raw memoize-frame occurrence. Do not also implement a nested body-run
simulation with a separately reconstructed raw occurrence tree.

Strong induction on the remaining actual raw finite count is sufficient. Most
cases consume one raw transition. A permitted recursive declaration consumes
its complete creation/closing prefix of3*binding-count+2 transitions. Cache-hit
expansion reuses an already retained finite pure evaluation certificate; its
possibly larger pure count is not a recursive induction argument. The method
does not need a termination witness for an unforced thunk, a no-reentry premise,
unique active addresses, or an acyclic heap/value condition.

The alternative all-outcome body decomposition is mathematically viable:
raw Decomposition.evaluates_split_all supplies a strictly smaller isolated body
run after paying the force-entry transition, so simultaneous simulation and
cache-witness construction need not be circular. However, transferring raw
body-entry occurrences through those reconstructed subruns adds trace-splitting
and containment bookkeeping. Forward histories make that provenance explicit
at the actual entry and close the cache certificate from already executed pure
steps. This is the chosen route.

## State, code domain and chosen representations

The immutable World maps each raw suspension address to finite body/capture/
descriptor Meaning. Durability.Extends retains existing meanings literally.
ValueRep and EnvRep are monotone under that extension. GroupRep records the
original creation template and remains meaningful after members are cached.

Memory.StateRep deliberately expresses only bounded raw memory and justified
cells for World entries. CellRep.thunk relates the raw capture to
Meaning.environment. CellRep.cached carries ValueRep plus an actual finite
Pure.Machine evaluation of that immutable body returning the represented value.
There is no initial body witness for an unforced cell. StateRep.memoize already
allows a cell that is cached before replacement, which is necessary to avoid
assuming the desired nonreentry result.

Hereditary code validity is a separate necessary condition. ExpressionAllowed
on the source and ParametersCompatible alone are insufficient: an allowed
primitive could return corresponding raw/pure closures containing a reference
expression, satisfying ValueRep while later raw execution allocates and pure
execution reports an excluded-effect fault. Require the needed code domain
through initial captures, stored meanings, closure/group data and permitted
primitive results as well as the visible source term.

Existing Grammar parses opaque inherited phrases and does not supply that
recursive validity. Static.HasType.recursive includes distinct binders, and
RecursiveBindingsHaveType.cons includes Core.RecursiveRhs. Full typing is not
needed: it would exclude useful expectedFunction, expectedBoolean and primitive
faults. Reuse ExpressionAllowed/PatternAllowed and require only each nested
recursive group's Core.Recursive.Permitted RHS shapes and binder Nodup. No
extra record-label uniqueness, nonempty-clause, namespace or value-type
condition appears necessary for the execution bridge itself.

Check finite Group descriptors by their source RHS code and outer environment;
do not expand Group.members recursively inside the domain predicate. Retain
the chosen pure values when worlds extend. ValueRep is a relation, not a
uniqueness theorem: a raw closure with an empty recursive component can have
both a plain closure view and a view with an empty group descriptor. Cache
certificates are canonical by their actual pure body evaluation, as in
CellRep.cached_unique. If cached output code validity is needed, derive it by
pure code-domain preservation or carry a domain witness for that chosen cached
certificate; do not silently infer it from StateRep alone.

## Per-occurrence history invariant

Pair raw and pure stacks one frame at a time. Ordinary frames carry the needed
environment/value representation and hereditary code-domain facts. A raw
memoize(address, callerEnv, innerPattern) frame pairs with the pure
force(pureCallerEnv, innerPattern) frame and its immutable World meaning M.

For every raw memoize occurrence at stack index i, retain a natural k and:

    Pure.Reaches k (Pure.start M.environment M.body)
      <currentPureControl, pureStack.take i>

The selected stack prefix contains exactly the frames inside that force's
body, excluding its own force frame and all callers below it. Using occurrence
positions, rather than an address-indexed map or set, permits duplicate active
addresses while proving them incompatible with a finite completion.

World extension preserves each history's start literally. The history is a
proof of an already executed finite pure prefix, not a premise that its body
will finish. Initial empty stacks have no history obligations.

## Local simulation cases

**Ordinary transitions.** Establish a local pure step or finite pure prefix,
uniform in an appended tail. Update the paired frames/values and advance every
older history through the corresponding stack prefix. Pure.Reaches.append
handles the caller suffix; composition advances the saved prefix. World
extensions transport representation facts without changing pure values.

**Uncached body entry.** StateRep supplies the thunk and represented capture.
The pure machine takes its actual suspended-pattern body-entry step, retaining
the exact body/capture/descriptor event. Push the paired raw memoize/pure force
frames. The new occurrence receives the zero-step history from M's isolated
body start; every older history advances by that entry step. This construction
does not require the address to be absent from older frames.

**Normal memoization.** The top occurrence's interior stack is empty and its
history ends at pure value q. Append the ordinary one-step final delivery to
that history with Reaches.evaluates, obtaining a finite evaluation of M's body
returning q in k+1 transitions. Control representation gives ValueRep for the
actual raw value. StateRep.memoize then justifies the raw write. Pop the current
history and advance older histories by the pure return-to-inner-pattern step.
An earlier nested write to the same address is not excluded as a premise.

**Raised return.** Pop the raw memoize/pure force pair without that frame's
write. Retain the reached raw state and every other cache certificate. Advance
older histories through the actual exceptional unwind. Source handlers remain
ordinary matching continuations. A machine fault remains terminal rather than
becoming a catchable packet.

**Cache hit.** Obtain the finite normal pure body certificate from CellRep.cached.
For a certificate of n transitions, replay an unfinished pure prefix of n+1:
one suspended-pattern entry, n-1 body transitions before isolated delivery,
and one return to the caller's inner pattern. The raw hit itself takes one
transition. Lift the replay through the existing caller tail and advance each
older history by that same local prefix. The inner pattern has not run at the
endpoint. Extra pure body entries generated by this replay are not additional
raw body entries; never claim equality of traces or counts.

**Recursive creation.** Consume the actual uninterrupted permitted creation
prefix as one simulation block. Creation.PendingGroup separates prospective
final meanings from pre-SRec raw captures. At closing, closed_new/closed_old/
closed_environment establish represented captures and retained old cells.
Only then require closed StateRep for the extended world. The pure machine's
one recursive-formation step reaches the corresponding body environment.
Advance old active histories by that pure step; creation enters no suspension
body. Arbitrary observations stopping inside creation need a pending-state
contract, but are unnecessary for this finite-completion bridge and its body-
entry observations. No successful closed invariant is assumed midway through
SRec preparation.

## Deriving absence of active reentry

At a new raw body entry for address a, suppose an older memoize occurrence has
that same address. The two World lookup equations identify the exact immutable
Meaning M. Extending the older occurrence's history by the new pure entry gives
a positive prefix from M's isolated start to that same start with caller frames
appended. Pure.recurring_prefix_not_terminates therefore rules out a finite
completion of M's body.

Construct the next history invariant even with both occurrences present, then
apply the simulation induction hypothesis to the strictly shorter remaining
raw run. Its finite pure continuation starts at M's body with the full caller
stack. Pure.not_terminates_append contradicts that continuation. Thus the
finite raw execution cannot contain the active reentry. No address-distinctness
or reentry-free property was used to construct the next invariant or invoke
the induction hypothesis.

Every actual uncached entry creates a paired occurrence and preserves its exact
meaning; active occurrences persist until their actual normal/raised exit or
a terminal fault. A final theorem may expose this as absence of body events
whose address already occurs in the raw memoize stack. Successful cache-write
counts, repeated exceptions and distinct creation/alias questions remain
separate corollaries, not implicit consequences of equal final values.

## Narrow helper APIs and ownership

The map worker added Pure.Recurrence helpers Reaches.one/trans,
evaluates_boundary_reaches and force_prefix_of_certificate. Their connected
client target passed the serialized focused check in
active-validation/suspension-pure-recurrence-r3.{log,json}, exit0,744jobs,
with unchanged recorded input hashes. The literal certificate replay reaches
the still-unmatched inner pattern in3 transitions and its actual failing
Bind continuation completes in6; a raised boundary is reached in3.
The existing15/8 recurrence clients remain checked. These facts establish
only the pure helper APIs, not this complete bridge design.

Existing Machine/Value/Representation/
Memory definitions remain untouched. Root owns frame/control representation,
history invariants, domain assumptions and the full raw bridge.

Raw Recursive.create_prefix already accepts a tail, while enter_body_prefix
and evaluates_iff start at an empty stack. The general raw
evaluates_strip_prefix helper is private. Root will coordinate only the narrow
append/strip exposure needed to consume recursive blocks under existing caller
frames. No new generic evaluator or alternative semantics is required.

The earlier all-outcome Decomposition and pure continuation laws remain useful
checked APIs, but this design does not schedule a second occurrence-tree
implementation. The main theorem and domain preservation remain unproved.
