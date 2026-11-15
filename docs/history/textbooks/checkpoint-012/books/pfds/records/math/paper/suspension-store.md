# Suspension memory slice — local ticket 10014

## Assignment and status

Implementation within the enclosing suspension-foundation loop; no nested
review/workflow. Fixed base: `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.
Shared worktree: `suspension-foundation`, branch `pfds/suspensions`.
Ownership began with `Applications/Suspensions/Store.lean` and
`Examples/SuspensionStore.lean`, and root subsequently assigned
`Applications/Suspensions/Continuation.lean`,
`Applications/Suspensions/Invariant.lean`,
`Examples/SuspensionInvariant.lean`,
`Applications/Suspensions/Recursive.lean`, and
`Examples/SuspensionRecursive.lean` within the same enclosing loop.
Root owns snapshots, the index, commits, entrypoint, tracker and all other
source paths. No staging or committing was performed by this worker.

Requirements read: `session/requirements/suspension-foundation.md` version 1,
the complete relevant memory/forcing/recursive-binding portions of
`session/research/suspension-foundation-inventory.md`, and repository
architecture, domain, implementation, example-driven-development and build
guidance. Root approved the types and operation argument order before the
first source draft.

Current focused status:

- Store and Examples.SuspensionStore compiled successfully in a combined batch
  that root subsequently interrupted during an independent prerequisite; it
  was not a successful whole batch. Their unchanged dependencies have since
  been consumed by the machine and later checks.
- Continuation r3 passed with unchanged recorded inputs, exit 0.
- Invariant r3, including all connected examples, passed with unchanged
  recorded inputs, exit 0 and 745 jobs. It retains the default proof limits
  and all lint checks.
- Recursive r3, including the typed cyclic client and inverse execution bridge,
  passed with unchanged recorded inputs, exit 0 and 778 jobs. Afterwards only
  documentation was clarified to distinguish RHS shapes from full inherited
  source well-formedness and avoid implying every answer class is reachable.
  No definition, theorem statement or proof was changed after that check.

Detailed evidence and source/client reviews follow. This is neither Appendix A
completion nor an acceptance claim.

## Source and mathematical boundary

The memory changes are from the supplied thesis Appendix A, printed pp.
133–135, reread directly for this slice, with the source distinctions recorded
in the foundation inventory.
The 1990 Standard ML Definition is the inherited base; its exact identity is
recorded by root in `session/research/sml90-source-identity.json`. This slice
does not restate inherited expression/pattern evaluation, Rec on function
closures, typing or exception propagation. Those remain other owned portions
of the same implementation.

The generic memory cell stores either a value or a code/captured-environment
pair. Reference and suspension uses share one address space. Exception names
remain a separate finite state component. The numerical frontier is an
implementation choice supplying finite memory and deterministic fresh
allocation, not a restriction on addresses appearing inside stored values or
environments. It imposes no acyclicity or backward-reference ordering.

## Public API agreed with core/evaluator owners

All names below are under `Suspensions`.

- `Cell Code Env Value`: `.value value` or `.thunk code capturedEnv`.
- `State Code Env Value`: `memory`, `next : Nat`, `exceptionNames : Finset Nat`.
- `Bounded s`: addresses at or above `next` are absent. Operations do not carry
  this law as a field; callers prove it for the executions being interpreted.
- `domain s : Finset Nat`: occupied addresses below the frontier. `mem_domain`
  proves that, on bounded states, this is the entire memory domain.
- `replace s address cell`; `memoize s address value`.
- `allocate s cell : State × Nat`; `delay s code capturedEnv : State × Nat`.
- `FreshAllocation beforeMemory cell address afterMemory`: a frontier-free
  pointwise relation stating freshness, installation and unchanged other cells.
- `srec s targets extendEnv`, with `targets : Finset Nat` and
  `extendEnv : Env → Env`.
- `RecursiveTargets s targets`: every selected address contains an unforced
  thunk. This is the applicability premise supplied by valid recursive source
  binding; it is not silently assumed for every raw SRec call.

Principal laws are `Bounded.fresh`/`occupied_lt`; `replace_lookup`/`other`/
`bounded_of_occupied`/`domain`/`overwrite`; `memoize_lookup`/`other`/`bounded`/
`domain`/`overwrite`; `allocate_lookup`/`other`/`bounded`/`realizes`/`extends`/
`retains`/`distinct`; `delay_captures`/`bounded`/`realizes`; `srec_thunk`/
`value`/`absent`/`other`/`isSome`/`domain`/`bounded`; and
`RecursiveTargets.updated`/`srec`.

## Statement review and intended cases

### Creation and finite memory

`FreshAllocation` mentions no chosen frontier, so the deterministic allocator
is a realization of a genuinely less prescriptive relation. Its relation
retains all other cell observations, not only old occupied values.
`allocate_realizes` needs `Bounded` to prove the chosen frontier fresh.
Allocation advances the frontier by exactly one and preserves exception
names. `Durability.Extends` is used only for this fresh operation, backed by
the preexisting `extends_put`; it is not claimed for replacement or SRec.

Creation stores the supplied code and actual captured environment. No body
evaluator is a parameter or invoked by `delay`. The later source-specific
machine still has to establish the corresponding evaluation rule and events;
this memory module alone is not a source evaluation proof.

The concrete creation case stores binding 10 to the number 1, then creates an
unrelated thunk with binding 10 to 2 and allocates an ordinary value cell. The
first thunk keeps its original environment, both thunks share memory with the
value cell, and exception names 17 and 23 remain unchanged. A separate case
uses equal code/environment in two creations and proves their addresses differ
while the first stored thunk remains intact.

### Replacement and repeated memoization

Raw point updates are total. A valid in-range address suffices for boundedness;
an actual old occupied-cell lookup supplies that premise and additionally
permits domain preservation. Memoization accepts an old cell of either kind.
Requiring it still to be a thunk would incorrectly exclude an outer successful
write after an inner reentrant success.

`memoize_overwrite` states equality of the whole final state after writing two
values at the same address with the state after just the later write. The
concrete case writes 7 then 8 and proves final value 8, unchanged unrelated
thunk/reference, fixed frontier, unchanged names/domain and boundedness.
This is a law of the two actual memory operations. It does not claim an
arbitrary source body terminates, nor replace the later evaluator witness for
the appendix's reentrant program.

### Recursive environment extension

SRec maps only environments in selected thunk cells. It keeps their code,
leaves all outside-target cells unchanged, and leaves values even at selected
addresses unchanged in its raw total behavior. Missing cells remain missing.
The pointwise `isSome` equality covers every address, independently of frontier
validity; the finite `domain` equality and boundedness follow separately.
No exception names or frontier entries change.

The source-specific valid-binding premise `RecursiveTargets` exposes old
thunks and their extended closures at every target. This does not by itself
prove the core's binding evaluator always supplies that premise; the core
correspondence must establish it for the allowed recursive forms.

The SRec case extends only the first thunk with a binding to address zero,
which is the thunk's own address. A tagged example payload distinguishes this
address from ordinary numerical values. The unrelated thunk, ordinary reference
cell, finite domain, frontier and exception-name set remain unchanged. A
separate raw-operation case selects the ordinary value cell and proves it is
unchanged without asserting `RecursiveTargets` for that invalid source-binding
selection.

## Remaining scope and validation

The core/evaluator owners consume this API using `Expr Primitive`, finite
captured environments and `Value Primitive`. Expression/pattern outcomes,
memoize-before-match ordering, exceptional body behavior, source rule
correspondence, actual recursive forcing and resource event counts are outside
this assigned store slice and remain required by the complete foundation spec.

Focused checks will be serialized by `active-validation/focused-build.lock`
with `LEAN_NUM_THREADS=1` in the pinned offline Nix shell. Logs remain outside
`session` while active and will be frozen here after completion. Full exact
candidate validation, exhaustive audit, final verification and both review
axes remain root-owned.

### First focused feedback

The initial combined command targeted `Examples.SuspensionStore`,
`Applications.Suspensions.Syntax`, and `Applications.Suspensions.Rules`.
It acquired the focused lock at 2026-11-02 17:26:54 UTC and ended with exit 1.
Its frozen log is `session/validation/suspension-store-r1.log`.

The only primary Store error was the pattern binder named `value` inside
`Cell.extendEnv`: Lean resolved it as the `Cell.value` constructor. The binder
was renamed to `result`, with the operation and intended laws unchanged.
Subsequent SRec errors and placeholder diagnostics were consequences of that
failed definition; no admission was present in source. All earlier Store
declarations compiled without additional errors. The example module was not
reached.

The batch also reported three deriving failures in root-owned Syntax, relayed
to root without changes to that file. Root owns those corrections. The next
coordinated evaluator batch can include the Store examples and Rules, reusing
the same shared prerequisites; this worker is not launching duplicate builds.

The next batch, owned by the machine worker (session 81972, lock acquired
17:30:38 UTC), recorded successful compilation of Store and its connected
example module. Root then requested interruption of that batch to narrow the
preexisting `Mathlib.Tactic` import in `Progress.Evaluation` in this foundation
worktree. The owning worker reported subprocess result -2, wrapper exit 254.
That interruption is not a Store proof failure and not a whole-batch pass.
The owned Store sources remain unchanged after their successful module checks.
The machine worker owns the next coordinated batch and its terminal record.

The machine worker's second coordinated batch ended with exit 1. Store's
checked sources were unchanged. Machine parsing rejected the helper name
`continue` as a reserved keyword; the owner is renaming it to `proceed` and
correcting two other local proof issues. The independent Rules-example
feedback belongs to root. The draft at commit
`804eb96598bad5eb5d4734b0f464dc1445612aa7` was captured in checkpoint 011,
explicitly incomplete and unaccepted. After the capture hold was released,
the new Continuation proof references were updated to the agreed helper name.

## Additional assigned slice: continuation laws

Root subsequently assigned `Applications/Suspensions/Continuation.lean`, in
namespace `Suspensions.Core.Machine`, within the same implementation loop.
No global finite-memory configuration invariant is being substituted for this
task. Store and its example stayed frozen while the independent new module was
drafted; it will not be compiled concurrently with the active batch.

The agreed API is `boundaryControl`, `appendFrames`, `step_append`,
`step_boundary`, `step_stuck_append`, `evaluates_append`, and `evaluates_split`.
It reuses `Progress.Evaluates`; no additional execution-closure datatype or
termination assumption is introduced.

The intended structural laws follow from the actual transition definition:
nonfinal steps inspect, push or pop only the existing stack prefix; appending
a suffix preserves the step and appends that suffix to its successor. A final
value, raised packet, matched environment or mismatch occurs exactly at its
corresponding control with an empty stack and the same current memory. A
final stuck result stays the same with an appended suffix, including a handler;
it is not a raised source exception. These are properties of arbitrary raw
configurations and do not require a global type-safety premise.

`evaluates_append` takes an isolated body run of n transitions, its terminal
boundary witness, and a residual run of m transitions from that boundary with
the caller's frames. The result has `(n - 1) + m` transitions: the isolated
run's final delivery is replaced by the residual processing of the same
control. Every `Progress.Evaluates` derivation has positive length, which
justifies this subtraction. For an empty appended suffix, the residual final
delivery has one transition, recovering the original n.

`evaluates_split` is the converse for an assumed finite plugged run ending at
one of those four non-stuck boundaries. It splits the original transition into
continuation, final boundary or stuck. A stuck case contradicts the observed
non-stuck final result by determinism; the continuation case decreases the
given finite length. No claim is made that arbitrary bodies terminate, nor
that fuel exhaustion proves divergence.

The connected intended use `memoize_wildcard_after_body` plugs a finite
value-producing body into one actual memoize/wildcard frame. The residual run
writes the cache in the body's resulting memory, matches the wildcard, and
delivers the empty matched environment. This should take n+2 transitions and
retain all earlier body effects. It exercises the generic composition law
against the source-critical write-before-match order rather than adding a
second evaluator. Root will use the general laws for independent source-rule
adequacy in its separate correspondence module.

Continuation status: complete proof draft written, not yet compiled. The large
transition case analysis is factored once into a private classification lemma
from which the public step laws follow. Later compiler/statement feedback must
be incorporated before any completion claim for this slice.


### First continuation feedback and structural factoring

The first focused target `Applications.Suspensions.Continuation` acquired the
shared lock at 18:03:52 UTC on 2026-11-02 and ended with exit 1. Its exact log
and source-hash record are `session/validation/suspension-continuation-r1.log`
and `.json`; all recorded sources were unchanged during this build. The
terminal result arrived after checkpoint 012 capture, so that checkpoint
accurately preserved an in-progress, unaccepted draft rather than this result.

The primary error was the monolithic private classification proof reaching
Lean's default 200,000-heartbeat limit (reported module time 212 seconds).
Four explicit arguments in a repeated simplification were also redundant.
The downstream public step laws then referenced the unavailable private proof;
there were no independent errors reported in the finite-run composition,
splitting or memoize/wildcard client proofs. This is not a successful module
check and does not establish any of those statements as accepted.

After capture release, the private classification was factored into separate
proofs for the nine control constructors. Expression and pattern constructors,
or stack and return-frame constructors, are now split before unfolding the
transition definition. This avoids first expanding the full unresolved match
tree on both sides. The four simple return/clause families reduce directly by
reflexivity after structural cases; remaining small matches use split and
ordinary simplification. The public statements and default heartbeat limit
are unchanged. This factored second draft still awaits focused compilation.

Root also assigned the subsequent `Applications/Suspensions/Invariant.lean`
and `Examples/SuspensionInvariant.lean` slice, sequenced after Continuation
passes. Its planned configuration invariant is bounded memory plus an
in-range address for each pending memoize frame. Actual thunk lookups justify
new frames; allocation increases the frontier; successful frame writes stay
inside it. This permits repeated frames for one address and cycles through
captured environments. The existing `Suspensions.Core.Prefix.observe` will
carry the invariant to finite unfinished observations, with no new runner or
charge for absorbed terminal iterations. No Invariant source exists yet.


### Planned invariant cases, before implementation

The finite successful case begins with one actual `delay` allocation of a body
returning integer 7. Matching its address against a suspended wildcard takes
five transitions: enter the stored body, return the atom, write the cache,
match the wildcard, and deliver the matched environment. The expected final
memory has the cached value at address zero and frontier one. Its boundedness
must be obtained from the initial bounded state and the execution theorem,
with `mem_domain` then exposing its complete finite domain.

The cyclic finite-prefix case first allocates a thunk whose body binds a
suspended wildcard against variable 1, then returns integer 0. SRec extends
that thunk's captured environment with variable 1 mapped to its own address
zero. Starting a suspended-wildcard match at zero reenters the same thunk after
five transitions. The residual control again evaluates the stored body; its
stack contains two memoize frames at address zero, separated by the pending
bind-match frame. Memory is still the same cyclic thunk store. The intended
prefix theorem should establish boundedness and in-range pending frames for
this reached configuration, including duplicated addresses. This finite
observation makes no divergence or global once-only assertion.

The existing Prefix module has now compiled successfully in the machine
worker's fourth coordinated batch. Its `advance` absorbs an already delivered
answer, and `observe` iterates that operation for a supplied budget. Invariant
preservation will concern the actual residual/result state; it will not count
absorbed suffix iterations as extra body execution. The proof will use that
existing API directly, alongside `Progress.Evaluates` for complete finite runs.

A negative raw-configuration case will justify the additional frame premise:
empty memory is bounded at frontier zero, but a forged value control with a
memoize frame for address zero writes a cell at that frontier without
advancing it. The resulting state is unbounded. This is not a reachable source
start; it demonstrates why bounded memory alone is insufficient for a theorem
about arbitrary machine configurations. The positive execution theorem must
establish its stronger configuration invariant from fresh empty-stack starts.


### Second continuation feedback

The factored second draft finished with exit 1; its log reports 173 seconds
and no heartbeat failure. Exact log and unchanged-input hashes are preserved
as `session/validation/suspension-continuation-r2.log` and `.json`.
The five remaining proof families left constructor equations introduced by
match splitting. Typical hypotheses identify `next` with a concrete Config
record while the goal asks for its component equalities; fault branches
similarly identify `answer` with a stuck record before a contradictory
non-stuck-result equation. Explicit `subst_vars` is now applied before ordinary
simplification in those local proof loops. The four direct structural families
and the later finite-run proof elaboration had no separate reported errors.
The third draft is still uncompiled; no proof limits or public statements
were changed by this correction.


## Later assigned slice: actual recursive-binding creation

After Invariant, root assigned `Applications/Suspensions/Recursive.lean` and,
if useful, `Examples/SuspensionRecursive.lean`. This must discharge the source
applicability premise from the real simultaneous creation path, not merely
repeat Store's assumed `RecursiveTargets` predicate.

The existing `Syntax.RecursiveRhs` has exactly function and delay constructors.
A possible source-specific creation fold can therefore retain ordinary failure
for every other raw expression, while interpreting these two permitted forms
by actual closure creation and `Suspensions.delay`. Each permitted binding
matches three machine transitions from a recursive control: select the RHS,
produce its closure/address, then collect it with the recursive frame. The
empty remaining-binding step subsequently applies SRec and enters the body.
Thus a proposed connected prefix theorem has 3 times the binding count plus
one transitions from a recursive control, or plus two from an expression start.
These are model transition counts, not host-time bounds.

The planned induction invariant states that every effective address binding in
the accumulating environment refers to an unforced thunk in the reached
memory. Functions add no address binding; delay allocates a fresh thunk;
subsequent allocations retain old thunk cells under Bounded memory. Effective
lookup handles repeated variable names. `Env.rec` changes only closures, so
its effective address bindings are the same. `Machine.addressRange` can then
supply actual targets satisfying `Suspensions.RecursiveTargets`, before the final
SRec update. A finite-execution correspondence for the fold is required; this
is not a substitute evaluator assumption. Captured environments may refer
back to the new addresses after extension, with no fixed-point axiom or
acyclicity condition. No source for this later slice has been written yet.


### Continuation checked

The third focused build passed: 743 jobs, exit 0, reported module time 164
seconds, with all recorded source hashes unchanged. Exact evidence is saved
in `session/validation/suspension-continuation-r3.log` and `.json`. The public
step, composition and inverse-splitting laws and the connected
`memoize_wildcard_after_body` n+2 client are now compiled under the default
heartbeat limits. The constructor-specific factoring and explicit
substitution resolved the previous feedback without changing statements or
suppressing any linter. This is focused implementation evidence, not complete
foundation acceptance. Invariant implementation begins after this check and
the checkpoint 013 source/report freeze release.


### Invariant first implementation draft

`Applications/Suspensions/Invariant.lean` and
`Examples/SuspensionInvariant.lean` are now written, not yet compiled.
Namespace `Suspensions.Core.Machine` exposes `FrameBounded`, `ConfigBounded`,
`OutcomeBounded`, fresh-start validity, `step_bounded`, `evaluates_bounded`,
fresh-start finite-evaluation corollaries, `evaluates_domain`, and the existing
Prefix observer's bounded/finished/unfinished corollaries.

`FrameBounded` says every equality of the current frame with a memoize frame
supplies an address below the frontier. It uses a nonrecursive equality
predicate. `ConfigBounded` combines Bounded memory with List.Forall on frames;
List.Forall tails stay opaque, with only its existing cons equations used.
The proof is split by actual control and return-frame constructors and reuses
Store's allocation, replacement and SRec laws. It neither unfolds a recursive
stack predicate on arbitrary tails nor introduces an ordering on addresses
inside stored values or captured environments.

The example draft contains the actual five-transition successful force,
its derived bounded final memory and complete finite-domain observation,
the five-transition pure cyclic reentry prefix with two address-zero memoize
frames, validity for every supplied finite prefix budget, and the forged
frontier-write counterexample. The latter starts with bounded memory but an
invalid frame stack; its actual next state is unbounded. This demonstrates the
need for the frame premise while the positive theorems derive it from fresh
empty-stack starts. Default proof limits and existing execution APIs are
unchanged. Recursive.lean has not yet been implemented.


### First invariant feedback

Invariant r1 finished with exit 1; the log reports 201 seconds and no
heartbeat failure. Exact log and unchanged input hashes are saved as
`session/validation/suspension-invariant-r1.log` and `.json`. The example was
not reached. Remaining core goals were specific FrameBounded facts exposed
only after a late source match split, and the returning memoize operation's
address bound still inside a conjunction.

Five constructor-specific simplification laws now cover constructor, record,
application-result, row and memoize frames. They do not unfold arbitrary
frame-list tails. The memoize return uses the conjunct frames.1, and two unused
initial rows simplification arguments were removed. The later finite-run and
prefix lifting proofs had no independent reported errors; this is not a module
pass. The corrected second draft awaits focused checking.

Recursive.lean is now a separate uncompiled draft, importing the stable but
not-yet-checked root-owned AddressRange helper. Its creation fold returns
Except Answer (Memory × Env), preserving the reached memory and raw machine
fault for rejected syntax. CreatedThunks tracks effective address-valued
bindings; creation derives it from the empty accumulator while retaining old
occupied cells only during fresh allocation. Closes is an operation-independent
componentwise SRec relation, including its unforced-target applicability
premise. The draft connects creation/closing prefixes and finite body evaluation
to the actual machine. Its first check will wait for AddressRange feedback.

### Recursive creation: source and client review before first check

Root's AddressRange helper has now compiled successfully, and Recursive's
first core-only check is queued under the shared focused lock. Invariant r2
is independently queued. Neither draft is claimed checked by this record.

The public creation contract uses the existing `RecursiveRhs` predicate for
function and delay expressions. `create_exists` proves that the finite
creation phase finishes without assuming termination of any stored body.
`create_preserves` tracks bounded memory, every effective address-valued
binding's unforced thunk, and retention of old occupied cells during fresh
allocation. `CreatedThunks.targets` supplies the source applicability premise
for the actual `Env.rec` address range. No immutable-extension claim is made
for SRec's later replacement of captured environments.

`Closes` states its applicability, exception-name preservation, pointwise
memory-domain preservation, outside-target equality, and exact thunk code and
environment replacement without mentioning the implementation operation.
`close_correct` realizes it with SRec; separate laws retain boundedness and the
frontier. `create_prefix` records three actual transitions per binding before
closing. `enter_body_prefix` adds expression dispatch and the final close, and
`evaluates_from_body` composes that prefix with any supplied finite body run.
These counts concern the existing machine transitions, not host execution time.
`realizes_recursive_binding` derives the target premise and source footprint
from permitted syntax and bounded initial memory, while retaining the actual
machine prefix as a conclusion. Captured values may contain cycles and aliasing.

The connected client `Examples/SuspensionRecursive.lean` is saved but still
uncompiled. It creates a function at identifier 1 and a self-referential delayed
expression at identifier 2 beside an existing reference at address 0 and an
unrelated thunk at address 1. The expected closed state preserves both old
cells and the exception names; the function identifier does not incorrectly
select heap address 1. The new address-2 thunk acquires its recursive environment.
The example uses the generic creation proof to derive RecursiveTargets, checks
the eight-transition entry prefix, and uses the body bridge to return that
suspension in ten transitions without forcing it. The finite-memory conclusion
uses the separate machine invariant. A rejected raw binding list first creates
a thunk, then reaches the same invalid-RHS fault in the fold and machine; its
five-transition run retains the allocated cell and reached memory. This case
does not extend the source permitted-binding domain.

### Invariant second feedback

Invariant r2 is terminal with exit 1 and unchanged recorded input hashes;
the compiler reports 110 seconds. The proof goals all elaborated. Its only
remaining errors are unused-tactic findings for a redundant `exact bounded`
fallback and the unused first `assumption` alternative before the actual
memoize-frame bound projection. These dead proof-search branches are removed
without changing any statement, premise, proof limit or linter setting.
The example target was not reached, so neither the module nor its clients are
yet claimed to pass. Exact evidence is saved in
`session/validation/suspension-invariant-r2.log` and `.json`.

### Recursive first feedback and exact converse

The first core check finished with exit 1, 122 reported seconds and unchanged
recorded source hashes. Creation, CreatedThunks, Closes, and the exact prefix
theorems elaborated before a reserved-keyword parse failure at the local
binder `prefix`. The later finite-run helper and its consumer were therefore
not checked. Evidence is saved in
`session/validation/suspension-recursive-r1.log` and `.json`.

The binder is now `reached`. A private inverse prefix-stripping proof and the
public `Recursive.evaluates_iff` are added: any finite evaluation of the whole
recursive expression yields a finite evaluation of its body in the actual
closed state and environment, with total count exactly `3 * length + 2 + steps`.
The forward direction uses the existing body bridge. The converse permits all
body answers, including stuck results, because the known creation prefix
contains no terminal step. It adds no typing, return-mode or termination
premise. The connected client derives a two-transition body run by stripping
the concrete ten-transition whole run after its eight-transition creation
phase. These new corrections and converse proofs are not yet compiled.

### Invariant checked with connected clients

The third focused check passed with 745 jobs, exit 0, and unchanged recorded
source hashes. The compiler reports 65 seconds for the Invariant module and
49 seconds for Examples.SuspensionInvariant. Exact evidence is saved as
`session/validation/suspension-invariant-r3.log` and `.json`.

The checked public API derives finite memory from bounded fresh starts through
the actual machine: `step_bounded`, `evaluates_bounded`,
`start_evaluates_bounded`, `startPattern_evaluates_bounded`,
`evaluates_domain`, `observe_bounded`, `observe_unfinished_bounded`, and
`observe_finished_bounded`. Arbitrary intermediate configurations additionally
need the explicit pending-memoize-frame bound in `ConfigBounded`; fresh starts
derive that condition with their empty stacks. This invariant constrains
neither address aliasing nor cycles in captured environments.

All connected cases passed: the actual five-transition successful force and
its finite-domain observation; the actual five-transition cyclic self-reentry
prefix with two memoize frames for address zero, together with boundedness at
every supplied finite budget; and the forged out-of-frontier frame whose next
raw machine step violates boundedness. The last case confirms that bounded
memory alone is insufficient for arbitrary forged continuation stacks. No
termination or divergence conclusion is inferred for the cyclic client.

This is complete focused evidence for the assigned finite-memory slice,
not acceptance of the foundation or the chapter. Recursive remains in its
second frozen check, with its client and new converse still unverified.

### Pending source-faithfulness correction in the recursive client

Read-only review while Recursive r2 was frozen identified a client issue:
directly delaying variable 2 under a recursive binding for variable 2 is
dynamically permitted but would require an infinite source type equation.
The general runtime and target-readiness theorems intentionally need no
typing premise, so their statements are unaffected. After the frozen check
terminates, the client will instead store
`bind (suspended wildcard) (variable 2) (atom (integer 0))` in its delay.
Under variable 2 of type integer suspension this body has integer type.
It still creates a cyclic thunk without forcing it, and the outer variable
body still gives the same eight-transition entry prefix and ten-transition
whole run. A small witness using the now-checked Static.HasType API will make
the new delayed right side's type explicit. This planned client correction is
not yet applied; frozen r2 inputs remain immutable.

### Recursive second feedback and corrected client

Recursive r2 finished with exit 1, 58 reported seconds and unchanged recorded
input hashes. Its only errors were the two finite-run helpers' residual goals:
simplification produced the explicit advance iterator while the goal retained
the definition of Prefix.observe. Both proof sites now expose that definition
with `change`; no operation, statement, count or premise was changed. The
client was not reached. Evidence is saved in
`session/validation/suspension-recursive-r2.log` and `.json`.

At this terminal boundary, the planned client correction was applied. The
new thunk's stored body forces variable 2 using a suspended wildcard and then
returns integer zero. Creation itself still never forces that body. The new
public `delayed_recursive_rhs_typed` consumes the checked Static.HasType API:
under variable 2 at the monomorphic integer-suspension type, the delayed right
side has that same type. The static owner confirmed the constructor proof
shape before this edit. Runtime contracts remain free of typing premises,
and the expected memory footprint and eight-/ten-transition observations are
unchanged. The next focused input record includes Static and Names as well as
the prior dependency closure. These new edits are not yet claimed checked.

### Recursive checked with typed and operational clients

Recursive r3 passed with 778 jobs, exit 0 and unchanged recorded input hashes.
The compiler reports 99 seconds for the core and 48 seconds for its connected
example. Exact evidence is saved in
`session/validation/suspension-recursive-r3.log` and `.json`.

The successful core check includes `create_exists`, `create_preserves`,
`CreatedThunks.targets`, `close_correct`, `close_bounded`, `close_next`,
`create_prefix`, `enter_body_prefix`, `evaluates_from_body`, `evaluates_iff`,
and `realizes_recursive_binding`. Source target readiness is derived from
actual unforced creation starting with the empty accumulator. The bound
addresses are characterized by effective lookup after Env.rec. SRec's source
relation preserves exception names, the memory domain, all cells outside that
range, and the code at each selected thunk while extending its environment.
The exact body equivalence retains the complete reached Answer, including its
state; it assumes neither body termination nor a return-mode premise.

The client check includes its Static.HasType witness for the delayed
self-forcing integer body, the derived target premise and source Closes
relation, the eight-transition entry prefix, the ten-transition whole run,
the recovered two-transition body run, and finite-memory conclusions using
the checked Invariant module. It also checks that the old reference at address
zero and the unrelated thunk at address one remain unchanged, even though one
is also the new function identifier. The raw invalid-binding case preserves
the delay allocation and reached state before the fault, outside the permitted
source-RHS-shape domain.

A brief read-only preparatory statement pass by the static worker confirmed
these mechanism and client connections. It identified two documentation
boundaries: Permitted checks only function/delay RHS shape, leaving inherited
distinct-binder, nonempty-match and identifier-classification restrictions to
separate source well-formedness; and a theorem uniform in Answer does not
claim every answer constructor is reachable from an expression start. After
the successful r3 check, only doc comments in Recursive.lean were updated to
make those points explicit. Definitions, theorem statements and proofs are
unchanged. The r3 exact hash record refers to the pre-clarification comments;
the final exact-candidate gate must check the current source as usual.

All assigned Store, Continuation, Invariant and Recursive implementation
slices now have focused proof/client evidence. No staging, commits, source
entrypoint changes, full-gate changes or acceptance decision were made by this
worker. Full foundation integration, exact-candidate validation, exhaustive
proof audit and final Standards/Spec reviews remain with the enclosing loop.
