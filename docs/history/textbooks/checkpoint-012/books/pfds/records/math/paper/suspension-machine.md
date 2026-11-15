# Suspension small-step machine development record

Local #10014, requirements suspension-foundation.md version 1. Implementation
slice owned by chapter02_map in the shared suspension-foundation worktree.
This record does not accept the foundation or advance chapter coverage.

## Current focused status

Machine and all local transition/trace-erasure laws compiled in r3. Prefix and
its completion/search bridge compiled in r4. The fifth runtime batch completed
with exit0: Examples.SuspensionMachine (17 actual closed-search cases) and the
root-owned Namespace example compiled, with 745 total jobs. Exact retained
evidence is active-validation/suspension-machine-r5.log and .json; its interval
is 2026-11-02T18:29:52.450359Z through 18:35:02.658018Z. This is focused
development evidence, not whole-foundation acceptance.

After checkpoint013 released its input freeze, two never-selected example
right sides were corrected to have the intended source result types:
exceptionalInner's successful branch now returns force(variable1), matching its
handler's suspension type; referenceInner's never-selected first clause now
returns false, matching the Boolean fallback. Their executed paths and
postconditions are unchanged. The mutual function/suspension example uses the independently stated
footprint below. Examples.SuspensionMachine subsequently compiled successfully
within r6 (126s), including that case and the two type corrections. r6 then
compiled the Derived forward module (75s) and ended exit1 on the single
Parameters-constructor parser error in its example file, recorded below. cachedReference and its checked dynamic theorem are unchanged.

Derived and all nine original derived-form clients are now green in r8,
including force_delay_value_iff, force_delay_raised_iff,
lazy_function_value_iff and lazy_function_raised_iff. The prior parser and r7
local proof-script errors were corrected without changing statement premises,
results or counts. r8 ran from 2026-11-02T19:35:32.110723Z to
19:37:49.467803Z, exit 0, with source hashes unchanged at start and end.
Derived compiled in 57s and Examples.SuspensionDerived in 62s, 746 total jobs.
Exact evidence is active-validation/suspension-derived-r8.log and .json.

The tenth derived-form client, lazy_formation_then_force, is now green in
r10. It checks public lazy formation, an actual intervening assignment and
later forcing from the reached state, with the independently predicted
13 / 6 / 39 transitions and exact reference/body/cache events. Its stored
fresh binding is retained literally. Only Examples.SuspensionDerived changed
after r8; the Derived library and common Machine/Prefix inputs are unchanged.
All ten derived-form clients and the eighteen runtime cases now have focused
compilation evidence. These are focused development results, not
full-foundation acceptance.

## Source and independent expectations, recorded before proof development

Read the complete source/architecture inventory. Inspected the 1990 Definition
text and page images at printed pp58–66 (physical PDF68–76): closure
application unrolls Rec, strict function/argument order, Match/Bind/handler
failure distinctions, broad constant/constructor FAIL rules, field lookup and
layered-pattern environment combination. Appendix A's forcing order and two
recursive counterexamples are recorded in suspension-foundation-inventory.md.
The Appendix A pp132–135 page images were also inspected directly, including
the printed0/1/2/3 clause answers, memoize-before-match rules and SRec footprint.

Expected discriminating observations:

1. A thunk created with x=1 and forced after x is rebound to2 returns1.
2. Two forces of one address enter its body once and hit the cache once;
   repeated creation allocates distinct addresses and can execute twice.
3. The appendix's three clauses on (ref false, delayed(assign true;1)) all
   fail: the application raises Match, the reference is true and the thunk
   contains1. Adding the fourth ref-true clause returns its answer with the
   same reference/cache effects.
4. A permitted recursive suspension guarded by a false reference can reenter:
   the inner call caches7, the outer call overwrites it with8. There are two
   body entries and two successful writes, and a later force returns8.
5. Replacing the outer increment by a raise preserves the inner cached7;
   the outer frame adds no write, and a later force hits7.
6. Assignment returns the unique source unit representation, the empty record;
   matching it against the empty record pattern succeeds and retains the write.
7. The cached-reference audit term delays a reference containing the identity
   function, forces it and assigns the constant integer0 function, then forces
   and reads the same reference and applies it to Boolean true. Its operational
   answer is integer0, with one thunk body entry and one later cache hit. The
   independent static owner investigates whether the exact1990 generalization
   rules assign Boolean to this same term; no type-safety claim is assumed.
8. Two separate evaluations of the same delay expression allocate two cells;
   forcing each enters each body once, unlike the aliased case.
9. If an outer thunk returns a new inner thunk whose body raises, forcing the
   nested suspension pattern caches the outer address before the inner
   exception. A handler can force the outer thunk again and obtain the inner
   address from the cache, while the inner cell remains an unforced thunk.
10. Two handled forces of one exception-raising body enter it twice and never
    write its cache. This is distinct from an exceptional inner pattern after
    a successful body return.
11. Forcing a thunk that returns a constructor containing a delayed raising
    expression exposes the constructor and inner address without entering the
    inner body. Root observation remains shallow.
12. A hygienic lazy function applied to a reference produces a suspension
    before matching its clauses. Mutating the reference before forcing that
    result changes the clause selected; the selected suspended right side is
    then forced by the book's derived sugar.
13. A thunk returning an exception constructor captured before its identifier
    is rebound returns that old constructor. An inner exception pattern using
    the rebound identifier resolves in the caller's current environment, so a
    value binding raises Bind while the old constructor remains cached.
14. A reference pattern containing a suspension pattern retains the latter's
    write and cache update when its inner constant pattern fails; a later
    ordered clause observes that changed state.
15. A raw ill-typed read after an ordinary reference allocation ends stuck with
    the allocated memory retained. It is neither Match/Bind nor unknown; this
    is a raw-configuration observation, without claiming source typing.
16. A simultaneous recursive function/suspension group has f(b)=if b then7
    else force s and s=delay(f true); evaluating f false returns7. An unrelated
    delay99 at0 keeps its original empty captured environment, ref5 at1 stays5,
    and s at2 has one body entry/one cache write and holds7. The frontier is3.
    This must use Rec to expose s in f's call environment and SRec to expose f
    in s's captured environment; traversing all indirectly reachable addresses
    instead of the direct recursive range would violate the unrelated-thunk
    observation. The case is intended to have Bool→Int and Susp Int binders.

These expectations were recorded before their implementation and proofs.
The dated focused-check history below distinguishes drafts from checked
connections through Progress.search_sound. No claim of
global at-most-once evaluation or type safety is assumed.

## Design boundary

Use a CEK-style explicit continuation stack with separate expression values,
raised packets, successful binding environments and pattern mismatch. All
final outcomes carry the current mutable store. Stuck raw configurations are
distinct from source exceptions; finite search exhaustion is unknown. A
suspension frame remembers its address, inner pattern and caller environment;
body evaluation runs under the captured environment and normal return writes
the cache before pattern evaluation. Exceptions unwind one frame without a
write at that frame. A cache hit enters matching directly.

Primitive semantics are supplied as a pure operation returning value/raised/
stuck; ordinary reference and exception-name effects remain in the machine.
Labels distinguish creation, body entry, hit, cache write, reference read/write,
fresh exception name and administrative/core work. A label does not claim the
host implementation of a whole finite environment or store operation costs1.
Root owns independent source rules and adequacy; shared worker owns Store.

The initial draft files exposed `Suspensions.Core.Machine.Config`, explicit `Control`
and `Frame`, `transition`, `step`, `measuredStep`, and `tracedStep`. The primitive
parameter and final outcomes have separate datatypes. Local equations describe
delay, cache hit, body entry, successful return, exceptional unwind and failed
clause continuation. Lexical/alias examples are drafted as finite evaluations
using `Progress.search_sound`; they are not yet claimed compiled. First shared
prerequisite compilation exposed nested deriving errors in root-owned Syntax;
these have been reported without editing another owner's file.

## Focused development checks

`active-validation/suspension-machine-r1.log` records successful compilation
of Syntax, Store and Examples.SuspensionStore. The batch was deliberately
interrupted with SIGINT at the parent's request while compiling the existing
Progress.Evaluation prerequisite: its broad Mathlib.Tactic import pulled in a
large theory bundle. Terminal subprocess result was-2 (wrapper exit254), not a
successful complete batch or a source failure. Machine and its examples had
not yet been checked. Root owns the import-only correction; no proof bodies or
frozen chapter candidates are changed by this correction.

After interruption, `addressRange` was corrected to use effective environment
lookup, excluding addresses hidden by an earlier association-list binding.
The source record domain still requires distinct field labels. Added the
generic `cachedReference` AST for the independent static owner to type, plus
the three/four-clause and canonical assignment-unit cases, still awaiting
the next focused compile.

The second batch (`suspension-machine-r2.log/.json`) ended with exit1. It
compiled the narrowed Progress prerequisite and the independent Rules module.
Machine's first feedback required renaming reserved `continue` to `proceed`,
specifying `f := id` in Finset.le_sup, and explicitly rewriting the transition
equation in trace erasure. Its transition had not parsed, so no concrete machine
case was yet checked. Root owns the separate implicit-relation elaboration
failure in Examples.SuspensionRules. These failures were preserved in
checkpoint011's unaccepted draft.

After capture release, those three local corrections were applied without
changing the transition design. The remaining independently listed core cases
are drafted in Examples.SuspensionMachine, including the two successful/
exceptional reentrance outcomes and the body-versus-caller environment case.
The next focused check includes the root-owned namespace and rule examples.

During the third batch, Applications.Suspensions.Machine compiled successfully
(165s), including all local transition and trace-erasure proofs. The corrected
root-owned Rules example also compiled. Namespace had separate reserved-binder
parser failures; the machine examples were still running at this status point.
The Machine source is now held stable for the shared Continuation development.

The third batch finished with exit1. All concrete cases initially exposed a
single proof-script error: explicit witness holes were presented before the
evaluation proof, so search_sound was applied to the wrong goal. The first
three witnesses are now inference placeholders; every expected conclusion is
unchanged. This feedback did not execute/disagree with the source programs.
The raw-stuck-with-retained-memory case is also drafted. Prefix is a separate
next target so an observer-proof correction will not block runtime feedback.

The fourth batch ended with exit1. Prefix compiled successfully (207s), with
all observer/evaluation/search and delay-prefix laws unchanged. Namespace's
module also compiled, but its example retained a reserved `variables` name.
Runtime witnesses were still not inferred: Lean required the anonymous
witnesses before entering the later proof bullet. The closed search_sound/rfl
equation is now inside the same constructor term as the witnesses, so inference
can complete there. Again, no expected program result has been weakened or
reported checked. Machine and Prefix are frozen for root's Return/Observation
and the shared Continuation/Invariant clients.

## Statement review boundaries

The transition equations quantify over primitive vocabularies, parameters,
environments, stacks and mutable states without requiring a typeclass for
value equality. They describe operations on raw configurations. Source
applicability, valid Match/Bind basis tags, record-label distinctness, primitive
laws and static judgments remain separate hypotheses or layers. In particular,
a raised primitive result is supplied by its parameter; global type safety is
not inferred from deterministic execution.

The finite examples start from an empty memory with exception names0 and1
reserved for Match and Bind. Their intended theorem form existentially gives
the reached answer, ordered event trace and actual transition count, followed
by explicit value/cell/event observations. Closed search equations must be
proved and passed to Progress.search_sound; expected postconditions are not
assumptions. Trace erasure connects the same finite run to the public
uninstrumented machine. This connection is not itself source-rule adequacy.

Allocation/body/hit/cache-write labels report the local transition selected.
They do not assign unit host cost to finite environment extension, SRec,
record-list assembly or arbitrary supplied primitives. The separate prefix
adapter requested by root will retain residual Config on bounded observation;
Progress.search remains unchanged, with none meaning unknown. Finished answers
will be absorbing in that adapter, and its bridge must retain the actual
finishing-step count rather than count an absorbing suffix as work.

## Bounded-prefix expectations before adapter proofs

A zero-budget prefix retains the initial Config. One existing machine step
on a delay expression allocates its thunk and leaves a residual value-control
configuration; its memory retains the body/captured environment, and no body
has been entered. The second step returns the address as a final Answer.
Any larger prefix budget leaves this finished answer unchanged, but the
actual finite evaluation still has two transitions. The adapter must express
completion as existence of an actual count bounded by the observation budget,
and recover the same count in Progress.search through search_complete.

## Derived-form expectations before proof development

Root assigned Derived.lean and Examples.SuspensionDerived.lean after the
machine/prefix checks. Planned exact contracts retain the allocated state as
the starting state of the body premise; they do not evaluate the body from
the original memory and postulate equivalence afterward.

For `force(delay body)`, there are seven explicit transitions before entering
the stored body with the memoize/clause/application frames. A normal isolated
body run's final delivery is replaced by six continuation transitions; a
raised run's final delivery is replaced by four. Thus independently counted
targets are body-count+12 and body-count+10 respectively. Normal return leaves
the body state updated at the suspension address; raised return leaves the
body state itself, including any reentrant update. These are planned actual
transition counts, not unit costs for evaluating an arbitrary body.

For lazy-function formation, strict argument evaluation begins after three
outer transitions. Its final delivery is replaced by seven continuation
transitions, producing the delayed ordered match with the fresh argument
binding explicitly retained in the captured environment: argument-count+9.
Names.fresh will supply absence from the conservative clause-name set and
caller environment keys. Such freshness does not remove generated bindings
from later returned closure environments; stronger comparisons belong to the
root-owned observational layer.

A raised strict argument propagates before lazy-result allocation. Its final
delivery is replaced by popping the argument frame and delivering the packet,
after the same three outer transitions: argument-count+4, with precisely the
argument's reached state. Any allocations in that state belong to the argument.

Discriminating first clients: a literal body takes two isolated transitions
and fourteen in force-after-delay; a reference-allocation body allocates its
reference at address1 after the suspension at0, whereas evaluating that body
from the original empty memory allocates address0. The latter blocks an
incorrect literal-state/value equality. An immediate raised body retains its
thunk and does not produce a successful cache write.

## Derived law coverage and explicit remaining scope

The initially compiled Derived draft constructs exact finite executions for normal and raised
force-after-delay bodies, literal bodies, normal strict arguments to lazy
sugar, and raised strict arguments. The normal force conclusion explicitly
memoizes at the chosen frontier address in the body-reached memory; the
raised conclusion is exactly the body-reached memory. The proofs use checked
continuation appending rather than treating a whole body as one transition.

Those initial laws are forward finite-execution laws. The later converse
additions below remain separate from arbitrary-program observational equivalence. They do not establish divergence equivalence,
renaming/private-garbage invariance, equality of event traces, or erasure of the
fresh lazy parameter from returned closure environments. A pure literal case
supplies only its stated scalar observation with a retained private cache cell.
The reference-allocation client deliberately exposes why literal address/state
equality with a body run in the original memory would be false.

Lazy-function formation proves strict argument evaluation followed by thunk
creation. Actual later ordered matching is witnessed by the checked
lazy_function_delays_matching runtime case; a general comparison of all forced
lazy-function results requires the source/observation relation and explicit
environment treatment owned by the parent. Freshness is checked through Names,
not used as an unsupported claim that captured environments are literally equal.

The exact Derived execution equations quantify over raw Memory without a
Bounded premise. Their chosen address is the allocation frontier; actual
freshness additionally follows from Store.Bounded, not from a raw operation's
signature. Any private-garbage or address-renaming corollary must retain that
validity/support domain. The parent owns the general renaming/private-allocation
layer, including explicit primitive equivariance; this worker will not replace
it with an assumed body-invariance premise.

The checked mutual_function_suspension client uses Rec to expose the suspension
inside the function, then SRec to expose the function inside the suspension.
Its source state contains an unrelated outer thunk at0 with captured environment
[] and reference5 at1. The exact reached state preserves both, caches7 at2,
and has frontier3, one body2/cacheWrite2, and no body0. This is a checked
operational case, while the shared owner's generic recursive-creation premise
and footprint development remains a separate proof obligation.

The next Derived additions are exact converse laws for finite normal/raised
force-after-delay and lazy-function formation. The implementation plan uses
continuation splitting and the existing forward laws plus finite-run uniqueness.
Inappropriate matched/mismatch body boundaries are ruled out by the concrete
memoize/argument frame's stuck result, rather than assuming value-type safety.
The public derived-form module therefore need not depend on the larger source
correspondence module. These converse laws were still unwritten at that status point; the subsequent
r6-terminal entry and current summary record their addition, still uncompiled.

## r6 terminal and converse-client expectations

The sixth batch ran from2026-11-02T18:54:06.517483Z to18:59:17.140584Z and
ended exit1. Examples.SuspensionMachine passed126s (now18 cases), and the
Derived forward module passed75s. Examples.SuspensionDerived had one syntax
failure at the Parameters constructor: nomatch consumed the remaining tuple
fields. Parenthesizing that lambda corrects the syntax without changing the
primitive operation or any expected result. No example success is inferred
from a parser-failed module.

The four finite-run converse laws are now drafted using green Continuation,
without Return/Correspondence imports. Fixed transitions are peeled, the
body/argument boundary is recovered, and existing forward laws plus uniqueness
recover the exact final state/count. A matched/mismatched boundary would
produce stuck at the known frame, so cannot explain the given non-stuck run.
This does not infer typing, divergence equivalence, or a result for exhausted
bounded observation.

Before writing their clients, the expected universal finite observations remain:
any normal reference-body force returns address1 in16 transitions with the
reference and private cache described above; any raised raisingBody force keeps
its allocated thunk and original packet in14 transitions; any normal lazy
formation with the reference argument returns address1 in13 transitions with
only the argument reference and deferred match allocated; any raised strict
argument remains the same packet/state in8 transitions. The tests of these
statements must recover the body/argument through the new iff laws, and compare
it with an actual closed body/argument run, rather than assume the observations.

The corrected example constructor, force_delay_value_iff,
force_delay_raised_iff, lazy_function_value_iff, lazy_function_raised_iff and
four universal concrete outcome clients are now frozen for r7. The original
forward theorem statements/counts are unchanged. No extra source imports were
introduced: the converse proofs use only the existing Continuation and Names
closure. The raw-state allocation comment now explicitly separates the chosen
allocation cell from freshness, which additionally follows from Bounded.

## r7 feedback and r8 correction

r7 acquired the lock at2026-11-02T19:14:32.577319Z and ended exit1 at19:18:01.
Its JSON records source hashes, all unchanged at both start and end. Derived's
new proofs had four local elaboration issues: the recovered force configuration
needed explicit unfolding of forceFrames; the recovered lazy configuration
needed explicit unfolding of its local closure/binder/lazyBody; two raised-case
state projection equalities needed explicitly reduced types before subst.
These were corrected without changing any theorem statement, premise, result,
count or the earlier green forward proof bodies. The same explicit state-type
annotation was applied to the four new client proofs before their first check.

r8 is queued as session71617, checking Examples.SuspensionDerived with the same
pinned environment and source-hash guards. Machine, Prefix and the now18 checked
runtime cases remain unchanged. The exact r7 log/JSON is retained alongside
r8's separate evidence; the failed run is not overwritten or counted as success.

## Planned composed lazy-formation / later-force client

Before writing or checking the additional client, its independent expectation
is recorded here. Use two ordered clauses: reference-to-integer-7 selects a
suspension of integer 9; the wildcard fallback selects a suspension of integer
11. Strict evaluation of the reference argument allocates reference 0 with 7;
lazy formation then allocates suspension 1, retaining the literal fresh argument
binding in its captured environment. This first run takes 13 transitions and
performs no ordered-clause matching.

An actual assignment run changes reference 0 to integer 8 in six transitions.
Later forcing suspension 1 reads that current reference, fails the first clause,
reaches the wildcard fallback and allocates suspension 2. It forces suspension
2 and caches integer 11 at both 2 and 1. The expected later-force run takes 39
transitions, with one each of body-entry 1, body-entry 2, cache-write 1,
cache-write 2 and reference-read 0, and no cache hit. The final frontier is 3,
reference 0 still contains 8, and both cached values are 11.

The independent count is 7 transitions to enter suspension 1, followed by the
26 non-delivery transitions of its stored body and the 6-transition successful
outer-force residual: 7 + 26 + 6 = 39. The isolated stored body takes 27
transitions: its ordered application takes 15, and the derived force adds its
3-transition pre-argument prefix and replaces the application's final delivery
with a 10-transition thunk force. This count is actual explicit-machine work,
including the final answer delivery, not a padded prefix budget.

The client will connect reached states using the public lazy-formation contract
and actual finite assignment/force runs. It will not erase the fresh captured
binding or assert arbitrary closure-environment equality. This is a planned
unproved client until its separate focused check succeeds.

## r8 terminal and composed-client draft

r8 completed successfully, exit 0, with both hash comparisons true. It checked
all forward and converse Derived contracts and all nine original clients;
the module and client compilation times were 57s and 62s. The exact terminal
record is retained without overwriting r7's failed evidence. This is the first
green check of the four iff laws and the four universal outcome clients.

The tenth client, lazy_formation_then_force, is now drafted exactly against the
previously recorded 13 / 6 / 39 transition expectations. It uses the public
lazy_function_value theorem for formation, a real traced formation run showing
no reference read/body entry, an actual assignment run, and a later traced
force from the assignment's reached state. Both before and after the write,
the stored thunk has the same literal captured fresh binding. The later trace
must witness the current-reference read, second-clause result 11, inner
allocation, two body entries, two successful cache writes and no cache hit.
The Derived library file itself is unchanged from the r8 checked hash.

r9 is queued as session 89298 against Examples.SuspensionDerived, with the
same pinned environment, focused-build lock and input-hash guards. Its
separate evidence paths are active-validation/suspension-derived-r9.log and
.json. The new client file is frozen until that run is terminal.

r9 is now terminal: start 2026-11-02T19:48:05.948256Z, end
19:49:00.282417Z, exit 1, both input comparisons true. The new client's traced
formation and actual assignment elaborated. Its later-force search equation
did not close by raw rfl. The independent 39-transition count and all expected
effects remain unchanged. The first correction is to prove the concrete fresh
binder equals 1 using Names' public defining equations and finite-set lemmas,
then rewrite that equality before the closed search reduction. This avoids
depending on definitional reduction through the well-founded name computation;
the corrected full search equation still has to be checked. No expected value
or count, machine operation, Derived contract, linter or proof budget changed.

r10 is queued as session 74461, with separate
active-validation/suspension-derived-r10.log and .json evidence and the same
input-hash guards. The parent independently enumerated the full later-force
path and confirmed 39: body-entry 1 at transition 7, allocation 2 at 23,
body-entry 2 at 27, cache-write 2 at 29, cache-write 1 at 34, and final delivery
at 39. This remains an independent expectation until the corrected equation
is accepted by Lean.

## r10 terminal: composed client green

r10 completed successfully, exit 0, from 2026-11-02T19:56:04.927681+00:00
to 2026-11-02T19:57:52.950009+00:00. Both source-hash comparisons are true.
Examples.SuspensionDerived compiled in 87s; the complete focused closure
reported 746 jobs. The separate log/JSON records are retained. The new concrete
binder lemma is proved using public Names equations, after which the actual
later-force search equation closes with its unchanged 39-transition count.
No new result, event count, assumption or implementation was substituted for
the previously recorded expectation.

The checked client connects a 13-transition lazy formation with no reference
read or body entry, a six-transition assignment, and a 39-transition later
force. The reference changes from 7 to 8 while the exact stored code/capture
remains. The first ordered reference clause then fails; the fallback returns
11 through a new inner suspension. The final reference contains 8, both
suspensions cache 11, frontier is 3, and the trace has one reference read,
one inner allocation, one body entry/cache write per suspension and no hit
at either suspension.

The final example SHA256 is
a4d3f37f2a216819ae7572e559da49c7ebc0db3df2a30b73c1ef6bd5f13066ff.
Derived remains at its r8 checked SHA256
e2a8a06345cb61ad736214e2d39cbf4b237b9e6d74fdb5752f2d9d84683446a5.
All owned source/report writes are held after this atomic status update for
the parent's checkpoint016 capture. No additional optional edits or checks
are underway. Full candidate validation and independent acceptance reviews
remain parent-owned; local10019 pure self-forcing remains a separate obligation.
