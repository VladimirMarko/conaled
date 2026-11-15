# Pure continuation and recurrence slice — local 10019

Status: the original continuation/recurrence slice and the subsequent prefix/
certificate helpers with their clients passed their respective focused checks.
Full acceptance and the raw heap-machine bridge remain open. This continues the existing
local10019 loop at fixed review base
`b422800fb5b6dc1253823057c0ea71644274d77c`. The current shared worktree is
`purity-foundation`; root owns commits, public entrypoints, full validation,
acceptance reviews, tracker state and durability checkpoints.

## Intended result and boundary

Prove a recurrence obstruction for the already checked unshared machine. A
positive actual finite prefix from configuration c to c with caller frames
appended is incompatible with any finite completion of c. The conclusion
covers normal values, source exceptions, matching outcomes and faults. This
must follow from deterministic finite evaluation and exact continuation
decomposition, not from a nonreentrancy premise or one failed fuel search.

The theorem is about the auxiliary pure interpretation. It is not the source
heap-machine nonreentry theorem, does not connect raw cache hits to unshared
evaluation, and does not close10019 or advance a chapter acceptance frontier.
The existing effectful machine and all earlier clients remain unchanged.

## Reuse and proof structure

The existing Progress.Evaluation API provides Machine, Evaluates, Terminates,
search and exact result/count uniqueness. Progress.Streams.advance iterates a
total coalgebra, and Resources.Workload.run sequences total measured state
transformers; neither supplies an unfinished prefix of this evaluator. The
existing Core.Prefix adapter is specialized to the raw memory-carrying machine.

Pure.Continuation therefore supplies only source-specific stack laws over
Progress.Evaluates. Its classifier checks every actual Pure.Control/Frame case.
Earlier transitions preserve appended tails; nonfault delivery occurs at an
empty original stack; a fault is unchanged by caller frames. An all-outcome
split separates an isolated body fault from a delivered body boundary followed
by any caller outcome, including a later fault. The latter count is n-1+m,
replacing exactly the body's isolated delivery transition. Since the residual
run has positive length, the isolated body count is at most the plugged count.

Pure.Recurrence adds a thin finished-absorbing advance function and defines
Reaches by Function.iterate of the existing step. It introduces no alternative
evaluation judgment. A prefix ending at an unfinished configuration cannot
contain a completed result. Splitting a hypothetical completion after p>0
prefix steps gives a remaining count m smaller than the original n. Splitting
the caller frames then produces an isolated completion of c of count at most m.
Progress.Evaluates.unique forces that count to equal n, a contradiction.

## Independent client expectations, written before checks

The existing cyclic source group is f()=force s and s=$(f()). Its finite group
descriptor is exactly Examples.SuspensionPureMachine.cycleGroup, with the
existing cycleBody and empty capture. No descriptor is reconstructed from a
growing member environment.

From isolated start(groupEnv, cycleBody), eight transitions select f's body;
the next seven enter s. Thus15 actual transitions return to precisely the same
isolated body control with these appended frames, in order: force at variable0;
the generated force clause; the force application return; the f application
return. The source cycleTerm first reaches that body in8 transitions: one group
formation followed by the seven-step force entry. The new client checks both
concrete prefix equations, derives absence of any finite completion for the
body and whole source term, then derives search=None for every fuel. These
expectations all passed unchanged.

The already checked23-step prefix and exact two body triples are retained.
They are not, on their own, evidence of divergence. Additional checked
continuation clients distinguish a body fault that a caller handler cannot
catch (one transition), a raised source packet that the caller can catch
(four body transitions plus seven caller transitions, overlapping the delivery
step, for ten total), and a normal body followed by a caller fault (two body
transitions and one residual caller transition). A terminating zero-step
recurrence demonstrates why the strictly positive prefix premise is necessary.
A normal literal body also uses the universal force-wildcard continuation law,
giving four transitions through return and matching.

## Statement review and validation

No existing Machine or Value API changed. The recurrence theorem quantifies
over the actual deterministic machine parameters and exact input configuration,
not merely equal returned values or syntactically equal bodies under different
captures. All-outcome splitting preserves faults with no type-safety assumption.
Source well-formedness and primitive interpretation laws remain separate from
the raw auxiliary statement. Reaches records an actual prefix equation; it is
not a renamed nontermination or nonreentrancy hypothesis. The positive premise
is witnessed by the concrete15-step recurrence. A private source-specific
classification proves that every actual Pure.Control/Frame constructor obeys
the stack rules, rather than assuming those rules about the evaluator.

Focused checks serialized on active-validation/focused-build.lock and recorded
the complete immutable local import/configuration closure. No extra axioms,
admissions, native proof shortcuts, relaxed linters or raised proof budgets were
introduced. Full-candidate audit and both independent review axes remain
root-owned acceptance gates.

First focused attempt, suspension-pure-recurrence-r1, ended with exit1 and
unchanged recorded inputs. Its only reported error was an extra residual
argument in the append proof's induction-hypothesis application: unlike the
raw memory-carrying version, the pure residual premise is fixed. The source
classifier and all-outcome decomposition generated no local errors. Removing
that extra proof application changes no statement, transition or expectation;
the failed round remains separate from the passing evidence below.

Corrected target Examples.SuspensionPureRecurrence passed in
active-validation/suspension-pure-recurrence-r2.{log,json}, exit0,744jobs. It ran
2026-11-02T20:35:26.817439Z through20:35:43.023304Z. All recorded source and
configuration hashes were unchanged. Pure.Continuation compiled in6.6s,
Pure.Recurrence in2.3s, and the connected client in2.3s. The session terminal
result was collected and the focused lock released. No optional rechecks
followed that sufficient focused result. The separately assigned helper
extension below preserves it as the evidence for the original slice.

Checked source hashes:

- Applications/Suspensions/Pure/Continuation.lean:
  44b6bef4fafe225ec0b1ca5579c16e9c19d778bc5ce8e27414d54507841c2656
- Applications/Suspensions/Pure/Recurrence.lean:
  ed1744f8e5b66c2d18f2ee6671833ee9dcec52b38fe3c63a490ca6dcb636b7f7
- Examples/SuspensionPureRecurrence.lean:
  759c6bdeda17eb0f50e6e0019c623e7eac11024713fa3ad5b10f63fae4c30e92

The reusable API includes Machine.evaluates_append, evaluates_stuck_append,
evaluates_split_all, evaluates_isolated_le, terminates_of_append and
not_terminates_append. Recurrence.Reaches.evaluates/remaining relate actual
prefixes to the existing finite judgment; Reaches.append transports them
through caller frames. The principal theorem is
Recurrence.recurring_prefix_not_terminates. The concrete cycle_body_recurs and
cycle_source_enters_body feed it, yielding cycle_body_has_no_finite_result,
cycle_source_has_no_finite_result and cycle_search_none for every supplied fuel.
cycle_body_entry_identity retains the exact source code/empty capture/group
descriptor event through the public Machine.body_transition law.

## Follow-on prefix and cache-certificate helpers

The selected raw bridge design is recorded separately in
session/research/pure-recursive-forcing-bridge.md. Its forward, per-occurrence
histories need only small additions to the existing pure prefix API:
Reaches.one/trans, evaluates_boundary_reaches, and
force_prefix_of_certificate. No existing Machine, Value, Representation or
Memory definition changes, and the earlier clients remain intact.

Before checking these additions, the expected observations are: a finite
nonfault evaluation of n transitions reaches its empty-stack delivery control
after n-1 actual transitions; a normal body certificate then expands a
suspended pattern to its still-unmatched inner pattern in n+1 transitions.
This is entry1 plus body(n-1) plus return1, under any unchanged caller tail.
The replay is auxiliary pure work, not the raw cache-hit cost, and it does not
assume successful inner matching.

The literal7 body's two-step certificate therefore yields a three-transition
unfinished prefix at literal0 versus7. Continuing under a value-binding frame
takes three more transitions: mismatch, Bind packet, delivery. The composed
answer must be raised Bind in six transitions, without entering the body99.
A raised-variable body separately reaches its raised boundary after three
transitions, omitting only the fourth isolated delivery. These expectations
were fixed independently before the new check; the existing15/8 recurrence
counts and statements are unchanged.

The helpers and three connected clients passed unchanged in
active-validation/suspension-pure-recurrence-r3.{log,json}, exit0,744jobs.
The round ran2026-11-02T20:53:57.266032Z through20:55:35.440560Z, with every
recorded import/configuration input unchanged. Pure.Recurrence compiled in63s
and Examples.SuspensionPureRecurrence in15s. Terminal session58310 was
collected; the focused lock is released. These timings describe the observed
check, not a performance claim. The complete original15/8 recurrence and
continuation clients were also retained and checked by the same target.

Current checked hashes are:

- Applications/Suspensions/Pure/Continuation.lean (unchanged):
  44b6bef4fafe225ec0b1ca5579c16e9c19d778bc5ce8e27414d54507841c2656
- Applications/Suspensions/Pure/Recurrence.lean:
  05ef3559e0dfbcdf346eb7da5e706ccc8a23f4b1b4695bc264af8fd3819046d5
- Examples/SuspensionPureRecurrence.lean:
  3d4627029f85ecdd1997b004f0f06df3c58b1f4a67f1011a014e04ab0cfcd41c

Statement review: boundary-prefix extraction requires boundaryControl answer
to be present and therefore makes no delivery claim for terminal faults.
Certified force replay uses an actual normal finite body evaluation from its
exact bodyEnvironment, not a totality axiom, equal body text under a different
capture, or a presumed cache-validity relation. Appending caller frames does
not evaluate them. Reaches.trans sums actual unfinished prefix lengths; the
n+1 replay count removes the isolated body's final delivery and includes the
two force transitions. The later raw bridge must separately establish which
heap cells possess such certificates and how actual raw histories are
represented. No new admissions, proof-budget changes or type-safety premises
were introduced. Source files are frozen for root's History client.
