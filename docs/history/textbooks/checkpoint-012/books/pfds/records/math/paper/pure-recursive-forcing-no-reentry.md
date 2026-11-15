# Local10019 raw self-reentry nontermination

## Source obligation and intended application

The thesis Appendix A.4 remark on printed page135 / PDF147 states the
qualitative pure self-forcing claim. The unrestricted raw machine remains
unchanged. The proof must connect actual source execution to the pure history,
without assuming nonreentry or replacing reentry with a blackhole fault.

The connected source client uses the existing mutual function/suspension
cycleTerm. Starting with an empty raw heap and environment, its exact prefix
after29 transitions reaches the next body0 event; the old memoize0 frame is
at stack index3. The event is transition30. The client supplies independent
prefix/event equations and the admitted source-domain/primitive laws, not a
manually postulated active history. The intended conclusion excludes every
finite raw outcome and yields search=none for every fuel.

## Public statements and dependency direction

Pure.Simulation.active_force_not_terminates combines the pure active-force
recurrence obstruction with finite_correspondence. Primitive compatibility,
hereditary primitive-output preservation, WorldAllowed, ConfigRep and
ConfigAllowed remain explicit. A same-address actual pending frame is the
reentry condition whose nontermination is proved, not an assumed invariant.

active_body_entry_not_terminates consumes an actual Prefix.observe equation
and a body event. body_entry_correspondence constructs the related admitted
pure configuration without any enclosing finite-run premise. body_event_iff
recovers the actual suspended pattern and thunk address from the unrestricted
transition. If the original raw configuration finished, strip_prefix would
give a finite residual execution, contradicting active_force_not_terminates.

finite_body_entry_not_active derives absence of a same-address pending frame
at every observed body event of a finite admitted run. source_reentry_not_terminates
constructs initial ConfigRep and empty histories from StateRep, represented
captures and admitted source code. No future body-result certificate, active
address uniqueness, source typing or success-only outcome restriction appears.

## Statement review and actual client

Root checked the proof direction and that the initial source theorem reaches
body_entry_correspondence. Ordered independently checked the prefix: recursive
creation8, first body entry15, function body23, second-entry configuration29.
The six pending frames retain the original memoize occurrence at index3.
The source CodeAllowed proof covers the nested permitted recursive RHS and
distinct binders. Empty primitives make compatibility/preservation vacuous,
while the actual name policy uses Match0 and Bind1. Universal search failure
is derived from nontermination, rather than from finite enumeration.

## Focused validation

First-round check passed all768jobs, with all frozen source/configuration
hashes unchanged. It ran2026-11-02T21:38:12.608152Z through
21:39:47.594797Z: core45s, connected client36s. The execution session became
unavailable after terminal completion; the successful automatic record and
complete compiler log survived and are preserved. This is not a failed check.
Evidence: validation/suspension-pure-no-reentry-r1.json and matching log.

NoReentry.lean SHA256:
907b2a1dcb84e29bf013eb8cfdd24da6ba86520fc351bb870c40a58ed4f1f455
Examples/SuspensionPureNoReentry.lean SHA256:
84fdee48fd637e00d5f26dad6cc83da273d4a347440495eeb1d6a60c24b726e6

No premise, count or result change was needed after compiler feedback. Default
proof budgets/lint settings remain. These results are development evidence;
successful cache consequences, complete isolated validation/audit and both
independent acceptance reviews remain open. The chapter frontier is unchanged.
