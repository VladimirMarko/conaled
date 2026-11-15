# Ordinary actual-step correspondence — local 10019

Status: ordinary correspondence core and connected clients GREEN (core r3 / client r2). No full-gate or acceptance claim. All owned Lean inputs are frozen for parent integration; no compiler remains active from this worker. This continues the existing10019
loop; root owns commits, tracker/entrypoint changes, full gates and acceptance.
Owned source files are Pure/Ordinary.lean and Examples/SuspensionPureOrdinary.
Existing Machine, History, Simulation, Forcing and representation definitions
remain unchanged. The helper dependency DomainState is shared-worker-owned;
its core and connected clients are now green and frozen (r3/r4).

## Agreed boundary

OrdinaryStepRep relates the actual one-step sum results in a fixed immutable
world. A next result retains exactly the input raw memory and ConfigRep. A
finished result retains that same memory and Compatibility.ResultRep. Normal,
raised, matched, mismatch and stuck observations remain separate.

IsOrdinary excludes exactly raw delay/recursive declaration evaluation,
suspended-pattern/address operands, and normal or raised control consuming a
top memoize frame. Intermediate raw recursive controls/frames have no stable
ConfigRep. A suspended pattern applied to a nonaddress remains an ordinary
fault. The theorem takes ConfigRep, DomainState.ConfigAllowed and
ParametersCompatible; it does not assume ParametersPreserve. Preservation of
the chosen output's hereditary code domain belongs to DomainState.step_preserves
under that separate primitive law.

This module establishes one ordinary raw step corresponding to one pure step,
not a finite-run bridge for allocation or forcing. It adds no evaluator,
memory mutation, totality premise, type-safety assumption or active-address
uniqueness condition. ordinary_event_ne_body concerns the actual raw event;
its shape premise alone suffices because the only body event comes from the
excluded suspended-pattern/address branch.

## Proof structure

Factor by current control family. Private constructors combine structural
ControlRep/FramesRep facts with the existing History.keep/push/pop/replace
updates. Their actual pure one-step equations hold for every caller tail, so
each pending occurrence advances at its correct take/index boundary. Terminal
faults keep their actual class and do not fabricate a successful continuation.

Source-expression and pattern effect predicates eliminate reference operations,
reference patterns and generative exceptions. Primitive selection is read
from the actual pure argument frame's allowed-value premise. Relational
primitive compatibility handles normal, raised and faulting outputs without a
new code-preservation assumption. Closure application uses GroupRep's actual
Rec/bodyEnvironment correspondence, retaining the selected finite descriptor.

## Expected clients, fixed before checking

- A literal7 evaluation performs one ordinary step to value7, preserving the
  complete raw memory. Its empty-stack value delivery is a separate step.
- Forcing integer7 as a suspension fails in one transition: raw expectedAddress
  corresponds to pure expectedSuspension. No body entry occurs.
- Applying the selected successor primitive to integer7 returns integer8 in
  one transition; applying it to Boolean true gives the corresponding primitive
  fault. These use actual parameter results and the generic compatibility law.
- A failed first clause keeps its original argument and starts the remaining
  clauses. The first clause's body99 is not selected; a wildcard fallback can
  subsequently select body8. The client must use ordinary_step for the actual
  mismatch/continuation boundary, rather than only prove a trace independently.
- A normal value under a bindMatch frame is an invalid continuation in both
  machines, despite every stored value/code being effect-restricted. This
  distinguishes code-domain preservation from type or control-mode safety.
- An ordinary literal body step under a pending memoize/force pair advances
  its actual zero-length body history to a one-step value prefix, preserving
  the represented memory. The existing Forcing.return_memoize may then use
  that returned ConfigRep to derive the two-step isolated body certificate and
  justify the actual cache write. This exercises nonvacuous history updates.

All expected values, faults, order and transition counts are independent of the
eventual proof scripts. Existing15/8 recurrence clients and all earlier public
APIs remain untouched. No acceptance or heap-machine nonreentry conclusion is
claimed by this draft.

## Focused feedback

Core r1 ended exit1 with unchanged inputs. The principal failures were missing
reductions of the existing step wrappers, two omitted relation arguments, a
record label metavariable, one tactic-layout error, and redundant tactics.
Core r2 ended exit1 with unchanged inputs after those corrections. Its only
remaining goals were the address-meaning unfolding in exception-pattern
mismatch and the nested record-match reduction on an unknown field list.
Both have been corrected without changing definitions, statements or premises;
core r3 passed (exit0, 758 jobs, 29s module time), with all recorded
source/config inputs unchanged. The connected clients were then checked separately; their preserved first feedback
and final passing evidence appear below. Logs/JSON retain each actual terminal status in
active-validation/suspension-pure-ordinary-core-r{1,2,3}.

The green core exports ordinary_step, not_ordinary_iff and
ordinary_event_ne_body with their original agreed assumptions. Core source is
frozen for the root-owned Execution proof. The ordered fallback client states
both exact five-step raw/pure residual observations as well as the reached
ConfigRep/domain, connecting the trace to repeated public ordinary_step uses.

## Statement and source-semantic check

- ordinary_step relates the actual Core.Machine.step and Pure.Machine.step
  values, retaining the complete raw memory by equality in both next/done
  cases. It neither abstracts away a fault nor assumes successful evaluation.
- not_ordinary_iff exposes exactly the five approved exceptional stable shapes.
  Raw recursive intermediates remain outside ConfigRep, rather than being
  ruled out by an unstated source typing hypothesis. Wrong nonaddress force
  remains ordinary and is handled by the related diagnostic pair.
- Pending-frame updates use the existing occurrence-indexed histories. Every
  retained occurrence receives the same actual uniform-tail pure step; no
  distinct-active-address premise is added. Cache completion remains in the
  root-owned Forcing theorem and is exercised through the returned history.
- Primitive compatibility handles value, raised and stuck results. The
  separate ParametersPreserve law is used only by the client composition of
  domain facts, never by ordinary_step. Source exceptions use the compatible
  Match/Bind tags; failed handler matching rethrows its original packet.
- Constructor/atom mismatch, exception lookup in the current matching
  environment, empty-record faults, missing fields and invalid continuation
  modes follow the existing machine equations literally. The finite group
  descriptor enters closure application through GroupRep.bodyEnvironment.
- ordinary_event_ne_body proves absence of an actual raw body-entry event
  from the shape premise alone. It makes no assertion about raw transitions
  omitted from ConfigRep having a pure interpretation.

No source syntax, evaluator, store, representation or domain definition was
changed for this slice. The full finite heap-to-pure correspondence and
nonreentry result remain parent-owned obligations; this local core theorem is
not acceptance of10019 or advancement of the chapter frontier.

Client r1 ended exit1 with unchanged inputs. Its three feedback items were
example elaboration only: an explicit raw config argument for the no-body
client, the fully qualified BasicOperation.successor constructor, and exposing
the local parameter abbreviation before rewriting step_preserves. Core source
and every expected outcome/count remained unchanged. Client r2 subsequently
passed with the three elaboration corrections.

## Final focused evidence and handoff

- Core r3: Applications.Suspensions.Pure.Ordinary, exit0, 758 jobs,
  29-second module check; 2026-11-02 21:26:51.877991–21:27:30.664241 UTC.
  Before/start/after source and configuration hashes agree.
- Client r2: Examples.SuspensionPureOrdinary, exit0, 760 jobs,
  86-second module check; 2026-11-02 21:34:23.159526–21:35:59.119443 UTC.
  All37 recorded local source/config inputs remained unchanged. The actual
  terminal session was collected and the shared focused lock released.
- Pinned offline Nix/Lean4.35, LEAN_NUM_THREADS=1, default proof limits and
  project lint settings were retained. No admissions or native_decide were
  introduced. The log retains the existing dependency module-system warnings.

Frozen terminal records/logs:

- active-validation/suspension-pure-ordinary-core-r3.{json,log}
- active-validation/suspension-pure-ordinary-client-r2.{json,log}

Earlier failures are preserved as core-r1/core-r2/client-r1; none is reported
as successful. Public core API is OrdinaryStepRep, IsOrdinary,
not_ordinary_iff, ordinary_step and ordinary_event_ne_body. Connected cases
are literal_step/literal_delivery, nonaddress_force and its no-body-event law,
successor_returns_eight/successor_boolean_fault, ordered_fallback_enters_eight,
wrong_return_mode_faults, pending_literal_step and pending_history_justifies_cache.
The last cache theorem consumes the ConfigRep/histories returned by the
ordinary body step and calls the already checked return_memoize law.

Frozen SHA-256 source identities:

- Applications/Suspensions/Pure/Ordinary.lean: `e73351ff23c7415d3f2938fe23f95be8ef68ef541e5772fbf1c037d8c197fcf4`
- Examples/SuspensionPureOrdinary.lean: `e2262f31771a9c0587eceab723c978121a68b72ae8739822405a151134ea9911`

No Git/index/entrypoint/tracker mutations were performed by this worker. Root
owns the next checkpoint commit, complete execution integration, full gates
and reviews. The worktree can contain other workers' unrelated active drafts;
this handoff freezes only the two owned Lean files and their evidence.
