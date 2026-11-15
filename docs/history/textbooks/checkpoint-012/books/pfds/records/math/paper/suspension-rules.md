# Suspension source-rule development

Owner root; partial implementation within local10014. Fixed base69f6f00.
Requirements: requirements/suspension-foundation.md v1. Source locators and
precise boundaries: suspension-foundation-inventory.md and sml90-source-identity.json.

## Independent expected case before the connected proof

Start with a counter reference at address0 containing0 and a suspension at
address1 whose body captures environment1. Evaluating its body increments the
counter and returns its captured value1. Match the suspension in a later caller
environment99 against literal0. The match must fail normally, while counter0
becomes1 and address1 caches value1. A later match against literal1 succeeds
without a further counter increment. This follows from the thesis's write-before-
match rule; the later caller environment must not replace the captured one.

This first source-rule client specializes the inherited core evaluation to one
explicit reference update and literal matching. The separate concrete machine
will supply arbitrary core syntax, recursion and the full source counterexamples.
Neither specialization by itself establishes complete Standard ML semantics.

## Definitions and statement review

Applications/Suspensions/Rules.lean defines the AppendixA forcing/reference-
pattern rule schemata over independent core evaluation and matching relations.
It uses Except for body value/exception and Except of Option for successful
bindings, ordinary failed matching and exceptional matching. States are retained
in every relation. No global termination or rollback premise is introduced.

The cached/thunk inversion theorems expose the independent premises. In the
normal thunk case the matching premise starts from memoize afterBody address value,
not the original store or the final successful-pattern store. It uses the caller
environment, whereas body evaluation uses the stored environment. A later match
may itself overwrite the same address: no unconditional final-cache theorem is
asserted. Body exceptions return the body's reached state without another write.
Conditional determinism requires both inherited judgments deterministic in
their outcomes AND final states; it does not assert this for arbitrary relations.

ClauseMatch and Alternatives record 1990 Rules124–128 with explicit state
threading. A failed clause feeds its reached state to the next clause. A pattern
exception stops alternatives; a successful pattern evaluates the selected body
under extended bindings. Exceptions and ordinary failure remain distinct.

Syntax.lean represents the selected core fragment and finite closure triples.
Env.rec maps a closure's third component to the original entire binding list;
lookup_rec, rec_domain, rec_closure and rec_address connect this realization to
Definition6.6. Environments use first-binding lookup; source addition is new
bindings ++ old bindings, with lookup_extend specifying precedence. No cyclic
Lean values or fixed-point axioms are used. Actual address cycles remain legal.

## Status

Initial Syntax/Rules drafts await focused compiler feedback and connected source-
rule example. No10014 acceptance, chapter advance, or complete source-rule/machine
adequacy is claimed. Full exact validation and both review axes remain required.

## First compiler feedback and retained correction

The generic Rules module compiled successfully in machine-focused round2.
The connected Rules example reached only one elaboration error: higher-order
inference at suspension_deterministic failed to recover the intended core
relations from implicit argument theorems. The correction names evaluateBody
and matchLiteral explicitly and supplies proof lambdas; the expected outcome
and all source statements are unchanged. Its next focused check is pending.

Namespace.lean and Examples.SuspensionNamespaces additionally give disjoint
even/odd variable/exception identifiers with lookup and update projection laws.
This reflects the 1990 Definition2.4 classification, preserving exception
lookup across ordinary variable extension. Values are already core values;
this is not a translation of unencoded closure bodies or a full parser.

Correspondence.lean is a draft dependent on the new Continuation module. It
instantiates source-rule schemata with finite expression/pattern executions
and uses stack composition to realize normal cache installation and exceptional
body propagation. Converse decomposition and connected correspondence clients
remain pending, as do compilation and full10014 acceptance.

## Subsequent development after checkpoint011

Machine-focused round3 compiled the explicit Machine module and the corrected
Rules example. Namespace parsing exposed reserved Lean command names used as
local binders; those names are now corrected without changing any proposition.
The Machine examples stopped at an existential-witness proof-script issue before
their expected outcomes were checked; the worker is retaining all conclusions
and correcting only witness inference. No successful example execution is
inferred from that failure.

Correspondence now additionally drafts forcing completeness by splitting the
actual body continuation, reference-pattern equivalence, deterministic results
and reached states, and sound realization of ordered source alternatives. The
converse forcing proof rejects impossible body pattern-result boundaries by
their immediate invalid-continuation fault; it assumes no global type safety.
The connected example uses actual core syntax for the counter-update/failed-
match/cached-retry case described above, and obtains independent source-rule
derivations through the converse theorem. These additions await compilation.

## Bounded observation and resource expectations, before implementation

The existing Resources.run executor will sequence the actual suspension
transition through a FreeAddMonoid of events, with no additional event once a
finished answer has been delivered. For delay of literal7 from empty memory:
budget0 retains the untouched initial configuration and an empty event list;
budget1 retains the allocated cell and the value-return control, with exactly
allocate0; budget2 returns address0 with events allocate0 followed by core.
Budget9 must return exactly that same answer and exactly those two events,
not nine charged steps. This distinguishes available observation budget from
the number of transitions actually executed.

The event-preserving executor's state projection should equal Prefix.observe.
Its completion/count projection should equal the existing Progress.search,
including none for unknown and the actual finite count for a finished result.
Existing relational observation composition can then project results or selected
effects while retaining the input index. Full machine results continue to
distinguish returned values, raised exceptions, failed matches and stuck faults;
the raw bounded observation additionally retains residual memory on unknown.
No host-runtime cost, forced-body atomicity or global at-most-once claim follows
from counting these explicit source-core transitions.

## Control-flow result classes, before implementation

An expression may return a value, raise a packet or get stuck. It must not
deliver a successful pattern environment or bare mismatch to its outer caller.
A pattern may deliver bindings, mismatch, a packet or a fault, but not an
expression value. Ordered clauses may deliver a value, mismatch, packet or
fault. These are frame-protocol properties, independent of payload typing,
memory validity, termination or the SUSP-STAT-001 preservation issue.

Expected discriminating cases: applying a one-clause function with literal0
pattern to literal1 raises the distinguished Match packet; a value binding
with those mismatching literals raises Bind; direct pattern execution returns
bare mismatch. Frame input/output classes, with expression values permitted
as clause results, should preserve these result classes for arbitrary finite
executions. This will justify the ordinary-expression premise when decomposing
ordered source-rule executions, without assuming a global type-safety theorem.

## Return-class first compiler feedback

Return r1 ended exit1 with all tracked inputs unchanged. The initial private
classifiers reached the default200000 heartbeat budget, including very small
control cases. The proof loop exposed recursive stackAllowed/expected defining
equations on symbolic tails before split-at-all-hypotheses; this permits repeated
arbitrary tail splitting. The correction supplies constructor-specific nil/cons
simplification equations and keeps unknown tails opaque. No statement or proof
limit is changed. Focused verification of the correction is pending. The r1 log
and automatic command/source-hash record are retained in validation/.

## Measured observation first compiler feedback

Observation r1 ended exit1 with all recorded source hashes unchanged. The only
errors were the two workload recurrence/composition proofs leaving a definitionally
equal partially applied workload function after simplification. Explicit rfl closes
those obligations; statements, semantics and proof limits are unchanged. The
completion/search and relational composition tranche elaborated without other
reported errors, but the module/examples still require successful verification.
The exact r1 log and automatic source-hash/command record are retained.

## Return-class second compiler feedback

Return r2 ended exit1 with every tracked input unchanged. The previous
heartbeat failures are gone. Remaining branches contain explicit equations
identifying a split answer/configuration with a constructor but retain opaque
projections; their contradiction or class property is not yet simplified.
The local classifier loops now substitute those constructor equations before
simplifying, following the independently compiled Continuation correction.
No statement, semantic operation or proof budget is changed. The r2 terminal
log and command/input-hash record are preserved; r3 verification is pending.

## Measured observation verified in focused round2

Observation and Examples.SuspensionObservation compiled successfully in the
pinned Nix shell: 750 jobs, exit0, all tracked inputs unchanged. The event-list
executor reuses Resources.run and the free additive monoid; its state projection
equals Prefix.observe, and its completion/count projection equals Progress.search.
The public client connects budgets0/1/2/9 to the actual delay transitions and
shows that completed-state padding incurs no further events. The relational
composition client preserves the input index. No source-cost-to-host-runtime
claim, source type safety, full audit or10014 acceptance follows from this
focused check. Exact terminal log and command/source-hash record are retained.

## Return protocol verified in focused round3

Return and Examples.SuspensionReturn compiled successfully:744 jobs, exit0,
all tracked inputs unchanged. The constructor-substitution correction preserved
all statements and default proof limits. The clients establish application
mismatch raising Match, binding mismatch raising Bind, direct pattern mismatch,
and the generic exclusion of expression-returned pattern environments. This is
control-flow preservation, not source value-type preservation. Terminal log
and command/input-hash record are preserved. Correspondence r1 is now queued
against the checked Return and Continuation modules; no success is inferred.

## Correspondence first compiler feedback

Correspondence r1 ended exit1 with all tracked inputs unchanged. Six dependent
case alternatives named fixed relation indices that Lean had already eliminated;
those alternatives now name only their genuine constructor arguments. Three
state equalities now carry their reduced types before substitution, and the
ordered-clause converse supplies the result and relation types explicitly when
constructing an `Except.map some` conclusion. These are elaboration corrections:
all source rules, machine operations, public statements and proof limits are
unchanged. The exact terminal log and command/input-hash record are preserved.
Focused round2 is pending; no correspondence theorem is yet accepted.

## Correspondence focused round2

Round2 ended exit1 with all tracked inputs unchanged. The earlier higher-order
constructor, projection-substitution and binder-count errors are resolved. Two
case-specific names for the already fixed final-state index are not retained by
Lean's dependent elimination; the proof now refers to the theorem's original
final state. The clause-resumption proof also unfolds start when normalizing
its appended-empty-stack configuration. These corrections retain the rules,
statements, expected outcomes and proof budgets. Exact r2 evidence is preserved;
round3 remains required.

## Correspondence verified in focused round3

Correspondence and Examples.SuspensionCorrespondence passed all747 jobs, exit0,
with every tracked source unchanged. The complete forcing/reference-pattern
equivalences and ordered-alternative soundness/completeness now connect the
independent rule schemata to actual finite machine execution. The clients use
the captured-value thunk, actual counter update, failed inner match and cached
retry, plus the three-clause failure/fourth-clause success distinction. The
proof retains each reached state, including effects preceding failure or an
exception. No source value-type preservation or global termination claim is
introduced. The exact terminal log/command/input record is preserved. This is
focused evidence; the complete10014 candidate gates and both axes remain open.
