# Local10019 actual finite execution and body-entry correspondence

## Intended cases and missing connection

Local delay/force/cache/creation rules were checked, but that did not establish
agreement of an arbitrary finite raw run or occurrence of an actual raw body
entry. The new public theorems compose those local laws through the existing
Prefix.observe, Recurrence.Reaches and Progress.Evaluates interfaces.

The connected finite client forces the same thunk twice and returns integer9.
Independent transition accounting gives raw21 versus pure23: the second pure
force adds body evaluation and force-frame return instead of one raw cache hit.
The second client retains an admitted expectedFunction fault at5 transitions.
Neither example supplies a cache-body evaluation as a premise.

## Public statements and proof dependencies

Pure.Simulation.finite_correspondence requires relational primitive compatibility,
hereditary primitive-output preservation, WorldAllowed, ConfigRep, ConfigAllowed,
and the actual finite raw evaluation. It returns an extended allowed world,
represented final memory and result, and an actual finite pure evaluation.
Its induction decreases the remaining raw count. Ordinary/force/cache steps
consume1; recursive creation consumes3*bindings.length+2, which is positive.
Cache reuse expands a stored CellRep witness; normal memoization creates that
witness from already executed BodyHistory. No active body termination,
first-write, distinct-active-address or source type-safety premise is added.

Pure.Simulation.body_entry_correspondence instead inducts on the observed raw
prefix index. It needs no enclosing finite evaluation. At every actually
observed body event, it returns a related admitted pure configuration, extended
allowed world and actual pure prefix. The intermediate raw recursive-creation
states do not have ConfigRep; the exact strict-prefix no-body-event theorem
excludes them from this observation contract. All ordinary, delay, normal and
exceptional memoize, uncached entry and cache-hit cases are exhausted by the
checked five-case classifier and ordinary_step.

The private ExecutionBlock only packages actual prefix/step equations and proved
representation consequences. It does not redefine a machine or assume the
simulation as a field of ConfigRep. Returned pure and raw transition counts
remain separate. Runtime exceptions, matching outcomes and faults are retained.

## Statement review and connected application

Root checked quantifiers, initial/final worlds, strict count decreases and
coverage of terminal versus unfinished outcomes. Map and Ordered independently
performed preparatory read-only passes; neither found circularity or a missing
control family. Ordered confirmed21/23 and5 by manual transition accounting.
The initially noted body-prefix client gap is addressed by the subsequently
drafted NoReentry source application: it must consume body_entry_correspondence
from an empty raw source start, not posit an active history. Its own terminal
validation status is recorded separately; this report does not infer it.

Both finite clients consume the public finite_correspondence result. Their
independent pure evaluations identify returned results/counts using deterministic
evaluation uniqueness; the resulting final StateRep comes from the theorem,
not a manually assumed final-world certificate.

## Focused validation

The first check passed all764jobs with39 frozen local source/configuration
hashes unchanged. Core37s and clients54s. No mathematical statement, premise,
count or returned-value correction was needed; default proof budgets and
project lint settings were retained. Exact command/times/hashes are in
validation/suspension-pure-execution-r1.json and its matching log.

Execution.lean SHA256:
2882d5135fe1987ff9fcdcecae0716873f443152e41d48902d15f5cab9ceb5cb
Examples/SuspensionPureExecution.lean SHA256:
6b1d973868f5d4f8dd41ff1690f5e8f8280807dfd2f555c38533ff6ce57aa3dc

This is development evidence. Full isolated-candidate build/audit, independent
Standards/Spec review and immediate final verification remain required.
