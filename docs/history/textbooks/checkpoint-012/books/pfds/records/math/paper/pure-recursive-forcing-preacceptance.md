# Local 10019: preparatory statement and requirements pass

## Status and scope

This is an author-performed, read-only preparation pass in the existing
implementation loop. The author implemented parts of this development, so
**this is not an independent Standards or Spec acceptance review**, an
exhaustive proof audit, or complete-candidate validation. No Lean source,
entrypoint, tracker, Git index or compiler process was changed or started.
Only this requested report was written.

- Fixed 10019 implementation/review base remains
  `b422800fb5b6dc1253823057c0ea71644274d77c`.
- The inspected recovery HEAD is
  `a0ceaca91d86107d2365e82c50a92e1147ef46e8` (checkpoint 020).
- Requirements are `session/requirements/pure-recursive-forcing.md`, version 1,
  SHA-256 `57ddefb472b9393a3fe890f880ad4eb94893f5aa6bd8be912da2d7dfa4f4ec55`.
- The source obligation is thesis Appendix A.4, printed page 135 / PDF page
  147. The source paragraph was checked in the existing research extract
  `research-pfds/suspension-foundation/thesis-p135.txt`; the original source
  identity and broader book/thesis boundaries remain in
  `session/research/suspension-foundation-inventory.md`.
- The scope reviewed includes the public contracts across `Pure/Syntax`,
  `Value`, `Machine`, `Continuation`, `Recurrence`, `Representation`, `Creation`,
  `Memory`, `Compatibility`, `Domain`, `DomainState`, `WorldDomain`, `History`,
  `Simulation`, `Forcing`, `Ordinary`, `RecursiveStep`, `Execution`, `Reentry`
  and `NoReentry`, their connected examples, raw BodyEvent/Decomposition and
  the added raw Recursive prefix laws. The pass inspected definitions,
  theorem premises/conclusions, the key proof dependency chain and client
  connections; it does not claim an exhaustive line-by-line proof audit.

During the pass, CachedProgram completed its focused check. ValuePersistence
remained in development. The discovered CachedClosure client gap was accepted
by root and assigned to the map worker. Those evolving additions are recorded
separately below and are not silently included in checkpoint 020 evidence.

## Overall finding

The central mathematical obligation now has a precise, non-circular theorem
about the original heap machine. A represented, admitted source that actually
reenters an address while its earlier memoize frame is pending has no finite
raw outcome. Its proof does not assume the result as a no-reentry invariant,
does not remove the thunk during forcing, and does not substitute a blackhole
semantics. The source client constructs its history through the actual
execution bridge from empty memory.

No substantive statement defect was found in that chain. Remaining work is
finishing the explicitly owned cache consequences/clients, preserving the
resource-claim boundaries below, and the required complete-candidate gates and
independent reviews. This report does not close 10019, TU.A or Chapter 4.

## Requirements-to-contract map

| Requirement | Existing contract and discriminating application | Finding |
| --- | --- | --- |
| Actual pure self-entry cannot finish | `NoReentry.active_force_not_terminates`, `active_body_entry_not_terminates`, `source_reentry_not_terminates`; `cyclic_source_has_no_finite_raw_result` | The public contract concerns the unchanged raw machine and all finite outcomes. |
| Nonreentry is derived, not assumed | `finite_body_entry_not_active`; occurrence-indexed `ActiveHistories`; `ConfigRep.active_force_pure_not_terminates` | Duplicate pending addresses are allowed by the invariant; their obstruction is proved. |
| Meaningful recursive/lazy domain | Existing Core.Expr/Pattern plus hereditary domain; finite Group descriptors; mutual f/s, nonterminating cycle, returned recursive closure | Broad source constructors are retained. The remaining connected raw cached-closure client is assigned, not replaced by a literal-only case. |
| Primitive restrictions | `OperationCompatible`, `ParametersCompatible`, independent `OperationPreserves`/`ParametersPreserve`; checked scalar/identity basis | The laws concern actual operation outputs, not whole evaluation or assumed adequacy. |
| References and observations | Reference expressions and patterns excluded; actual pointer-equality discriminator; expectedAddress/expectedSuspension fault relation | Address renaming alone is correctly shown insufficient. Code-bearing primitive output also needs hereditary preservation. |
| Exception/name effects | Fixed packets, raise and ordered handlers retained; newException excluded; basis tags must agree | No unproved type-safety or exception-rollback assumption is used. |
| Preserve unrestricted semantics | Raw Machine/Store/Rules/Syntax definitions unchanged from final 10014 development base; old effectful clients retained | Reentrant overwrite, outer exception retaining inner cache and repeated exceptions remain meaningful. |
| Separate successful reuse/resources | Forcing certificate replay; new CachedProgram; in-progress ValuePersistence | These establish different facts. They must not be described as a proved universal write-count bound. |
| No equality of heap/cost from value agreement | Immutable World separate from mutable memory; ResultRep rather than raw equality; raw21/pure23 example | No equal trace/count/heap theorem is inferred. |

The namespace on the headline theorems is
`Suspensions.Pure.Simulation`; the module names in the table are locators.

## The mathematical chain and its assumptions

### Hereditary source and value domain

`ExpressionAllowed` and `PatternAllowed` reuse the existing syntax. They
exclude reference allocation, reading and assignment, reference patterns, and
generative exception declarations. Functions, constructors, records, strict
application, bindings, branching, recursive declarations, delays, suspension
patterns, fixed exceptions and ordered matching remain available.

`RecursiveForm` adds only permitted function/delay right-hand sides and distinct
recursive names at every nested declaration. `CodeAllowed` combines these
conditions. It does not add typing, nonempty matches, record-label distinctness,
identifier sorting, termination or an acyclicity premise. Ill-typed application
faults are deliberately admitted and exercised in the bridge examples.

The finite Value/Env/Group domain inspects stored code and earlier captures
without recursively expanding Group.members. Member construction and effective
body-environment preservation are theorems. This is what permits mutual f/s
and closure captures referring back to their suspension while keeping finite
Lean values and a stable body input.

The source theorem remains a theorem about the stated Core fragment. It does
not turn this fragment into a complete Standard ML syntax, basis, namespace
or typing development. The inherited 10014 namespace/static/source-rule
boundaries remain applicable. In particular, purity is not the published
extension's false unrestricted type-safety claim.

### Operations, state and past execution are separate

Primitive implementations are parameters. Relational compatibility is
quantified over actual related inputs in every world; output-domain preservation
is a separate requirement on admitted values. Compatibility alone admits an
effect-bearing returned closure, which the existing negative client rejects
through the second law. The basis supplies concrete identity and scalar
operations, including an actual primitive-fault case. These are nonvacuous
local applications even though the source cycle itself uses Empty primitives.

World gives an immutable meaning to a represented address. Extends preserves
that meaning literally. It is not a claim that all raw heap cells are world
entries, that meanings identify unique raw addresses, or that raw closures
have unique interpretations. StateRep requires bounded memory and justified
cells at world entries. Unforced thunks need represented code/capture; only
cached values need a successful finite pure-body certificate.

Initial cached cells therefore carry an explicit certificate. Newly allocated
unforced cells do not. Actual recursive creation, its permitted-RHS decoder,
the pending creation receipt and SRec closing construct the recursive meanings
before body execution. Old cells and captures survive. No future body result
is smuggled into the creation invariant.

Each pending memoize occurrence has an actual past pure prefix to the current
control and the portion of the pure stack inside that occurrence. A successful
return closes that past prefix into a body certificate; a cache hit replays an
already stored certificate. Thus finite correspondence does not use the desired
no-reentry fact to justify its own caches.

### Actual execution and the obstruction

`finite_correspondence` inducts on the remaining actual raw transition count.
Ordinary, delay and force/cache operations consume one raw transition;
recursive creation consumes the positive `3 * bindings.length + 2` prefix.
The pure expansion of a cache hit uses its stored witness, not a recursive
induction call on an unproved body. ResultRep retains values, exceptions,
matching outcomes and the admitted diagnostic faults.

`body_entry_correspondence` instead inducts on the actual observed raw-prefix
index. It assumes no terminating enclosing run. Intermediate recursive creation
states are not assigned a false stable ConfigRep: their exact no-body-event
law excludes them from this observation contract. At an observed body event,
the theorem supplies an extended world, related admitted configuration and
actual pure prefix.

The old occurrence's history followed by the next pure force transition is a
strictly positive recurrence at the same immutable body/environment input.
The all-outcome continuation split extracts an isolated finite completion from
any alleged finite plugged run, including faults. Deterministic evaluation-count
uniqueness contradicts the positive recurrence. This obstruction, composed with
finite correspondence and raw prefix stripping, excludes any finite raw answer.

This direction suffices for the stated no-reentry obligation. A converse
pure-to-raw termination theorem, full denotational adequacy, contextual
equivalence or general complexity bounds are not claimed or requested as
additional prerequisites by this pass.

### Source client connection

The checked `cycleTerm` source starts with empty memory and environment. Its
29-transition prefix consists of recursive creation/closing to state 8, first
body entry to state 15, function-body selection to state 23 and six further
transitions to the second suspended-pattern control. The next transition,
number 30, emits body0. The old memoize0 frame is at zero-based stack index 3,
behind the inner force clause, inner application result and f's application
result. The outer force's remaining frames are still present below it.

The client calls `source_reentry_not_terminates`, which consumes
`body_entry_correspondence`; it does not supply a manually postulated active
history. All hereditary code, represented initial state/capture and primitive
premises are discharged. Universal search-none is derived afterward from
nontermination, never inferred from one finite search exhaustion.

## Exceptions, new allocation and successful caching

The relevant distinctions must survive the final scope statement:

1. **Successful body versus successful inner match.** A successful body writes
   its value before inner matching. Later mismatch or a matching exception
   cannot undo that write. The local forcing clients exercise rejection after
   the actual write and a subsequent hit.
2. **Raised body.** A raised packet pops a memoize frame without that frame's
   own cache write. This does not assert rollback or blanket preservation of
   the original thunk after arbitrary recursive effects. The unrestricted
   outer-exception client retains the inner successful cache. The local pure
   fixed-exception example retains a thunk only because its actual body path
   performed no intervening cache write.
3. **Retry after an exception.** A never-successfully-memoized body may be
   entered repeatedly after handlers return. The raw repeated-exception client
   has two body events and zero writes. Its newException setup is outside the
   pure source predicate; it remains a valid unrestricted counterexample to
   an unconditional one-entry claim. Fixed exceptions are retained in the
   pure language, so the no-reentry theorem must not be paraphrased as forbidding
   sequential retry after the earlier frame has exited.
4. **New allocation versus aliasing.** Two identical delayed expressions may
   occupy different addresses and share the same pure meaning. The actual
   repeated-creation client runs each body once and has no cache hits. The
   pointer-equality discriminator likewise uses two realized allocations.
   Meaning equality does not identify the addresses or imply a shared cache.
5. **Counts.** Pure replay counts measure the unshared interpreter. They are
   not raw transition counts or book-level cost bounds. The existing 21/23
   example and later-hit 3/5 example deliberately retain the difference.

No raw default blackhole state or guard was introduced. A read-only diff
against final 10014 development commit
`c8ea1f8267b701f9797a52b1c8d3f9156422ccf6` shows no changes to raw
Machine/Store/Rules/Syntax definitions. Raw Recursive was extended with
stack-parametric prefix/evaluation/event laws, retaining the old public
specializations; its creation/closing operations were not replaced.

## Remaining findings and assigned follow-up

### PREP-10019-01 — actual cached recursive closure: assigned

The planned discriminating source
`s = $(fn b => if b then 7 else (force s) true)` is represented structurally,
accepted by the hereditary domain and executed by the pure interpreter. The
stable checkpoint did not yet connect its actual raw cache, containing a
closure that refers back to s, to finite_correspondence and the later hit.
The literal CachedProgram client does not exercise that capture.

Root accepted this gap and assigned NEW
`Examples/SuspensionPureCachedClosure.lean` plus its report to the map worker.
Reuse the existing returningClosure expression. Retain an actual raw source
execution, derive the reached cache validity through the public bridge, then
apply the cached closure on the false branch so that its captured s is forced
and the returned closure is applied at true. The result must be 7, with the
actual hit distinguished from active body reentry.

A useful API boundary was sent to the owner: finite_correspondence ending in
integer7 returns StateRep but does not by itself expose world lookup0, since
StateRep is one-way. Recover that meaning from an actual recursive-creation
or body-entry prefix and transport it through the residual world extension;
do not postulate the final world or cache certificate. Manual count predictions
were raw53/pure51 for the complete existing source and raw36/pure38 for a
later direct application of the recovered closure to false. These are planning
predictions only; the owner must record actual focused evidence.

### PREP-10019-02 — successful-write multiplicity: keep the boundary explicit

Shared's ValuePersistence is deliberately stronger in effect scope but weaker
in payload/count scope: a value cell stays a value cell under the bounded
unrestricted machine, so later suspended-pattern inspection hits the current
payload and emits no new body event. Reference assignment and already pending
reentrant memoize frames may still overwrite that payload. The original
reentrant two-write client must remain valid.

Consequently, ValuePersistence plus a later-hit example must not be described
as an unrestricted at-most-one cache-write theorem. Nor does the current
finite-body-entry-not-active theorem alone state a trace-count bound. A pure
source at-most-one successful write corollary would additionally require
pending-frame provenance/count reasoning from the empty source stack and the
actual event trace. That corollary is not currently proved by the inspected
public API and is separate from the completed no-reentry implication.

The version-1 requirement asks to state separately which reuse or write-count
results follow. The current defensible scope is certificate-backed reuse,
value-cell persistence/no later body entry once cached, and explicit concrete
counts. If later chapter/resource coverage claims a general per-address
write-count bound, retain it as a separately proved obligation. This report
requests neither a general complexity theorem nor a silent scope change.

### Work already owned, not rediscovered gaps

- **ValuePersistence (shared):** actual one-step, finite-run and observed-prefix
  value-cell persistence; later force-hit/no-body consequences; retained
  overwrite/repeated-exception diagnostics. Its final focused evidence is
  still to be supplied at this report's preparation boundary.
- **CachedProgram (map):** now focused-green, first round, 764 jobs, unchanged
  inputs. It derives the final cache/world from the actual source execution
  through finite_correspondence, then feeds the recovered certificate into
  reuse_cached. Independent raw/pure source counts are 15/15; later matching
  counts are 3/5. This closes the earlier literal source-to-cache-to-reuse gap.
- **CachedClosure (map):** newly assigned as PREP-10019-01, not yet treated as
  completed evidence here.

Historical method/model/integration reports intentionally record earlier open
states. The final candidate's scope or ledger must point readers to the later
Execution/NoReentry/cache reports, so those snapshots are not confused with
current proof status. Do not rewrite their historical evidence as though the
results had existed at their original checkpoint.

## Architectural fit and acceptance boundary

The new machine is a source-specific nonmemoizing interpretation over the same
Core syntax. It reuses Progress.Machine/Evaluates/search/uniqueness instead of
introducing a competing generic evaluator. Reaches and Prefix.observe are
thin observations of actual transitions. Resource instrumentation uses the
existing ordered event-list/Measured interface. Immutable worlds reuse
Durability.Heap, put and Extends. Structural representation, code-domain
preservation, actual operations and compatibility laws remain distinct.

The private ExecutionBlock packages already proved local step/prefix facts;
it is not a simulation axiom stored in ConfigRep. The source-specific finite
correspondence exposes its relation and final-memory evidence directly. There
is no justification for forcing it into a stronger equal-count or decoder-only
contract, or claiming parity with a full denotational semantics. Existing
source-rule and observational adapters remain available from 10014 without
being silently expanded by this theorem.

The new cached recursive-closure client is the useful remaining composition
experiment. No additional generic framework or broad optional test campaign
was identified as necessary for the stated no-reentry claim.

Root still owns integration of all source files into the public entrypoint,
immutable complete-candidate build, exhaustive declaration/axiom audit,
matching validation record, independent Standards and Spec reviews and immediate
final verification. The separate corrected-import, Chapter 2 and 10014 gates
remain separate; their status cannot be inferred from these focused results.
The chapter frontier and whole-book/whole-thesis coverage are unchanged.

## Root implementation follow-up before checkpoint021

PREP-10019-01 now has a complete focused-checked implementation, not an
independent acceptance disposition. Examples/SuspensionPureCachedClosure.lean
reuses returningClosure verbatim, derives address0's meaning from actual creation,
then its final cached-state/capture relation through finite_correspondence.
The later application consumes reuse_cached under actual four-frame continuation.
First check passed768jobs with all45 inputs unchanged; source53/51 and later36/38
counts and one-body/one-write/one-hit source trace passed unchanged. Exact report:
research/pure-recursive-forcing-cached-closure.md and its validation r1 record.
ValuePersistence's terminal r3 also passed748jobs, including all boundary clients.
PREP-10019-02 remains the documented scope limit: no general write-count theorem
is asserted. Both independent acceptance axes and the exact complete gate remain.
