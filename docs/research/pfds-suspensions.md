# PFDS suspension semantics and observations

This is the implementation record for local ticket10014, a cross-cutting
prerequisite of the book/thesis reconstruction. Its source scope is the
suspension mechanism in the supplied book's Chapter4, the thesis's Chapter2,
and all changes in thesis AppendixA, printed pp131–135. The book's stream
algorithms and exercises retain their Chapter4 owner; the lazy-heap application
retains its Chapter3 owner. Source identities and chapter accounting are in
[the union ledger](pfds-union-coverage.md).

**This development remains unaccepted.** Syntax, memory operations,
the independent forcing rules, the explicit machine, continuation and return-
class laws, source-rule correspondence, static and grammar rules, bounded-prefix
observation, measured observation, finite-memory invariants, recursive-creation laws,
and address algebra have focused compilation evidence with their recorded connected
clients. The four derived-form equivalences and all ten clients, including the
composed lazy-call/reference case, also compile. Address-relocation execution
transport, both directions of the force observations and all their connected
clients now have passing focused checks.
Full candidate build, exhaustive proof
audit, final verification and both independent review axes remain required.
The authoritative local tickets, statements, compiler reports and recovery
records accompany the repository in durability checkpoints.

## Source boundary and local reuse

[AppendixA](https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf)
extends the1990 StandardML Definition. The book cites the revised1997 edition.
This implementation uses the
[official1990 Definition](https://smlfamily.github.io/sml90-defn.pdf)
for the inherited rules, with exact locators recorded in the source audit.
It does not silently replace1990 generalization with a later value restriction.

The implemented core has Boolean and mathematical-integer atoms, closed record
rows, constructor/exception forms, functions and strict application, bindings,
references, exceptions, recursive function/suspension groups and dollar forms.
Primitive and datatype signatures are parameters. The static fragment omits
modules, type declarations, explicit annotations and open-row elaboration.
The surface adapter retains opaque inherited grammar categories; it is not a
complete StandardML parser. No general type-safety or termination theorem is
assumed for this effectful extension.

The domain uses `Durability.Heap` for cells, `Progress.Machine`, `Evaluates` and
`search` for finite execution, `Resources.Measured` and `run` for observations,
and existing indexed relational squares for composition. It leaves the original
foundation interfaces unchanged. It adds neither a general execution framework
nor a claim that every source effect fits a pure categorical interpretation.
The earlier immutable shared-list/tree model remains appropriate for its own
clients. Suspension replacement and recursive environments have different laws.

The terminology below describes this source domain. General programming terms
are kept here rather than added to the project's architectural glossary; this
follows the domain-modeling workflow's glossary scope.

## Creation, forcing and outcomes

A suspension is represented by an address in the same memory used by ordinary
references. Its cell holds either an expression with its captured environment
or a cached value. Creation stores that expression/environment without running
the body. A cache hit uses the stored value and performs the requested inner
pattern match. An uncached force runs the body under the captured environment,
then writes its normal result before matching in the caller's environment.

The [memory library](../../Applications/Suspensions/Store.lean) separates these
operations from their predicates and laws. `Bounded` places occupied addresses
below the allocation frontier, providing finite memory and a fresh next
address. `FreshAllocation` describes the source's unrestricted fresh choice;
`allocate_realizes` makes the deterministic frontier policy one valid choice.
There is no converse claiming that all source fresh choices have the same
literal address. Replacement preserves the domain only under its stated
occupancy premise; immutable `Extends` is used for fresh allocation, not for
cache replacement.

The [independent source rules](../../Applications/Suspensions/Rules.lean)
retain states at every premise. A normal value, raised packet, successful
pattern environment and ordinary mismatch remain separate outcomes. A failed
or exceptional inner pattern retains the body's memoization and earlier
effects. An exceptional body returns its reached state without a successful
write from that force frame; inner evaluations may already have written cells.

The [machine](../../Applications/Suspensions/Machine.lean) adds explicit stuck
faults for malformed raw inputs. It evaluates the body through ordinary local
transitions and explicit continuation frames. Body evaluation is not an opaque
assumed-terminating host operation. `memoize_before_match`,
`raised_skips_memoize` and `failed_clause_retains_state` expose the relevant
state transitions. The primitive-operation interface supplies operations;
source basis validity and client laws remain separate obligations.

## Recursive environments and reentrancy

[Core syntax](../../Applications/Suspensions/Syntax.lean) uses finite closure
triples. `Env.rec` installs the original simultaneous binding environment in a
closure's recursive component, following the inherited Rec operation. It does
not construct cyclic Lean values or assume a fixed-point axiom. Address cycles
remain possible.

`srec` updates the captured environments of the targeted unforced thunks.
Its laws preserve memory domain, exception-name state, value cells and cells
outside the target set. `RecursiveTargets` separately records the source
premise that relevant targets are thunks. Recursive right-hand sides are
restricted to functions and suspensions; creation uses the same outer
environment before the simultaneous Rec/SRec extension is installed.

The [recursive-creation laws](../../Applications/Suspensions/Recursive.lean)
connect the actual creation fold with an exact machine prefix. They derive
the thunk-target premise from permitted function/delay right-hand sides and
bounded initial memory, then justify the simultaneous environment update and
its footprint. Both directions of the body equivalence account for three
creation transitions per binding and two entry/closing transitions, retaining
the complete reached answer. The core and typed connected client passed
focused round3. Subsequent documentation clarifies that permitted RHS shapes
do not supply inherited distinct-binder, nonempty-match or name-classification
conditions; those remain separate source well-formedness obligations.

Reentrant forcing is permitted. The operational cases distinguish an inner
successful cache write followed by an outer successful overwrite from an
inner successful write followed by an outer exception. Consequently neither
globally at-most-once evaluation nor rollback is an unconditional law of this
machine. Stronger pure or nonreentrant client claims need their own proved
restrictions. No blackhole marker or exception cache is inserted.

The appendix's additional statement that pure self-forcing cannot terminate is
tracked separately as local10019/TU.A.4.PURE. It remains unproved. Complete
AppendixA and Chapter4 coverage require it as well as this general extension;
an assumed nonreentrancy condition does not discharge that source claim.

## Syntax and static obligations

The [surface grammar](../../Applications/Suspensions/Grammar.lean) separates
atomic, application and full expression/pattern categories. The dollar
production belongs to the full category and consumes its following expression
or pattern. Checked derivation cases distinguish `$f x` from `f ($x)` and the
corresponding constructor-pattern forms. Identifiers exclude the reserved
spelling `$`; this does not exclude every longer symbolic identifier containing
that character. Token classification and omitted inherited syntax remain
explicit parameters.

[Static semantics](../../Applications/Suspensions/Static.lean) retains the
independent equality and imperative attributes of type variables. Reference
types admit equality irrespective of their payload; suspension and function
types do not. Imperative types contain only imperative free variables, so
closed function types meet that condition. Scheme instantiation preserves
attributes and fixes unquantified variables.

The1990 `Clos` operation withholds fresh imperative variables for expansive
bindings but still quantifies fresh applicative variables. Non-expansive
bindings may quantify both. The dollar rule is non-expansive independently
of its body's effects. The context records ambient scoped type variables and
value/exception bindings. Open supplied signatures require their free type
variables accounted for in ambient scope; the explicit signature-scoping
contract and its clients passed the focused static checks.

`force` is the derived suspended-variable function. The concrete macro uses
binder0, requiring that identifier to be variable-classified in a raw context.
The [namespace adapter](../../Applications/Suspensions/Namespace.lean) injects
variables into even identifiers and exception identifiers into odd identifiers,
so it supplies that distinction for encoded clients. The closed initial-basis
force function and its polymorphic scheme have separate static clients.

[Names](../../Applications/Suspensions/Names.lean) conservatively records all
identifier dependencies, including exception-pattern lookups. Lazy-function
sugar requires a fresh generated binder. Its typing transport additionally
accounts for ambient type-variable scope: adding an otherwise unused parameter
can change `Clos` if its free type variables were not already in the context.
Fresh term spelling alone does not discharge that obligation.

The source audit identifies SUSP-STAT-001, a polymorphic cached-reference
counterexample in this delimited effectful core. The same public core expression
has checked Boolean typing and a checked finite execution returning integer0,
together with the inequality of their atom types. The combined static client
passed focused round8. No source rule has been changed to manufacture a global
preservation theorem. The result concerns the stated 1990 plus Appendix A
fragment; a complete Standard ML parser/elaborator is outside this development.

## Finite correspondence and derived forms

[Continuation composition](../../Applications/Suspensions/Continuation.lean)
relates isolated execution to execution with caller frames appended. It
replaces the isolated final delivery step by the residual run, accounting for
the exact subtraction of one transition. The inverse splits a given finite
non-stuck execution; it does not assume arbitrary bodies terminate.

[Return classes](../../Applications/Suspensions/Return.lean) distinguish the
control protocols of expressions, patterns and ordered clauses. For example,
expression evaluation cannot return a raw pattern environment or mismatch.
This invariant concerns control flow, not the types of returned values, and
therefore does not assume away SUSP-STAT-001.

[Correspondence](../../Applications/Suspensions/Correspondence.lean) instantiates
the source's inherited judgments with finite expression/pattern runs. Its
forcing and reference-pattern equivalences and ordered-alternative
correspondence retain intermediate states and outcome distinctions. The
concrete source-rule clients include a captured-value thunk that changes a
counter, fails a pattern, remains cached and changes which later clause can
match. The complete module and clients passed focused round3 with unchanged
tracked inputs; full candidate acceptance remains separate.

[Derived forms](../../Applications/Suspensions/Derived.lean) state force-after-
delay from the state after allocation. A normal body return is followed by the
cache write and derived-force return; a raised body retains its reached state.
The exact transition counts are body-count+12 and body-count+10,
respectively. Lazy-function formation evaluates its strict argument but delays
ordered matching in the newly stored body; its normal formation count is
argument-count+9, with raised arguments costing argument-count+4. The new
converse laws recover the corresponding actual body or argument execution
from each finite normal/raised completion and retain the exact counts. These
are conditional finite-execution laws, not termination or host-runtime bounds,
and passed focused round8 with their original nine clients. The composed
lazy-formation/later-force reference client passed round10: formation takes13
transitions, an intervening reference assignment takes6, and later forcing
takes39. The later match reads the updated reference and selects the fallback
clause, retaining both nested cache writes and the changed reference.

Fresh term names prevent capture, but literal closure environments can still
contain the generated binding. Allocation likewise leaves a cell in memory.
Neither issue is erased silently. The first simple-value clients expose the
allocated/cache state; stronger comparisons under private garbage or address
renaming belong to explicitly justified client observations.

The new [address algebra](../../Applications/Suspensions/Renaming.lean),
[execution transport](../../Applications/Suspensions/Relocation.lean) and
[force observations](../../Applications/Suspensions/ForceObservation.lean)
address that private-allocation obligation. The algebra, execution transport,
observation laws and their connected clients passed focused checks.
The injection
fixes addresses below the original frontier and shifts later addresses by one.
It renames values inside records, constructors, captured closure environments
and finite recursive bindings. Related heaps agree at every represented address;
the extra private cell is omitted. Primitive equivariance is a separate law.
Initial memory is bounded and its existing cells/captured environment are fixed
by the relocation. Those premises constrain initial data, not the desired body
execution. The normal/raised observation laws transport arbitrary finite
body executions, with twelve/ten additional explicit transitions, respectively.
A connected reference case proves that old address0 contains7 and the newly
returned reference to contain9, at direct address1 versus delayed address2.
The general simulation also preserves individual transition events and both
finite-run directions. The force/direct comparison is stated for finite normal
and raised runs, with the given extra transition counts; it does not claim equal
ordered event traces, or an equivalence of faults, unknown budgets or divergence.
The dangling-capture case checks why a fixed explicit capture is required even
with bounded empty memory. Existing cell contents have their own separate
fixedness premise. All these clients passed ForceObservation round2 with unchanged
recorded inputs. Source typing and identifier classification remain separate
from these raw runtime laws.

[Finite memory](../../Applications/Suspensions/Invariant.lean) passed its focused
round3 check with all connected clients. It tracks the allocation frontier with bounds on pending
memoization-frame addresses. Memory boundedness alone is insufficient for a
forged raw frame. The intended cyclic-thunk example retains two reentrant
memoization frames for the same valid address; this is a finite-prefix invariant,
not a divergence proof. The separate Recursive laws derive SRec's target-thunk
premise from actual permitted creation and have passing focused evidence.

## Budget, resources and compositional observations

[Prefix observation](../../Applications/Suspensions/Prefix.lean) returns either
a finished answer or the entire residual configuration. Fuel exhaustion is
unknown, with retained memory; it is neither source mismatch nor a divergence
proof. `finished_iff` relates a finished observation to an actual finite run
within its budget, and `finished_iff_search` connects the existing evaluator.

[Measured observation](../../Applications/Suspensions/Observation.lean) sequences
the actual transitions through `Resources.run` and a `FreeAddMonoid` of events.
Finished answers absorb further budget without adding events. The proved
completion projection agrees with `Progress.search`, including the actual
transition count, while its state projection agrees with `Prefix.observe`.
The delay-literal client distinguishes zero budget, an allocated unknown prefix,
two-transition completion and an unchanged two-event result under budget9.
This layer and its connected clients passed the focused round2 check; full
candidate validation remains separate.

`completionSquare` and `observedSquare` reuse existing indexed membership and
observation composition. A view may select returned values or effects, but the
choice is explicit and retains the original input and actual count. Equal
returned values do not imply equal memory, event traces or resource usage.
Event weights are chosen after recording the ordered events. These measures
count explicit core transitions; they do not establish the host implementation
cost of arbitrary primitive functions, map operations or recursive environment
construction. Later algorithmic cost claims must supply their own compatible
primitive-cost model and source correspondence.
