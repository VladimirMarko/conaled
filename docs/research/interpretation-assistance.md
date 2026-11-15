# Finite interpretation diagnostics (#462)

The bounded prototype selects explicit native route templates and checks their
certificates in Lean. It supports diagonal selected-row extension, image-only
transport, selected-witness erasure diagnostics, and additive observations of
executed resources. No common recursion interface, general proof importer or
automatic interpretation search is introduced.

The [CLI documentation](../../experiments/interpretation-assistance/README.md)
contains runnable commands and exact status meanings. Its
[registry](../../experiments/interpretation-assistance/registry.json) lists
constructions, targets, observations and optional certificates. The
[prospective protocol](../../experiments/interpretation-assistance/protocol.md)
separates author work from supplied setup, permits native fallback and requires
an independent readiness gate. The [frozen trial archive](../../experiments/interpretation-assistance/trial/README.md)
retains the completed author comparison, preparation, and every attempt.

## Checked evidence and boundaries

`SquareKit.InterpretationDiagnostics` prints the actual requirement definition
from Lean's environment. The checker audits every current-module logical
declaration, including private/generated helpers, and the result's transitive
axioms. It prints the root names. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. This is local experimental proof checking; the
repository's full candidate audit remains the acceptance gate for integrated
modules. Imported unused axioms are outside the local root set; any axiom used
by a local declaration is in its transitive audit.

Each request saves generated source, compiler output, hashes and exit status.
A valid result must be present and pass the audit. Failed elaboration can create
Lean recovery placeholders, so the checker requires both successful exit and
the audit marker. There is no success cache. Registry entries and author
support are trusted local Lean input; this is not a sandbox or a hostile-code
proof service. Accepted dependencies and project artifacts must be provisioned
and held stable as documented in the repository README.

`InterpretationAssistance.seeded_reweight` is the only new mathematical helper.
It combines existing `Resources.reweight_bind` and `Resources.reweight_run` for
arbitrary additive source and target observations. It does not assume numeric
costs, commutativity, termination of arbitrary recursion, or a compiler backend.
The resource development entry instantiates it at the actual square-program
seed and visit-charged transitions. Recovering the independently specified
compiled result and simplifying a cost formula remain caller obligations.
Statement review checked all initial states, inputs and observation types;
the proof reuses both native preservation theorems without another induction.

Diagonal templates consume #461's coverage helpers unchanged. The omitted-code
case checks the negation of its extension obligation; image-only transport
remains available with a different input domain. The erasure case checks
noninjectivity of witness projection, without denying the ability to choose
some representative. A supplied ill-typed certificate is rejected evidence,
whereas an absent certificate is missing evidence. Neither is called a
mathematical impossibility. An unknown registry ID is finite registry exhaustion.

## Validation and preparation status

Real CLI tests retain successful composition/image/resource requests, missing
and wrong evidence, independently checked refutations, unsupported imports,
forbidden proof dependencies, and an unused private axiom that cannot be hidden
behind a valid result. External budget tests exercise direct and internal CLI
checks, cap refusal and the coordinator cutoff snapshot. The author support
path is checked as part of every generated source, not trusted as already proved.

Development failures are retained in the coordination evidence. The initial
checker needed explicit Lean imports and metaprogram types. The first resource
request exposed a constructor encoding error for `AddMonoidHom`; named fields
repaired it without changing the mathematical contract. The first budget-suite
attempt reused a directory intended for immutable receipts; distinct state and
request directories repaired the harness. Final receipts and exact candidate
validation accompany the review handoff rather than being inferred from this
source description.

The implementation was designed against the accepted #444/#461 contracts and
the earlier #293/#235/#249/#25 author evidence. Those studies found native routes
could be as useful as assistance and exposed audit/logging limitations. This
trial therefore separately scores mathematical completion, actual tool use and
specific work removed. Preparation cost is not author savings. The implementer
has seen held-out task specifications but not reference solutions or their
successful transcripts; these are held-out applications, not blind discovery.

## Completed author comparison

The frozen direct arm made 3 actual Lean invocations. H1 passed on its first
full submission; H2 needed a second attempt to expose a folded execution before
rewriting. The assisted arm made 13 invocations: 11 inside three CLI requests,
plus two successful first full-submission checks. Counting only full submissions
would hide most assisted checking. Independent statement review finds both
final task pairs satisfy the frozen obligations. Independent replay reproduced
all 16 recorded outcomes, including the expected direct failure, and audited
all 15 passing snapshots. The audits include local/generated declarations and
allow only `propext`, `Classical.choice` and `Quot.sound`.

The assisted result uses the generated extension package and two generated
resource transport applications. Both authors manually supplied the substantive
extension and additive laws. Compiler connections, modeled resource formulas,
selected-witness properties and negative controls remained author obligations.
The image route was native. The assisted author had no failed check and made
no diagnostic-driven repair, so this trial does not demonstrate improved repair
from diagnostics. Failure handling is established by separate development tests.

Adopt the finite registry and typed diagnostics as a retained experiment with
actual consumer evidence. Investigate whether exposing exact requirements helps
on tasks that produce diagnostic repairs. Defer broader interface adoption to
#235/#290 and new recursion/compiler syntax to #109. Reject a productivity
ranking from one author per arm on these two tasks. Preparation and reference
checking are costs of the study, not author savings. Native direct routes remain
available, and no common recursive abstraction or framework migration follows.

The prospective protocol, source/tool freezes, independent readiness gates,
private reference attempts and template applicability checks are archived with
all author sources, outputs and counted receipts. Private preparations were
released only after completion. The implementer knew task descriptions before
development; private solutions were withheld. Cooperative isolation and model
metadata limitations are recorded in the launch manifest. The archive preserves
historical pending statuses rather than rewriting them as prospective success.

Independent readiness review found that certificate-phase process failures were
initially reported as rejected evidence (462-SPEC-1). The corrected runner path
separates budget refusal, ordinary Lean error diagnostics and infrastructure
failures. Actual tests first complete request checking, then make the launcher
unexecutable, terminate the checker, or corrupt the runner state. These remain
checker failures; ordinary type/audit rejection remains rejected evidence. The
prototype freeze was renewed after this correction, before any author dispatch.
