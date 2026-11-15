# Parser selection with preparation, query and storage limits

Issue #309 connects the four existing `ParserWorkload` policies to
`Resources.Prepared`. It retains ordinary parsing, retention, normalization,
and their combination as separate choices. Selection uses the shared finite
catalog optimizer, with feasibility established before the objective is
compared. It does not discover policies or optimize beyond this catalog.

## Caller contract

`ParserSelection.rawOps` prepares an immutable source `Spine` at a fixed depth.
Its state contains both that original source and the actual existing `Setup`.
`Valid` requires source identity and equality with the setup produced for that
source and policy. Recognition equivalence between two parsers is insufficient:
they can select different witnesses. No update operation is admitted. A changed
parser requires another preparation; zero maintenance is not a free update law.

The caller separately chooses maximum view depth and maximum word length.
`Request` encodes all requests within this envelope using a finite view and a
finite Boolean vector. `Request.ofRaw_raw` proves that every raw request
satisfying the two size bounds is recovered exactly. The service accepts a borrowed raw list through `AdmittedRequest`, so vector
materialization is not hidden inside its charged query. `raw_laws` and
`raw_bounds` connect this service to the same profile; `ops` is the finite
encoding adapter used during enumeration. The envelope may exceed
preparation depth. The examples prepare to depth two but admit views and words
through three, so both rejected depths and rejected word lengths occur inside
the theorem's domain. Their word-length traversal, comparisons and result
wrapper are charged. Requests beyond the public envelope require a separately
accounted admission mechanism; they are outside the uniform deadline theorem.

The original source and every setup allocation remain live until teardown.
This includes normalization intermediates, closures, retained decisions and
snapshot nodes, even if they become unreachable. A query arena remains live
until its answer is consumed synchronously, then is released. The consumer
cannot retain pointers into that arena. These are the unchanged
[complete workload](complete-parser-workloads.md) lifetime conventions, not a
new collector or a statement about Lean heap layout. Input storage is borrowed;
source construction, instrumentation and consumer copying remain outside the
session tariff.

## Cost and universal bounds

A tariff assigns a natural coefficient to each of the nine existing event
categories. `cost` retains derivative, nullable, normalization, map, closure,
snapshot, validation, traversal and allocation events. `cost_append` preserves
sequential work composition; `batchCost_unit` recovers the existing `Run.work`
when every coefficient is one. Custom zero coefficients mean an operation is
unpriced in that chosen objective, not that the operation is absent.

`worst` enumerates the entire finite request domain and takes the maximum of
actual query work or allocation. `le_worst`, together with raw-request
coverage, supplies a bound for every admitted request, including rejections.
This can be expensive for large bounds: the number of Boolean words grows
exponentially. Profile synthesis is executable but has no claimed fast
asymptotic implementation. The service deadline covers the represented query
execution after preparation, not enumeration of its profile.

The profile records actual setup work, maximum query work, source plus setup
retention, and retention plus the largest query arena. `bounds` instantiates
all five shared obligations, including preparation peak and query peak.
`batch_peak` also connects the bound to the existing actual `Run.peak`.
The uniform service profile reserves query capacity even for a zero-count
objective; the actual empty batch uses only the source and setup arenas.

## Exact known batches and unknown future words

`chooseOffline` receives `offlineInput` containing the source and an admitted
batch. Its objective is exact setup plus query work for that supplied batch.
Computing the objective may execute the four modeled workloads, and computing
profiles enumerates admitted queries. This selection and profiling work is
outside the subsequent preparation/query budgets. Nothing here makes online
policy selection free.

`chooseFuture` receives the source, public bounds and a maximum query count,
without future words. Its objective is setup plus count times worst query
work. `batch_upper` proves this bounds every admitted batch of at most that
length. Minimizing this upper bound does not prove minimum actual work for an
unknown batch. The same feasible-catalog theorem applies to both objectives.

`chosen_minimal` supplies catalog membership, all phase constraints and
objective minimality. `choose_none_iff` says that `none` means every catalog
entry is infeasible. Equal objectives retain the first feasible catalog entry,
following the shared selector. `chosen_correct` preserves the exact native
`Decision`; `chosen_resources` connects startup and capacity limits to actual
prepared work and live arenas. `chosen_deadline` and `raw_deadline` retain the full query tariff.

## Checked choices

For the eight-map source with payload `[true,false]`, preparation depth two
and admission bounds three, the exhaustive unit-tariff profiles are:

| Policy | Setup work | Maximum query work | Retained slots | Peak slots |
|---|---:|---:|---:|---:|
| Ordinary | 0 | 259 | 33 | 202 |
| Retained | 1221 | 7 | 821 | 822 |
| Normalized | 46 | 114 | 60 | 124 |
| Combined | 728 | 7 | 449 | 450 |

The known twenty-query workload selects combined under roomy limits; the
single short query selects normalized. The already-simple parser selects
retention without normalization. A capacity and peak limit of 200 excludes
the repeated-workload winner and selects normalized. A query deadline of seven
excludes both direct policies and selects combined even for the short batch.
A deadline of two admits no policy. A zero-query objective selects ordinary;
its actual empty-session peak is 33 slots, compared with 449 for combined.

The hundred-element witness still incurs 5729 map work units and 11621 retained
slots under combined retention. These observations prevent the selection
experiment from treating witness maps or persistent setup intermediates as
free. They are abstract event/slot counts, not elapsed-time measurements.
The profile table is separate from the older workload table because maximum
query cost quantifies over the admission envelope rather than the supplied
batch alone.

## Selected witnesses and shared-interface fit

The measured spine has a constant payload, `List Bool × PUnit`. Its prepared
adapter therefore fits a fixed answer type directly. General parser answers
still have type `Decision (P word)`. `semanticAnswer` retains the word and exact
decision in a dependent pair; `semanticAnswer_exact` preserves both, including
the chosen empty nullable-star witness. This semantic adapter makes no
transport-spine cost claim for nullable star and introduces no general dependent
memoization API. The native parser and retention APIs are unchanged.

The first adapter check exposed a concrete universe restriction in #305:
`Setup` inhabits `Type 1`, while `Prepared.Ops` and `Storage` initially required
all carriers in `Type 0`. The shared declarations now have independent universe
parameters: `Ops`, `Profile`, `Storage`, `Reduction`, `Reduction.Arena` and the
representation family in `selected_agreement`, with their inferred laws and
bounds generalized consistently. Operations and law statements otherwise stay
the same. Existing preparation and LCA clients remain required compatibility
checks. This was a representation-fit correction, not evidence for another
selection framework.

## Validation and remaining scope

Checked examples are in `Examples/ParserSelection.lean`; executable checks are
in `scripts/ParserSelectionTest.lean`. The existing
`scripts/ParserWorkloadTest.lean` remains part of validation. They cover repeated
and short workloads, already-simple and heavy-witness sources, storage and
deadline exclusions, no feasible policy, zero queries, exact payloads and charged
rejections. Final acceptance also requires the repository build, exhaustive
proof audit and independent Standards and Spec review.

The remaining boundaries belong to the existing parser/resource agendas:
arbitrary witness closures or richer grammar costs, consumer-retained outputs,
alternative reclamation, faster certified profile synthesis and concrete target
cost refinement. No current result requires replacing the native interfaces or
adding a universal dependent cache. #174 owns resource/backend development;
#263's broader memoization agenda and #235 retain any future demonstrated
preservation mismatch. This bounded adapter does not claim physical elapsed
time, byte-level storage or a general author-productivity result.
