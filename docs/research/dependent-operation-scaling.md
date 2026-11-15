# Dependent operation contracts and measured scaling

This reports the checked interface and frozen two-author experiment for
[#358](https://github.com/VladimirMarko/conaled/issues/358). Both authors
completed three cumulative scales and the fixed repair. Independent statement
assessment found that all eight checkpoint submissions meet their frozen
requirements. All eight exact snapshots replayed successfully and passed
separate exhaustive axiom checks, including helper and generated declarations.
The measurements below do not establish a general or asymptotic productivity
advantage.

## Choosing a bounded client after the architecture comparison

A client selects a position in an array of length n+1. Its state is
`Fin(n+1)`, retaining the selected value and its bound. Insertion changes both;
reflection changes the chosen position; symmetric padding changes the bound
by two while moving the position by one. Reset is noninvertible. These
operations are more than the earlier successor/double index schedule with a
predetermined payload. The held-out extension adds rotation, halving and
compression, the last changing the type to `Fin(n/2+1)`.

This selects an intrinsically indexed frontend as a bounded alternative to
extending the full reference calculus now. The
[#366 comparison](architecture-scaling-study/designated-map-comparison.md)
did not construct the quantified dependent source/model interpretation. This
experiment does not assume it. Source indices are host naturals; each term
has a genuine indexed typing derivation. Substitutions replace variables by
terms at the same index. It does not include arbitrary dependent binders,
object-language universes, higher identity or changes to type expressions by
object-level substitution. The selected tail depends on the actual result,
but is attached semantically, not admitted as a new source Sigma constructor.
These are limits of the chosen task, not proposed limits on conaled's language.

The [#364 interaction comparison](architecture-scaling-study/interaction-hiding-comparison.md)
informs an explicit distinction: local execution correctness does not license
reordering different operations. The checked reflection/padding interchange
holds, reflection/insertion fails, and changing padding to two left insertions
invalidates the former interchange. The trial includes independent interaction
and repair obligations rather than counting only larger syntax.

The [#365 controls](architecture-scaling-study/binding-probability-controls.md)
keep richer binding and probabilistic settings eligible; this deterministic
finite client cannot select among those frameworks. The
[#360 ownership result](operational-owned-handle-modes.md) likewise warns that
a structural interface does not supply a domain protocol. The
[#361 selected certificates](varying-selected-certificates.md) preserve the
importance of varying fibers and chosen values. None is evidence that this
selector requires every available interface.

## Local laws and actual boundaries

[`Syntax`](../../SquareKit/DependentOperation/Syntax.lean) specializes the existing
`DependentBranchTheoryMaps.Rules` and `Derivation` to unary operations indexed
by input/output naturals. A context supplies selected variables at each index.
Term application consumes an actual premise derivation; `graft` supplies typed
substitution. A compiler is the existing `TheoryMap` specialized to these
rules. Its fields contain primitive derivation certificates, not global
correctness theorems.

[`Local`](../../SquareKit/DependentOperation/Local.lean) derives named boundary
lemmas. `eval_subst` and `eval_twice` specialize the existing interpretation of
grafting. `compile_meaning` specializes `interpret_transport` from primitive
certificate compatibility. Independent code emission produces one variable
load followed by a list of instructions. `emit_sound` derives execution of
that list from the behavior of each primitive emitted word. `emit_lower`
compares the exact instruction words after a second lowering, using list
concatenation, not a success flag or an existential result.

[`SelectorBase`](../../SquareKit/DependentOperation/SelectorBase.lean) specifies
four operations and two independently implemented machine realizations:

- `(total bound, position)`, where reflection computes subtraction;
- `(left distance, right distance)`, where reflection swaps coordinates.

Their operations do not call each other or the source interpreter. Encodings
are injective on selected positions, and local laws retain the output bound
as well as the payload. No proof is stored in the runtime pair or instruction
list. Both realize the same finite mathematics; this is representation reuse,
not two different foundational logics or higher models.

[`Selector`](../../SquareKit/DependentOperation/Selector.lean) instantiates the
shared execution and quotation results. The native `native_distances` helper
independently proves whole-term execution by induction and is available for
baseline reuse/generalization. The comparison does not force the native author
to rebuild a separate proof for every closed expression.

[`Lowering`](../../SquareKit/DependentOperation/Lowering.lean) constructs actual
typed rule certificates. Symmetric padding expands into left insertion then
right insertion, so target syntax differs from source syntax. `lowering_meaning`
uses the existing local interpretation theorem. `lowering_quote` proves its
erased instruction word is exactly the independent macro/list compilation.
`lowering_twice` connects that same typed compilation to arbitrary two typed
substitutions. The examples then attach a selected dependent tail by the
actual equality of interpreted outputs; no global tail-preservation field is
assumed.

## What the checked applications establish

[`DependentOperationScaling`](../../Examples/DependentOperationScaling.lean)
constructs a position transformation with input bound3 and selected value1.
Insertion, padding and reflection produce bound6/value3. Reflection substitution
changes the selected output to2; a second reset substitution changes it to1.
The actual flattened word is `[left,left,right,mirror]` before substitutions.
The distance machine after both substitutions returns `(1,5)`, rejecting `(0,6)`.
The dependent tail chooses the last member of `Fin(i+1)` and follows the chosen
output through the general two-substitution theorem. Former native and shared
schedule results are explicitly retained as regressions.

Statement review checks that the signatures change the actual output index,
substitution is universally typed rather than just closed evaluation, source
and target equality compare selected values, and runtime correctness depends
only on primitive word laws. The independent expected values were calculated
before connecting them to the generic theorems. Development failures concerned
Lean inference/unfolding, list associativity and an invalid tactic import; none
is mathematical evidence against the represented operations. The primitive
fixtures are inhabited and include noninvertible operations.

## Architectural and cost comparison

| Route | Setup and reusable result | Marginal obligations |
|---|---|---|
| Native helpers | Independent structural execution proof; native operations and concrete machine contracts | Generalize the helper or extend its cases; admit new operation/index behavior and realization equations; retain quotation/substitution connections |
| Existing indexed theory laws | Actual primitive certificates and local interpretation compatibility | Admit new rule certificates and model operations; reuse interpretation of transport/grafting |
| Named local-contract layer | Thin specializations of those laws plus generic list emission/lowering | Supply new primitive emitted words and their independent machine laws; whole-term execution and named substitution laws are reused |
| Intrinsically indexed frontend | Indexing excludes malformed compositions before interpretation | Expose admissible operation indices and typed substitutions; cannot claim arbitrary dependent-calculus admission |

A block-normalized representation, as in #364, would require the mixed laws it
uses. The insertion/reflection control rejects that normalization here. A
representation requiring all primitives to be invertible would reject reset
and the held-out compression. Thus ordered, typed syntax is retained without
claiming it is universally superior. Authors may propose another representation
under the same outcomes and charge its setup/repair work.

New backends still need independent algorithms and primitive correctness laws.
New interactions still need their own mathematical hypotheses. The framework
does not discover those proofs, choose an implementation, or establish a full
reference-calculus model. These are retained costs, not fields renamed away.
Preparation effort before instrumented trial dispatch is not measured author
time. The focused build log is development evidence; acceptance requires the
full candidate build/audit, verification and independent review.

## Frozen protocol and execution

The [protocol](../../experiments/dependent-operation-scaling/protocol.md) and
[held-out task](../../experiments/dependent-operation-scaling/task.md) define
three cumulative scales, exact mathematical outcomes, independent realizations,
interaction controls, repair, budgets and stopping rules. The
[independent oracle](../../Examples/DependentOperationTrialSpec.lean) defines
only the mathematical operations and selected examples, not their compilers or
backend implementations. No held-out solution has been prepared.

Independent Standards and Spec reviewers approved candidate
`2838b20125fc4253f55eb1feb45f069f604175df` before author exposure. The coordinator
exported separate public closures with private pinned dependencies, checked
success and deliberate-failure handling through both the original wrapper and
the timing runner, recorded hashes, and dispatched fresh authors without
conversation forks. Neither author prepared or reviewed the fixture. Native support contains Syntax and SelectorBase; shared support
adds Local, Selector and Lowering. Exact author attempts, failures, resource
metadata or its absence, assistance, checkpoint results and later replay must
be preserved. Setup is separate from marginal work and from checking overhead.

The points vary depth, admitted primitives, realizations and interactions
together. They are cumulative observations, not independent samples or an
estimate of each dimension's causal effect. These measurements cannot establish asymptotic scaling. Wider model admission
remains with #289/#290; #107, #108 and #260 retain their existing status.


## Observed author work

The [preserved evidence](../../experiments/dependent-operation-scaling/evidence/README.md)
contains exact submissions, all failed checks, checkpoint records, frozen input
manifests, preparation and smoke receipts, independent statement assessment,
and coordinator replay. Both authors completed early, within every time and
attempt cap. No mathematical assistance or task changes occurred after exposure.

| Cumulative stage | Depth / new primitives / realizations | Native reported active seconds / checks | Shared reported active seconds / checks |
|---|---|---:|---:|
| A | 1 / 1 / 1 | 64.85 / 2 | 110.77 / 3 |
| B | 4 / 2 / 2 | 45.00 / 1 | 49.28 / 1 |
| C | 9 / 3 / 3 | 134.00 / 4 | 124.92 / 2 |
| Fixed repair | Counterclockwise rotation, all admitted realizations | 84.83 / 1 | 76.90 / 1 |

Times come from author checkpoint records minus recorded build-lock waits.
They include reading, editing, checking and reporting within those intervals.
Final delivery-report preparation after the last endpoint was not independently
timed, so these numbers are not exact total labor. Native stage boundaries
were reported to whole seconds; the shared author conservatively charged
30 seconds for its initial reading before the first timestamp. The native arm
started about a minute earlier because the second agent allocation initially
hit the thread limit. These are not synchronized, controlled timing samples.
Both authors' exact model and reasoning configuration were unavailable; no
explicit model or reasoning override was supplied.

The runner recorded 16.39 seconds of checking and 5.15 seconds of lock waiting
for native, versus 13.79 seconds and less than 0.001 seconds for shared. Each arm
had three failed archived Lean checks. Additional shell or missing-file
invocation mistakes are retained in the author records; they are not silently
counted as successful checks. Maximum observed Linux child high-water RSS was
1,552,780 KiB for native and 1,557,976 KiB for shared. This measurement is not
aggregate concurrent process memory. Framework design, earlier library work,
preparation, freeze review, copying, setup smoke checks and later replay are
separate costs; total pre-instrumentation design time is unknown. The recorded
closure/dependency export took 16.51 seconds for native and 90.70 seconds for
shared. These include filesystem copying under changing host load, not just
interface-specific preparation; they are not author-productivity measurements.

The native author wrote reusable whole-term preservation and quotation proofs
once, then reused them. The shared author used the prepared emission and
substitution helpers. Both retained genuine indexed source terms and chose two
executable passes: macro emission followed by instruction-word lowering. The
frozen task permits this; neither author supplied a second intrinsically typed
target syntax. The prepared library fixture separately checks typed lowering.
Neither route stores source derivations, correctness proofs or precomputed
answers in runtime instructions.

Both authors still supplied primitive meaning, emission and independent
realization laws. Adding a backend required its own algorithms and local laws;
adding interactions required separate statements and counterexamples. At C,
both reused general substitution reasoning and derived selected-tail results
for all three realizations. These tails reconstruct the chosen last member
from the selected runtime value. They do not preserve arbitrary incoming tail
witnesses or provide a general dependent-binder compiler.

For repair, both changed local rotation behavior and the relevant primitive
laws and concrete observations. Both obtained repaired answers 2, 0, 4, 3 and 5.
Native reported 16 existing declarations changed and four oracle declarations
added; shared reported 20 changed and five added. Those textual counts depend
on proof factoring. Neither changed its generic global preservation, quotation
or general substitution proofs. This is concrete evidence of local change
containment in both approaches, not evidence that the named shared interface
alone caused it.

## Architectural conclusion and next triggers

Composition worked in both arms. The native author finished sooner overall;
the shared author used fewer checks and had lower recorded marginal times in C
and repair. One author per arm, three confounded cumulative points, anticipated
later tasks and different setup support do not isolate the effect of any one
interface. The experiment establishes usability and reuse for this bounded
workload, not broad productivity or asymptotic superiority.

Retain the existing indexed theory laws, the native specializations and the
optional named local-contract helpers. No broad migration is justified by
these measurements. The native baseline already had powerful reusable laws;
forcing repeated manual proofs would have produced a misleading comparison.
The next discriminating author study under #235 should target an actual repeated
obligation that these helpers did not absorb, with separately varied dimensions
or independent authors/replications if a productivity claim is needed. Full
source/model admission remains #289/#290. Binding, higher identity, ownership,
probability and richer observations keep the separate owners and triggers in
the [disposition ledger](architecture-scaling-study/disposition.md).
