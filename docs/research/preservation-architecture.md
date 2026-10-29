# Preservation architecture after the first shared-law experiment

This is the first milestone of [#235](https://github.com/VladimirMarko/conaled/issues/235).
The [#231 experiment](preservation-experiment.md) established reuse of covered
relational preservation and ordered consequences in compiled reactive execution
and recovery evidence. It did not establish one interface for all preservation.
The [inventory](preservation-contract-inventory.md) and the experiment's
compatibility table remain the source-backed record of native contracts and
missing adapters.

## A family of compatible laws

`Interaction.Refines` covers each admitted target behavior by a related source
behavior. `Refines.property` transfers a property respected by that relation;
`Refines.bound` specializes this argument to ordered observations. These laws
are useful when the required result is a proposition about the covered target.
They do not choose executable witnesses or supply a probability distribution,
dependent substitution, comparison isomorphism or scheduler.

The checked counterexamples in `Examples.PreservationBounds` locate two
specific losses. Equal support does not determine a stochastic kernel's mass.
Equal selected payloads do not determine which of two duplicate occurrences
was selected. No additional rearrangement of the resulting Boolean facts
recovers the missing data. A client that requires the richer observation must
retain it before applying a propositional consequence.

This is a mismatch with a proposed *predicate-only universal interface*, not a
defect in the scope of `Refines.bound`. The repository already has richer native
interfaces: stochastic tables interpret into kernels, indexed representations
retain family-dependent carriers, and categorical comparisons retain arrows
and coherence. Those interfaces remain part of the preservation family.

| Approach | Obligation and consequence |
|---|---|
| Extend the ordered-bound interface with every richer judgment | Would add witness, measure or categorical data irrelevant to the current two clients. The experiment supplies no common operations that justify such a record. |
| Keep compatible native layers | Use `TyRep`, `SubCert` and `TermCert` for indexed data; kernel interpretation for mass; natural comparisons for coherence. Reuse each layer's composition laws, then derive properties with the appropriate forgetful observation. This preserves existing callers. |
| Add a client-specific adapter | State the source and target judgments, actual retained comparison data and composition theorem. A property consequence is useful, but does not become an inverse of witness or mass erasure. Implement when a concrete client needs this connection. |

The current choice is compatible native layers with small derived lemmas.
There is no justified blanket retrofit from #231 alone. A future adapter or
interface expansion must identify an actual repeated obligation or unsupported
client; the compatibility table records those requirements without claiming
their implementations exist.

## Specialization and author evidence

The first experiment retains direct and shared proofs under the same
assumptions. Direct arithmetic is simpler for a constant cell count; existing
local-to-run transport removes repeated trace induction. These are different
observations about author effort. Naming a general theorem is not evidence that
every specialization became easier.

The independent comparison for this milestone uses one operational bound and
one indexed term transport. The latter deliberately requires dependent result
types, so a weaker unindexed scalar observation cannot count as completion.
Each author must solve the same contract through direct and shared/native
specialized routes. The prospective protocol fixes the candidate, tasks,
permitted public documentation and tools, route order, assistance recording and
stopping budget before authoring begins.

The [trial record](../../experiments/preservation-authoring/README.md) retains
the frozen protocol, prompts, successful sources, setup failures and compiler
diagnostics. Two agents who did not design the interfaces worked independently
against `dc3aad9`, with opposite route orders. Both completed all four routes on
their first actual Lean submissions, without private proof hints or stronger
assumptions. Public examples and implementation source were available; this was
not a test of discovering the mathematics without assistance.

| Matched task | Direct/native route | Shared/specialized route | Result |
|---|---|---|---|
| Bound the effect observation of optional encoded recovery states | Unpack image witnesses and use the existing invariant | Construct optional coverage, compose it, and supply costs, monotonicity and comparison to `Refines.bound` | Both authors found the direct proof shorter. The shared route exposes reusable coverage and bound conversion but adds concepts for this small task. |
| Transport an indexed term through two certified substitutions | Construct code and its commutation proof, including an explicit dependent cast | Apply `ac.reindex (s.compose t)` | Both authors retained the same dependent result type and decoded equality. The specialized route removes the caller's explicit cast without requiring decoder injectivity. |

[Author A's checked applications](../../Examples/PreservationAuthorA.lean) and
[author B's checked applications](../../Examples/PreservationAuthorB.lean)
preserve their successful proof bodies. Each indexed example uses a redundant
`Nat × Bool` context decoded to `Nat` and a family `n ↦ Fin (n+1)`; distinct
representations decode equally. The resulting certificate keeps the `Fin`
witness and changing index. The operational examples admit an acknowledged
recovery state but do not infer eventual acknowledgment or physical durability.

Neither task exposed a semantic or usability regression requiring a retrofit.
Keep the direct bound proof available; do not require clients to reconstruct
coverage when their native invariant suffices. Retain the indexed facade,
which removes equality bookkeeping while preserving the richer contract.
These observations support compatible specializations rather than a mandatory
single author interface.

The evidence is limited to two agents and these tasks. Both read public source,
and each saw its first route before writing the second. Author B recorded 200
seconds of total wall time; author A recorded an 88-second interval after
initial setup, so those times are not comparable effort measurements. One
author A missing-file diagnostic was overwritten during setup; the failure and
preserved shell error are disclosed in its report. Exact model serving revisions,
token counts and isolated reasoning time were unavailable. No human-usability
or causal productivity claim follows. The protocol follows #117's matched-task,
exposure and assistance distinctions without depending on its proposed surfaces
or using #108's fresh theorem.

## Continuing ownership

The two FRP realizations add concrete tests of this separation. The
[finite circuit service](indefinite-reactive-service.md) uses the existing
circuit syntax and initialized-machine semantics, with operational derivations,
temporary-storage accounting and separately constructed conditional progress.
Its representation-change route reuses #231's bound law, but another backend
still owes local work, storage and progress evidence. A retained-state comparison
alone does not certify its evaluator or host allocator.

The [bounded lifecycle driver](frp-driver.md) instead reuses exact consumer
compilation. Publication may fail after an internal transition. Neither a
semantic equality nor a resource bound supplies external acknowledgment or
crash recovery. Its numeric codec laws and tested text/IO boundary have different
acceptance evidence. Adding a general preservation record would not discharge
those boundary obligations.

These clients therefore support keeping operations, semantic comparisons,
resource observations and environmental progress assumptions separately usable.
They also supply future regression clients: a change to shared transport must
preserve the indexed author examples, compiled circuit observations and driver
failure distinctions that it claims to cover.

[#235](https://github.com/VladimirMarko/conaled/issues/235) remains the owner of
continuing compatibility and specialization usability. Its first milestone
does not close discovery. The [language direction](../language-direction.md#evolving-preservation-laws-and-usable-specializations)
and [architectural guidance](../agents/architectural-quality.md#preservation-family-changes)
make new families, changed interpretation laws and author difficulties triggers
for revisiting the record.

The #231 handoff assigns typed/coherent routes to #36/#200, probability-aware
transport to probability/#200, operational adequacy to #193/#234, and admitted
crash/recovery observations to #196/#225. Their acceptance remains in the
experiment's handoff and the scope-owning issues. The other inventory rows
remain compatibility requirements to instantiate when a consumer needs them.

For each newly exposed mismatch, retain the native judgment and a concrete
positive or negative witness. Compare an extension, a separate compatible layer
and an adapter. If a retrofit is justified, create a scoped implementation issue
with affected consumers, migration and validation obligations. Check old and
new clients together under their original assumptions; preserve witnesses,
observations and resource properties actually claimed. Rerun affected author
tasks and retain previous failures rather than replacing their record.

No universal classification or automatic inference is claimed. Useful concrete
clients can proceed while the wider programme remains open.
