# Local #1008 Maps — independent planning review

2026-11-02. Root reviewed the plan written by the independent `maps_plan`
agent. This is a bounded source/reuse planning assessment, not either required
implementation review axis, compiler evidence, or chapter acceptance.

Plan: `../specs/1008-Maps.md`, SHA-256
`ec2664992b15240b54452ace437d12055ac1b0cc08e9b319b43e6bb211023f99`.
Source: complete pinned `Maps.v`, SHA-256
`19e79f4b7ac5bce3ffc246e19dd926b14fa5720b47d9618d2607d809d0504aea`.
Inspected implementation context: candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, whose full validation is pending.

## Outcome

No actionable omission or incorrect proposed contract was found. All 23
inventory records occur exactly once in the obligation table. All six standard
exercises, four source examples, and six source-proved partial-map laws are
accounted for. The complete source has no optional/advanced exercises, aborted
proofs, or pedagogical evaluation/check commands omitted by that table.

The plan preserves unrestricted Nat-key function spaces, explicit defaults for
constant maps, and Option-valued partial maps. It does not replace those spaces
with finite maps or infer enumeration from the function type. The total-map
different-key theorem and partial-map theorem have their actual, differing
source variable orientations. Shadowing retains the later write. Partial
self-update retains the essential `m k = some v` premise. Complete function
equalities are distinguished from single-query equalities.

I inspected the pinned Function update definitions and consequential public
theorem types: update_apply, update_self, update_of_ne, update_idem,
update_eq_self, update_comm, comp_update, and update_comp_eq_of_injective.
Their argument orders, assumptions, and conclusions agree with the plan.
The source's written-key/query Boolean comparison requires the recorded symmetry
adaptation. Value mapping requires no injectivity; key reindexing does. The
proposed default-forgetting connection does not claim reflection of absence.

The staged table draft's relevant operation, law, two-write, binding, and
default-forgetting declarations were checked. Its noninjectivity witness takes
an actual key; the proposed Nat/Bool cases meet that requirement. The exact
Dijkstra lookup/write theorem, incremental assignment and total-assignment
interfaces, ListFusion reachable fold theorem, and AbstractFIFO Simulation
shape support the proposed bounded composition choices. Their finite-domain,
group, invariant, and observation assumptions remain explicit. No new generic
map hierarchy, arbitrary-history executor, or runtime claim is mandated.

The chapter source, all nine listed provider/input identities, and the plan
digest were verified. The referenced VFA license file exists. The plan's
proposed wrappers and examples still require elaboration, statement review,
ordinary isolated integrated validation, both independent implementation review
axes, final candidate verification, and an uploaded recovery checkpoint after
the predecessor chapter is accepted.

No compiler was started and no project source, dependency, cache, configuration,
or checkout changed in this review. Only this review record was written.
