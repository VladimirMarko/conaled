# Curated textbook checkpoint 024

[Issue #582](https://github.com/VladimirMarko/conaled/issues/582) receives this
checkpoint under the continuing textbook owner
[#558](https://github.com/VladimirMarko/conaled/issues/558). It retains the new
mathematics, source code and mathematical ticket requirements. The archive,
Git bundle, environment setup, troubleshooting, diagnostics, raw logs, caches
and packaging machinery are excluded from both this copy and the newly
introduced Git history.

## What is new

The donor candidate `68affd0a049a9a537ec583c225e0fccd574f2fcc` adds twelve
linear commits after the already received upstream
`c214fb0720ffc998951255a7e4b5f2e80a299186`. Their 59 changed paths recover
measured tree folds, suffix traversal, shape-sensitive work, structural and
weighted observations, ordered-search connections, enumeration/reconstruction,
balancing, completeness and maximum caches. The VFA change qualifies Preface
and Perm coverage; it introduces no new sorting implementation. There is no
new PFDS implementation in this candidate.

The new tree code uses existing `BinaryTree`, `Trees.fold`, `Resources.Measured`,
`Trees.Cached`, ordered-search and relational composition interfaces. Useful
starting points are:

- [Measured balancing pipelines](../../../../Examples/TreeBalancePipeline.lean):
  compare actual literal, direct-suffix and construction-plus-invocation
  executions with equal results and distinct complete declared costs.
- [Ordered-set balancing](../../../../Examples/TreeBalanceSearch.lean):
  compose rebalancing with insertion and directed membership through existing
  set laws and valid-state observations.
- [Tree cache tariffs](../../../../Examples/TextbookTreeTariffs.lean):
  six cache-node value, cost and validity specializations extracted from mixed
  diagnostic input and integrated as ordinary mathematical examples.
- [FDSA Chapter 4 correspondence](../../../research/fdsa-chapter04-coverage.md)
  and [VFA correspondence](../../../research/vfa-coverage.md): source obligations,
  actual theorem owners and remaining qualifications.

The measured pipeline is already a reusable integration example. For a full
request on `N` input nodes, it proves source-model costs `7*N + 2 + A`,
`4*N + 2`, and `6*N + 3`, where `A` is the sum of left-subtree sizes. It
retains construction work and the nil boundary. These are declared operation
counts, not physical runtime, allocation or sharing guarantees.

## History and curation

[source-map.json](source-map.json) maps the twelve original commits to the
received commits and records the extracted tariff fragment. Only selected
patches were applied to the receiving branch. Their non-entrypoint source
bytes agree with the originals; `SquareApplications.lean` retains both the
receiving imports and the new imports. No original donor parent or unrelated
ref was attached to the receiving history.

All other advertised donor ref tips were already represented by existing
history, using the checkpoint-012 rewrite registry where needed. No new
independent side-branch mathematics was found. The earlier restoration registry
and its tool remain unchanged; this new map is not an extension of its
unchanged-tree reconstruction contract.

[archive-disposition.json](archive-disposition.json) identifies the input and
retention boundary. [Mathematical notes](mathematical-notes.md) retain the
needed paper-level distinctions and source pointers after removing operational
material. [TICKETS.json](TICKETS.json) preserves all 78 `CTB-` identities and
their mathematical requirements, dependencies and historical statuses. Those
statuses describe the producing session, not current GitHub acceptance.
Operational-only tickets retain their identity and omission disposition.

CTB means **conaled textbooks**, as defined in the
[namespace registry](../issue-lineages.md).

The twelve original commit subjects already used `CTB-` IDs. Received subjects
retain them and add the real receiving issue `#582`. Existing VFA, FDSA, PFDS
and INT identities keep their meanings. Actual GitHub references, including
`#174`, `#420`, `#448` and `#558`, are not rewritten as local tickets. See the
[namespace registry](../issue-lineages.md).

## Acceptance and remaining scope

The receiving repository's instructions and exact-candidate validation/review
procedure govern acceptance; producing-session process instructions have not
been imported. Historical focused checks do not substitute for the receiving
full build, exhaustive axiom audit and both independent review axes. The
acceptance record belongs to #582.

This intake substantially advances #561's FDSA tree/resource recovery. It does
not close that issue's other donor families or whole-book coverage. #559 owns
remaining total-table/map contracts, #560 sorting specifications, #562 actual
tape sampling, #563 the remaining VFA drafts, and #564 PFDS persistence and
suspension connections. The next practical client should use these results to
justify a representation choice while retaining complete demand and cost
observations; adding the checkpoint does not itself supply that client.
