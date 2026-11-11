# Five architecture investigations

These investigations assess model combination, local universes, demand and sharing, dynamic arrays, and measured callbacks. They propose bounded comparisons and preservation requirements. They do not adopt an architecture or approve implementation of the proposed experiments.

The assessed source is [e80c51d9](https://github.com/VladimirMarko/conaled/tree/e80c51d968925be3809ba3acc3259de7041b504b). The concurrently completed #472 guard-price implementation is outside that assessment. Publication may occur on a later commit without changing the source inspected by the assessors.

| Investigation | Issue | Reconciled assessment |
|---|---|---|
| Combining independent models | [#473](https://github.com/VladimirMarko/conaled/issues/473) | [Model combination](model-combination/synthesis.md) |
| Local universes beyond weak units | [#474](https://github.com/VladimirMarko/conaled/issues/474) | [Local universes](local-universes/synthesis.md) |
| Delayed demand and memoized sharing | [#475](https://github.com/VladimirMarko/conaled/issues/475) | [Demand and sharing](demand-sharing/synthesis.md) |
| Literal and eager dynamic arrays | [#476](https://github.com/VladimirMarko/conaled/issues/476) | [Dynamic arrays](dynamic-arrays/synthesis.md) |
| Traversals with varying callback costs | [#477](https://github.com/VladimirMarko/conaled/issues/477) | [Measured callbacks](measured-callbacks/synthesis.md) |

Each directory preserves the neutral brief, three initial assessments and a coordinator synthesis. The perspectives are contract/foundations, implementation/use, and alternatives/generality. Each assessor received a fresh minimal context and was instructed not to read other reports before saving its own. Capacity limits required staged execution. The assessors share a model family; this process supplies no evidence of model diversity or absence of shared assumptions.

The brief and initial assessments are preserved verbatim. Their `/tmp/conaled-wave-20261111/design-challenges` paths identify the original task location. References to `../source` identify the read-only checkout of the assessed revision, not a directory shipped with this report. Repository-relative source paths and line numbers refer to that pinned revision. The manifest records hashes of the preserved initial artifacts. Synthesis links resolve within this durable bundle.

The reports distinguish inspected code, mathematical proposals, literature claims and executed checks. No new Lean experiment or author-productivity trial is implied by an assessment's recommendation. Publication review checks the documentation and evidence record; it is separate from the three design perspectives and from any future implementation acceptance.

The ADWH investigations follow the owner's criteria: retain useful built mathematics, cover the book with factual corrections, and serve conaled. Historical checkpoints supply evidence rather than architectural authority. Shared mechanisms must preserve current native operations, observations and clients under their existing hypotheses.
