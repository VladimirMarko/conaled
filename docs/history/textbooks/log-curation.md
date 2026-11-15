# Historical log curation

The checkpoint-012 compiler and environment transcripts are deliberately
omitted after a content audit. No theorem, counterexample, useful stronger
unfinished claim or necessary proof strategy was identified that survived
only in these logs. The useful mathematical content already has retained
source and note owners, listed below. No raw transcript or copied theorem
dump is required by this disposition.

This replaces the initial blanket preservation claim. It does not change
the retained source, accept a deferred development, or provide a new Lean
build or axiom audit.

## Exact omitted set

The set is every file key in
[the original manifest](checkpoint-012/MANIFEST.json) that begins `books/`
and ends `.log`. The original manifest records each path, size and SHA256;
[preservation.json](preservation.json) records the selection and its digest.
This defines the exact set without maintaining a second path inventory.

| Records | Logs omitted | Original bytes |
| --- | ---: | ---: |
| FDSA | 452 | 16,881,034 |
| PFDS | 218 | 5,610,995 |
| VFA | 111 | 2,884,741 |
| Common integration | 7 | 2,400,009 |
| **Total** | **788** | **27,776,779** |

All original selected bytes were rehashed before curation. The audit processed
every file, grouped repeated progress and generated diagnostic contexts, and
inspected the identified mathematical goals, printed declarations, probes,
counterexamples and meaningful review/proof-development families. Significant
candidates were compared with surviving statements, hypotheses, examples,
notes and donor source; finding a file with the same name was only a coverage
check. Large generated contexts were inspected through their propositions,
transition cases and bounded context views. This is full-input screening and
targeted semantic comparison, not a manual reading of every repeated line or
a formal equivalence proof for every historical rejected goal.

The curated checkpoint copy contains **9,130 original manifested entries plus
the original manifest: 9,131 files**. The omitted source bundle, setup material
and old guidance snapshots keep their separately documented dispositions.
Retained payload files keep their original bytes.

## Useful mathematics and where to continue

These are surviving owners, not new results extracted from compiler errors.
The [donor dispositions](checkpoint-012/books/common/analysis/donor-dispositions.json)
and [book coverage account](checkpoint-012/books/common/COVERAGE.md) retain
their distinction between active library, staged mathematics and book completion.

### FDSA

- **Probability and selection boundaries.** The
  [conditional-order account](../../research/fdsa-permutation-tail.md) and
  [boundary example](../../../Examples/PermutationTailBoundary.lean) retain
  the biased conditional-order counterexample and the required whole-order
  law. The [selection correspondence](../../research/fdsa-selection.md)
  retains the median-of-medians counterfamily, strict-half correction,
  all-equal behavior and positive-size premise of the scan-tail bound.
  These source corrections remain owned through [#558](https://github.com/VladimirMarko/conaled/issues/558);
  the executable sampling bridge in [#562](https://github.com/VladimirMarko/conaled/issues/562)
  is a separate obligation.
- **Actual costs and validity.** [Cached-tree costs](../../research/fdsa-tree-cache.md)
  retain the callback cost in `Resources.TreeCache.nodeRun_cost`; value
  correctness and cache validity have separate theorems. The
  [potential-accounting note](../../research/fdsa-potential-accounting.md)
  retains the initial-credit and signed/invariant boundaries. Their old
  elaboration failures add no missing mathematical statement.
- **Statement probes.** All 39 explicit Lean input commands found in the
  FDSA logs resolve to 33 retained input files beneath the
  [provenance drafts](checkpoint-012/books/fdsa/records/math/drafts/fdsa-control/provenance).
  This includes the 1,391- and 1,321-statement inputs. Keep those programs
  and their declaration sources; inspect the actual candidate's types when
  required, rather than treating old printed output as current acceptance.

### PFDS

- **Return protocol and exceptions.** The
  [suspension account](../../research/pfds-suspensions.md) distinguishes
  control-flow return classes from type preservation and retains the
  SUSP-STAT-001 cached-reference counterexample. The large failed Return
  case split does not supply another unfinished theorem.
- **Entries, writes and debit support.** The
  [body-count account](../../research/pfds-body-counts.md) retains an actual
  exception-retry example with two body entries, zero successful cache
  writes, and one distinct body address. The at-most-one-entry result keeps
  `NoMemoizeUnwind` explicitly; finite pure normal return alone does not
  supply it. Pending-or-value and settled-address proof strategies already
  appear in that note and [cache accounting](../../research/pfds-cache-counts.md).
- **Identity and costs.**
  [Pure-compatibility examples](../../../Examples/SuspensionPureCompatibility.lean)
  retain the pointer-equality obstruction despite injective-renaming
  equivariance. [Signed potential](../../research/pfds-signed-potential.md)
  and [persistent accounting](../../research/pfds-persistent-accounting.md)
  retain initial/final terms and the distinction between support and
  multiplicity. [#564](https://github.com/VladimirMarko/conaled/issues/564)
  owns the remaining algorithm-specific connections.

### VFA

The useful staged counterexamples and key correspondence remain with
[#563](https://github.com/VladimirMarko/conaled/issues/563):

- [Unary comparison](checkpoint-012/books/vfa/records/research/drafts/unary-costs/README.md)
  retains the explicit constructor-call cost `min n m + 1`, its measured
  clients and the refutation of difference-only bounds.
- [Observing queue peek](checkpoint-012/books/vfa/records/research/drafts/queue-costs/README.md)
  retains reachable repeated-reversal witnesses and the state-potential
  obstruction. The source operation returns a value without installing
  normalized queue state.
- [Positive keys](checkpoint-012/books/vfa/records/math/drafts/positive-keys/VFAStaging/PositiveKeys.lean)
  retain shifted encoding/decoding, PNat adapters and the unshifted zero/one
  collision.

The import/instance failures, generated values and historical helper-test
output have surviving corrected source, producers and meaningful summaries.
Their transcripts add no identified missing mathematics.

### Shared maps

The [shared integration account](../../research/textbook-integration.md#maps-shared-partial-meaning-valid-states-and-weaker-observations)
and [public map client](../../../Examples/TextbookMaps.lean) retain presence
versus default lookup, the valid-tree restriction and the interface's universe
boundaries. The public-type probe input and correction notes also survive in
the [common evidence](checkpoint-012/books/common/evidence).
[#559](https://github.com/VladimirMarko/conaled/issues/559) owns remaining
total-table and map-operation work.

## Reading historical evidence

Raw log references inside the frozen checkpoint records identify evidence
available to the original session. Under this disposition those paths can be
absent intentionally. The original manifest's hash identifies an omitted
file; it is not a claim that its bytes are retained in Git.

Structured receipts, review conclusions, failure summaries, counterexamples
and meaningful unresolved findings remain. For example, the common
[full-build summary](checkpoint-012/books/common/evidence/full-validation-r5-summary.json)
records the old failed attempt without keeping its progress stream. A
summary preserves the recorded outcome; it does not reproduce the raw run or
validate today's candidate. Do not convert an intentionally absent transcript
into a missing-proof task or diagnose the historical process termination.

For subsequent work, retain new mathematical information in the existing
source or a concise owner-linked note, with hypotheses and proof status
explicit. Preserve a log extract only when necessary information is absent
from those artifacts. Build progress, download output, heartbeats, superseded
syntax failures and derived declaration dumps need no permanent copy here.
