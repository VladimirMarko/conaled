# Toolkit author effectiveness under recorded conditions

This bounded investigation belongs to [#249](https://github.com/VladimirMarko/conaled/issues/249)
under [#235](https://github.com/VladimirMarko/conaled/issues/235). It tests the
accepted ordered-summary interface with independent authors, using the
[agreed distinctions](../language-direction.md#elegance-author-capability-and-language-constraints)
between mathematical structure, Lean encoding and author effort. The
[archived protocol](../../experiments/toolkit-authoring/protocol.md) fixes the
contracts before dispatch. No interface was redesigned for the trials.

## Scope and prior evidence

The tested source is `f071f18966d1ee875cdb5f328903d18a714732dd`.
[OrderedSummary](../../Applications/Sequences/OrderedSummary.lean) separates
full decode, arbitrary monoid summary, optional cache validity, local operation
laws and batch fusion. Its List and DList specializations instantiate those
laws without requiring a container type class. The
[implementation record](ordered-summary-implementation.md) supplies the public
explanation available to the authors.

The [earlier #235 trials](../../experiments/preservation-authoring/README.md)
compared an operational effect bound and indexed dependent term transport.
They found different benefits: unpacking a native invariant was simpler for
that bound, while `TermCert.reindex` removed explicit dependent equality
bookkeeping without erasing the indexed witness. This investigation retains
that evidence and selects different tasks. It does not repeat those tasks or
claim a trend between the two runs.

[#117](https://github.com/VladimirMarko/conaled/issues/117) supplies a prospective
matched-task protocol for embedded Lean, slean and Agda-like surfaces. At this
investigation it remains blocked on surface design (#116), with no completed
trial record in its issue. We use its exposure, assistance and checked-outcome
distinctions, not hypothetical author results. Neither #108's reserved fresh
theorem nor a new surface language is involved.

The newer [bounded buffers](../../Applications/Sequences/BoundedSummary.lean)
and [durability](compositional-durability.md) developments are adjacent
consumers, not additional trial families. These trials do not measure authoring
crash protocols, resource recurrences, bounded-word implementations or recursive
proof transport between mathematical settings. Their practical conclusions
apply to this ordinary Lean sequence interface.

## Matched contracts

| Family | Direct route | Shared or specialized route | Retained result |
|---|---|---|---|
| A: established DList batch client | Native DList/List induction plus primitive summary laws | Existing DList batch specialization | Full decoded sequence and ordered summary for arbitrary monoid, including noncommutative monoids |
| B: new reverse-list realization | Native reverse/list reasoning and primitive summary laws | Prove local decode laws; instantiate cache validity, append preservation and batch fusion | Valid empty/append caches, full decoded batch and ordered summary under the same assumptions |

For B, `decode r = r.reverse`, push stores `a :: r`, and represented append is
`y ++ x`. Cache validity states that the stored monoid value summarizes the
*decoded* sequence. All plain lists are valid representations; arbitrary
cached values are not. Neither route can replace full-history equality with a
lossy summary or assume the desired result as a hypothesis. The shared route
must derive guarantees from the existing laws. Direct proofs may use native
list and summary primitives but cannot use the shared batch/fusion theorems.

The acceptance cases include empty and nonempty inputs, an ordered
`FreeMonoid Bool` observation, histories of equal length with different contents,
and an invalid reverse-list cache. These expose empty-seed handling, reversed
multiplication order and accidental loss of history information. No resource
or physical execution claim is in the contract.

## Conditions and limitations

Two fresh agents received the frozen protocol with no conversation-history
fork. Neither designed the tested interface. They could read public source and
examples, use shell and Lean, and work in separate assigned artifact directories
inside one isolated checkout. They were forbidden to read one another's work,
change library interfaces, spawn agents or use external model calls. Source
revision and dependencies were shared and fixed; only the coordinator prepared
the copied private build cache. Authors invoked Lean without output files.

Author A's order was A direct, A shared, B direct, B shared. Author B's order
was B shared, B direct, A shared, A direct. Each had a 15-minute wall-clock cap
from its own recorded start, or completion. This is counterbalanced exposure,
not a crossover experiment with independent observations: each author knew an
earlier solution before writing its counterpart. Public examples also expose
relevant proofs. Neither route represents blind mathematical discovery.

Only one configuration was available under the authorized inherited-model
setup. Exact serving model revision, configured reasoning effort, token usage,
pricing and internal context handling were not exposed. No override or paid
external call was made. Two agents are not two capability tiers. These data
cannot estimate a capability trend, a cheaper-worker trade-off, general human
usability or causal productivity savings. Wall times include compiler activity,
setup and uncontrolled host contention.

The [environment record](../../experiments/toolkit-authoring/setup/record.md)
discloses an unrelated stale copied GraphEmission artifact, its reproduction
and rebuild. Both authors received only an environment-ready message, with no
mathematical hint. The coordinator's setup faults must not be counted as author
proof failures. Lean was 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; dependency and flake pins are retained
in the frozen revision.

## Observed obligations and diagnosis

Both authors completed all four routes without a mathematical hint or a changed
contract. Their sources, per-attempt diagnostics, commands, timestamps and
assistance records are preserved in the
[trial archive](../../experiments/toolkit-authoring/README.md). A completed its
report in about 5m36s; B in about 5m18s, including the audit repair. Both were
inside their 15-minute caps. Each first submitted proof failed once, then all
remaining mathematical route submissions passed. These are observed outcomes,
not comparative speed estimates. Both also recorded a Python-outside-direnv
setup error, without a precise event timestamp.

| Observation | Reproducible evidence | Diagnosis and limit |
|---|---|---|
| Established DList specialization discharged both client results directly | Each author's A shared uses `dlist_batch_decode` and `dlist_batch`; direct A proves accumulator-generalized fold results | Useful specialization of the same laws; no new vocabulary or weaker observation. The trial was selected around existing helpers, so it does not establish universal convenience. |
| New representation reused batch arguments after supplying local laws | Each B shared instantiates `batch_decode` and `batch_summary` with reverse decode and cons push | Repeated induction is removed, but decode orientation and laws remain the realization author's mathematical responsibility. |
| Cache specialization requires connecting a concrete validity predicate to generic validity | A uses `valid_iff`; B packages `⟨trivial, hx⟩` and projects `.2` | Alternative caller encodings of the same conjunction. The `True` invariant introduces small visible boilerplate, not a different guarantee or a requirement for a larger abstraction. |
| A direct first attempt did not simplify DList's empty decoder | [Attempt01](../../experiments/toolkit-authoring/author-a/Attempt01.log), repaired in Attempt02 with explicit `Batteries.DList.toList_empty` | Local normalization knowledge; the same statement checks after adding the lemma. Not a mathematical obstruction or evidence Lean cannot express the design. |
| B shared first attempt hit a simplifier recursion limit in the invalid-cache example | [Attempt01](../../experiments/toolkit-authoring/author-b/Attempt01.log), repaired in Attempt02 by applying `FreeMonoid.toList` to an equality | Concrete interaction of rewrite rules, with a working proof at the existing recursion limit. The warning names a possible loop involving `FreeMonoid.of`; it does not establish a fundamental elaborator limit. |
| A final experimental audit initially omitted local declarations | Final experimental-path audit versus corrected explicit package-root audit, retained in each author's archive | Validation harness scope, not proof failure. A successful audit message alone did not establish coverage of the trial theorems. |

No mathematical expressiveness limitation was demonstrated. Both authors kept
arbitrary monoids, ordered multiplication, full sequence equality and invalid
cache rejection. No cast or dependent equality transport was required by these
tasks. That absence says little about interfaces with dependent indices,
nontrivial representation invariants or coherence requirements.

The specialized A route exposes familiar operations and named conclusions. B
has a longer path: choose decode, state local laws, connect the validity
predicate, then use the same shared vocabulary. A retained the bridge as an
explicit equivalence; B used the conjunction directly. Neither needed a second
container hierarchy or a representation conversion at runtime. These are
source-level obligations, not measurements of runtime work or proof-author
reasoning effort. The general interface remains accessible when the concrete
DList specialization no longer fits.

## Recommendations and continuing ownership

Keep the existing DList specialization and general observation-law interface.
The trial supplies no evidence for replacing them, introducing a mandatory
container class, or rejecting a mathematically elegant alternative. Current
success also does not prove that the encoding is optimal. The small `True`
invariant bridge is visible effort that a future consumer can assess against
the cost of adding another facade.

Under #235, use this archive as an onboarding example: show the direct and
shared claims beside one another, explain why reverse append is `y ++ x`, and
make the empty-decoder normalization lemma discoverable. Preserve both full
sequence and summary observations. A law-only facade should be considered when
another consumer repeats this boilerplate; it should derive from the same
`Valid` and batch laws and preserve a direct path to the general interface.
These trials alone do not justify a substantial retrofit or a new
implementation issue.

The validation lesson is actionable now in this experiment's replay procedure:
select a supported project module identity and inspect its audit root count.
Do not change the integrated library's audit scope merely to include arbitrary
archived experiments. A future reusable experiment runner would need its own
scope, negative audit test and tooling review; this bounded investigation uses
recorded commands rather than changing build policy.

Near-term adoption cost, mathematical generality and Lean encoding remain
separate assessments. An observed problem with a future cheaper author should
first produce a reproducible failed obligation and diagnosis. A newer author
succeeding on the unchanged task changes evidence about that configuration;
it does not by itself demonstrate a better design. Conversely, a better
specialization can help the same author without changing the mathematics.

## Repeatable reassessment owned by #235

1. Retain this revision, protocol, attempts and checksums. At a relevant design,
   Lean/toolchain or author change, choose the affected unchanged task families
   first. At workstream planning checkpoints, also review promising alternative
   abstractions and consumers that this sample did not cover. No scheduled
   automation or language migration is implied.
2. Freeze candidate sources, task statements, allowed helpers, documentation,
   tool access, assistance rules and stopping budgets before new authors see
   the task. Exclude prior solution archives from a fresh trial's supplied
   context; record accidental exposure. If public source already contains the
   complete solution, retain that disclosure and choose an additional matched
   holdout when discovery is the question.
3. When authorized capability/cost configurations are available, run fresh
   authors in each configuration against the same frozen design and budget.
   Record provider/model revision, effort and context settings, token ceiling,
   actual usage and price where exposed. Use matched tasks and counterbalanced
   orders with replication; missing metadata stays missing. A lower monetary
   budget and lower capability are different experimental variables. Do not
   infer either from elapsed time alone.
4. Compare design revisions under fixed author and toolchain conditions where
   feasible, and compare author configurations on an unchanged design. Record
   first submitted checks, eventual completion, semantic mistakes, syntax and
   elaboration diagnostics, assistance, repairs and incomplete outcomes. Avoid
   pooling later practiced routes with fresh attempts. Preserve old failures.
5. A proposed replacement must list affected consumers, migration and
   refactoring work, helper dependencies and changed assumptions. Check recovery
   of the established DList clients and the reverse-list client under their
   original contracts, including order and invalid-cache cases. Recheck actual
   bounded-buffer or durable consumers if the change touches their shared laws;
   these sequence trials do not certify those consumers by analogy.
6. Assess mathematical expressiveness, Lean realization and observed author
   effort separately. Recommend documentation, inference, a checked
   specialization or a deeper redesign according to the diagnosed cause. Track
   substantial changes as separately scoped #235 children with independent
   review, rather than extending this completed trial indefinitely.


## Validation boundary

The final archived sources compile under Lean 4.35.0. Their explicit
package-root audit invocations include the local trial modules: A has 38
logical declarations and 28 named theorems; B has 25 and 20 respectively.
Both audit logs report only the three permitted foundational axioms. The
archive distinguishes unsuccessful attempts, insufficient-coverage audit runs,
a superseded harness and the accepted byte-identical replay copies. This fixes
the protocol's erroneous assumption that auditing any experimental path would
include that path's declarations.

Author statement reviews inspected universal domains, monoid assumptions,
right-multiplication order, reverse representation semantics, cache hypotheses
and the connection from positive cases to the route's theorem. Coordinator
source review confirmed that the direct routes use native induction and the
shared routes actually apply the named library laws. No integrated Lean module,
public interface, toolchain or dependency was changed. The archive needs its
own checks; the integrated library's normal build does not certify its files.
