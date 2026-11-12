# Six-author dependent-conversion trial, 2026-11-12

All six fresh author sessions submitted checked proofs for the released initial,
scale, repair and held-out tasks and met the frozen negative rubric. All six
exact-source coordinator replays passed. All twelve production audit contexts passed. Independent report
review and publication are separate gates, recorded with the accepted revision
on [#423](https://github.com/VladimirMarko/conaled/issues/423). This is a bounded authoring observation; it does not establish a general
productivity advantage.

The source was `1d9d4357f93b91a0f01ddef3103a7e4b72e5dc0e`; the accepted execution
package was `31c08c126952242843af1ac74411efb396743a0b`. This report starts from
integration `59be9f3c25421ddbe07cca0cb933904a3fd10881` and incorporates the
separately reviewed Wasm naming correction at `7084050efc13b7b1ce131ea4bf0a23845b777b37`. The
[protocol](../../../docs/research/dependent-conversion-authoring-protocol.md),
[freeze](../execution/freeze.json), [phase rules](../execution/phase-policy.json)
and author instructions are unchanged. Historical preparation receipts retain
their original pending states and candidate labels. Current acceptance must be
read from this report's gates and the later exact-candidate review receipts.

## Cohort and exposure

The frozen assignment and sequential order were service, direct, service,
direct, direct, service. Three fresh sessions used each route. Root spawned each
as a direct child without conversation history or model overrides. Actual
bootstrap metadata was checked before initial release: gpt-6-astra, medium,
openai, CLI 0.161.0. Exact serving revision is unavailable. Bootstrap reports
identified generic tools, repository instructions and environment, without prior
mathematical task material. Session identifiers and selected metadata are in
[cohort.json](cohort.json) and the per-author summaries.

Each author received only the listed public library and current task definitions,
its own work and a private warm output root. The direct route exposed five
project library modules; service exposed ten. Later tasks stayed sealed until
the previous submission and receipts were archived. Repair changed the assigned
base argument and required a new index plus rejection of the old index. The
coordinator preserved the old module and switched to a fresh output root,
excluding old Repair and author helper artifacts before compiling the change.
Inline helper source was recompiled where reused.

This was policy isolation on an unrestricted host, not an OS sandbox. Authors
reported no mathematical assistance, accidental exposure or interruption.
Coordinator instructions and observations support staged exposure but cannot
prove absence of unobserved reads, suspension or throttling. Only environment
and protocol clarification was supplied. The uniform explicit-output rule was
that Lean's root must contain the recorder snapshot; ordinary no-output checks
could use the public root. The failed post-completion notification to slot 1 is
retained; it had no helpers affected by that clarification. A failed
post-completion notification to slot 3 is also retained. No author was replaced.

## Outcomes by author and dimension

“Checked” means the exact submitted task theorem compiled and its native source
policy/import check passed. It does not mean its final exhaustive audit passed.
Scale dimensions are separate factorwise families: composition lengths 1, 4, 8;
context base widths 2, 4, 8; substitution counts 1, 2, 4. No combined scale trend
is inferred. Initial and held-out tasks preserve both explicit result indices;
scale preserves its stated index equation; changed repair preserves its new
index and rejects the old one.

| Slot / route | Initial | Composition | Context | Substitution | Both repair stages | Negative IndexTask | Head rejection | Held-out |
|---|---|---|---|---|---|---|---|---|
| [1 service](authors/slot-1/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Optional HeadTask checked | Checked |
| [2 direct](authors/slot-2/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Reasoned rejection | Checked |
| [3 service](authors/slot-3/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Optional HeadTask checked | Checked |
| [4 direct](authors/slot-4/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Reasoned rejection | Checked |
| [5 direct](authors/slot-5/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Reasoned rejection | Checked |
| [6 service](authors/slot-6/summary.json) | Checked | Checked | Checked | Checked | Checked | Checked | Optional HeadTask checked | Checked |

The common rubric required an explicit, evidenced rejection of changed-head
FuncEq and a checked IndexTask. Slots 2, 4 and 5 supplied rejection prose and
limited same-type/distinct-syntax diagnostics, not a proof of FuncEq
inequivalence. Their diagnostics alone do not establish that inequivalence.
Slots 1, 3 and 6 additionally proved HeadTask. None reported uncertainty as a
successful rejection. The checked separating interpretation was an upfront
fixture admission obligation and was withheld from all authors.

All final authored Lean files are readable under `authors/slot-N/`. There are
40 selected files. Slot 5's earlier combined ScaleDraft.lean is additionally
retained as historical, unselected work; its successful compile remains an
attempt. Its separately selected Composition, Context and Substitution files
carry per-dimension evidence. Slots 1, 2, 4 and 6 share one scale source and
its successful compile/policy pair across the three dimensions. A shared command
is one invocation, not three. Slot 3 has separate sources and checks.

## Failures, helpers and maintenance

| Slot | Recorded author command failures | Repair and helper observation |
|---|---:|---|
| 1 | 1 scale compile | Finite-list simplification repaired. No authored general helpers. |
| 2 | 1 initial compile | Explicit context annotation repaired elaboration. Seven general helpers in ScaleProof are repeated byte-for-byte in HeldOutProof. |
| 3 | 4 compiles | Initial converter namespace-resolution failure, then one finite-list simplification failure in each scale dimension. No general helpers. |
| 4 | 1 initial compile | Explicit context annotation repaired elaboration. Seven general scale helpers; repair and held-out do not import or reuse their artifacts. |
| 5 | 1 initial compile | Explicit context annotation repaired elaboration. Six shared helpers copied into each scale source and held-out; expand_equal copied into both repair sources. Unchanged helper source was recompiled inline. |
| 6 | 1 scale compile | Finite-list simplification repaired. No general helpers. |

Every recorded failure, original attempt source and output is retained through
[evidence-map.json](evidence-map.json). Slot 1 also had a missing-context-path
error before Lean started, retained as text, and an unsuccessful coordinator
supplied-definition compile whose recorder snapshot fell outside the chosen
root. These are distinct setup errors. Slot 2's first coordinator replay failed
because an incomplete private Examples output root shadowed later roots;
replay-02 corrected the output setup without changing author bytes. None of
these is silently folded into mathematical noncompletion or erased by success.
No started-only recorder attempts remain in the frozen submissions. No extension
or author replacement was used.

The general helper names and final file sizes are recorded per author. Negative
same-type/distinct-syntax diagnostics are separate from reusable general helpers.
Service authors reused the supplied conversion/normal-form interface; that
library's implementation and proof obligations belong in upfront cost, not a
claim of zero work. Direct authors' helpers are author work even when copied
unchanged into a later file. These small held-out observations do not measure
long-term maintenance.

## Validation gates

All six selected-source replays and native source-policy checks passed. Frozen
submission hashes, fresh output hashes, commands and dependency correspondence
are retained. Original phase compilation against the restricted repair baseline
is distinct from later replay against the full Repair fixture, whose baseline
declarations are unchanged.

[All twelve production audit contexts passed](audit-completion.json). Each used the complete accepted-source
mirror, all ten fixture/reference modules and that slot's selected submission;
private references are coordinator-only. Slot 2 needs two import-order contexts
to expose both copies of its seven repeated helper names as original owners.
Slot 5 needs six such contexts for its repeated helpers, including both repair
sources. A single combined-import success does not establish origin coverage of
all copies. Slot 4's additional origin probe found no shared-helper conflict.
The drivers, origin observations, inventories and queue commands are retained.
Overlapping module/declaration counts must not be summed as independent results.

| Gate | Current state |
|---|---|
| Accepted source and execution package | Passed before task release; exact identities retained |
| Six author phase checks and frozen submissions | Complete |
| Six exact-source coordinator replays | Passed |
| Full production audits for slots 1–6, including all helper-owner contexts | Passed; twelve contexts |
| Independent Standards and Spec review of this report/evidence | Required before publication; exact-candidate outcome recorded on #423 |
| Root acceptance and publication | Exact accepted revision recorded on #423 |

The coordinator who assembled this report is ineligible to review its own work.
Root owns serialized audit execution, independent reviewers and final acceptance.
No trial-effectiveness conclusion or adoption recommendation follows while these
gates remain open. Even after they pass, six sessions on one configuration do
not establish a general route advantage or causal scaling law.

See [costs.md](costs.md) for incremental and upfront costs, and
[evidence.md](evidence.md) for receipt reconstruction and replay boundaries.

The original queued processes disappeared without completion evidence; the cause
is unknown. Their pending records were archived before root resumed the unexecuted
jobs. The completed first-author audit was not repeated. The original and later
receipts coexist under distinct evidence-map keys. All retained source, artifact
and driver identity checks passed. An unrelated Wasm naming-policy failure in
the shared controller is preserved separately and did not fail an author audit.
