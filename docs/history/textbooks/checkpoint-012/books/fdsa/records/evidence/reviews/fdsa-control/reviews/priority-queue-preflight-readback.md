# Shared priority-queue preparation: root readback

Status: bounded read-only preparation. No scope is frozen, no new Lean source
is authorized by this note, and no chapter or shared unit is activated or
accepted. Three disjoint source/API/case preflights are in progress. The sole
compiler/checker remains Chapter 1 session 83124 on candidate 07e480f.

## Primary source and current project reading

Root read the complete Chapter 14 text (printed pp.179–182), the complete
`Priority_Queue_Specs.thy` and `Heaps.thy`, and the existing Chapter 14 inventory.
The exact inspected source identities are:

| Local primary reading | Bytes / lines | SHA-256 |
| --- | --- | --- |
| chapter14.txt | 4,808 / 102 | `b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a` |
| Priority_Queue_Specs.thy | 1,654 / 36 | `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a` |
| Heaps.thy | 2,946 / 93 | `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe` |

The source figure has seven base laws and two merge laws. The pinned companion
adds an `is_empty` operation/law; this is an explicit extension, not a missing
figure line. Minimum and deletion source laws retain nonempty valid inputs.
The observation is a multiset, so one minimum occurrence is removed and
duplicates remain significant. General item/priority pairs specialize to the
source element-only model; they do not imply canonical tied payload selection.

Root also read the complete actual project modules at the clean 07e480f repair
branch, including the existing real Huffman client rather than inferring its
role from a filename:

| Module | SHA-256 |
| --- | --- |
| Search.PriorityInterface | `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6` |
| Search.ExactPriority | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| Search.LeftistQueue | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| Huffman.Priority | `c06cfbe28f488d5aed5ddc2cc2f8002244eb22818c875b3f752dfccc393048e1` |
| Huffman.SourcePriority | `de80cc229d7854a18efcf6901cc166a41a258d7371ddfef54ac603884eb9af4c` |

Existing `Operations` separates executable state/add/remove from observations
and evidence. `ExactLaws.add_exact` and `remove_none` are unconditional over raw
states; `add_valid` and `remove_spec` require the actual invariant. Preserve
that stronger existing interface: its source-law adapter is one-way, not an
equivalence with all source ADTs. The weaker keyed interface deliberately permits
replacement and cannot establish multiset insertion.

The real leftist implementation has separate Ranked, Heap and occurrence
observations. `combineQ_entries` is unconditional, while `combineQ_valid` uses
the two actual valid inputs. `deleteQ` returns the root pair and an actual merge
of its children. Projecting it gives a semantic peek but does not justify
constant-time execution; a direct root match needs its own agreement. The
existing `nullQ` is already a direct structural emptiness test. `exactList`
appends inserted occurrences and sorts on removal, so it does not solve the
source constant-time sorted-list exercise.

## Minimum and observation boundary inspected

Root inspected the pinned definitions of `IsLeast` (LE only), `IsLeast.unique`
(PartialOrder), Finset minimum/minimum-with-nonempty-proof and their generated
`to_dual` lemmas (LinearOrder), plus Multiset coercion, addition, erase-cons and
sub-singleton declarations. Membership and lower-bound facts do not require
decidable equality of payloads. Entry-multiset decomposition is the capability-
minimal deletion fact; priority erasure/subtraction can add its local decision
requirement. Antisymmetry is needed when deriving equal selected priority values
from two least-element specifications, but it does not determine a tied payload.

The proposed scope is still under assessment: a small observation adapter and
merge compatibility for the existing carrier/API, consumed by actual clients
and existing realizations. There is no decision to add a parallel queue hierarchy,
silently depend on unaccepted XA01, or replace the source algorithms with an
existing implementation of a different recurrence.

All concrete heap algorithms, sorted-list constant-time exercise, plain naive
merge, heap enumeration/costs, Cartesian-tree construction/uniqueness and all
later chapter obligations remain queued. Source findings and final bounded
report identities will be appended after every complete report has been read.

## Complete stopped preflight readback

All three preparation authors stopped their report writes. Root then read all
416 source-report lines, all 257 API-report lines and all 424 case-report lines
in complete bounded sections. Their final ordinary byte identities are:

| Report in `../research/` | Bytes / lines | SHA-256 |
| --- | --- | --- |
| priority-queue-source-preflight.md | 29,031 / 416 | `79fff00277221c6c5279841a5eb88517f57a2e52cf8b0f1ac393492a87bdec79` |
| priority-queue-api-preflight.md | 31,737 / 257 | `12927ddbc7198cd6d9e8f23587671fe42134373b699d8a99282930108a36b2f8` |
| priority-queue-case-preflight.md | 26,693 / 424 | `4b642e8382a65e4369bb9e84e0a141fa8ec29d2104651b4bc51c478c15445278` |

No concrete mathematical or inspected-API mismatch was found. In particular,
the exact raw-state law strength, one-way source contract mapping, seven/eight
base-law counts, optional empty behavior and both valid merge premises remain
consistent. The actual leftist client shapes independently give merged entries
[1,3,1,2], inserted entries [1,1,2,2,3] and residual [1,2,2,3]. The generic
client must carry actual intermediate validity, not just recalculate a target
multiset. The source's sorted-list constant-time exercise and naive plain-node
merge are not supplied by the existing list/leftist realizations.

The chosen central observed-removal proposal is equality of
Option(priority, residual priority multiset) across valid queues with equal
initial priority multisets and explicit antisymmetry. Both payload and carrier
universes remain independent. The inspected `Multiset.cons_inj_right` provides
the cancellation without any equality decision. The swapped tied Bool payload
case demonstrates both this positive priority observation and the false
stronger selected-item/residual-entry claim. A local indiscrete Bool priority
preorder isolates the need for antisymmetry itself.

The preparation also identified a useful positive finite-model fact: every
finite entry multiset has a valid representative from actual add and empty.
Priority-only realizability takes an explicit payload value; Unit supplies it,
while Empty payloads with Nat priorities cannot realize the singleton {1}.
This adds no surjectivity assumption, default or new representation. The
source report's zero-helper tariff in the later leftist analysis remains
separate from existing positive local-access models; no resource conclusion
belongs to this proposed observation unit.

## Bounded design selected for a requirements draft

Root requested a mutable requirements draft for proposed FDSA-XH01 on original
base `07e480f6ec9958d4975bb90151005b84f2907614`, with exactly six prospective
paths: new `Applications/Search/PriorityMultiset.lean`,
`Applications/Search/PriorityMerge.lean`, `Examples/PriorityModels.lean` and
`docs/research/fdsa-priority-queues.md`, one added example import in the public
root, and an append-only reconstruction-map section. No existing queue or
consumer source is to change and no unaccepted shared branch is required.

The prospective operations are ordinary views of existing Operations and a
supplied merge. Evidence remains separate. At most a two-field compatible-merge
evidence record is justified by two concrete realizations, actual sequential
clients and observational algebra; it adds no carrier, queue hierarchy or
executor. Actual leftist combineQ and list append supply the witnesses. A
direct leftist root peek is a small missing access operation with a raw value
correspondence; it receives no cost claim. The source finite-support minimum
uses the existing LinearOrder/min' boundary, while the general observation
theorems retain weaker assumptions.

The complete frozen scope, clean branch/start identity and successful pre-code
checkpoint 0050 are still required before any source authoring is released.
The source author is preparing only the mutable draft; root will read and
finalize it. These readbacks are implementation preparation, not an independent
final axis or evidence of elaboration, audit success or chapter completion.

## Scope frozen after complete draft readback

Root read the full stopped 538-line requirements draft and retained its original
SHA-256 `ded238065a0e9e02202c162111e60d4cd262dae25a9bbd678fa84c079446123d`.
The mathematical scope and examples are unchanged. Final names, the two-field
merge evidence packaging and disjoint ownership were resolved in the new frozen
requirements, 34,360 bytes / 581 lines, SHA-256
`ea6e81e44065a8c0d7a719374cf377c1692b81672a96af71b7c92aeaf348d6ca`.
The full assessment is `priority-queue-requirements-assessment.md`.

A pinned-shell read-only baseline check confirmed clean 07e480f and absence
of all four new paths. All seven relevant existing queue/Huffman source files
match their original committed blobs, as do the original root and source map.
The new isolated branch/start record and successful checkpoint 0050 still
precede source release. Authors may read the final scope and plan only; no
source has been released by this readback or the requirements assessment.
