# FDSA-002 — Sorting

Current continuation, checkpoint 0084: insertion/top-down, quicksort and
natural-run values have focused checks. Top-down comparison execution, its
all-length/power-of-two/real-log bounds and connected cases passed focused
build and statement inspection at 7fb7c3e. All full chapter gates and remaining
112-obligation coverage are still pending; no chapter acceptance is claimed.

State: active after accepted Chapter 1 at 07e480f. Triage: in-progress. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 13.
Depends on: FDSA-001.

## Scope

Cover every mathematical construction, theorem and exercise in this source unit,
with exact scope and reusable existing declarations inventoried before implementation.
Preserve the book's assumptions and cost model; harmonize with conaled interfaces.

Exact chapter requirements were recorded before activation in
`reviews/chapter02-requirements.md`, SHA-256
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`.
They bind the full107-row source/reuse maps and retain separate probability
and cost-model obligations. The chapter remains queued.

## Completion gates

- [x] Item-by-item source coverage and reuse/gap map completed.
- [ ] Definitions and proofs implemented without admissions or additional axioms.
- [ ] Checked uses and statement review retained.
- [ ] Applicable immutable-candidate build and exhaustive proof audit passed.
- [ ] Independent Standards and Spec reviews have no unresolved findings.
- [ ] Accepted candidate verified and recovery checkpoint saved/uploaded.

## Primary source links

- https://isa-afp.org/entries/Efficient-Mergesort.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Sorting.html

## Prepared scope and dependencies

All 107 obligations C02-001 through C02-107 are retained in
`research/chapter02-obligations.md` and mapped individually in
`research/chapter02-reuse-plan.md`. This preparation does not activate the
chapter before FDSA-001 acceptance.

The source proof plan is `research/mergesort-proof-plan.md`. It preserves the
book's floor-left split and comparison-only metric. The standard Lean sorter
splits ceil-left; on `[0,1,2]`, its logical comparison count is 3 while the
book's is 2. Value correctness alone does not identify those recurrences.

Provisional shared prerequisites are tracked independently:

- FDSA-X002: measured insertion and stable/rank clients, with focused builds
  passed and full gates pending.
- FDSA-XB01: shared list calls for algorithms that explicitly charge those
  traversals. Chapter2's merge comparison bound does not charge them.
- FDSA-APP-A/C: standard list and typed notation correspondences.

Implementation ownership and any parallel task graph will be established at
chapter activation using the applicable conaled workflow. The chapter must
cover the exact source algorithms, all displayed claims and all seven
exercises; accepted shared results may be reused only with their explicit
source/domain/cost bridges. No formalization or acceptance is claimed for
this queued chapter by these preparation records.

C02-024 coverage correction: the average-input and randomized-pivot claims in
§2.3 remain separate mathematical obligations, even though their source proofs
are external to the book. The earlier inventory's expository exclusion has
been corrected in both the source inventory and reuse plan. See
`research/quicksort-average-proof-plan.md`
for precise distinct-key distributions, measured correspondence obligations,
independent rational cases, harmonic API reuse and the necessary append and
pivot-selection qualifications. This is preparation, not a verified theorem.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter02-obligations.md`,
SHA-256 `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter02-obligations.md`,
SHA-256 `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.

The frozen Chapter 2 requirements remain unchanged at SHA-256
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`.
Read the reconciliation's explicit C02-088/108–112 clarification
with them; the comparison counters are unchanged, while builder
construction/materialization have a separate declared observation.

The later shared closure-model preflight is recorded in
`research/difference-list-cost-preflight.md` and FDSA-XD01. It makes the
representation-size qualification explicit: unfolded invocation weight and
distinct shared closure-creation events differ. The positive source asc bound
must be tied to its actual singleton-seeded push recurrence; arbitrary D-law
functions and shared self-composition do not acquire an output-length bound.
The frozen chapter requirements and comparison counters remain unchanged.

Later preparation: `research/quicksort-conditional-mean-preflight.md`
connects the proposed actual source recurrence, on-head-event child inputs,
the saved conditional marginal laws, integrability and rank reindexing.
It uses no joint-independence assumption and does not activate the chapter.
The corrected AFP/Isabelle attribution for the builder source is retained in
`reviews/difference-list-provenance-correction.md`; read that erratum with
the historical closure preflight.

`research/natural-runs-proof-plan.md` records the literal mutual scanner,
raw-builder adapter, termination measure, ordinary correctness and exact
comparison-count targets. It also retains the tail-pass counterexample to
automatic exact-cost/stability transfer and the separate actual builder/work
correspondence. Its additional keyed natural-sort route is optional for the
selected Exercise 2.7 client; the frozen chapter scope is not expanded.

The separate check of the conditional-mean plan is retained in
`reviews/quicksort-conditional-mean-source-preflight.md`. It found no concrete
source/API mistake, but supplies no formal proof or acceptance result.

`research/random-pivot-api-preflight.md` independently prepares the actual
fresh occurrence-pivot PMF execution, exact two-filter source observation,
strict child lengths, support bound and justified real mean. Its direct
mean proof does not claim a full distribution identity with random input
order. All source cost, duplicate and payload assumptions remain explicit;
no implementation or chapter activation is supplied by this plan.

## Bounded mergesort readiness, 2026-11-02

Three complete source/API/mathematical notes have been read by the root
coordinator and their writers have stopped:
`research/mergesort-value-api-readiness.md`,
`research/mergesort-cost-readiness.md`, and
`research/mergesort-case-readiness.md`.
Exact file identities and the unchanged retained inputs are recorded in
`reviews/mergesort-readiness-identities.json`.

The floor-left plan is retained. Existing merge/sorting contracts supply
the value, sortedness, stability and uniqueness route; each-input sublist
facts still supply the missing merge converse. Generic comparator
compatibility proves sortedness, not stable ties. The source comparison
execution must bind actual returned child values, and the all-length
ceiling-log bound has an explicit real-log/BigO route with constant two
and threshold two. Per-pass comparison equality must not be transported
through a changed next-pass run order; the retained three-equal-singleton
case distinguishes total counts three and two.

This preparation preserves the original 107-row frozen snapshot together
with the current 112-row reconciliation. No sharper merge bound, exact
top-down worst-case formula, second cost model, new acceptance gate or
additional case campaign is required. C02-108's exact scan and C02-109–112's
separate actual operational bridges remain mandatory. Chapter 2 stays
queued behind accepted repaired Chapter 1 and the recorded minimal shared
foundation prefix. Checkpoint 0039 is saved successfully; it supplies no
compilation, final review or acceptance credit.

## Ordered insertion readiness — 2026-11-03

FDSA-XI01's three complete stopped source/API/case reports and root assessment
are retained at `research/ordered-insertion-{source,api,case}-preflight.md` and
`reviews/ordered-insertion-preflight-assessment.md`. They preserve C02-009 and
C02-094–098 and all 112 current obligations. The missing sortedness iff,
all-members cons value equation and distinct filter equalities are thin
observations over existing insertion. Existing sublist/permutation/filter
length laws supply the proof routes; positive filtering needs sorted input
and transitivity, whereas negative filtering needs neither. Existing stable
sorting and X002 clients remain reusable, without treating their final result
as coverage of every displayed helper or transporting cost through a value
equality. The bounded later-consumer check does not justify a separate shared
unit; implementation stays in this chapter after activation. The exact initial
prefix remains c80eec92f5458eccfd1c34c8314d666c2a1e3847 after repaired C1 acceptance.

## Accumulator quicksort readiness — 2026-11-03

The existing C02-101 exercise now has three complete stopped report-only notes:
research/quicksort-accumulator-source-readiness.md (18,282 bytes/294 lines,
SHA-256ce8c019bfe437bbdb71e5863119469a67c0f0d1a7961a3c0f879566731025eba),
research/quicksort-accumulator-api-readiness.md (21,912/341,
SHA-256aeec34427e96f45ede40f9631a201a443f1eded796abf49a04fd861d17f4572f),
and research/quicksort-accumulator-case-readiness.md (19,851/363,
SHA-2566251ba2623d7988496be3e54dbdea8085f878810db276f7fec673429319f09f0).
Root read the complete final reports, including every case-report delta.
The bounded disposition is reviews/quicksort-accumulator-readiness-assessment.md;
exact report/input/source states are in the separate readiness-identities.json.

The proposed nested worker uses strict-left and nonstrict-right tail filters,
first-input-length termination and an induction quantified over every suffix.
The left IH consumes the actual right-result/pivot suffix. Independent empty,
singleton, all-equal and mixed cases distinguish incorrect nesting and an
empty-suffix-only specification; the total argument-length measure can stay8.
The actual body must satisfy the no-append requirement. This source exercise
provides no separate cost formula or full tail-recursion/constant-stack claim.
No extra framework or theorem quota is selected. Ordinary quicksort remains
an earlier source-definition prerequisite; all cost/probability work is retained.

All112 current rows, the frozen107-row snapshot and the exact initial
c80eec92f5458eccfd1c34c8314d666c2a1e3847 prefix remain unchanged. Chapter2
stays queued behind repaired C1 acceptance. Checkpoint0064 will preserve the
readiness packet and prior receipt/recovery records; no Lean source, build,
review approval, chapter transition or acceptance occurred.

The complete readiness packet is now saved in checkpoint0064, with all645
payload hashes and53 unchanged source refs inspected. The source bundle is
unchanged from0063. This preservation accepts no C02 row, creates no source
unit, and does not activate Chapter2; all original prerequisites remain.

## Bounded three-way quicksort preparation assigned — 2026-11-03

C02-102 remains an existing queued obligation. Three separate report-only
investigations now check the exact Exercise2.3 source recurrence, reuse of the
existing partition content/order facts, tail-length termination, dependency
placement and discriminating duplicate/pivot cases. No implementation or
additional shared unit is selected. Current112 rows, original107-row snapshot,
frozen scope and exact initial foundation prefix are unchanged. No other new
Chapter2 preparation is selected absent a concrete issue. C1 remains active.

## Three-way quicksort readiness complete — 2026-11-03

The three stopped reports are research/quicksort-three-way-{source,api,case}-
readiness.md, at324/476/350 lines. Root read them completely, including all
case-report final deltas, and recorded the exact identities and preserved
inputs in reviews/quicksort-three-way-readiness-identities.json. The separate
root assessment records the bounded disposition. All112/107 rows, the initial
prefix and every original requirement remain unchanged.

The actual printed sorter partitions the tail, emits one pivot and its full
equal block, and recurses only on strict sides. Tail-filter bounds prove the
required decrease without pivot membership in the tail. Existing XQ01 already
drafts the independent partition fragment; no additional extraction is needed.
Standard permutation/multiset and pairwise interfaces supply the correctness
route. The five independent cases distinguish multiplicity/order failures and
source recursion that cannot be certified by final values alone. Printed
three-filter, two-partition pure and one-pass measured executions retain their
separate cost boundaries. No new cost, keyed stability or stack target is added.

Checkpoint0065 will preserve the completed packet and prior post-archive
records. This is source preparation only, with no implementation, build,
review approval or chapter activation. C1 remains the active prerequisite;
no further C2 readiness packet is selected absent a concrete issue.

## Activation — 3 November 2026

Chapter 1 acceptance and checkpoint0077 satisfy the sequential prerequisite.
The exact initial prefix is merged into immutable candidate0c93725, with two
focused compiler findings pending. All112 obligations remain. See
reviews/chapter02-active-scope.md and reviews/shared-foundations-round1.md for
current ownership, frozen scope and validation; earlier queued text is history.

## Current development continuation — checkpoint0083

The full foundation check for exact f17cc6b is newly recorded and has no terminal
result at capture. Quicksort's two value modules and type inspection passed at
840252e. The ordinary-merge prerequisite's three focused targets/type inspection
passed at72a0951; its independent reviews/full integrated gate remain pending.
Natural-run one-run laws and connected cases are authored, still uncompiled;
bottom-up values remain uncompiled. Exercise2.5 alternating splitting/sorting
is an uncompiled committed draft43242f4 retaining the checked insertion prefix.
All112 obligations and all cost/probability, stability, operational and exercise
claims remain mandatory. No new component or Chapter2 acceptance is claimed.

## Checkpoint0085 continuation — 4 November 2026

Bottom-up and alternating value modules passed all four focused targets at
98696d86162bd93c1cba46719eeb65bf6cabe65a;126 public declaration inspections and
source/type readback passed. All actual earlier failures are retained. Top-down
comparison costs and natural values remain focused checked. The cumulative
compiler checkout is8ec1d9cb, whose first six-target measured-cost build closed
exit1, clean unchanged HEAD. Quicksort's resource library passed; example name,
natural simp and reserved list-builder binder diagnostics remain for correction.
Random-pivot source is pending after a complete pre-code handoff and durability
checkpoint. Bottom-up cost source remains pending. All112 obligations, full
chapter validation, independent final reviews and acceptance remain mandatory.
Foundation full attempt2-recovered has no secured terminal result at capture.

## Checkpoint0086 development evidence

This section records the latest development state. Accepted main remains exact
R07e480f; isolated foundation f17cc6b is unchanged, with no secured terminal
result at current inspection. Its actual live host process belongs to root;
saved process/session records do not establish post-recovery liveness. The
first-acceptance sequence and independent source assessments above remain.

Current clean compiler checkout is1ffb61fceaf7c893e25a35339f6e1fce8531021d,
on cumulative work/fdsa-ch02-development. Deterministic quicksort cost and
natural comparison pairs passed their individual targets in recorded attempt2;
list-builder core passed attempt3 and its corrected examples passed the next
list-builder/partition attempt. Every enclosing failed aggregate retains actual
exit1, complete closed logs and native records. No false aggregate success is
reported. Explicit universe/argument inspection of all174 public declarations
from those six modules passed at1ffb61fc, exit0,45.323s. See the focused summary
and type records; original authors are doing read-only full type/source readback.

The two list builders retain exact costs n(n+1)/2+n+2 and2n+3, with identical
values. The arbitrary-comparator scan retains exact n-1 comparisons (natural
subtraction at zero), separate from builder/scanner operational work. QuickSort
retains actual T/A observations and bounds, suffix equality and partitionMass
identity; expectation claims remain pending. These are focused development
results, not Chapter2 acceptance.

Bottom-up comparison draft7f17c441 has an actual failed first central build.
All eight diagnostics are recorded; proof-only correction1e4b34bbb12d83a48678132c79243eefc5a9f4f2
is held in the author tree and awaits its next check. Definitions/contracts/
cases are unchanged, including the independent3-versus2 complete-count witness.
The complete105-public-declaration source inventory is preserved.

XQ01 exactde54102 was merged into development with two documented append-only
import/map resolutions. Its shared core and existing Selection.ThreeWay,
Selection.Consumers and RankSelection targets passed. The core's three unused
simp arguments were removed inb3bdc12b. A measured value proof then needed one
pure projection reduction; successor0612e80a0c297a38fa1add6e837dc7781e1bbd9c
on work/fdsa-partition-proof-fixes contains only that additional proof repair
and is uncompiled at capture. Both failed attempts and stable findings
XQ-ELAB-001/002 remain. Final full-scope independent reviews/gates are pending.

New source-only conaled-ch02-three-way, work/fdsa-ch02-three-way, is clean at
a338b540ada6d1aa85e5c7c3adfe1edd4cea4a8c, parentexactde54102. Its two uncompiled
files implement literal three-filter sorting, full occurrence/order correctness,
all-equal/mixed/pivot-absent cases and explicit altered-root boundaries.

Random-pivot author tree is clean at080e2f63ad4ef56dd18a5889d14dcf8c9100f049,
parent6122dd02. Its two uncompiled files implement an actual recursive PMF with
fresh uniform occurrence indices, actual filters/recursive results/append,
support and pathwise value/cost laws, finite Nat cost support, equal-key family
and fixed small mass cases. The full62-public/eight-private static assessment
is retained. Finite expectation, actual bind-mean bridge, rank law, recurrence,
harmonic formula, asymptotics and separate uniform-input analysis remain
mandatory. This source is not a completed probability formalization.

All source/ref/control authors are held for capture; read-only statement
assessments do not mutate candidate inputs. Ten worktrees and all current refs
are included with the same standalone recovery rules. Next merge the exact held
bottom-up/partition corrections and the two new algorithm drafts into the
exclusive compiler checkout, record exact resolutions/identities, and continue
focused validation. XD01 and XU01→XU02→XU03 retain their required full acceptance
sequence after the first foundation gate; no unrelated prefix is substituted.

## Recovery continuation for checkpoint 0089

Complete112-row source reconciliation is saved, including existing rank clients and all15 public-import gaps. Natural composition all105 explicit declarations and complete readback now pass. Generic ordinary uniqueness3b727e8 (nine declarations) and random mean7b1851c (32 declarations) are complete uncompiled source drafts, with full author/root source assessments. Natural operations remain in implementation after checked0ec9954 alignment. No obligation is accepted by these records.

## Checkpoint 0090 continuation — 4 November 2026

No acceptance or ticket closure. Uniqueness now has individual two-target passes and all9 explicit type/source assessments, while the unrelated aggregate failure remains. Mean proof repairs through1f315fdb and whole-order support repairs throughfbc9a32 preserve every public contract. XU02 core compiled; its complete triple/types remain pending. Natural operations e1f3b5c has106 fully source-assessed claims; actual quicksort transport5a3af21 has11. Their first check joins the mean and XU02 targets at immutable centrale4965499, live at capture. Harmonic/rank plans are approved; the numerical two-file draft is deliberately untracked/uncompiled and preserved, rank source has not begun. Uniform-input plan awaits root assessment. XU03 remains source-only at6f76a4d. All112 obligations, original dependency order, full audits, both axes and immediate verification remain mandatory. CURRENT.md and exact provenance control continuation.


## Checkpoint0091 continuation — 4 November 2026

No acceptance or ticket closure. Closed attempt4 at e496 exited1, preserving
actual mean/transport individual passes and XU02/natural failures. Full/native
logs are secured. Proof successorsbdac970 andc7aa6fa retain every contract/case.
Clean centralc0440a99 now runs the recorded12-target check including first
Tail6f76a4d, numerical012ff45 and rankc19a85f compilation. Numerical23public+
1private and rank30public+7private complete source assessments have zero
findings. Uniform-input has a coherent1116-line two-file UNTRACKED draft at
204dba; written125-claim assessment/commit/root review and compilation remain.
The actual random-growth bridge and final112-row/public-import documentation
preparation remain unfinished. No prepared inspection program or partial log
is success. Exact foundation first acceptance, shared sequence, all112 Chapter2
obligations, full audits, both independent axes and immediate verification
remain. Read CURRENT.md and actual provenance; then continue the complete book.
