# Bounded source-scope reconciliation

Recorded 2026-11-02. **Source preparation only; no chapter acceptance or
implementation result.** This record applies the non-Chapter1 findings from
`coverage-scope-audit.md` to the queued obligation inventories.

Audit SHA-256:
`2ee191f35850404e0236dfe326581839d67396e52f37c05970d7a0553a12a69b`.
The audit itself remains unchanged as the record of what was found before
these repairs.

## Preservation and edit boundary

Before any inventory edit, the eleven affected files were copied byte-for-byte
to `../reviews/source-inventories-before-scope-repair/`, using their original
filenames. Every copied file was verified against the original SHA-256 before
editing. That directory's `manifest.json` records the old paths, byte counts,
digests, audit digest and frozen Chapter2 requirements digest. Its SHA-256 is
`a62faf9db1ec0493be7681408438937ae3802a7de48c15fac8456bf1a8a3a0a7`.

**Chapter1 was not edited.** CSA-01 belongs to the coordinator's separately
frozen cost-model addendum and retained review. This reconciliation does not
supersede that repair, its requirements, or its candidate evidence.

All original obligation IDs are retained. New rows are appended only where
the source claim or its model bridge needed explicit decomposition. No Lean,
ticket, Git, build, acceptance or remote file was changed by this work. Every
affected chapter remains queued. Open conjectures remain unproved statements,
not new axioms or promised proofs.

## Changes and reasons

| Audit finding | Inventory changes | Mathematical reason and exact scope |
|---|---|---|
| CSW-01 | Chapter2 C02-088 is mandatory; C02-108–112 append five explicit subobligations. | Printed pp.21–22 assert linear best-case natural sorting and difference-list composition/materialization claims, and explain quadratic repeated ordinary-list append. Retain exact sorted-input behavior/comparisons, the append-cost sum, separate builder construction/application observations, the actual asc-builder representation bound, and linear scanner work in that named model. The source comparison counters are unchanged. See the frozen-requirements clarification below. |
| CSA-02 | Chapter3 C03-047 now requires a measured linear bound for actual `select0`. | Exercise3.1 p.33's pedagogical proof waiver does not waive the user's formal scope. C03-051 at k=0 is reusable only with an actual implementation/cost bridge. Tail recursion, one pass and the nonempty-domain value theorem remain required. |
| CSM-01 | Chapter3 C03-052 retains its exact sensitivity theorem; C03-081–083 separately append a coordinate-query model, indistinguishability argument and n-query lower-bound bridge. | The displayed Exercise3.4 statement was not omitted. The new, separately labelled bridge gives a precise bounded computation meaning to p.32's algorithmic optimality assertion. It assumes deterministic adaptive access with values available through charged coordinate queries and correct selection on all inputs; a distinct-only alternative needs a fresh/distinct adversarial replacement. It is not a general hardware or randomized lower-bound project. |
| CSW-02 | Chapter4 C04-073 now mandates concrete local-work bounds. | §4.4.1 pp.57–58 already asserts constant smart-constructor overhead. Require actual cached-size access/construction bounds under the explicit tariff, and a generic local overhead plus supplied `f` cost. The existing invariant/fold correctness theorem alone does not prove these costs. |
| CSW-03 | Chapter5 C05-094 now mandates the finite expected-search calculation. | §5.5 p.67 compares the displayed three-key trees under equally likely keys. Fix the uniform distribution on `{3,6,9}`, count actual visited nonempty nodes/three-way comparisons, and prove costs `2,1,2` versus `1,2,3`, hence expectations `5/3<2`. No absent-key, infinite-uniform or different tariff generalization is inferred. |
| CSW-04 | Chapter8 C08-071 no longer makes instrumentation optional. | It is explicitly the prerequisite of the already-required C08-072/073 height and logarithmic operation bounds. The lack of a printed numerical time recurrence requires choosing and proving a tariff, not dropping the result. No new bound is invented by the wording change. |
| CSW-05 | Chapter9 C09-016 now requires a checked numerical enclosure. | Printed p.107's 1.44 coefficient is an approximation. Retain a rational enclosure or equivalent justified rounding and the exact coefficient in C09-015; neither equality to 1.44 nor an upper bound by 1.44 is substituted. |
| CSA-03; CSW-06 | Chapter10 C10-095/100 distinguish deterministic from expected work; C10-108 makes the weight-balanced instance mandatory; C10-112–118 append the treap extension. | Printed p.117 advertises weight-balanced trees; p.125 additionally names treaps. The already-pinned paper's Theorem9 p.7:24 fixes treap work as expectation over a shared random priority assignment. New rows retain actual join/set recurrences, all-priority semantic correctness, fixed-before-sampling inputs, shared distinct priorities, primitive-work correspondence and uniform expected work. They do not make treaps deterministic StronglyJoinable instances or import the paper's parallel-span theorem. |
| CSW-07 | Chapter21 C21-102 makes a precise `Prop` declaration mandatory; an appended section specifies the recovered primary conjecture model. | The book p.252 reports Dynamic Optimality as open. The existing Sleator–Tarjan PDF, Conjecture1 p.684, supplies arbitrary successful-access sequences, offline competitors, root-search cost `1+depth`, unit rotations anywhere between accesses, and a linear startup term. Uniform constants precede trees/sequences/traces. The conjecture is not proved, assumed or turned into an axiom. Variant/metric correspondence is kept separate. |
| CSW-08 | Chapter26 source-discrepancy item2 now explicitly refers to required C26-009. | The uniquely-decodable-code optimality bridge was already mandatory in C26-009. Removing the later conditional wording prevents that existing obligation being overlooked; no additional coding theory or source paper is added. |
| CSA-04 | Chapter27 C27-067/179 distinguish cache-bound/tree results from the asserted graph extension; C27-180–185 append the missing graph/cache obligations. | Printed p.340 affirmatively asserts cached fail-soft search over distributive-lattice game graphs. Require minimal primary source recovery, the independent graph value/termination domain, actual cached recurrence, cache invariant and exact squash/stronger relation, valid cache reuse and an implementation correspondence. The exact cited source contracts remain unrecovered; no invented cyclic algorithm, unqualified hash cache, universal speedup or `O(V+E)` claim substitutes for them. |
| CSW-09 | AppendixC's correction item3 and closing handoff now require both finite and infinite branches of the AC-078–080/084 correspondence. | Printed p.357 leaves A unrestricted; p.359's ordinary Isabelle set folds use the neutral element on an infinite indexing set. A standard finite fold plus this infinite branch remains mandatory; existing exact declarations may witness it without a new notation wrapper. |

The nine wording findings have all been reconciled. CSA-02/03/04 are retained
as explicit mathematical obligations rather than bibliography-only material.
CSM-01 remains visibly separate from the exercise's exact statement, and CSA-01
remains with the coordinator's active Chapter1 repair.

## Chapter2 frozen-requirements clarification

`../reviews/chapter02-requirements.md` was **not modified**. Its SHA-256 before
and after this reconciliation is
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`.
It freezes the earlier 107-row inventory at
`edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`;
the preserved snapshot reproduces those exact bytes.

The edit is an **explicit scope clarification of C02-088**, not a silent
replacement of those frozen requirements:

1. All original C02-001–107 statements remain required. The frozen natural-run
   section already requires sorted-input scan/merge behavior. C02-108 gives
   its exact source-recursion/count targets.
2. C02-109–112 separate the remaining mathematical claims printed in the same
   pp.21–22 passage into reviewable requirements. Their builder/append/local
   work metrics are declared separately from `Cruns`/`Cnmsort` and the merge
   comparison counters.
3. The frozen resource table forbids **unstated** DList materialization charges
   in the source comparison count. That boundary remains. The clarification
   does not change those counters or transfer machine-runtime claims through
   value equality; it explicitly requires a different named observation for
   the source's separate operational statements.
4. Arbitrary D-law builders retain their semantic worker theorems. Bounds for
   such arbitrary worker inputs need a supplied construction/cost contract.
   The positive runtime theorem is tied to actual asc-generated builders.
   Composing many empty identity builders shows why represented output length
   alone cannot bound every possible builder history in an application-count
   model; preserve a checked independence/boundary witness later.

Read this recorded clarification together with the frozen requirements when
preparing the next immutable Chapter2 candidate. No requirement was relaxed,
and no chapter was activated by this source-preparation work.

## Genuine remaining recovery and proof boundaries

- **Li et al. graph/cache extension:** the minimal primary construction,
  revision/license, graph progress domain, exact cache keys/entries, window
  premises and complete correctness relation still need recovery. C27-180–185
  deliberately keep these unresolved instead of guessing them. The displayed
  squash equation is the minimum value observation described by the book;
  any stronger recovered fail-soft/cache contract also remains required.
- **Treap and weight-balanced realizations:** the relevant paper/model/work
  statement is pinned and recovered. A concrete executable source or existing
  Lean realization and the full recurrence/rank/work correspondences remain
  implementation/proof work. No further paper algorithms or parallel bounds
  are made mandatory. Theorem12's reversed size condition and missing treap
  expectation qualifier are recorded; Theorem9 is the precise work target.
- **Dynamic Optimality:** the bounded primary-source inspection resolved the
  comparator and linear startup statement. It did not prove the conjecture or
  establish a metric/transition correspondence to the chapter's particular
  functional variant. Those model correspondences are separate from the
  unproved proposition; adjacent paper conjectures are not imported.
- **Conditional cost models and query lower bounds:** the clarified rows are
  mathematical proof obligations, not completed Lean facts. They require
  actual execution/observation links, not numerical functions merely named
  after the desired behavior. This work did not select a new global compiler,
  machine, or lazy-language semantics.
- **Earlier source limitations remain visible:** in particular, the direct
  Karp1994 paper access limitation already recorded in Chapter3 was not
  resolved by this task. Its retained independently provable probability
  targets were neither weakened nor reclassified.

No new downloads or broad external-source campaign occurred. The only
additional primary reading used the already-pinned Sleator–Tarjan PDF to
resolve the conjecture statement; the joinable-tree result had already been
checked during the audit.

## Mechanical consistency checks

- All eleven preserved snapshots still match their original manifest hashes.
- Every original table-row ID remains present; no duplicate table-row ID was
  introduced. Appended counts are 107→112 for Chapter2, 80→83 for Chapter3,
  111→118 for Chapter10 and 179→185 for Chapter27. The seven other affected
  inventories retain their row counts.
- The frozen Chapter2 requirements and the completed scope audit remained
  byte-for-byte unchanged.
- No Lean compilation or acceptance check was run. Hash/ID checks verify the
  reconciliation record, not the future mathematical proofs.

## Old and new inventory hashes

All filenames below are relative to `research/`. Their pre-edit copies are
under `reviews/source-inventories-before-scope-repair/` with the same basename.

| Inventory | Old SHA-256 | New SHA-256 |
|---|---|---|
| `chapter02-obligations.md` | `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `chapter03-obligations.md` | `f7508b53983b68f7c5b74cb295fe59886f5d975dc865ff7b128e150bea8006eb` | `eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed` |
| `chapter04-obligations.md` | `7f070734ebffcb26350514a2bfde9d30732236408922435d4b54029c3387e407` | `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4` |
| `chapter05-obligations.md` | `a80e32867234bf2bb2d291ee7bb249afc051dde128cb3c1f7879609567831a45` | `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad` |
| `chapter08-obligations.md` | `1c55482207ef854a43b8d54c1f7a128ad71f01ad5054f5a8415340ac772dd783` | `16e26a46452d06401e1f50317fb8d7e3ad4a341a2070870b07c7014f1b2e07e1` |
| `chapter09-obligations.md` | `daf503cbdbbd80320bbe4b6cfe2c73102f39dcf50ae49cbd544907eec95c689b` | `6ade1fd1a470c64d613212098e311d2e0189f62bd82045dbb2f8f4387f426285` |
| `chapter10-obligations.md` | `2bc962c3041e5e4d5ba15bdcf01d5b278ff91231fb83f347982a7ff585eac321` | `f3703190c2c5591a8b8685e88205652ca412e90fedb3b467ceb5d4bfd55eac0b` |
| `chapter21-obligations.md` | `f1f98be9fd8c625d5a8585ce832818c3e8b5b4fcb0fa0ef66d1051469897fe25` | `e9ec73c1de2835060646f62fd7d675b192b4f1960742f917952a4fbf78265a51` |
| `chapter26-obligations.md` | `2b9e79d9221eee57ed2ef19d76ac357157ceb9501bfc565ced831cdd90af0825` | `c1803a540a887977be6bf2a75e3291a6f1665ea7167786939b04a40b0b8ecb61` |
| `chapter27-obligations.md` | `49b7665f87a87b78a3990a650a02ffea803051105d589376d4c8f672dda86d5f` | `4a7c5a4675822ac7ed0dad125be33b4eb637410ed04beaf8cc07da4672b22ea3` |
| `appendix-c-obligations.md` | `ee6b8fa54832c50fcd8a3d1201d958aa63b42b9203bd89c779afb3ecb354689f` | `499d6d0632bf6f160add2edb7171588f1b23b96a314f25f7543a62c9ae614e2f` |
