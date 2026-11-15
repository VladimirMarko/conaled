# Coverage scope audit

Prepared 2026-11-02. **Read-only audit of the 27 chapter and three appendix
obligation inventories.** This note proposes corrections; it does not edit
those inventories, implement Lean, change tickets, or certify coverage.

## Result and boundaries

The principal remaining omission affects Chapter 1: the inventory retains the
cost equations but classifies the surrounding mathematical comparisons of cost
models as explanatory material. Two advertised extensions also lack explicit
coverage: treap set operations in Chapter 10 and cached game-graph search over
distributive lattices in Chapter 27. Other findings concern mathematical claims
already mentioned in an inventory but described as optional or merely useful
evidence. Those categories are separated below.

The audit used the July 27, 2026 book, printed pp.1–359, from
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Printed page p is PDF page p+6 in one-based numbering. Suspicious passages were
checked against the saved chapter text and, for the priority findings, directly
against the PDF. The existing Chapter 10 cited paper was consulted only to
identify the already-asserted treap work model; no new paper campaign or
downloads were undertaken. Appendix A–C checks were independently delegated
and their exact findings reviewed here.

The governing distinction is the one recorded in `../DECISIONS.md`:

- A mathematical assertion remains a formal obligation when its proof is
  omitted, elementary, cited elsewhere, or waived pedagogically in an exercise.
- An explicitly open conjecture needs a precise, labelled proposition, not a
  promised proof or a new axiom.
- Bibliography, implementation history, practical performance reports and
  methodological opinions do not automatically require another complete
  algorithm, external development, or universal performance theorem.
- A conditional mathematical claim needs its mathematical conditions and a
  corresponding proof. Calling it conditional does not alone discharge it.

This is a scope audit, not a second exhaustive verification of every formula,
source defect, algorithm or proof already recorded in the inventories. The
input digests at the end freeze the notes examined.

## A. Clear omissions or explicit proof waivers

### CSA-01 — Chapter 1 cost-model comparisons are mathematical obligations

**Source:** §1.5, printed pp.7–8; §1.5.2, p.9.
**Inventory locations:** `chapter01-obligations.md`, headings “1.5 Running
time” and “1.5.2–1.5.3”; the latter says that no additional algorithm theorem
requires a proof. Chapter 1 has no numbered C01 obligation IDs.

The source makes three distinct claims in addition to defining its tariff:

1. Charging variable accesses, constructors and primitive operations, rather
   than assigning them zero additional cost, changes the count by only a
   constant factor. The explanation on p.9 is a constant added to each
   defining equation.
2. Omitting the entry charge of a nonrecursive function preserves the
   asymptotic class, subject to the explicit zero-body-cost exception on p.8.
3. The eager call-count analysis also upper-bounds lazy evaluation, potentially
   loosely (p.7, first bullet).

These are mathematical comparisons of observations. They are not additional
algorithms, but that does not make them nonmathematical. The source's separate
refusal to verify a complete compiler/runtime/hardware stack on p.9 is a valid
boundary and must remain intact.

**Existing formal gap, inspected at frozen candidate
`1aabd512284fe86254278ac631eda061d311050b`:**

- `conaled-ch01-review/Applications/Resources/CallCount.lean` proves
  `tick_value`, `tick_cost`, and the primitive/let/argument/if/case algebra.
  None compares a coarse and a refined tariff or two evaluation strategies.
- `Applications/Resources/Measured.lean` supplies additive observations and
  `reweight_bound`; the latter transports an already-given inequality and does
  not establish the missing comparisons.
- `docs/research/fdsa-reconstruction-map.md`, “Call-count conventions,” maps
  nonrecursive inlining to a convention without a comparison theorem. Its
  “Resource and interpretation boundary” correctly excludes hardware claims
  but again treats the remaining discussion as no additional algorithm theorem.
- The map mentions an identically zero cost function. That qualification is
  weaker than the pointwise/eventual positivity needed for the usual Big-O
  comparison.

**Proposed bounded correction:** retain three explicit conditional proof
obligations. For a fixed finite program, use an execution-block or trace
observation with a uniform bound K on primitive/local work per charged entry;
prove the refined count is bounded by K times the coarse count, with a root
constant or positive-entry condition stated explicitly. The constant must be
independent of the runtime input. This can be a reusable trace theorem; it
need not introduce a complete source-language compiler.

For one omitted entry, prove `T <= T+1 <= 2*T` when `T>=1`, and preserve the
zero-cost counterexample. An asymptotic version needs eventual positivity on
the chosen input filter, or must compare against `T+1`. Merely assuming that T
is not identically zero is insufficient: `T(n)=0` on even n and `T(n)=n` on odd
n gives infinitely many failures of any bound `T(n)+1 <= C*T(n)`.

For the lazy claim, name call-by-need with sharing, the finite terminating
domain, the counted events, and the trace/simulation condition which justifies
the upper bound. The book says lazy evaluation but does **not** explicitly
define sharing on p.7; that interpretation must be declared. A conditional
demand/observation theorem must not be advertised as an already-proved
simulation for every source program or for Lean's runtime.

A useful independent boundary is the fixed recurrence
`f(0)=1; f(n+1)=let x=f(n) in x+x`. Eager evaluation and memoized shared demand
make `n+1` calls to f; unshared call-by-name duplicates the recursive demand
and makes `2^(n+1)-1` calls. These are proposed checked boundary witnesses, not
newly compiled results of this audit. Thunk-allocation, forcing and garbage
collection overhead require their own tariff if counted.

The explicit fixed-size addresses/numbers on p.9 belong to the conditional RAM
rationale. They do not justify unit bit-complexity for unbounded Lean Nat/Int
arithmetic. No actual hardware theorem is requested by this correction.

### CSA-02 — Exercise 3.1's linear-time claim is still waived

**Source:** Exercise 3.1, p.33. **ID:** C03-047.

The exercise requests a linear-time, tail-recursive minimum selector traversing
the list once, then excuses the textbook reader from proving its runtime.
C03-047 repeats that excuse as an absence of a linear-time theorem obligation.
This conflicts with the whole-book formal scope, just as the already-corrected
Exercise 9.4 waiver would have done.

**Proposed correction:** require a measured linear bound for the actual
`select0` implementation on its nonempty domain, retaining its traversal and
value requirements. Reusing C03-051 at k=0 is sufficient only after a checked
algorithm/cost correspondence with the actual `select0`; the existing
C03-050 bridge is for `select1` and does not supply that missing bridge.
No additional probability work is involved.

### CSA-03 — Chapter 10 has no treap applicability/work row

**Source:** Chapter Notes, p.125. **Nearest IDs:** C10-095–108; none mentions
treaps. The source explicitly includes treaps in the generalization and
attributes the displayed `O(m*log(n/m+1))` work bound to it.

The existing pinned paper, Blelloch–Ferizovic–Sun, *Joinable Parallel Balanced
Binary Trees*, <https://doi.org/10.1145/3512769>, author copy
<https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>, SHA-256
`c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`,
resolves the important qualification. **Theorem 9, p.7:24 (PDF24)** gives this
work bound **in expectation for treaps**, for its Figure 13 union,
intersection and difference algorithms. Table 3 uses
`m=min(|T1|,|T2|)`, `n=max(|T1|,|T2|)`; directional difference need not swap
its actual operands.

Section 2.1, p.7:5, uses random priorities attached to keys and requires equal
keys across the two inputs to have equal priorities. Footnote 4 on p.7:4 makes
the algorithms deterministic after priorities are fixed. A precise sufficient
model is: fix finite ordered sets A,B before sampling; sample a uniform
distinct priority ranking of `A union B`; construct both canonical treaps
using that shared ranking; then measure the actual operation. Prove semantic
correctness for every ranking and a uniform expected-work bound for
`1<=m<=n`, handling empty operands separately. Uniform marginal priorities
alone, or an arbitrary deterministic hash, does not establish this model.

**Proposed correction:** add mandatory concrete treap join/invariant,
shared-priority probability, algorithm correspondence, and expected-work
obligations. Do not instantiate the inspected deterministic AFP
`StronglyJoinable` contract merely because a treap has valid BST/heap
invariants. The paper treats treaps as weakly joinable. Keep C10-100's
pointwise finite bounds scoped to their actual deterministic instances.

The book does not state the paper's numerical parallel-span theorem, so that
theorem is not added here. The paper itself gives span with high probability,
separately from expected work. Its Theorem 12 on p.7:28 prints the reversed
size condition `m>=n` with the same expression and loses the treap expectation
qualifier; use Theorem 9 and record that source discrepancy rather than copy
Theorem 12 unqualified.

### CSA-04 — The cited lattice game-graph/cache extension lacks a witness

**Source:** Chapter Notes, p.340, paragraph about distributive lattices and
Li et al. (2022). **Nearest IDs:** C27-067, C27-163, C27-179.

This paragraph makes an affirmative mathematical extension claim: fail-soft
alpha-beta over distributive lattices on a game graph using a cache, with
correctness stated through the squashing operation. It is more specific than
a bibliography entry. C27-067 retains same-value-problem cache-bound reuse in
the earlier ordered setting; C27-163 retains tree/lattice correctness. Those
two results do not by themselves prove a cached graph algorithm correct.
C27-179's general bibliography exclusion must not swallow this specific claim.

**Proposed correction:** retain a bounded existence/implementation-correspondence
obligation for the asserted graph/cache extension, resolving its precise
source domain before acceptance: finite acyclic unfolding or explicit depth
policy, position identity and any value-preserving symmetry, cache key and
validity conditions, proper window assumptions, and the actual squash-based
correctness relation. A concrete source-compatible algorithm or an explicitly
proved instantiation can witness it. The book does not supply a complete graph
recurrence in this paragraph, so this audit does not invent one or claim to
have recovered the cited proof.

This does not request the entire Li et al. paper, correctness for arbitrary
cyclic games, arbitrary hash collisions, or an unstated `O(V+E)` cache theorem.
The classification follows the same retained-existence discipline already used
for the externally cited real-time deque claim in C20-118.

## B. Existing claims whose wording should become mandatory

These are not asserted to be wholly absent: the listed rows already mention
the mathematics. Their conditional/discussion wording could nevertheless let
an implementation close the chapter without a witness.

| Audit ID | Book location and inventory ID | Wording issue and proposed correction |
|---|---|---|
| CSW-01 | §2.6 pp.21–22; C02-088 | The row calls a sorted-input one-run/count specialization useful evidence and labels the entry explanatory. Require the actual nonempty sorted-input `runs xs=[xs]` and zero merge-comparison specialization, hence the linear best-case comparison bound. Retain the conditional operational claims for difference-list composition/materialization as explicit cost obligations for the chosen construction model, not merely prose. |
| CSW-02 | §4.4.1 pp.57–58; C04-073 | The source asserts constant smart-constructor overhead for cached size. The row asks for a measured specialization only if a performance claim is made; the book already makes it. Require a bound for actual `sz`/`node_sz` under unit local-access/arithmetic/constructor assumptions, and give arbitrary `f` its own cost contract. C04-067/068/072 are value/invariant laws, not that cost bound. |
| CSW-03 | §5.5 p.67; C05-094 | The finite average-search example is conditional on retaining the prose claim. Retain it unconditionally with the row's precise uniform distribution on the three present keys and unit visited-node/three-way-comparison tariff: balanced average `5/3`, chain average `2`. Do not infer a uniform distribution on an infinite key universe or a theorem for arbitrary failed queries. |
| CSW-04 | Chapter8 pp.95–97 and operation discussion; C08-071–073 | C08-071 begins with conditional claim wording, while C08-072/073 already require height-based and logarithmic measured bounds. Remove the optional reading and cross-reference those required witnesses. This is wording hardening, not a newly discovered missing asymptotic target. |
| CSW-05 | Corollary9.3 explanation p.107; C09-016 | The decimal approximation is retained only if its displayed precision is formalized. Preserve its approximation meaning with an explicit checked enclosure, such as the already-proposed `1.440 < 1/log2(phi) < 1.441`, or equivalent justified rounding. Keep the exact irrational coefficient in C09-015; do not replace it by an incorrect upper bound of 1.44. |
| CSW-06 | Introductory applicability p.117; C10-108 | The weight-balanced join/rank/work instance is conditional on claiming that family covered. The book already advertises it. Require the concrete instance and its contracts. The existing paper supplies a possible join route with its actual weight-balance parameter restrictions; no automatic transfer from the AVL/RBT AFP instances follows. |
| CSW-07 | Chapter Notes p.252; C21-102 | The chapter introduction correctly retains an unproved Dynamic Optimality Conjecture statement, but the row makes formalizing its BST-model proposition optional. Make the precise labelled proposition mandatory. Preserve the open/unproved status; no proof, axiom, or claim about later research status is required. |
| CSW-08 | Coding assertions pp.305,317; C26-009 and source-discrepancy item2 | C26-009 already retains the uniquely-decodable-code optimality bridge. The later discrepancy paragraph says “If formalizing the broader optimum claim.” Replace that conditional with a reference to mandatory C26-009. This is not a new coding-theory obligation beyond the existing row. |
| CSW-09 | AppendixC pp.357,359; AC-078–080/084 | The ordinary set-fold infinite-set convention is already retained, but the explanatory paragraph and closing handoff make its adapter conditional. Require a correspondence covering finite sets by `Finset.sum/prod` and infinite sets by the source neutral-element convention. Existing declarations can witness this; a new wrapper is not inherently required. |

For CSW-01, separate an implementation-model theorem from a Lean runtime
claim. A semantic difference-list invariant alone proves neither constant
execution cost nor linear materialization. State whether linearity is in
constructed closure/representation size or emitted list length, and prove the
actual ascending-run builder has the required relation between them. Arbitrary
composition histories with empty functions need not have a size controlled by
output length. No universal cost theorem for all extensionally valid functions
should be inferred from C02-061's value invariant. The book's observation about
better Haskell performance is an empirical/practical comparison, not a new
universal theorem.

## C. Model boundary to resolve explicitly, without overstating the omission

### CSM-01 — Selection sensitivity versus an algorithmic lower bound

**Source:** p.32's asymptotic optimality assertion and Exercise3.4, pp.33–34.
**ID:** C03-052; also `selection-proof-plan.md`'s corresponding row.

The inventory exactly retains the exercise's displayed formal statement:
each coordinate of a distinct integer input can be replaced so that the
selected value changes. The book itself uses that statement as its formal
interpretation of the need to inspect every element. Thus this is **not an
omitted displayed theorem**.

However, the same chapter also asserts asymptotic optimality of the linear
algorithm. A theorem about input sensitivity alone does not quantify over
algorithm executions. Preserve the distinction and give the lower-bound
reading an explicit bounded bridge if it is used to claim formal optimality:
in a deterministic adaptive coordinate-query model, correctness for all
length-n integer inputs and trace indistinguishability for inputs agreeing at
queried coordinates imply that every coordinate must be queried. C03-052
supplies the adversarial input change; the bridge supplies the computation
argument. If the correctness domain is restricted to distinct inputs, retain
or prove the needed distinctness of the adversarial replacement as well.

This gives a meaningful `n`-query lower bound without formalizing arbitrary
hardware or every language semantics. Its relation to the algorithm's chosen
resource tariff still needs a named per-query contract. No new randomized
lower-bound model is inferred here. The independent selection-plan reviewer
agreed that this bridge is distinct from sensitivity; no plan/inventory was
edited during this audit.

## D. Checked nonissues and exclusions that should remain

The following checks also identify why a keyword hit was not treated as a
missing mathematical obligation. They cover all 30 input notes.

| Chapter/appendix | Source locations and checked disposition |
|---|---|
| 1 | pp.1–5 syntax/type examples, including an incomplete Fibonacci recurrence, do not specify another full algorithm. §1.5.2 p.9 explicitly declines a verified hardware stack; retain that boundary while fixing CSA-01. §1.5.3 p.10's preference for explicit bounds does not import every theorem in an asymptotics library. |
| 2 | C02-024 now retains both average-input and randomized-pivot quicksort claims from pp.16–17. Exercise2.6 p.29 expressly does not demand equality of intermediate merge-pass lists; C02-105 retains its actual result/cost requirements. Proof-case premises C02-091 are not independent extra algorithms. CSW-01 is separate from the completed probability-scope correction. |
| 3 | C03-059–080 now retain expected/worst/tail claims on p.35 with explicit distributions and tariffs. C03-058 retains Exercise3.8's exact mathematical inequalities despite its paper-only instruction. Hybrid-performance advice does not specify a complete new Introselect recurrence. CSA-02 and CSM-01 are distinct remaining issues. |
| 4 | p.48 names postorder but expressly omits its definition; it states no additional postorder theorem. C04-020 retains the optional no-duplicates strengthening of Exercise4.2. C04-018 retains both linear accumulator traversal and a correctly qualified quadratic direct-traversal family. The chapter does not assert a Catalan formula merely because a reusable enumeration library has one. |
| 5 | Chapter Notes p.76's exact rotation-diameter and NP-membership assertions remain in C05-092/093 despite external proofs. The unresolved complexity question is not an assertion of NP-completeness or an axiom. A citation to an interval-tree application does not require that entire application. CSW-03 concerns the actual finite average example. |
| 6 | pp.79–83 abstraction functions/invariants need not be executable data; their correspondence laws remain C06-006/019. A stronger interval coalescing policy is an optional implementation choice, not a printed requirement. Later consumers' contracts are scheduled cross-chapter, not waived. |
| 7 | p.86's omitted complexity details remain explicit C07-054 logarithmic-operation obligations. p.91's factorial, repeated-insertion and comparison-sorting arguments remain C07-055–062, with duplicate/domain corrections. Chapter Notes p.94 are attribution, not additional quantitative claims. |
| 8 | All printed helper/invariant/map/Set laws and the linear list-construction exercise remain inventoried, including alternative algorithm variants. Chapter Notes p.104 give history rather than another precise performance theorem. Existing mandatory C08-072/073 prevent CSW-04 being a missing bound. |
| 9 | C09-061 already preserves logarithmic height for fixed generalized balance parameter despite Exercise9.4's proof waiver. p.116's external-source reference does not demand that source's sharper unstated constants or every theorem. CSW-05 only tightens the printed numerical approximation. |
| 10 | C10-095–110 retain the advertised optimal work and the substantial mismatch between the printed red-black join and the newer AFP work instance. p.118 expressly does not develop parallel efficiency: C10-111 retains branch independence without importing the external paper's numerical span results. CSA-03 and CSW-06 are specific named-family defects. |
| 11 | C11-013 retains the Braun-index converse even though its proof is omitted in the prose. All eight exercises and the linear-conversion assertions remain inventoried. Differing proof scripts for the same update law are not extra behavior obligations. |
| 12 | pp.152–153's invariant-free semantic laws remain stronger than the invariant-preservation laws; the invariant's space claim is retained in C12-031. Chapter Notes p.164's naming/history and alternative implementations do not supply another concrete cost formula. Companion-only `delete0` is not a substitute for the printed shrinking deletion. |
| 13 | The general dimension construction of §13.3 is retained in C13-081 onward. p.175's survey references to point-search k-d trees and other applications do not specify another complete point-search algorithm. The region-versus-point distinction is a model boundary, not an omitted theorem. |
| 14 | Chapter Notes p.180 discusses imperative decrease-key and a cited functional priority-search-tree implementation. It gives no new operation law, recurrence or quantitative bound to add to this chapter's specified ADT. Existing exact-multiset queue laws remain mandatory. |
| 15 | Exercise15.2's lack of an intermediate raw-list equality requirement is preserved in C15-079; semantic/invariant/cost conclusions remain. C15-067 onward retain linear heap construction, including the all-length extension and the recorded defect in an insufficient generic sublinear-merge argument. p.189's alternative-heap attribution does not import another algorithm. |
| 16 | pp.191–193's Braun priority-queue algorithms and domain restrictions remain retained. Chapter Notes p.193 is provenance, not an extra performance result. Invalid-shape pattern gaps are explicit domain adaptations, not proof waivers. |
| 17 | pp.195–202's binomial algorithms, rank/arithmetic claims and bounds remain retained. Chapter Notes p.202 is historical attribution, not another mathematical claim discarded through citation. |
| 18 | p.213's automatic monadic transformation is not a requirement to port Isabelle/ML tooling; the value/consistency/composition laws remain C18-042/043. p.225's externally proved quadrangle/root-monotonicity and quadratic optimal-BST claims remain C18-111 onward. Other cited dynamic-programming examples do not require every companion algorithm. Concrete hardware seconds on p.203 do not become portable theorems. |
| 19 | Binary-input potential accounting and actual histories remain C19-017/018; unary traces cannot silently spend one persistent input's potential twice. Chapter Notes p.232's attribution does not add an unstated algorithm. |
| 20 | C20-118/119 explicitly retain p.244's real-time deque and lazy real-time queue mathematical claims; neither is dismissed as external prose. The judgement that a method is simpler remains analysis. Conditional lazy costs require their own model, as the existing rows acknowledge. |
| 21 | C21-084 retains Lemma21.5 despite p.252's omitted proof. C21-098–101 retain static optimality with primary theorem/domain correspondence; a similarly named AFP file is not substituted. The dynamic conjecture is unproved, with only CSW-07's statement-wording correction needed. |
| 22 | C22-053 retains the symmetric merge-analysis case omitted in the exposition. The companion's separate `merge2` algorithm is not a printed extra requirement. Chapter Notes p.255 is attribution. |
| 23 | C23-073–077 retain the improved constant insert/meld and logarithmic delete-min amortized bounds in p.263's notes. Empirical comparisons are not universal machine theorems. The vague report of an unfinished final analysis does not specify a conjecture formula or require solving an open problem. |
| 24 | pp.288–289's unprinted auxiliary invariants and displayed distance consequences remain C24-104 and related rows. Chapter Notes pp.290–292 describes graph models and proof methods; references to matching, flow and refinement systems do not request those algorithms. The chapter supplies no general DFS/BFS `O(V+E)` theorem; C24-137 correctly does not invent one. |
| 25 | C25-003/004 retain p.293's naive-search expectation with an explicit input model; the KMP worst-case linearity claim remains retained. Companion while-loop variants can witness a proved correspondence without requiring duplicate algorithms. p.304's implementation history and external-file buffering comments do not assert a new universal theorem. |
| 26 | C26-009 retains optimum coding beyond the tree theorem; C26-087–097 retain all p.318 runtime claims, including their representation/presorted-input corrections. The Huffman-algebra question concerns proof style, not a stated mathematical result. CSW-08 prevents the already-retained coding bridge becoming optional in the handoff. |
| 27 | C27-170–178 retain p.340's affirmative random-tree optimality assertion with precise primary models. Source-only abandoned `oops` experiments are not book theorems or accepted facts. Exercise27.11's lattice clamp and printed hard/soft relations remain covered. CSA-04 identifies the separate graph/cache assertion rather than importing every cited program. |
| A | pp.344–345's displayed list equations remain A-001–020. No equation is supplied for empty head/minimum or invalid lookup; explicit failure/domain adaptation preserves rather than waives the valid equations. Reverse cost belongs to Chapter1/B without discarding an AppendixA assertion. |
| B | pp.347–348's seven list and four selection elementary properties remain B-002–023. B-024–060 retain all later printed recurrences; their asymptotic proofs are chapter-owned. B-050's partial residual case needs a domain proof, while B-060's exhaustive Option cases can be simplified by a proof. |
| C | pp.355–359's editor escapes and typography are syntax descriptions, while their mathematical operations and eta correspondence remain retained. AC-086 records the interval typo with corrected meaning/counterexamples. Infinite indexing sets need CSW-09's unconditional correspondence. No appendix contains a further open conjecture. |

## E. Handoff

The parent was notified of CSA-01 before completion because it affects the
active Chapter1 acceptance boundary. The current frozen full check remains
candidate evidence; this audit neither stops it nor treats it as evidence for
the missing comparisons. Later chapters remain queued.

Reconcile each finding explicitly in its owned inventory and implementation
plan. Where a row already contains the obligation, tighten the handoff rather
than create a duplicate framework. Resolve CSM-01 as a model-boundary decision,
not as an assertion that the displayed exercise was forgotten. Preserve the
legitimate exclusions in section D. This audit has not changed any existing
inventory, Lean file, ticket, Git state or remote file.

## F. Input snapshot

The following SHA-256 digests identify the notes inspected. Paths are relative
to `fdsa-control/research/`.

| File | SHA-256 |
|---|---|
| `chapter01-obligations.md` | `4d42c151a767838081170d03b557f54a789d82506406f281b114f49527120b20` |
| `chapter02-obligations.md` | `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d` |
| `chapter03-obligations.md` | `f7508b53983b68f7c5b74cb295fe59886f5d975dc865ff7b128e150bea8006eb` |
| `chapter04-obligations.md` | `7f070734ebffcb26350514a2bfde9d30732236408922435d4b54029c3387e407` |
| `chapter05-obligations.md` | `a80e32867234bf2bb2d291ee7bb249afc051dde128cb3c1f7879609567831a45` |
| `chapter06-obligations.md` | `078bb9759e7bfd9245cfff69443f7722ae4b49295da61f311689da874bb20146` |
| `chapter07-obligations.md` | `8e9aa9dda75c04a4c6a09a40feead8a2ff8d7ebc64c7dd47c0344921a6f41bde` |
| `chapter08-obligations.md` | `1c55482207ef854a43b8d54c1f7a128ad71f01ad5054f5a8415340ac772dd783` |
| `chapter09-obligations.md` | `daf503cbdbbd80320bbe4b6cfe2c73102f39dcf50ae49cbd544907eec95c689b` |
| `chapter10-obligations.md` | `2bc962c3041e5e4d5ba15bdcf01d5b278ff91231fb83f347982a7ff585eac321` |
| `chapter11-obligations.md` | `ec4a0763833c45d4ff3cd0a06b90cb3fd270a245b61bab2c52608066554213fc` |
| `chapter12-obligations.md` | `246779209f9f855837a8bb20bc7f2f58c37cd66144c85960fed6cb3426a0ef28` |
| `chapter13-obligations.md` | `de2ffeda482de966604adb7b59bc211d40dc6d1895f7fbb28ca682b14a6f8e54` |
| `chapter14-obligations.md` | `9222adc24498e1f0e8df361c1a936cc5656fce0f2b4caf7570bc0515a5e4434d` |
| `chapter15-obligations.md` | `03f2571e833fa0eb826a3d6d1a1dbf53a62626a9278b5dc1a0fe911aac15812c` |
| `chapter16-obligations.md` | `180865d8315609bd24687b5ce0c2cbf7e75995769ac10db74e621cc693585108` |
| `chapter17-obligations.md` | `3ffde1d8021bf3dcb0aa9c3430b30e945c2fad2d16f3aca9b886e166a6dcebe2` |
| `chapter18-obligations.md` | `ead4b0cc69ebdbd4ea767b272c2cdafd57262ce2d0ca13cd0e7273cc9fa55337` |
| `chapter19-obligations.md` | `1d9d22ca8d801d7c0ba47910d0f6519dd7c76acd787164be3a382ad818c220c6` |
| `chapter20-obligations.md` | `deaa46226bc68126f6c0b92f0ea175329d53eb23908b1491d575388ab15010e9` |
| `chapter21-obligations.md` | `f1f98be9fd8c625d5a8585ce832818c3e8b5b4fcb0fa0ef66d1051469897fe25` |
| `chapter22-obligations.md` | `805b5d297ee9088a01ed4adf7f3816debd7e9a4f02777364fc85f522a1935939` |
| `chapter23-obligations.md` | `01c1184e372e574b0487822e844ff5f2abecd6c7e05fa3d59961972d785ea700` |
| `chapter24-obligations.md` | `5187150f423dfa75c730e3e09bb2740851e85c0fc8ff1b8494d6dd5a4d585329` |
| `chapter25-obligations.md` | `13b30148bf4094e8f1a98bffd8d6fe3fcf7071828582ff384f788c99934ce042` |
| `chapter26-obligations.md` | `2b9e79d9221eee57ed2ef19d76ac357157ceb9501bfc565ced831cdd90af0825` |
| `chapter27-obligations.md` | `49b7665f87a87b78a3990a650a02ffea803051105d589376d4c8f672dda86d5f` |
| `appendix-a-obligations.md` | `91233486d25272ef0e6be256f40de1ed35bee61bb6b8d8dfb9845d36cc869002` |
| `appendix-b-obligations.md` | `8bf1101e774269ead99ccb23d7de237f0a208cc9a3d2d0522a4ab464ed6981e6` |
| `appendix-c-obligations.md` | `ee6b8fa54832c50fcd8a3d1201d958aa63b42b9203bd89c779afb3ecb354689f` |
