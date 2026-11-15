# FDSA-XT02 — independent receiving Spec review

## Source-stage disposition

**Overall: Blocked pending qualified actual public types and complete receiving-candidate validation. Source assessment is complete, with zero new concrete Spec findings.** This continues the original XT02 Spec axis and all five frozen requirement groups, not a replacement or narrowed review. XT02-SP01 remains carried: its source correction is independently confirmed; confirmation against the eventual validated candidate remains pending.

The immutable receiving candidate is `27c5908b07c7a03feefc09472a8701ef940b7aaf`, tree `2833c54c80e93940eaea859737d6854fb2ce933e`. Its parent and actual merge base are accepted XT01 `90469ce4ba3fc49397d369a5db7d58aec7014f58`. The original unit base remains `64c6b777d828ecfe83234fc2aed94600a1f24297`; the original donor remains `974a97321a8ec174b56104c7e6efaaca881b6639`. Requirements version 1 is SHA-256 `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.

The preserved original Spec report, `tree-shape-spec-preparation-20261104.md`, remains 17,550 bytes and SHA-256 `cf5e7daa6041c8adb5bcd304bea7dc8b91b18b3c45776234ef65d0c8f6491d08`. Its full source assessment and detailed original source receipt are retained. Its old prerequisite statuses describe the historical drafting stage: accepted Chapters 1–3 and XT01 retain their subsequent acceptance. This review gives no Chapter 4 or later chapter acceptance.

## Original scope and current identity

The complete original six paths remain in scope:

- `Applications/Trees/Shape.lean`
- `Applications/Trees/ShapeLog.lean`
- `Examples/TreeShape.lean`
- `SquareApplications.lean`
- `docs/research/fdsa-reconstruction-map.md`
- `docs/research/fdsa-tree-shape.md`

The original donor diff has 838 added lines. The receiving diff has 854, owing to the 16-line dated reception preamble; no formal source was added beyond the original unit. All three formal blobs exactly equal the donor: Shape 11,019 bytes / 267 lines / SHA-256 `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3`; ShapeLog 2,796 bytes / 69 lines / `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b`; Examples 12,648 bytes / 297 lines / `2bcf2b65fa7a0eccc043c3bc7ba66d1bfdcd469489eab52d9085fdfb3db0b516`.

All 91 original complete authored headers reconcile exactly with the receiving source, including their original contexts. The inventory remains 90 public names: 11 definitions and 79 theorems, plus one private recursive definition. The three modules contribute 29, 7 and 54 public names respectively. There are no authored instances or anonymous examples. Headers and source counts are not elaborated-type or kernel-audit evidence.

Independent import traversal still gives 29 local sources, 14 direct external imports and 54 edges. All 26 inherited local sources exactly match accepted XT01. Only `Applications/Resources/TreeCache.lean` and `Examples/TreeCache.lean` differ from the original XT02 donor's inherited inputs; those are the accepted XT01 proof-only corrections already assessed in this same reviewer's preceding XT01 axis. Current receiving qualification must use their accepted bytes. None of that prior validation is relabelled as XT02 validation.

All 15 retained governing guidance identities match both the original donor and receiving candidate, including the applicable skills, glossary, ADRs and README. Ten validation/toolchain/configuration files and all nine manifest pins match the incorporated accepted base. The original source/API/case preflight identities remain unchanged; the current local ticket's appended historical source-review status was read in full. The existing full fresh Chapter 1 native baseline remains authoritative; routine source additions on unchanged configuration introduce no fresh trigger.

## Complete reading and source evidence

During the immediately preceding read-only preparation I read the complete frozen requirements, preserved Spec report, original start/candidate/round/finding records, all three complete donor formal modules, the complete donor note, all root/map integration changes, and the independent case expectations. Exact donor equality permits retaining that completed source assessment here. I then read every receiving integration change and the complete 196-line current note. The source note's original body is unchanged after the added reception context. The accepted reconstruction map is an exact byte prefix of the receiving map, and the public root differs by exactly one `Examples.TreeShape` import.

The pinned book text identity is SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`, corresponding to the retained July 27, 2026 PDF identity `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. I freshly read complete printed pages 49 and 51–54. The original complete page inspections at 47–49, 51–54, 128–130 and 183–186 remain attributed to the preserved assessment at matching identity. No fresh whole-manuscript, rendering, Isabelle rebuild or later mirror/manuscript revision-equality claim is made. No manuscript was copied into review deliverables.

Relevant actual pinned Mathlib source was reread for the Nat power/log and ceiling-log implications, the real logarithm order equivalences with their enclosing base-greater-than-one binder, both natural floor/ceiling bridges, and `Real.rpow_natCast`. All four API file identities match the original receipt. The complete BinaryTree API reading and unchanged XT01 fold/cache/source analyses are retained at their verified identities. The original complete source/API preflight analyses remain reusable without claiming new full readings of those unchanged reports.

## Full mathematical assessment

### XT02-01 — minimum height and source predicates

The minimum observation is the ordinary structural fold, with zero at nil and `min left right + 1` at a node. It measures nearest external empty-leaf depth. Its map law permits arbitrary, noninjective label functions between independent universes. The minimum/maximum inequality follows from actual child inequalities. No inhabited payload, ordering, equality decision, finite type or nonempty-tree premise appears in the source statements.

Complete is independently recursive: nil is true; a node requires equal maximum child heights and complete left and right children. Its equivalence to equal minimum/maximum height is a proved characterization, not its definition. AlmostComplete is the additive depth-gap condition, with the exact natural-subtraction equivalence. The source includes nil, complete-implies-almost-complete, immediate-child closure and map invariance. This is the source's external-depth convention, with no left-packing requirement. It supplies neither the executable Boolean checker nor general subtree closure.

### XT02-02 — sharp capacity and equality characterizations

Both universal power bounds include nil with its one external leaf. Structural induction compares powers at the smaller child minimum or larger child maximum. Complete trees attain both bounds. Incomplete trees make both bounds strict without an almost-complete or nonempty premise. The lower strict proof's equal-minimum branch correctly uses complete/minimum/maximum equivalence to recover equal maximum child heights if both children were complete. Both equality converses retain the correct equality orientation. The arbitrary-power counterexample prevents confusing equality at a tree's own height with being some power of two.

### XT02-03 — natural rounding and height optimum

The universal inequalities reuse the actual `Nat.log` and `Nat.clog` implications. Almost-complete exactness distinguishes complete trees from incomplete trees. The latter have `height = minHeight + 1`, and the strict power bounds determine the rounded values. No invalid predecessor bound is introduced at height zero. The complete branch includes nil through logarithms of powers.

The height optimum quantifies over unrelated payload types and universes. Only the first tree is almost complete; the size premise is the full node-count inequality. The proof uses the canonical `numLeaves = numNodes + 1` identity and the arbitrary competitor's capacity bound. There is no stronger strict height conclusion, equal-size restriction, common-label assumption, converse or uniformly positive-size existence assertion over Empty.

### XT02-04 — actual real correspondence

Real analysis remains in the separate ShapeLog module. The actual real sandwich and both incomplete strict bounds consume the corresponding discrete inequalities. Every analytic equivalence receives base two greater than one and the positive canonical external-leaf count; rewriting a real power at a natural exponent uses the pinned conversion theorem. The complete real equality follows from the sandwich and completeness/height characterization.

The almost-complete floor and ceiling statements use the exact pinned natural-rounding bridges. They are actual real-logarithm statements, not floating-point calculations or newly defined logarithms. The positive leaf count, including one at nil, supports the intended nonnegative interpretation without excluding the empty tree.

### XT02-05 — all connected cases and meaningful boundaries

| Case group | Independently assessed public connection and consequence |
| --- | --- |
| Empty and singleton | Arbitrary BinaryTree Empty is reduced through the existing public empty-tree theorem. Nil predicate laws and complete/height equivalence establish the intended zero/one boundaries. Logarithms use the new almost-complete theorems; real equality uses the complete theorem. |
| Complete three-node tree | The upper-capacity equality converse supplies completeness; the minimum equality, minimum height two and real height equality consume public results. There are four external leaves. |
| Two-node right chain | It is incomplete and almost complete, with three leaves and minimum/maximum one/two. Public strict capacities and real strictness coexist with equal rounded endpoints, so strict rounded versions are explicitly false. Child closure and the subtraction equivalence are exercised. |
| Actual XT01 asymmetric sample | The saved four-node Nat-labelled sample has five leaves, minimum two and height three. Its almost completeness supplies natural and real rounding. The separate wrong-offset proposition rejects substituting nodes for nodes plus one. |
| Noninjective maps and annotation erasure | The explicit constant Nat-to-Unit map preserves the sample's shape. Complete shape is relabelled separately. Erasure uses the actual projection map and public shape transport without a validity premise. The actual pair annotation consumes its erasure theorem. |
| Malformed size annotations | The saved corrupt tree has the same erased shape and minimum two while recursive size validity fails. The example does not claim that its corrupt size fields compute minimum height. |
| Actual minimum-height cache | The minimum reader specializes the public cached-reader theorem and unconditional erasure/minimum transport. The actual sample is built by annotate, whose validity and erasure establish a root result of two. No executor or tariff is added. |
| Power count and optimality nonconverses | A three-node chain has four leaves but is incomplete. A genuinely Bool-labelled four-node witness has leaves five, minimum one and height three; comparison uses the Nat-labelled sample and the cross-type optimum. Its universal optimality against any competitor with at least four nodes is paired with explicit failure of almost completeness. |
| Recursive sibling-height balance | The private predicate contains both local height inequalities and both recursive child predicates. The seven-node fixture has eight leaves, minimum two and maximum four, satisfies that predicate at every node, and is not almost complete. This is no AVL framework or invariant bridge. |
| Arbitrary saved chains | The universal rounded bounds apply to all chain lengths without an almost-complete premise or unjustified exactness claim. |

The public statement `localBalanceCounter_balanced` exposes the private recursive predicate. Its full definition has been assessed. The future actual public-type inspection must preserve and interpret the actual generated private reference, rather than guessing its name or treating it as an unexplained premise. Private and generated declarations remain in exhaustive audit scope.

## Retained finding XT02-SP01

The original snapshot is 12,640 bytes, SHA-256 `9b0aacf07d1e9fe62f540abba5d24a387f3e962c9711d253fdb8d105001436f7`. Independent exact comparison shows precisely one comment replacement: the original necessity wording becomes the sufficient assertion that recursive validity makes the cached minimum agree with the structural observation. Every formal byte outside that comment is unchanged in the donor and current receiving candidate.

The original counterexample remains valid: a root annotation one, left singleton annotation 99 and nil right child has actual root read one and structural minimum one. Its root minimum equation also holds, while recursive child validity fails. Thus the old necessity wording was false. The actual source theorem states only sufficient recursive validity and consumes the public cached-reader/erasure laws. The correction is source-confirmed, with final actual-type/validated-candidate confirmation still required. The finding is retained under its original ID and severity; no new finding or weakened expectation replaces it.

## Receiving documentation and coverage limits

The dated reception preamble accurately distinguishes accepted prerequisites from original drafting history. It retains the original base/donor, SP01 and full five-group scope. The new map section uses status-neutral wording and points to local current records without asserting an existing XT02 acceptance. Accepted root/map content is preserved.

The unit retains all original chapter obligations: enumeration, executable completeness, maximal/complete/almost-complete constructor exercises, arbitrary subtrees, Braun/weight-balance and array operations, search/order invariants, leftist representation and queue work, measured fold/traversal/merge costs, physical storage and sharing. A source connection to Chapters 4, 11 or 15 does not close their coverage ledgers. Existing leftist and random-access carriers and proofs remain unchanged.

## Validation boundary and receipts

The original 4,230-byte prepared 90-name program, SHA-256 `28622fb1c6417798d4d4c476e9e3d307792c62e881f0158446ca2938434b83ca`, remains unexecuted preparation evidence. No actual receiving public types, focused terminal or full check/audit terminal has yet been supplied to this Spec stage. Source header reconciliation does not replace any of them. Current compiler-object rehashing is deferred while the root builder owns the outputs.

The independent source reconciliation is `provenance/tree-shape-spec-receiving-20261105/source-reconciliation-27c5908.json`, SHA-256 `29978ad7f74dc89ab0818fc3db780dd907b0c07eb33271f2efce954a6f2287c9`. It binds all original scope, source/header/closure/guidance/configuration identities and preserved records. Complete read boundaries are retained in the accompanying source-stage ledger, including the preceding read-only preparation and receiving-document reads.

All subsequent corrections remain within this original full scope and retain SP01 and actual failed/successful run history. Passing requires qualified complete actual types, the matching applicable full candidate check and exhaustive audit, and the final independent axis assessment. Root then owns immediate qualified verification, exact local acceptance and durability. Those later coordinator actions do not create a circular ordinary review gate. Only Nix is waived; official compiler/Lake/dependency pins and proof restrictions remain mandatory.

This reviewer has run no Lean/Lake/check/audit, project helper or process poll, and changed no source, ref, index, cache, project output, entrypoint, ticket or old report. Writes are limited to the explicitly authorized new receiving Spec report/provenance paths. The accepted XT01 final reports remain immutable.
