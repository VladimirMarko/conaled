# FDSA-XT02 — independent receiving Spec review

## Current source and actual-type disposition

**Overall: Blocked pending the matching complete receiving-candidate check and exhaustive audit. The complete original source assessment and all 90 actual public-type assessments are complete, with zero new concrete Spec findings.** This continues the original XT02 Spec axis and all five frozen requirement groups. XT02-SP01 remains carried: its source correction and sufficient-only actual theorem type are independently confirmed; confirmation against the fully validated candidate remains pending.

The immutable receiving candidate is `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`, tree `d002afee18c38828f01221837f4c3f302ab155cc`. Its parent is proof-correction candidate `5b3b9ab1d72a70ca454abe68790327bcbb352d3c`, whose parent is initial reception `27c5908b07c7a03feefc09472a8701ef940b7aaf`. The incorporated accepted base and actual merge base remain accepted XT01 `90469ce4ba3fc49397d369a5db7d58aec7014f58`. The original unit base remains `64c6b777d828ecfe83234fc2aed94600a1f24297`; the original donor remains `974a97321a8ec174b56104c7e6efaaca881b6639`. Requirements version 1 is SHA-256 `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.

The preserved original Spec report, `tree-shape-spec-preparation-20261104.md`, remains 17,550 bytes and SHA-256 `cf5e7daa6041c8adb5bcd304bea7dc8b91b18b3c45776234ef65d0c8f6491d08`. Its full source assessment and detailed original source receipt are retained. Its old prerequisite statuses describe the historical drafting stage: accepted Chapters 1–3 and XT01 retain their subsequent acceptance. This review gives no Chapter 4 or later chapter acceptance.

## Original scope and current identity

The complete original six paths remain in scope:

- `Applications/Trees/Shape.lean`
- `Applications/Trees/ShapeLog.lean`
- `Examples/TreeShape.lean`
- `SquareApplications.lean`
- `docs/research/fdsa-reconstruction-map.md`
- `docs/research/fdsa-tree-shape.md`

The original donor diff has 838 added lines. Initial reception had 854, owing to the 16-line dated reception preamble, and its three formal modules were byte-exact donor copies. Current reception retains that complete scope and adds only four reviewed proof-body corrections in two successor commits. Shape remains 11,019 bytes / 267 lines / SHA-256 `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3`; current ShapeLog is 3,070 bytes / 73 lines / `24ba63bd0a8bc04afdcc1f559ae398a7438f8fe9618cc3e29c8d790499bd5629`; current Examples is 12,924 bytes / 303 lines / `d0f831e3aedca3571a77320485559dcb107664a21f34cd69c46be303a56ecb54`. Exact reconstruction after replacing those four proof bodies with their original bodies recovers the initial formal files. Current formal source is therefore not described as wholly byte-exact donor source.

All 91 original complete authored headers reconcile exactly with the receiving source, including their original contexts. The inventory remains 90 public names: 11 definitions and 79 theorems, plus one private recursive definition. The three modules contribute 29, 7 and 54 public names respectively. There are no authored instances or anonymous examples. All actual 90 expanded types have now been read separately; source-header equality is not substituted for that evidence. The private predicate and generated declarations remain within the full source/audit scope.

Independent import traversal still gives 29 local sources, 14 direct external imports and 54 edges. All 26 inherited local sources exactly match accepted XT01. Only `Applications/Resources/TreeCache.lean` and `Examples/TreeCache.lean` differ from the original XT02 donor's inherited inputs; those are the accepted XT01 proof-only corrections already assessed in this same reviewer's preceding XT01 axis. Current receiving qualification must use their accepted bytes. None of that prior validation is relabelled as XT02 validation.

All 15 retained governing guidance identities match both the original donor and receiving candidate, including the applicable skills, glossary, ADRs and README. Ten validation/toolchain/configuration files and all nine manifest pins match the incorporated accepted base. The original source/API/case preflight identities remain unchanged; the current local ticket's appended historical source-review status was read in full. The existing full fresh Chapter 1 native baseline remains authoritative; routine source additions on unchanged configuration introduce no fresh trigger.

## Complete reading and source evidence

During the immediately preceding read-only preparation I read the complete frozen requirements, preserved Spec report, original start/candidate/round/finding records, all three complete donor formal modules, the complete donor note, all root/map integration changes, and the independent case expectations. Initial exact donor equality and the subsequently verified four-body-only corrections permit retaining that completed source assessment. I then read every receiving integration change, the complete 196-line current note, both complete proof-correction diffs and the complete combined correction diff. The source note's original body is unchanged after the added reception context. The accepted reconstruction map is an exact byte prefix of the receiving map, and the public root differs by exactly one `Examples.TreeShape` import.

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

The public statement `localBalanceCounter_balanced` exposes the private recursive predicate. Its full definition has been assessed. The actual expanded type at native lines 407–408 uses `_private.Examples.TreeShape.0.TreeShapeExamples.SiblingHeightBalanced`, instantiated at Unit and the actual counterexample. I reconciled this exact printed reference with the complete recursive predicate in current source lines 275–279: both sibling height inequalities and both recursive child predicates are required. Private and generated declarations remain in exhaustive audit scope.

## Retained finding XT02-SP01

The original snapshot is 12,640 bytes, SHA-256 `9b0aacf07d1e9fe62f540abba5d24a387f3e962c9711d253fdb8d105001436f7`. Independent exact comparison shows precisely one comment replacement: the original necessity wording becomes the sufficient assertion that recursive validity makes the cached minimum agree with the structural observation. Every formal byte outside that comment was unchanged between the original snapshot and donor, and the initial receiving formal modules exactly matched that donor. The current candidate separately contains the four documented proof corrections elsewhere; the min_reader comment, statement and proof remain unchanged through those corrections.

The original counterexample remains valid: a root annotation one, left singleton annotation 99 and nil right child has actual root read one and structural minimum one. Its root minimum equation also holds, while recursive child validity fails. Thus the old necessity wording was false. The source theorem states only sufficient recursive validity and consumes the public cached-reader/erasure laws. The actual expanded type at native lines 363–368 confirms exactly that direction, with zero and the real minStep callback and no converse or local-root-only premise. The correction is source/type-confirmed; matching full candidate validation is still required. The finding is retained under its original ID and severity; no new finding or weakened expectation replaces it.

## Receiving documentation and coverage limits

The dated reception preamble accurately distinguishes accepted prerequisites from original drafting history. It retains the original base/donor, SP01 and full five-group scope. The new map section uses status-neutral wording and points to local current records without asserting an existing XT02 acceptance. Accepted root/map content is preserved.

The unit retains all original chapter obligations: enumeration, executable completeness, maximal/complete/almost-complete constructor exercises, arbitrary subtrees, Braun/weight-balance and array operations, search/order invariants, leftist representation and queue work, measured fold/traversal/merge costs, physical storage and sharing. A source connection to Chapters 4, 11 or 15 does not close their coverage ledgers. Existing leftist and random-access carriers and proofs remain unchanged.

## Actual receiving execution and correction evidence

Both failed runs remain recorded as failures. Attempt 1 on `27c5908` closed with actual exit 1 (`749654`): Shape built, while the two ShapeLog rewrite proof bodies did not normalize the cast natural base two to literal real two. Attempt 2 on `5b3b9ab` closed with actual exit 1 (`303ee9`): ShapeLog built, while the two literal-real worked-example proofs needed the same explicit normalization. Their complete outer logs remain 6,245 bytes / SHA-256 `fe1efdfbe87df7cc20613b7733d3627e05ef4477c031db7a7c61303d05589578` and 6,507 bytes / `aff7e923b5bae6f55b4d8ee6756e06435f920709fa4b00316e2ee0e7b09eb1f3` respectively.

The first correction composes the existing natural log/clog identities with the symmetric pinned real floor/ceiling bridge and explicit `Nat.cast_ofNat`. The second supplies the actual minimum/leaf/maximum values for rightTwo and explicit cast normalization in its strict real inequalities and the sample rounding equations. The pinned Nat cast definitions were read in context. No definition, statement, assumption, surrounding universe/namespace/variable/option context, or independent case expectation changed. Every original header, including the private predicate, still matches exactly. All four proof changes continue to use the intended public laws.

Focused attempt 3 on exact `e61bb6f` closed with actual exit 0 (`52ba6b`). All three target modules passed; Shape and ShapeLog were replayed and Examples.TreeShape was built. Its complete 3,632-byte log has SHA-256 `b41c0a2ccd8a61fa737c70302d0861d7a6f9d3812ee10602a1bc97d79b63f40e`. Independent reconciliation verifies matching candidate and clean status at both boundaries, actual/owned/recorder/native exit agreement, the unchanged native one-thread command, and exact prefix + complete native output + suffix reconstruction. This focused result is not a full candidate check or exhaustive audit.

The actual public-type program is 4,199 bytes, SHA-256 `fab2460caafba1f3f28a09006c4e220b9c735857e02294091486cdf4e8461c33`. Its original ordered 90 names and three imports are unchanged; its ten complete-printing options exactly match the accepted XT01 printing profile. The program was read in full. The actual invocation on exact e61 closed with exit 0 (`221199`). Its complete native output is 30,252 bytes / 430 lines / SHA-256 `1df9da87b91e300b1cb9ac92ac52b379ddeba30231a0f149bbab50ba322e5cd7`; the complete outer log is 30,613 bytes / `f5b5ecaaf2ae9c28d5ea3ffa7911b139180765790762e0700d9c968c6f73f69b`. All 90 blocks are unique, remain in original order, and reconstruct the entire native output. No display elision was observed.

I read every actual type completely in untruncated ranges 1–150 (`5e5cf4`), 151–300 (`6316cc`) and 301–430 (`07cdd9`), all actual exit 0. The statements preserve arbitrary payload universes and noninjective maps, universal capacity bounds, incompleteness-only strict power/real bounds, almost-complete exact rounding, and unrelated-type height optimality with only the intended first-tree shape premise. Nil/Empty cases include one external leaf. The actual concrete counterexamples and the wrong-node-offset proposition remain present. Annotation erasure remains unconditional; minimum-cache correctness retains its recursive-validity sufficiency. The exact private predicate reference is interpreted above. Each of the 90 blocks has its own saved line range, byte/hash identity and independent semantic assessment; source headers are not used in place of actual types.

Before/after saved input identities are exactly equal across all 29 local sources, 87 local compiler objects and traces, 10 configuration files, nine clean pinned dependencies, 12 runtime items, three roots and the exact program/name order. All 29 observed sources independently match immutable e61 Git blobs, and all 26 inherited sources match the accepted base. Configuration, dependency and runtime identities also match the accepted XT01 post-full observations. These saved observations do not independently prove the origin of every loaded object or exclude transient inputs; the matching full validation and its integrity guards remain necessary. I did not rehash current compiler objects during root's active build.

The verification file inherited by the focused and type runs still names accepted `90469ce`, SHA-256 `329f0d0087adc21b3446d7f10b67c472cdf62238ccf578865eec20569c04da61`. It supplies no XT02 full-check credit. No matching full e61 terminal or audit has yet been supplied to this stage. No session was polled by this reviewer.

## Validation boundary and receipts

The complete original requirements, original Spec/source assessment and source-stage report/hold remain unchanged. The initial source-stage report is preserved separately as `source-stage-report-27c5908.md`, so its old missing-evidence status and exact initial-donor observations remain historical evidence. The initial receiving source reconciliation and ledger are retained with all original requirements, scope, source/header/closure/guidance/configuration identities. Their detailed complete read boundaries are reused only at matching identities.

Current independent records are `source-corrections-e61bb6f.json`, `actual-types90-assessment-e61bb6f.json`, and the three separate focused-attempt assessment files in `provenance/tree-shape-spec-receiving-20261105/`. They bind the actual commands, complete closed logs, terminals, original names and scope, exact proof corrections and input observations. The current source/type-stage receipt binds their completed contents and this report. Routine immutable reconciliation included one reviewer bookkeeping assertion from mistakenly double-escaping source-header newlines; it stopped before creating the correction record, was corrected, and all 91 ordinary-newline headers were then verified. It was neither a compiler run nor a source finding.

The full original source and actual-type scope is complete with zero unresolved concrete source/type findings. Overall review remains **Blocked** until the matching ordinary full candidate check and exhaustive audit are supplied and independently assessed. Existing Chapter 1 fresh acceptance remains valid; unchanged configuration, compiler/Lake, dependencies and proof policy provide no new fresh trigger. Only Nix is waived.

All subsequent corrections remain within this original full scope and retain SP01 and both actual failed runs. Passing requires the matching applicable full candidate check and exhaustive audit plus this final independent axis assessment. Root then owns immediate qualified verification, exact local acceptance and durability. Those later coordinator actions do not create a circular ordinary review gate. This unit provides no Chapter 4 or later chapter acceptance.

This reviewer has run no Lean/Lake/check/audit, project helper or process poll, and changed no source, ref, index, cache, project output, entrypoint, ticket or old report. Writes are limited to the explicitly authorized current receiving Spec report/provenance paths. The accepted XT01 final reports remain immutable.
