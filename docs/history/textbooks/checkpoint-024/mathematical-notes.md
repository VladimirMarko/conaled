# Retained mathematical requirements and assessments

These notes project the mathematical content of the CTB specifications and assessments. Historical CTB status is not receiving acceptance. GitHub issue #582 owns this intake; current mathematical statements and their correspondence maps have the owners listed below. Source path and SHA-256 records identify each projected input. Operational instructions and records are omitted.

The companion ticket projection preserves all 78 CTB identities, chapter coordinates, mathematical requirements, dependencies and historical statuses. Requirements expressed in the historical imperative remain historical requirements; the final owner documents distinguish supplied constructions from unresolved obligations.

## Shared contracts and Chapter 4 correspondence

The common carrier is `BinaryTree`, with independent semantic observations, ordinary `Trees.fold`, measured executions and explicit representation adapters. Preserve arbitrary label universes, occurrence multiplicity and order wherever observed. Additional hypotheses belong on the theorems that need them. Value equality alone establishes no cost, allocation or physical-sharing equivalence.

`docs/research/fdsa-chapter04-coverage.md` owns C04-001 through C04-076, all eleven exercises, the enumeration uniqueness and no-tree-equality bonuses, and Lemma 4.1 through Corollary 4.12. Its source is the preserved July 27, 2026 manuscript ledger, printed pages 47–58, SHA-256 `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`. The assessment did not reread the primary PDF. The two row assessments and combined CTB-23 report are deduplicated into that owner rather than retained as competing maps.

Preserve node/external-leaf distinctions, minimum height and strict/nonstrict power bounds, complete-tree characterizations, real logarithms and natural floor/ceiling bridges with positive leaf counts, height optimality across unrelated label types, arbitrary maps, cache erasure and conditional local-operation costs. Almost completeness means external leaves on adjacent levels, without a left-packing condition. A local height-balance condition is weaker. A correct root cache does not establish recursive cache validity.

The source corrections and restrictions remain explicit in the coverage owner: arbitrary reconstruction requires its distinctness domain, balancing retains successful-input premises, almost-complete constructors require the shorter-child completeness condition, local callback work must be charged, and no false source claim becomes an axiom. Contextual terminology and omitted postorder are dispositions, not newly claimed algorithms.

## CTB-2: measured folds

Owner: `docs/research/fdsa-tree-fold-resource.md`; code: `Applications/Resources/TreeFold.lean`, `Examples/TreeFold.lean`, `Examples/TreeFoldCache.lean`, `Examples/TreeFoldObservations.lean`.

`run` executes left result, right result, combining callback and post-body entry observation through one ordinary fold. Raw observations require only `Add`; grouping and order are part of the contract. `run_value` erases to the actual callback-value algebra. `run_value_of` relates it to an independently supplied algebra under the stated pointwise law. Preserve independent payload, summary and observation universes.

Additive-hom reweighting transports that same execution without commutativity. An input label map is semantic transport, not automatically a charged preprocessing pass. Structural natural work is exactly `e*(2*n+1)` plus the zero-entry execution with its actual callback work. Constant and bounded callback results quantify uniformly over actual reached summaries of arbitrary finite child trees under fixed parameters, not arbitrary impossible summaries or only the chosen input's subtrees.

Nil costs `e`; a singleton with callback charge `k` costs `3*e+k`. Zero entry, reset callbacks, empty payload types, product projections and noncommutative ordered traces remain discriminating cases. Existing annotation clients consume generic cache validity, reader and erasure laws. Actual measured appends include their terminating call. The asymmetric inorder executions with costs 15, 23 and 25 illustrate equal values with different work.

## CTB-70 and CTB-71: suffix invocation and traversal work

Owners: `docs/research/fdsa-tree-accumulator-invocation.md`, `docs/research/fdsa-tree-traversal-work.md`.

The append-free suffix operation is a function-valued ordinary fold. It invokes the right child first; the left receives the actual returned suffix with the root label consed. Append occurs in the independent value specification. Theorems quantify over every suffix, including recursively returned suffixes. Its natural invocation cost is `e*(2*n+1)`; a proportional linear bound retains the positive-size premise. Nil, zero entry, empty labels, duplicate occurrences and right-first traces remain part of the domain.

Construction of the function and invocation of the returned function are separate measured programs. One use and two actual uses charge their corresponding operations; repeated application is not memoization or physical sharing. Comparing materialize-then-append with suffix invocation requires all-suffix resource observations: empty-suffix agreement is insufficient. Tail position alone does not prove constant stack space.

Let `A(t)` sum the sizes of all left subtrees. The canonical observation is a fold; a private paired summary does not create a second public size carrier. Retain map invariance, repeated-child occurrence behavior, sharp triangular bounds, labelled chains and complete-tree families. A fixed reached-callback cost `d*numNodes(left)+c` gives actual total work

```
e*(2*n+1) + d*A(t) + c*n.
```

The callback condition ranges over actual returned summaries from arbitrary finite child trees. Zero coefficients are permitted. Quadratic left-chain and linear right-chain results use the standard asymptotic interfaces and their explicit boundary cases. They do not imply quadratic work for every input or callback.

Retain the different single-append, literal right-associated, left-associated and full annotation programs, including terminal append charges and the three cache-helper charges. The same size, height and inorder can accompany different work. Materialize-then-append costs `4*n+2+A(t)` while construction-inclusive `buildOnce 1 1` costs `4*n+2`; their values agree for every suffix. Right chains give full measured-result equality; left chains expose the exact excess. The nonempty leaf-labelled `Bracketing.Tree` copied-cell model remains distinct from node-labelled `BinaryTree` and its terminal-invocation tariff.

## CTB-72: structural observations and weighted paths

Owner: `docs/research/fdsa-tree-structural-weighted.md`.

Keep the independent structural label set, ordered preorder and canonical inorder; membership, length and arbitrary-map bridges connect their meanings without defining one specification as the other. Structural `Subtree` has empty/self containment, transitivity and the source set recurrences. `Complete` and `AlmostComplete` inherit along arbitrary structural descendants using the existing shape predicates. No label equality or inhabitance is required.

Natural node-weight observations retain independent `sumTree`, `wpld`, `wpl0` and `wpl` recurrences. For every depth,

```
wpld d t = d * sumTree t + wpl t.
```

This uses root depth plus one, unlike Huffman's leaf-depth convention. Nil, singleton root weight, zero root weight, arbitrary depth and equal total weight with unequal path length prevent conflating the observations. The value equation is not a runtime improvement theorem.

## CTB-73: ordered observations and abstract sets

Owner: `docs/research/fdsa-tree-search-observations.md`.

Ordered-tree `entries` uses canonical `Trees.inorder`, retaining existing clients. Raw `Contains` and `All` correspond to the independent set observation even for unordered trees. Structural orderedness is equivalent to strictly pairwise ordered inorder under the stated relation hypotheses: the forward argument uses transitivity; the converse structural argument does not add it. Keyed results order keys without ordering payloads or requiring key injectivity. Nondecreasing input alone does not meet a strict BST contract.

Observer congruence transports `AbstractSet.Laws` while fixing operations and validity. Observer equivalence is needed only on valid states, and valid outputs are obtained from the actual empty/insert laws. The baseline and candidate insertion realizations compose through existing `Laws.insertSquare` and relational composition. Repeated insertion words, an unordered tree, bad descendants, unordered payloads and repeated keys exercise the boundaries. A lawful nonvacuous instance whose observers disagree on invalid states demonstrates why global observer equality is unnecessary. The semantic bridge does not equate comparison counts or sharing.

## CTB-74: enumeration, levels, reconstruction and rose trees

Owner: `docs/research/fdsa-tree-traversal-exercises.md`.

Enumeration is an actual deterministic list program with prescribed-inorder soundness/completeness, set correspondence and `Nodup` even for repeated labels. Preserve left-spine insertion/removal, disjointness and small enumeration orders. It needs no label equality or inhabitance, and is not replaced by noncomputable set enumeration.

Level collection uses one structural traversal with an aligned append merge preserving unmatched tails; its collector has no depth parameter, height loop or numeric arithmetic. Preserve exact length, all-index default-empty correspondence and bounded optional lookup. One traversal does not imply linear total list work.

The executable `Option` reconstruction uses decidable equality and the first root occurrence, with decreasing recursive domains. Both the optional parser and its explicit empty-tree fallback round-trip under preorder `Nodup`. Missing, surplus and inconsistent traversals remain failures. Preserve the same-label-multiset impossibility consequence, repeated-label ambiguity and the parser's actual selected shape. Do not strengthen this to universal parser soundness or an exact failure characterization without a proof.

The minimal labelled rose carrier has an ordered list of children. Mirroring recursively mirrors each child and reverses child order; nested involution follows. Asymmetric and repeated-child cases remain. The unlabelled attach-based LCA carrier is a different interface.

The connected public client states: if `t ∈ enumTree xs` and `preorder t` is duplicate-free, then `reconstruct? (preorder t) xs = some t`. Its distinctness premise is essential.

## CTB-75: consuming balance and whole-program costs

Owner: `docs/research/fdsa-tree-balancing.md`; shape owner: `Applications/Trees/Shape.lean` and `Applications/Trees/BalanceShape.lean`; composed clients: `Examples/TreeBalanceSearch.lean` and `Examples/TreeBalancePipeline.lean`.

The `Option` balancer consumes a left prefix, then obtains the root and right recursive input from the actual returned suffix. `take`/`drop` are specifications, not replacement execution. Zero requests return nil and the untouched input. Failure is exactly undersized input. The nil-fallback wrappers retain conditional requested-size formulas. All occurrences and order survive; labels require no order, equality or inhabitant.

Measured `balRun` erases unconditionally, including failures. On success it charges `2*n+1` entries under the declared tariff; failed `balRun 1 []` is a separate boundary. Primitive arithmetic and projections in that tariff do not establish machine arithmetic or bit complexity.

A reusable cross bound for unrelated label types is

```
AC(s) ∧ AC(t) ∧ s.numLeaves ≤ t.numLeaves + 1
  → s.height ≤ minHeight t + 1.
```

Its proof uses `height = Nat.clog 2 leaves`, `minHeight = Nat.log 2 leaves`, the strict next-power bound and `Nat.clog_le_of_le_pow`. Actual leaf counts are positive, including nil's one external leaf. Applying both cross bounds and both child AC bounds yields the sufficient adjacent-leaf-count constructor criterion. This is not the exact Exercise 4.8 characterization.

A successful positive request `n=k+1` has child requests `m=(k+1)/2` and `k-m`. Their leaf counts are `m+1` and `k-m+1`, with `R≤L≤R+1`. Success alone implies the necessary input length. Induction must retain the actual suffix-fed right call. A result has `n+1` leaves, yielding both discrete heights and the source real logarithm floor/ceiling formulas. Nil-fallback wrappers are almost complete even on failure, but formulas in the requested `n` still need sufficient input. In particular `balList 1 []` has height zero. Counts 0, 1, 2, 3, 4, 7 and 8 give `(height,minHeight)` respectively `(0,0)`, `(1,1)`, `(2,1)`, `(2,2)`, `(3,2)`, `(3,3)`, `(4,3)`; the ten-node figure gives `(4,3)`. Powers-of-two shorthand must retain the `k=0` boundary.

The strongest full-list ordered interpretation is `Ordered (balanceList xs) ↔ xs.Pairwise (· < ·)` with the relation assumptions of the ordered owner. Successful-prefix versions use `take n`; tree rebalancing preserves orderedness and the independent label set. Keyed payloads need no payload order or injectivity. Repeated labels remain legal balancing inputs while refuting strict-BST claims. Height optimality is not runtime optimality, and its converse does not characterize almost completeness.

For actual frontend-to-consumer compositions, let `N=t.numNodes`, `A=leftSizeSum t` and `n≤N`:

| Frontend | Frontend work | Work including `balRun n` | Full request |
| --- | --- | --- | --- |
| Literal right-associated two-append | `5*N+1+A` | `5*N+2*n+2+A` | `7*N+2+A` |
| Single append | `3*N+1+A` | `3*N+2*n+2+A` | `5*N+2+A` |
| Direct suffix invocation | `2*N+1` | `2*N+2*n+2` | `4*N+2` |
| Construction-inclusive accumulator | `4*N+2` | `4*N+2*n+3` | `6*N+3` |

The programs pass actual returned lists through `Resources.bind`. Their erasure is unconditional and their successful suffix/cost laws preserve the domain. Do not replace the bare single-append frontend with materialize-then-append, which executes another full-list append even for an empty suffix. At `N=n=0`, literal/direct cost two and staged cost three. For full nonempty inputs the literal-minus-staged difference is `N+A-1`; staged construction adds `2*N+1` to direct invocation. There is no uniformly cheaper policy across the omitted boundaries.

## CTB-76: completeness, maximal subtree and exact constructor law

Owner: `docs/research/fdsa-tree-completeness.md`.

One canonical fold computes `(completeFlag,height)` with nil `(true,0)` and node height `max hl hr+1`; the flag combines child flags and equality of natural heights. Height projection and reflection refer independently to `BinaryTree.height` and `Trees.Complete`. No label equality, inhabitance or classical executable predicate decision is introduced. The checker and `Bool × Nat` cache use this same algebra. Generic cache laws supply constructor preservation and reader correctness over every descendant. A local reader/constructor is distinct from a complete annotation traversal.

The maximal-complete-subtree fold retains the reconstructed original, shape summary, selected descendant and selected height. It selects the whole tree when its flag is true; otherwise it chooses the taller child result with an explicit deterministic tie policy. It never compares labels/trees, enumerates subtrees, calls the whole-tree checker on children or runs an extra child traversal. Original and shape projections have unconditional fold-fusion equations; selection correctness requires the invariant of reachable fold results. That invariant includes structural containment, completeness, exact stored height and maximality against every complete descendant. Nil and the parent are included; equal-height maxima need not be unique.

The observable tie fixture has left child `node 1 (node 2 nil nil) nil` and right child `node 3 nil nil`; choosing the singleton rooted at 2 distinguishes a left tie. Unit-labelled equal winners would not. Structural containment establishes no allocation or physical-sharing theorem.

Exercise 4.8 requires exactly

```
AlmostComplete (node a l r) ↔
  AlmostComplete l ∧ AlmostComplete r ∧
  (l.height = r.height ∨
   (l.height = r.height + 1 ∧ Complete r) ∨
   (r.height = l.height + 1 ∧ Complete l)).
```

The right side contains only the allowed child predicates, heights and arithmetic; minimum height can occur inside the proof. Parent AC gives `max hl hr ≤ min ml mr+1`. If `hl=hr+1`, its cross inequality and `mr≤hr` force `mr=hr`, hence completeness of the shorter child. The symmetric and equal-height cases give the other alternatives and the converse. Existing `localBalanceCounter` with `almostFour` and `rightTwo` refutes the weaker child-AC/height-difference formula; establish the actual child-AC premise rather than substituting sibling balance. Preserve nil and every branch boundary.

## CTB-77: raw maximum caches and optional adapters

Owner: `docs/research/fdsa-tree-maximum-cache.md`.

The source carrier is `BinaryTree (α × α)`: nonempty annotations are raw `α`. Its reader yields none exactly for nil without a validity assumption. The actual smart node starts with its real key and combines present child annotations, never an invented bottom/default. Readers and adapters need no order; local construction and transport need only `Max α`; greatest-element semantics uses the stated lawful linear order. Recursive validity is stronger than a correct root and is preserved only under the child hypotheses.

Lift maps raw annotations to `some`, preserving keys and shape. Reader, erasure and smart-node compatibility plus exact validity equivalence connect it to `Trees.Cached.Valid none combine`. Generic smart-node and reader laws supply source correctness; the independent whole-tree fold ignores stored annotations. Projection uses each node's own key as the optional fallback. Projection after lift is unconditional. Generic validity is sufficient, not necessary, for lift after projection and projected validity: an incorrect all-some cache also round-trips. A node annotated none refutes an unconditional inverse. The exact representation condition is presence at every actual node; no new general framework or unused predicate is needed merely to state this example.

Generic annotation is an actual adapter client. Independent maximum semantics uses canonical inorder and standard `List.max?`, retaining the distinction from the WithBot-valued `List.maximum`. The bridge requires both attainment and greatestness:

```
mx t = some m ↔ m ∈ setTree (erase t) ∧
  ∀ x ∈ setTree (erase t), x ≤ m
```

under valid raw caches. A loose bound or a reader that silently recomputes the whole tree is insufficient. Preserve the arbitrary-map image law `setTree (t.map f) = f '' setTree t` without injectivity or label equality. Negative keys `-5,-2,-9` expose invented-zero defaults. Repeated maxima, asymmetric children, nil, forged descendants and numerically wrong all-some caches preserve the intended boundaries. Maximum observations forget order/multiplicity; erasure/inorder correspondence must retain them.

## CTB-3 and CTB-4: VFA source qualification

Owner: `docs/research/vfa-coverage.md`. Exact primary identities and all four exercise names are retained in the ticket projection. The Preface supplies no theorem/exercise package; optional and advanced exercises remain within whole-book scope. Source prose qualification is not a machine-checked whole-book theorem.

The Perm map covers all 30 lexical records, four exercises, surrounding mathematical prose, the two replaced teaching attempts and the three originally admitted exercises. Records are not theorem counts. `maybe_swap` changes only the first two entries, preserving empty/singleton inputs, equality and arbitrary suffixes. Its generic permutation law needs no comparator laws; idempotence uses asymmetry; first-pair correctness uses a separate two-branch relation. It does not sort the entire list. Preserve arbitrary payloads/maps/universes and the comparison-preserving map condition.

Arithmetic examples retain Nat domains, truncated subtraction and the `k=0` counterexample, including opaque function/product expressions. Five Boolean/proposition reflection laws retain both branches through proof-carrying decisions. The butterfly example allows repeated variables; arbitrary-list permutation, non-permutation and four-entry examples retain their exact statements. Extra permutation properties consume their real public laws; a grading stub supplies no theorem.

Rocq's source Forall is inductive; the relevant Lean `List.Forall` is recursive conjunction. `forall_iff_forall_mem` uses list recursion and `List.Perm.mem_iff` uses permutation induction. Their composition preserves universal predicate transport without claiming an unwritten duplicate induction proof. The checked-prefix client uses `OrderCertificate.adjacent_correct` and `firstPair_iff_chain_take_two`. `TextbookSorting` consumes comparator-independent permutation and sorting uniqueness/synchronization, retaining keyed-record observations and the antisymmetry boundary. Value agreement does not remove equal-key payload order or imply equal costs.

## Deferred book requirements

The ticket projection retains the whole VFA, FDSA and PFDS programmes. This intake does not close the later chapters. In particular, total maps need not provide partial-map observations; unrestricted function multisets need not have finite support; source selection/alternating merge sorts retain their stability counterexamples; positive-key transport, unary comparison work and state-preserving queue-peek counterexamples remain distinct tasks.

PFDS requirements preserve actual evaluator work and persistent histories, delayed construction versus forcing, body entries versus cache writes, exception/reentry boundaries, allocation timing, operation schedules and all source variants. Log-star bounds are not logarithmic or constant bounds. Lazy rebuilding and algorithm initialization costs are mathematical requirements, not environment records. The retained-version amortization failures, pending-block `[4,6]` counterexample, corrected deque singleton cases and catenation's lost-element counterexample remain explicit in their chapter tickets. Existing tree invocation costs do not discharge the queue/suspension integration in #564.

## Projected source records

Each row identifies the source content from which the mathematical projection was made. The named owner contains the detailed final statement map.

| Source path | SHA-256 | Mathematical owner |
| --- | --- | --- |
| `work/evidence/CTB-2-CORRECTIONS-r2.md` | `2843effa1ce276ed197f5df6e4c1b3066661b32c02363af6372e37c369ccb324` | `docs/research/fdsa-tree-fold-resource.md` |
| `work/evidence/CTB-2-STATEMENTS.md` | `db97aa086a17f03fa7e8049735a2d1ab7caace35537a91228f1ce8193a6a2a1a` | `docs/research/fdsa-tree-fold-resource.md` |
| `work/evidence/CTB-23-IMPLEMENTATION.md` | `8b0b8534f48ee80bafdd3bc2449d22590e47bfe51b574ff22532eb2cc43aa86d` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/CTB-23-ROWS-1-37.json` | `5869f425205da7d4d9c8fa2699453814ce29d3e76c31253d774aaaba2dc1a844` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/CTB-23-ROWS-1-37.md` | `ba36ddde98af3f0f99aa7b47962b634cc4af05e850ade16dae71bd2785d1548d` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/CTB-23-ROWS-38-76.json` | `8f90763b0111c002e725b8a3009c4a0d5fb006cea7aadd4ebe979ac09c928a63` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/CTB-23-ROWS-38-76.md` | `b0d01dcd5fab4bf3415ef88f93c097d8101afb88414958738b994284b59ce324` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/CTB-4-AUDIT-PLAN.md` | `0c9707d92a72ac47cbe741894dfa8003eec1d5cf9ef540a5ca1b9ac40918c5dd` | `docs/research/vfa-coverage.md` |
| `work/evidence/CTB-4-IMPLEMENTATION.md` | `415db6a7853c527c7882e828b5d930ee6d105bff1343d725f8063f0d8a4783d3` | `docs/research/vfa-coverage.md` |
| `work/evidence/CTB-4-PREPARATION.json` | `b3025e402ecce91a484cabcc4b0c5da8269aeea58f5d6485a65839b26ae7e8a7` | `docs/research/vfa-coverage.md` |
| `work/evidence/CTB-4-PREPARATION.md` | `d827f6221738fc9cd40a7d55b595787891b4cffe88a1f79a367d9f54693b20ab` | `docs/research/vfa-coverage.md` |
| `work/evidence/CTB-70-IMPLEMENTATION.md` | `51724a57661f3e3fac3a6022556623b2f088521bce5b8cab825b75e5e9398944` | `docs/research/fdsa-tree-accumulator-invocation.md` |
| `work/evidence/CTB-71-IMPLEMENTATION.md` | `1dda891ec61041ae5156c4671500988d6b99af26c86ac261c911496417508249` | `docs/research/fdsa-tree-traversal-work.md` |
| `work/evidence/CTB-71-PREPARATION.md` | `956bbc9b9212db9d0ff53f2d556920de4718acfc9e36ed65890f96ad4013375a` | `docs/research/fdsa-tree-traversal-work.md` |
| `work/evidence/CTB-72-IMPLEMENTATION.md` | `f00cbc0c43361ba7ee3c18d41ff37ced711631c38f9ed1037c2687f2fee1d352` | `docs/research/fdsa-tree-structural-weighted.md` |
| `work/evidence/CTB-72-PREPARATION.md` | `8500417bf017050c6c3817118013488f435f0e1296ec3703d21a8f245573a390` | `docs/research/fdsa-tree-structural-weighted.md` |
| `work/evidence/CTB-73-IMPLEMENTATION.md` | `e0433211d22c6681bb50bcd127cb15eb7ff1a26f6f2c26314165f9a51f0cb5ec` | `docs/research/fdsa-tree-search-observations.md` |
| `work/evidence/CTB-73-PREPARATION.md` | `0b7d28a282809a85921c4a90fc2044cb538c55d1914cc7e4eeb313e012f968dd` | `docs/research/fdsa-tree-search-observations.md` |
| `work/evidence/CTB-74-IMPLEMENTATION.md` | `0d8526827b21070ae41bf9ce13ca44256b3419281f05b42791c4e99955aef1e1` | `docs/research/fdsa-tree-traversal-exercises.md` |
| `work/evidence/CTB-75-IMPLEMENTATION.md` | `0d5a165a828e271948f254a87dc1da277d2d1de5c769ed028af9d20e9d4bc1a4` | `docs/research/fdsa-tree-balancing.md` |
| `work/evidence/CTB-75-core-IMPLEMENTATION.md` | `e1d68451c025f030e1c59aebb0f350dccd23a53a1fa0add17488dd5d69bc6607` | `docs/research/fdsa-tree-balancing.md` |
| `work/evidence/CTB-75-cost-component.md` | `838c85cca781908763100f031ba7b40ade42267e3845a429990fcd7a7171de9d` | `docs/research/fdsa-tree-balancing.md` |
| `work/evidence/CTB-76-IMPLEMENTATION.md` | `3ea8e8b1c0493e6b9249f1d93941f913ce35af1c7e06b12006d662b305f38f32` | `docs/research/fdsa-tree-completeness.md` |
| `work/evidence/CTB-76-core-IMPLEMENTATION.md` | `0f77c15fd18e7505a085ec39cc9aabd483680f0d3742153a80b12d3a935b2ba3` | `docs/research/fdsa-tree-completeness.md` |
| `work/evidence/CTB-76-mcs-IMPLEMENTATION.md` | `ceba1f7eca78945d03c504988bb2280bbd4f63f751093463eeaea4f7931f363b` | `docs/research/fdsa-tree-completeness.md` |
| `work/evidence/CTB-77-IMPLEMENTATION.md` | `55c1bbc4f47c2659765e3462bafa220994ee50b6c68ff1d99061f579ec2671e2` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/CTB-77-core-IMPLEMENTATION.md` | `e7451ae43bb45ec287acfa12667b230e50ad6631b83c4864ab74c0df29d708f2` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/CTB-77-order-IMPLEMENTATION.md` | `169b9def00775eead89dde7ba00cdff2effd56dc0078d30f89c44eb656562d4c` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/FDSA-C04-BALANCE-PREPARATION.md` | `a5129ce21b7d511b82f5be47a6b47ce2a40f2daa118c870031daaa308f74663d` | `docs/research/fdsa-tree-balancing.md` |
| `work/evidence/FDSA-C04-BALANCE-SHAPE-ASSESSMENT.md` | `c1fd9fc99875e081ec77f6d4826d1410331ee14ae407b2cd48ebc3e33c76e67d` | `docs/research/fdsa-tree-balancing.md` |
| `work/evidence/FDSA-C04-COMPLETENESS-PREPARATION.md` | `c454864128b836c67a60df6619052486c08fffd470328d9c23e41565997c5c35` | `docs/research/fdsa-tree-completeness.md` |
| `work/evidence/FDSA-C04-EXERCISES-PREPARATION.md` | `c8d15c90597929f35e9ce02269a2f63ffb689faef2c7ad49e0bd04d48d6e7fcd` | `docs/research/fdsa-tree-traversal-exercises.md` |
| `work/evidence/FDSA-C04-MAXIMUM-CACHE-API-NOTES.md` | `d1190a3d932a8103a8bf5f049f13373d48045bfbf0b5e814a6ddb8c62cedad6c` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/FDSA-C04-MAXIMUM-CACHE-PREPARATION.md` | `c74ba1090a91f87bab103372c7aaa1dcc1ba34af67125ecc991e05e5a5aa2a70` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/FDSA-C04-RECOVERY-NOTES.md` | `30ee38c6413a26a0d0863e9b11dd736ece42a7c666e75fcba0bce206a84100ad` | `docs/research/fdsa-tree-fold-resource.md`, `docs/research/fdsa-tree-accumulator-invocation.md`, `docs/research/fdsa-tree-traversal-work.md`, `docs/research/fdsa-tree-structural-weighted.md`, `docs/research/fdsa-tree-traversal-exercises.md`, `docs/research/fdsa-tree-balancing.md`, `docs/research/fdsa-tree-completeness.md`, `docs/research/fdsa-tree-maximum-cache.md`, `docs/research/fdsa-chapter04-coverage.md` |
| `work/evidence/FDSA-C04-REMAINING-DESIGN-ASSESSMENT.md` | `a6ff834066f0278e557f3d2aa702542e83d8188522e491877dba2194e6b5d7e8` | `docs/research/fdsa-tree-completeness.md`, `docs/research/fdsa-tree-maximum-cache.md` |
| `work/evidence/FDSA-C04-ROW-RECONCILIATION.json` | `e61c65b92d41e5d1b485a98fed005c8637c0d39a10bcda14a4766771e0675ba9` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/specs/CTB-23.md` | `514c0ffc7392a0c5a58d344c580cc402a5e34a0f5db8bc514f05219395006043` | `docs/research/fdsa-chapter04-coverage.md` |
| `work/specs/CTB-4.md` | `47cc596442e1e0dc70da848bd6e99afb0b596539710c660471f19aef95b645cd` | `docs/research/vfa-coverage.md` |
| `work/specs/CTB-70.md` | `13528c3bf0e02715b95a36b2ea088057b2f44cbb063f674e38f28e9cefa1cd46` | `docs/research/fdsa-tree-accumulator-invocation.md` |
| `work/specs/CTB-71.md` | `5afe0dbf2a5b5152f79019fdf8f3666ae71fbc46801f43397e77d2d0c740232a` | `docs/research/fdsa-tree-traversal-work.md` |
| `work/specs/CTB-72.md` | `f0d397cd2eb455ea9a0f92d161ed9b9a62e5d3d9331872a7d6d5f0b269713e19` | `docs/research/fdsa-tree-structural-weighted.md` |
| `work/specs/CTB-73.md` | `2422721dac3c2ffcee8756033cffea3d6d17cda4a0eccba4c3714a87370b6dfa` | `docs/research/fdsa-tree-search-observations.md` |
| `work/specs/CTB-74.md` | `b6a1b78c154bbd8cc26a931706c859f820f88f0394a540a8e78f3d91514fe273` | `docs/research/fdsa-tree-traversal-exercises.md` |
| `work/specs/CTB-75.md` | `c538e0e070bbaa9d6d9d31ca0664cd043c475c2db903d41408a37a8934067fe8` | `docs/research/fdsa-tree-balancing.md` |
| `work/specs/CTB-76.md` | `c579ad37c534607f6fe29fbc49750a7a0070d43e9ea0b261df7603e2a494dc5b` | `docs/research/fdsa-tree-completeness.md` |
| `work/specs/CTB-77.md` | `1360cb6f8563e234bf2fcb8d5dd7aeb3296de93628798c8f13bd90c5a64ce6e8` | `docs/research/fdsa-tree-maximum-cache.md` |
| `work/specs/CTB-78-REQUEST.md` | `f7ea4cd87904260bfa309f3a962a02cde7cf79b098609d692367778404d3cc56` |  |
