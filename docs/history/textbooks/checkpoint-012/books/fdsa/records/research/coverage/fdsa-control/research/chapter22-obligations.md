# Chapter 22: Skew Heaps — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-022`.

**State: queued; source preparation only.** This inventory covers printed
pp. 253–256 of the pinned July 27, 2026 book: every merge equation, the
inherited priority-queue operations, all correctness and amortized claims,
the proof of Lemma 22.1, and Exercise 22.1. Printed p. 256 is blank. No Lean,
Git, ticket or acceptance state was changed; no build or additional
implementation/review loop was run.

## Sources and exact pins

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 22 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; PDF pp. 259–262. Printed pp. 254–255 were also visually inspected for the integer potential and the cost/proof equations. |
| Direct companion implementation | <https://isa-afp.org/entries/Skew_Heap.html>; <https://isa-afp.org/browser_info/current/AFP/Skew_Heap/Skew_Heap.html>. |
| Fixed implementation archive | <https://isa-afp.org/release/afp-Skew_Heap-2026-10-26.tar.gz>, SHA-256 `0aa18ccafebd4767acc96ab29d3b653faaaf437fdfa7912f49fa9e29ed3f0437`. `Skew_Heap.thy`, 2,576 bytes, SHA-256 `212435f75ba99eb103c274cae4909ee4ac272add055ac3ffd1665eda7ea3a114`. |
| Direct analysis | <https://isa-afp.org/browser_info/current/AFP/Amortized_Complexity/Skew_Heap_Analysis.html>. |
| Fixed analysis archive | <https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz>, SHA-256 `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`. This supporting snapshot postdates the manuscript. |
| Analysis theory | `Skew_Heap_Analysis.thy`, 7,443 bytes, SHA-256 `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b`. |
| Framework support | `Priority_Queue_ops_merge.thy`, SHA-256 `1878defbd25e6fa4eb9d269d6da36f31049ed9e050586fab8203cd498e4488ea`; `Amortized_Framework.thy`, SHA-256 `74376411045129de46686fae882364cda484ce0b3d8b5069b1b085c96ea7d681`, both in that fixed analysis archive. |
| Shared heap interpretation | Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, `src/HOL/Data_Structures/Heaps.thy`, SHA-256 `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`; `Priority_Queue_Specs.thy`, SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`. |
| Shared tree support | Same Isabelle revision: `src/HOL/Library/Tree.thy`, SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`; `Tree_Multiset.thy`, SHA-256 `90524399a3894d8646c21377429a096345a0ddede243d966f8dd141853228508`. Fixed raw URLs use <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/> followed by this revision and the given source path. |
| Licenses | AFP BSD license SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`; shared Isabelle BSD-3-Clause copyright SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Retain relevant notices for translated source. |
| Lean reuse | Inspected conaled `1aabd512284fe86254278ac631eda061d311050b`; relevant existing APIs were already present at `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`, Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

The full implementation and analysis theories were read, including the later
framework instantiation. A scoped scan of these two theories, `Heaps.thy`
and `Priority_Queue_ops_merge.thy` found no `sorry`, `oops`, `axiomatization`
or `admit`; this is not an Isabelle rebuild or independent proof audit.
The implementation additionally defines `merge2`, which continues down a
nonempty remaining spine when the other input is empty. The book uses
`merge`, and neither value identity nor cost identity with `merge2` is
assumed. Porting that extra algorithm is not required by a displayed book
definition or assertion.

## Carrier, assumptions and reuse

Write `E` for the empty tree and `N(l,a,r)` for a node, `n(t)` for labelled
node count, `ell(t)=n(t)+1` for empty-leaf count, and `M(t)` for the multiset
of labels. Lean's existing `BinaryTree.node` takes its label first.
Skew heaps keep no cached rank, weight or balance bit. Their only semantic
validity requirement for the priority-queue contract is heap order.

| Existing API or earlier obligation | Exact reuse and remaining boundary |
|---|---|
| `BinaryTree α` in `Mathlib/Data/Tree/Basic.lean` | Exact ordinary node-labelled carrier. Its `nil` constructor exists even for an empty label type; a new skew-tree datatype is unnecessary. |
| `BinaryTree.numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ`, `numLeaves_pos`, `height_le_numNodes` | Exact size/height observations and logarithm positivity. Use the current names, not deprecated `Tree` aliases. |
| Chapters 4 and 14 | Share the queued traversal/multiset observation, plain-tree heap order, optional root minimum and heap-to-exact-queue adapter. These are prospective dependencies, not accepted existing code. |
| `Search.PriorityInterface.Operations`, `ExactLaws`, `ExactQueue` | Correct occurrence-sensitive queue contract. A merge operation needs its two compatibility laws against the same observation and invariant; the weaker keyed interface is insufficient for insertion multiplicities. |
| `ExactQueue.add_exact`, `remove_spec`, `remove_none` | Existing client-facing occurrence and minimum laws. A source-element specialization can use item type `Unit` and priorities equal to source elements; the general interface need not order payloads. |
| `List.Perm`, `List.Perm.map`, `Multiset.coe_eq_coe`, `Multiset.coe_add` | Connect a shared traversal observation to the displayed multiset sums without discarding repeated values. |
| `LeftistQueue.combineQ_entries`, `combineQ_size`, `all_combine`, `combineQ_heap`, `deleteQ_spec` | Useful proof patterns and common semantic contracts. They are theorems about a different algorithm: leftist `fork` swaps by cached rank, whereas skew merge swaps unconditionally and uses a different recursive argument order. None proves skew execution or its time recurrence. |
| `LeftistQueue.rank_size`, `rank_log` | Existing exponential-to-log proof pattern. The leftist rankedness invariant and cached rank are not skew `lrh`/`rlh`. |
| `Resources.Measured`, `pure`, `bind`, `reweight`, `reweight_bind` | Measure the actual skew merge once, preserve its value erasure, and cast the natural work with `Nat.castAddMonoidHom Int` when matching Appendix B's signed result type. No copied arithmetic-only cost function detached from the value recursion. |
| `Resources.run`, `run_state`, `run_invariant`, `run_value_fusion` | Reuse actual unary traces and observation/invariant transport. Binary melds need the Chapter 19 input-occurrence accounting, not an uncharged second heap. |
| `Resources.charge_iff_signed`, `run_potential`, `run_cost_le` | Existing potential API is natural-valued. The integer node-count potential can be related to a natural count, but these declarations alone do not express the book's real logarithmic budget. Reuse the Chapter 19 signed/real telescoping extension rather than a skew-specific framework. |
| `Nat.le_log_of_pow_le`, `Nat.log2_eq_log_two`, `Real.log2_le_logb` | An exact route from `2^k≤ell(t)` to `(k:Real)≤Real.logb 2 ell(t)`. The inspected `Nat.le_log_of_pow_le` requires `1<b`; at `b=2` it avoids defining another logarithm. |
| `Real.le_logb_iff_rpow_le`, `Real.logb_le_logb_of_le`, `Real.logb_nonneg` | Alternative direct real-power bridge and the required monotonicity/nonnegativity. These APIs require `1<base` and positive arguments (or argument at least one for nonnegativity). All tree leaf counts are positive. |

A scoped search of current conaled applications/examples and the relevant
Mathlib/Batteries data libraries found no existing skew-heap execution to
reuse. Implementation needs only a decidable comparison; size, contents and
potential bounds do not need its order laws or a heap invariant. Heap
preservation uses the comparison/order laws; the source assumes a linear
order, while the existing generic priority interface permits the weaker
lawful linear-preorder capabilities where sufficient. Do not propagate an
unneeded payload order or `Inhabited` assumption into structural lemmas.

## 22.1 Value algorithm and priority-queue correctness: p. 253

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-001 | Skew heaps implement the occurrence-based mergeable priority-queue ADT on ordinary heap-ordered binary trees. | Reuse the shared carrier and Chapter 14 exact-queue/merge compatibility boundary. No balance invariant is promised. |
| C22-002 | `merge E t=t`. | Return the same input tree without traversing it. |
| C22-003 | `merge t E=t`. | Includes the overlap at `(E,E)` consistently. |
| C22-004 | For `t1=N(l1,a1,r1)`, `t2=N(l2,a2,r2)` with `a1≤a2`, return `N(merge t2 r1,a1,l1)`. | Preserve the **swapped recursive argument order** `(t2,r1)` and unconditional child swap. |
| C22-005 | In the other node/node branch, return `N(merge t1 r2,a2,l2)`. | Actual call is `(t1,r2)`; comparator equality belongs to C22-004. |
| C22-006 | Merge terminates on every raw finite tree pair. | Source measure `n(t1)+n(t2)` strictly decreases in both recursive calls. No heap premise. |
| C22-007 | `n(merge t1 t2)=n(t1)+n(t2)`. | Primary `size_merge`; independent of heap validity. |
| C22-008 | `M(merge t1 t2)=M(t1)+M(t2)`. | Primary `mset_merge`; all occurrences are retained, even across equal roots. |
| C22-009 | The set of labels of the merge is the union of input sets. | Primary `set_merge`, derived from C22-008; reuse as a heap-order proof helper, not as a replacement for the multiset theorem. |
| C22-010 | Heap-ordered inputs produce a heap-ordered merged output. | Primary `heap_merge`; root lower bounds and the selected comparison case justify the new node. No disjointness or distinctness. |
| C22-011 | `empty=E`. | Reuse the Chapter 14 structural empty operation. |
| C22-012 | Companion `is_empty` agrees with structural emptiness. | Inherited `Heaps.Heap.is_empty`; its multiset-emptiness law follows from the shared observation. The printed Chapter 14 figure omits this additional companion operation. |
| C22-013 | Nonempty `get_min(N(l,a,r))=a`. | Direct optional root match or nonempty proof-domain operation; valid heaps make this a minimum. Do not implement it by evaluating deletion. |
| C22-014 | Empty minimum is unspecified in HOL and has no arbitrary result requirement in Lean. | Use `none`/domain restriction, with the source correspondence asserted only on nonempty heaps. |
| C22-015 | `insert a t=merge (N(E,a,E)) t`. | Singleton is the **first** argument; this matters for equal-key shape and Exercise 22.1. |
| C22-016 | `del_min E=E`. | Total concrete convenience case; empty minimum remains unavailable. |
| C22-017 | `del_min(N(l,a,r))=merge l r`. | Remove exactly the root occurrence. Children, not the original whole heap, are merged. |
| C22-018 | Empty, insertion, deletion and minimum satisfy all base priority-queue laws, including companion emptiness. | Primary `skew_heap: Heap_Merge` and inherited `Heaps.Heap`/`PQM` interpretations. Use the Chapter 14 eight-law mapping, with validity/nonempty premises where applicable. |
| C22-019 | Merge satisfies multiset addition and validity preservation for the mergeable ADT. | C22-008 and C22-010 give the two extra laws. Source order is a linear order; a generalized payload/priority implementation must show its specialization. |
| C22-020 | Duplicate insertions remain separate occurrences, and deletion removes one minimum. | A repeated-key client is required for the intended observation; a set-only queue cannot discharge this interface. |

## Exercise 22.1 and absence of a worst-case balance invariant

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-021 | For every k, supply k numbers whose successive insertion from empty yields height k. | Choose `List.replicate k 0`; the exercise imposes no distinctness premise. A decreasing sequence of fresh minima is an alternative. |
| C22-022 | Prove the chosen sequence yields a left chain: `L0=E`, `L(k+1)=N(Lk,0,E)` and `foldl (fun t a => insert a t) E (replicate k 0)=Lk`. | C22-015 and the equality branch C22-004 reduce each nonempty step to `merge Lk E=Lk`. This is an algorithm-specific inductive proof, not just an existential height bound. |
| C22-023 | `height(Lk)=k` and `n(Lk)=k`; each Lk is a valid heap. | Structural recursion and reflexivity of the element order; covers k=0. No balanced-tree theorem applies. |
| C22-024 | Despite such shapes, insertion and deletion have amortized logarithmic bounds. | Retain the genuine mathematical claim via C22-058–065 and actual trace composition. Height alone does not prove any individual operation is slow; the repeated-key insertions here cost only 1 initially and 2 thereafter in the source tariff. |

## Appendix B.10 execution correspondence

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-025 | `TM : Tree α → Tree α → Nat`; either empty input gives cost 1. | B-053 and generated `T_merge`; returning an entire nonempty input does not traverse it. |
| C22-026 | Node/node cost is 1 plus the cost of the actual selected recursive call, `(t2,r1)` or `(t1,r2)`. | Match C22-004–005 exactly. Comparison and constant reconstruction are not separately charged under this source recursive-entry tariff. |
| C22-027 | A measured merge erases to the value merge and satisfies C22-025–026 on every input pair. | Missing exact execution/cost correspondence; equality of contents or final queue behavior does not suffice. |
| C22-028 | Raw `TI a t : Int` is `(TM (N(E,a,E)) t : Int)`. | B-054 and `T_insert_def`; the signed type is intentional, and the insertion wrapper adds zero. |
| C22-029 | Raw `TD E=0`; raw `TD(N(l,a,r))=(TM l r:Int)`. | B-055 and `T_del_min_def`; no deletion-wrapper tick. |
| C22-030 | Raw insertion/deletion costs remain nonnegative despite their integer codomain. | They are casts of natural measured work; empty deletion is zero. Potential subtraction below uses signed arithmetic rather than natural truncated subtraction. |
| C22-031 | The later AFP framework uses a distinct tariff: Empty 1; Insert `TM(singleton,t)+1`; Delete 1 at E, otherwise `TM(l,r)+1`; Merge `TM(t1,t2)`. | Primary `cost`; preserve a named bridge to the raw counts. The source's corresponding insertion/deletion budgets have `+2`, not the book's `+1`. |

## 22.2 Potential and spine observations: p. 254

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-032 | `rh l r : Nat` is 1 if `n(l)<n(r)` and 0 otherwise. | Mathematical shape observation; “not right-heavy” includes equal sizes. It is not a cache or an operation performed during merge. |
| C22-033 | `rh l r≤1`, and its two possible values justify casting `1-rh l r` into a signed group. | Primary `rh1`; required by the natural-difference/signed-subtraction step in the long proof. |
| C22-034 | `Phi E=0`, with `Phi : Tree α → Int`. | Exact source domain; can share a natural counting observation with an explicit cast theorem. |
| C22-035 | `Phi(N(l,a,r))=Phi l+Phi r+(rh l r:Int)`. | Counts all right-heavy nodes, not just those on a spine. No heap/order premise. |
| C22-036 | Phi is nonnegative on every tree. | Primary `Phi_nneg`, structural induction; the source framework's analysis invariant is True. |
| C22-037 | `lrh E=0`. | Natural count of right-heavy nodes on the left spine. |
| C22-038 | `lrh(N(l,a,r))=rh l r+lrh l`. | Recurse left, not right. |
| C22-039 | `rlh E=0`. | Natural count of not-right-heavy nodes on the right spine. |
| C22-040 | `rlh(N(l,a,r))=1-rh l r+rlh r`. | Natural subtraction is exact here because C22-033 bounds the indicator; recurse right. |
| C22-041 | `2^(lrh t)≤n(t)+1`. | Primary `Gexp`; induct on the tree, split the size comparison. In the increment case compare `2*(n(l)+1)` with `n(l)+n(r)+2`. |
| C22-042 | `2^(rlh t)≤n(t)+1`. | Primary `Dexp`; in the increment case `n(r)≤n(l)` yields `2*(n(r)+1)≤n(l)+n(r)+2`. This includes equal child sizes. |
| C22-043 | First inequality (22.1): `(lrh t:Real)≤log₂ ell(t)`. | Primary `Glog`; standard power/log bridge plus positive leaf count. |
| C22-044 | Second inequality (22.1): `(rlh t:Real)≤log₂ ell(t)`. | Primary `Dlog`; no heap or balance premise. |

The prose about right-heavy nodes motivates this particular potential. It
does not state a universally monotone function from total Phi to merge
time: for example, `merge E t` always costs 1 regardless of `Phi t`. The
precise mathematical relationship asserted and proved is Lemma 22.1 below.

## Lemma 22.1 and its displayed calculation: pp. 254–255

For a binary merge write
`AM(t1,t2)=(TM t1 t2:Int)+Phi(merge t1 t2)-Phi t1-Phi t2`.
All natural spine counts on the right of an integer inequality are cast to
`Int`; logarithmic inequalities subsequently cast the whole signed charge
to `Real`.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-045 | Merge amortized charge subtracts **both** input potentials, preserving signed arithmetic. | Matches the book and Chapter 19 binary-operation convention; not unary `TM+Phi(new)-Phi(first)`. |
| C22-046 | Lemma 22.1: `AM(t1,t2)≤lrh(merge t1 t2)+rlh t1+rlh t2+1`. | Primary `amor_le_long` and shorter `amor_le`; every raw tree pair, with no heap premise. |
| C22-047 | Empty-input induction cases use unchanged output, zero empty potential, work 1 and nonnegative spine counts. | At `(E,E)` the inequality is equality `1≤1`; this catches a zero-base-call mistranslation. |
| C22-048 | In the selected-root case `a1≤a2`, set `m=merge t2 r1`; expansion gives `TM t2 r1+1+Phi m+Phi l1+rh m l1-Phi t1-Phi t2`. | Exact algorithm/cost/potential unfolding; all terms are interpreted in Int. |
| C22-049 | Cancel `Phi l1` to obtain `TM t2 r1+1+Phi m+rh m l1-Phi r1-rh l1 r1-Phi t2`. | Uses the potential of the actual first input node; no monotonicity assumption on Phi. |
| C22-050 | The induction hypothesis on `(t2,r1)` bounds this by `lrh m+rlh t2+rlh r1+rh m l1+2-rh l1 r1`. | Preserve the extra 1 for the current merge entry, hence the displayed `+2` before regrouping. |
| C22-051 | Replace `rlh r1+1-rh l1 r1` by `rlh t1`. | Apply C22-033 before moving between Nat's `1-rh` and Int subtraction. This is the explicit step in the primary long proof. |
| C22-052 | Replace `lrh m+rh m l1` by `lrh(merge t1 t2)` and rearrange to the target. | Exact output is `N(m,a1,l1)`; child order matters. |
| C22-053 | The other comparison case has the corresponding complete calculation on `(t1,r2)`. | The book omits this symmetric proof case; the primary proof closes it. Cover it, rather than assuming structural commutativity of merge. |

## Logarithmic bounds and operation histories: p. 255

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C22-054 | `ell(merge t1 t2)=ell(t1)+ell(t2)-1`. | C22-007 plus `numLeaves_eq_numNodes_succ`; all leaf counts are at least 1. Specify Nat versus Real subtraction when rewriting casts. |
| C22-055 | Applying (22.1) to Lemma 22.1 gives `AM≤log₂ ell(merge)+log₂ ell(t1)+log₂ ell(t2)+1`. | Cast the integer inequality into Real and use the three separate spine bounds. |
| C22-056 | For positive x,y and base b>1, `log_b x+log_b y≤2*log_b(x+y)`; also `log₂(ell1+ell2-1)≤log₂(ell1+ell2)`. | Primary `plus_log_le_2log_plus` and ordinary monotonicity. Each summand is separately bounded by the sum's logarithm; no advanced logarithmic inequality is needed. Positivity of `ell1+ell2-1` follows from leaf counts. |
| C22-057 | `AM(t1,t2)≤3*log₂(ell(t1)+ell(t2))+1`. | Primary `a_merge`; exact book bound, valid without heap order. This is an amortized charge, not a per-call upper bound on TM. |
| C22-058 | `(TI a t:Real)+Phi(insert a t)-Phi t≤3*log₂(ell(t)+2)+1`. | Primary `a_insert`; singleton leaf count is 2 and singleton potential is 0. All signed-potential terms are cast to Real. |
| C22-059 | Empty deletion satisfies the displayed bound. | TD and potential change are both zero; `ell(E)=1` gives a positive right side. Do not manufacture a merge call in this case. |
| C22-060 | At `t=N(l,a,r)`, deletion charge is `AM(l,r)-rh l r`, at most `3*log₂(ell(l)+ell(r))+1`. | Exact potential subtraction removes the deleted root's indicator. Since `ell(t)=ell(l)+ell(r)`, this is stronger than the final displayed bound. |
| C22-061 | `(TD t:Real)+Phi(del_min t)-Phi t≤3*log₂(ell(t)+2)+1`. | Primary `a_del_min`; combine C22-059–060 and logarithm monotonicity. Keep the common `+2` in the logarithm and `+1` outside, despite available stronger nonempty bounds. |
| C22-062 | These local bounds imply the stated logarithmic amortized insertion/deletion complexity along the actual state trajectory. | Chapter 19 telescoping, with nonnegative terminal potential and explicit initial potential. For k operations and every prestate having at most N nodes, total raw work is at most `Phi(initial)+k*(3*log₂(N+3)+1)`. From empty the initial term is zero. |
| C22-063 | Binary meld composition accounts for both supplied heap occurrences and cannot spend one persistent heap's potential repeatedly for free. | Reuse Chapter 19's expression/usage-tree or live-heap-state model. The existing unary `run` over one tree is not by itself a binary-meld accounting theorem. |
| C22-064 | In the distinct AFP framework tariff, arities are Empty 0, Insert/Delete 1, Merge 2; upper budgets are respectively 1, `3*log₂(ell+2)+2`, and `3*log₂(ell1+ell2)+1`. | Primary `exec`, `cost`, `U`, `Amortized` interpretation with invariant True and real cast of Phi. Do not transfer the book's raw insertion/deletion bound unchanged to this larger work count. |
| C22-065 | The bounds provide the advertised amortized logarithmic operations without a worst-case logarithmic height invariant. | Connect C22-023's valid linear-height family to the exact costs and telescoped bounds. A separate raw worst-case cost example below makes the distinction concrete. |

## Boundary evidence, source correspondence and placement

No false displayed theorem was found in this chapter. The material hazards
are interpreting equal child sizes as right-heavy, swapping the wrong
recursive arguments, counting the wrappers under the wrong tariff,
forgetting the deleted root's potential, or assuming that a final multiset
equality establishes execution-cost correspondence.

The following small cases were independently recomputed with a literal
Python model of the displayed recursion (k through 6). They are research
sanity checks and proposed future Lean clients, not formal acceptance.

| Operation/family | Exact outcome in the book's raw metric |
|---|---|
| `merge E E` | E, TM=1, zero potential change, AM=1. |
| `insert 0 E` | A singleton, TI=1, zero potential change. AFP framework insertion cost is instead 2. |
| `insert 0 Lk`, k≥1 | `L(k+1)`, TI=2, both potentials zero, despite height increasing from k to k+1. |
| `del_min E` | E, TD=0; AFP framework deletion cost is 1. |
| `del_min Lk`, k≥1 | `L(k-1)`, TD=1, zero potential change; framework cost is 2. |
| Merge a valid right chain with labels `0,1,…,k-1` and the singleton k, k≥1 | TM=k+1, initial total potential k-1, final potential 0, AM=2; result is a valid left chain with k+1 nodes. This witnesses a linear individual merge while the amortized charge stays small. |

The exercise's repeated-number solution is permitted because the priority
queue observes multiplicities. If a distinct-number example is preferred,
inserting successive fresh minima yields the same left-chain shape; that is
an alternative solution, not a new requirement to strengthen the exercise.
Neither the potential nor the size observations should be recomputed by the
executable merge: they belong to its analysis and proofs.

Place the plain-tree skew operations and their exact priority-queue adapter
beside `Applications/Search`, sharing the earlier ordinary-tree heap
observation. Place measured execution and potential inequalities beside
`Applications/Resources`; reuse the cross-cutting Chapter 19 accounting
extension. Keep a small connected example that combines duplicate-aware
queue behavior, the measured recursion and its bound. The chapter notes'
four historical references identify the origins of the displayed algorithm
and proof; they do not state additional separate paper-wide theorem coverage.

