# Chapter 18: Dynamic Programming — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-018`.

**State: queued; source preparation only.** This note performs no Lean
implementation, build, ticket/acceptance change or remote write. Chapter 1
remains the active sequential chapter. Every coverage row is an obligation for
future checked implementation, correspondence and review.

## Sources, versions and licenses

| Source | Inspected identity |
|---|---|
| Book | Simon Wimmer, Chapter 18, printed pp. 205–225; p. 226 is blank. PDF pages 211–232, July 27, 2026 version of *Functional Data Structures and Algorithms: A Proof Assistant Approach*. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Memoization entry | Simon Wimmer, Shuwei Hu and Tobias Nipkow, *Monadification, Memoization and Dynamic Programming*, first published May 22, 2018, <https://isa-afp.org/entries/Monad_Memo_DP.html>. Pinned dated archive <https://isa-afp.org/release/afp-Monad_Memo_DP-2026-10-26.tar.gz>, 72,106 bytes, SHA-256 `6002e6377004f9705ab2bcc2c9ea161a9f140c6f4d848245b8c30f07741ecf57`. |
| Optimal BST entry | Tobias Nipkow and Dániel Somogyi, *Optimal Binary Search Trees*, first published May 27, 2018, <https://isa-afp.org/entries/Optimal_BST.html>. Pinned dated archive <https://isa-afp.org/release/afp-Optimal_BST-2026-10-26.tar.gz>, 15,254 bytes, SHA-256 `ae46784efbe4ec8979cfd2746ecfba273aa2da590bb55b081c6068f13431d9da`. |
| Direct PDF links | <https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bellman_Ford.html>, <https://isa-afp.org/browser_info/current/AFP/Optimal_BST/Optimal_BST2.html>, and the memoization entry above. The mutable browser pages are reference locators; the dated archives and file hashes below identify the inspected source. |
| Extra primitive definitions | Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, `src/HOL/Library/Extended.thy` and `State_Monad.thy`. The book deliberately omits extended-integer arithmetic equations, so their precise source semantics are material. |
| Licenses | Both AFP entries advertise the BSD license. Shared <https://isa-afp.org/LICENSE> SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`; Isabelle BSD-3-Clause COPYRIGHT SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Preserve relevant notices in adaptations. |
| Lean reuse | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; read-only workspace HEAD during this inventory `1aabd512284fe86254278ac631eda061d311050b`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. These observations do not assert acceptance of any intervening local work. Inspected Lean library files are Apache-2.0. |

### Exact companion files

Paths beginning `M/` are relative to the `Monad_Memo_DP` archive directory;
`O/` paths are relative to `Optimal_BST`. Local extracted directories are
`book-source/afp-Monad_Memo_DP-2026-10-26/Monad_Memo_DP/` and
`book-source/afp-Optimal_BST-2026-10-26/Optimal_BST/`.

| File | Bytes | SHA-256 |
|---|---:|---|
| `M/example/Bellman_Ford.thy` | 39605 | `2451d6ee91f3ab0185b3981bc5472b44527be52ab1d3f7f0afd4a4c1c0147396` |
| `M/example/OptBST.thy` | 16779 | `48f1d9c7c3f163966a4704e2f15d2007b0077a74b54c1f1c87838f95f50f7d46` |
| `M/example/Example_Misc.thy` | 4187 | `a787bc1eaa5795bea717a5a8829022c1a0e2d717f9c6b2a107a7a95c9cfc2e94` |
| `M/state_monad/State_Monad_Ext.thy` | 1503 | `0f7b6e0e37944f0f7c4ce6bf6c9aabafeb5c1e4b3f16ab22888dc8edfc0b6558` |
| `M/state_monad/DP_CRelVS.thy` | 9585 | `cc7d0f8da00b5b071e7b40c23366bc50a84e9d4e496384e3683296bd82254140` |
| `M/state_monad/DP_CRelVS_Ext.thy` | 8205 | `5c1cf3e78c1f216ee60ac9c23f87ea8d668657ab5d36ff2cc653e4a47af1ce59` |
| `M/state_monad/Memory.thy` | 6260 | `28a35fa15c7de7ff0774c7a80f4164b7b6ef411241f44a74a1c12da657de392b` |
| `M/state_monad/Bottom_Up_Computation.thy` | 5646 | `bd2a0eebede9a4c3edcb604b78e9829a15011e57be8175cbbaba8fea270c422c` |
| `M/state_monad/State_Main.thy` | 7742 | `241b2b297efd9ddf22a968c85f05d1f7eb69e1e28dd6d1419ff913571d9e7ddd` |
| `O/Weighted_Path_Length.thy` | 8063 | `c82ec0d066538e506188bbb0d584223bc5ffce780d1e602d51fde95da483036d` |
| `O/Optimal_BST.thy` | 8273 | `14a8d9cdbd5d9611043e59b51c627fbf5a131f6b9da24914e634856759d6a37a` |
| `O/Quadrilateral_Inequality.thy` | 19800 | `71be20ad2b0c1b129ca8298cfc8e0c1d0cae26db7a2d49cfa451c8b92687ef2f` |
| `O/Optimal_BST2.thy` | 17793 | `ee3071a8f2b7a12c0ad84b1672f195e8691c69e2063bb5e36af2a36c450344bb` |
| `O/Optimal_BST_Memo.thy` | 2085 | `0d695960fa89484c4155ab176d0b16353e8d88e5a1ce941ec9e3bd8c44bb505c` |
| `O/Optimal_BST_Code.thy` | 1223 | `0ac6c5e4bb4692f6a509fa35f5d8e92b5e585200541f04fa660960b22af6c807` |
| `O/Optimal_BST_Examples.thy` | 1505 | `5a3de5f9cdb9bdfe0b76dea499cd91ed767418683d50d12f7631a78438774a9c` |
| Isabelle `Extended.thy` | 8227 | `efae7ab122105a0b3836aa18cf6744ef32889b2c001c199c2092eade27f0eea2` |
| Isabelle `State_Monad.thy` | 8365 | `64594c524b12007842490b78a70b4b98b39628b21cd907af0ed17ddbf3406eba` |

The dated sources postdate the manuscript. This note does not claim the exact
book was generated from those archives. A source scan found no admission
markers in the listed core theories. The larger memoization archive contains
two `oops` commands in `heap_monad/DP_CRelVH_Ext.thy` and
`example/Min_Ed_Dist0.thy`: these abort attempted proofs rather than establish
theorems. They must not be misreported as completed results or assumed as
axioms. No Isabelle session or Lean build was run here.

Scope includes the starred §18.3, all displayed definitions and numbered and
unnumbered mathematical propositions, the graph/tree numerical examples, and
the promised efficient realizations with their actual resource assumptions.
There are **no numbered exercises** in this chapter. The AFP's additional
knapsack, edit-distance, CYK, imperative-memory and code-generator developments
are references and reusable support, not extra book chapters. This note does
not turn that entire AFP entry into a coverage requirement. It does require
the generic principles actually used by the book to have checked Lean
interfaces and meaningful executable witnesses.

## Main semantic and reuse decisions

The chapter mixes four different things: a pure mathematical recurrence,
programs evaluating it, a state-consistency proof method, and resource claims
about particular memory realizations. Each needs an explicit correspondence.
Neither extensional equality of results nor preservation of a consistent
cache proves that subproblems are retained or computed only once.

| Existing object | Reuse and limit |
|---|---|
| `Nat.fib` and its standard lemmas | The pinned Lean/Mathlib Fibonacci function uses iteration on `(a,b) ↦ (b,a+b)`. `fib_zero`, `fib_one`, `fib_add_two` and the prefix-sum identity are a strong mathematical specification and a bridge to the introductory loop. It is not the naive two-recursive-call evaluator, so its implementation cannot inherit that evaluator's call cost. |
| `StateM σ α`, standard `pure`, bind, get and set | Definitionally the same state transformer `σ → α × σ` up to the source's single wrapper constructor. Reuse the standard state monad and prove the book's run equations, rather than add a parallel monad hierarchy. |
| `Relator.LiftFun`, `List.Forall₂` | Match the function and list relators. The indexed characterization of `Forall₂` supplies the book's equal-length/indexed formula. |
| `List.mapM` | Same left-to-right state effects, but the standard executable implementation uses an accumulator and reversal. Its lawful-monad correspondence with direct cons recursion supports semantics; the two literal recurrences/costs should not be identified without proof. |
| `Mathlib.Order.WithBotTop.EInt` | It is `WithBot (WithTop Int)`, an exact ordered carrier for finite integers and two infinities. Its standard addition makes the outer bottom absorbing, so `⊤+⊥=⊥`, unlike source `∞+(-∞)=∞`. The reversed standard nesting `WithTop (WithBot Int)` is a promising exact arithmetic carrier; verify all required operations. Alternatively use an explicitly named source addition or a checked no-bottom-domain bridge. |
| `Optimization.argminLast` in `Applications/Optimization/SelectionTies.lean` | Already has `argminLast_eq_some_iff`, `argminLast_correct`, and `argminLast_cons` with the source's last-tie policy. Ordinary `List.argmin`/project `argmin` uses the first tie. The existing last selector uses reversal; its checked semantic recurrence is useful, but extra traversal and score evaluations need their own cost account. |
| `Applications/DynamicProgramming/Batch.lean` | `arrayAssign`/`arrayAssign_batch` support simultaneous row updates with bounded, distinct indices, size preservation, written values and untouched cells. Useful for a Bellman–Ford rolling-row implementation after the graph recurrence is established. |
| `Applications/Bracketing/Cached.lean` and `Bracketing/Array.lean` | Already demonstrate stored `(cost, leafCount, tree)` values and checked diagonal table refinement. Their nonempty leaf-labelled trees, split recurrence, first-tie selection and Nat/list indexing differ from the book's empty-leaf node-labelled BST with Int interval labels. Reuse the technique and common abstractions, not an asserted algorithm identity. |
| `Resources.Measured` | Existing measured bind/erasure/reweighting is the appropriate common accounting interface. `KnapsackSourceCosts` has a specific copy/case tariff, which is not a generic time model for all dynamic programs. |
| Finite maps / graph interfaces | Reuse lookup/update contracts and graph/path observations where their real types and semantics fit. A size-balanced `Std.TreeMap` is not the book's red-black memory implementation. Unit-edge shortest-path length is not signed weighted single-destination distance. No inspected project theorem directly completes the book's memoization, signed Bellman–Ford or Knuth optimal-BST development. |

For the book's abstract memory `K → Option V`, consistency makes sense even
for infinite domains. Do not strengthen all logical results to finite memory
merely because an executable realization is finite. Conversely, cost/cardinal
claims require an actual finite representation and explicit lookup/update
costs. Optional failure or a nonempty-domain witness handles partial minima,
tree roots and list weights; a blanket `Inhabited` assumption is unnecessary.

Additional precise reuse references, checked by a separate read-only agent:

- `Batteries/Control/LawfulMonadState.lean` supplies `LawfulMonadStateOf`,
  `modify_eq`, `modifyGet_eq`, `set_bind_get`, `modify_bind_modify`, and the
  lawful `StateT` instance. These are state algebra, not the missing cache
  consistency/retention theorem.
- Lean `Init/Data/List/Monadic.lean` supplies direct `List.mapM'`,
  `mapM'_cons`, `mapM'_eq_mapM` and `mapM_cons`; use the lawful-monad bridge
  for the accumulator implementation in `Init/Data/List/Control.lean`.
- `Std.TreeMap.getElem?_emptyc`, `getElem?_insert`, and
  `getElem?_insert_self` in `Std/Data/TreeMap/Lemmas.lean` supply checked map
  equations under `TransCmp cmp`. The insert equation tests comparator
  equality, so ordinary key equality needs a lawful comparator bridge.
- `Dijkstra.Core.Distance = Option Nat`, `Weights n = Fin n → Fin n →
  Option Nat`, `Walk`, `Shortest`, `toTop`, `dle_iff` and `toTop_plus` in
  `Applications/Dijkstra/Core.lean` are useful project precedents. Nat costs
  exclude negative edges. `Dijkstra/Semantics.lean` supplies `walk_iff`,
  `path_iff_route`, `shortest_iff`, `no_path_iff` against the project's
  heuristic-search semantics, with the same restriction.
- `Mathlib/Combinatorics/Quiver/Path/Weight.lean` has `Quiver.Path.addWeight`
  and `addWeightOfEPs`, with nil/cons/composition equations, over an additive
  monoid and thus over Int. Its snoc paths carry actual edges; the book's
  cons vertex lists permit nonedges through infinity. Prove that bridge
  before reusing the weight laws. These APIs establish no weighted shortest
  path theorem on their own.
- `Optimization.NetworkPaths` supports Int weights and `cost_cons`,
  `cost_append`, `paths_mem_iff`, but takes one edge from each prescribed
  layer. It is not the unrestricted graph-walk/negative-cycle model.
- `Bracketing.Array.fullTable_read`, `fullTable_entry_cached`,
  `fullTable_sourceEquations` and `fullTable_unique_solution` are checked
  table-development patterns. Their distinct recurrence/carrier/tie rules
  remain material, as the table above records.

## 18.1 Fibonacci and memoization: pp. 205–211

Write `F` for the Fibonacci specification and `Store K V = K → Option V` for
the abstract store. Let `empty` be the all-`none` map. A computational variant
must state its recursive evaluation order and whether it checks/caches base
cases. Those differences change the final store even when the result agrees.

| ID | Source obligation | Exact algorithm, domain or proof requirement |
|---|---|---|
| C18-001 | `F 0=0`, `F 1=1`, `F(n+2)=F(n+1)+F n`. | Use the existing Fibonacci specification. A separate source evaluator or checked trace realizes the two recursive calls; do not redefine the mathematical sequence unnecessarily. |
| C18-002 | Introductory imperative loop: initialize `(a,b)=(0,1)` and perform `n` updates `(a,b)←(b,a+b)`; return `a`. | Give a pure executable iteration/state analogue and prove the invariant after `k` steps `(a,b)=(F k,F(k+1))`. This supplies the explicitly asserted equivalence, including `n=0`. |
| C18-003 | Figure 18.1's recursion and the naive inefficiency claim. | Check `F 5=5`, that its naive recursion evaluates `F 3` twice and `F 2` three times. A useful exact call-entry recurrence is `C 0=C 1=1`, `C(n+2)=1+C(n+1)+C n`, hence `C n=2·F(n+1)-1`. Hardware statements about particular seconds are commentary, not portable timing theorems. |
| C18-004 | `fib₁` threads a store explicitly. Base cases write keys 0 or 1. At `n+2`, look up `n`, evaluate it on a miss, then use the resulting store to look up/evaluate `n+1`, and finally write `n+2`. | It does not first consult its own top-level key. Preserve this algorithm and the left-to-right state dependency. Its result theorem requires correct cached values actually consulted; global `cmem` is the convenient sufficient invariant. |
| C18-005 | Generic explicit-state `memo k f`: a hit returns its stored value and unchanged store; a miss runs `f m=(v,m')` and returns `(v,m'[k↦v])`. | The update uses the **post-computation** store. This p. 207 definition is the intended cache-accumulating operation, and has a direct standard-StateM realization. |
| C18-006 | `fib₂ 0=memo 0(return 0)`, `fib₂ 1=memo 1(return 1)`; at `n+2`, memoize a body that evaluates `fib₂ n`, then `fib₂(n+1)`, then adds. | Both base cases and all recursive keys consult/store the cache. Prove termination independently of cache hits using decreasing natural arguments. |
| C18-007 | Source `state S A` wraps `S→A×S`; `run_state(State f)s=f s`. | Reuse `StateM` with a trivial wrapper correspondence if the source constructor needs to be exposed. Result precedes state in the product. |
| C18-008 | `return x` runs to `(x,s)`; binding `a` to `f` first runs `a s=(x,s')`, then runs `f x` on `s'`. | Standard `pure`/bind run equations and monad laws provide the requested sequencing, without another effect implementation. |
| C18-009 | `get` returns `(s,s)`; `set s'` returns `((),s')`. | These equations distinguish reading the original state from reading after a recursive computation. |
| C18-010 | Source `memo₁` as literally printed on p. 209: read `m`; on a miss run `a`, then `set(m[k↦v])`; on a hit return the stored value. | This is a distinct defective cache program: it overwrites updates made by `a`. Retain its precise run equation and a diagnostic witness, rather than silently treating it as C18-005. |
| C18-011 | Corrected monadic memoization reads the current state again after `a`, or uses `modify` to insert into that post-state. | Show exact equivalence to C18-005 and to AFP `state_mem_defs.checkmem` with `mem_correct_default`/`mem_correct_rbt_mapping`. AFP `update` performs a fresh `get`; it does not implement the printed stale-store write. |
| C18-012 | Small lost-update counterexample. | From `empty`, let `a` store key 0 with value 0 and return 1; memoize it at key 1. Literal `memo₁` finishes with only `1↦1`, corrected memo retains both `0↦0` and `1↦1`. Both stores remain Fibonacci-consistent. Formalize this to demonstrate that consistency alone cannot certify retention. |
| C18-013 | `fib₃ 0=return 0`, `fib₃ 1=return 1`; at `n+2`, memoize the sequential evaluation of `fib₃ n` and `fib₃(n+1)` and return their sum. | Base cases are not memoized, unlike `fib₂`. Keep a literal-printing diagnostic and a corrected intended executable version, with explicit naming/disposition. |
| C18-014 | Lifted application has type `State S (A→State S B) → State S A → State S B` and runs function computation, argument computation, then the resulting stateful function. | It is not ordinary applicative application of a pure function. Define it through existing bind and prove its run equation and simplification on pure operands. AFP `fun_app_lifted` is exact. |
| C18-015 | `fib₄` replaces the two argument applications by lifted application with three layers of `return` around curried addition; its base cases stay pure. | Expand the monadic syntax and prove equality to the matching `fib₃` state transformer, retaining evaluation of `n` before `n+1`. Do not use commutativity to assert equal stores for arbitrary computations. |
| C18-016 | Value correctness of all displayed Fibonacci variants from a consistent store; empty-store result equals `F n`. | Their stores need not be equal. For example, corrected `fib₂ 2 empty` caches 0,1,2, whereas corrected `fib₃ 2 empty` caches only 2. Equality of first components is the common claim. |
| C18-017 | Memoization's avoidance of repeated non-base calculations needs a retention/domain proof. | For corrected `fib₃`/`fib₄` from empty, each key 2 through `n` is computed on at most one miss and remains cached; base calls may repeat. Under a call-entry observation, exact count is 1 at `n=0` and `2n-1` for `n≥1`. Map operations and arithmetic have separate charges. |
| C18-018 | Literal `memo₁` fails the preceding performance claim even while returning correct Fibonacci values. | At `n=5`, literal `fib₃` uses 11 recursive entries and ends with only key5; corrected uses9 and keeps keys2,3,4,5. A recurrence for literal empty-store call count is `C0=C1=1`, `C2=3`, `Cn=C(n-2)+C(n-3)+3` for `n≥3`, yielding non-linear growth. Formalize the witness and any claimed asymptotic consequence from the actual measured evaluator. |

## 18.2 Correctness through relations: pp. 211–213

| ID | Source obligation | Precise relation or inference |
|---|---|---|
| C18-019 | `dom m={k ∣ m k≠none}` and `cmem m ↔ ∀k∈dom m, m k=some(F k)`. | Equivalent option-elimination formulation: every stored value at `k` equals `F k`. No requirement that every Fibonacci key is stored. |
| C18-020 | The unrestricted-memory value theorem is false. | With `m 2=some 7`, literal or corrected `fib₄ 2` returns7 on the hit, while `F 2=1`. Keep this small checked negative example and the corrected consistent-memory theorem. |
| C18-021 | Equality consistency `v ▷ a` means: for every consistent input store, `run a m=(v',m')` implies `v=v'` and `cmem m'`. | The quantification is over all consistent stores, which strengthens the insufficient empty-store induction hypothesis. It says nothing about domain inclusion/cache retention. |
| C18-022 | General consistency `v ▷[R] a` replaces result equality by `R v v'` while retaining post-store consistency. | Generalize over result types and relation; equality consistency is its equality specialization. Reuse a common logical interface rather than a new relation for every algorithm. |
| C18-023 | Function relator `(R ⇒ S) f g ↔ ∀x y,R x y→S(f x)(g y)`. | `Relator.LiftFun` supplies this exact notion. A memoized function's codomain relation is itself consistency, producing the nested relation used by the application rule. |
| C18-024 | Return rule: `R x y → x ▷[R] pure y`. | No memory changes; holds for an arbitrary consistency invariant and any relation. |
| C18-025 | Equation (18.3): `F n ▷ a → F n ▷ memo₁ n a`. | Value/consistency correctness holds for both literal and corrected memo in the simple map model. Prove the intended corrected theorem and, for defect diagnosis, make clear why this theorem does not reject the stale-store version. General arbitrary `R` needs appropriate stored-value compatibility, not an unchecked extension of the equality rule. |
| C18-026 | Equation (18.4): `x ▷ xm` and `f ▷[(=) ⇒ (▷)] fm` imply `f x ▷ (fm · xm)`. | Runs `fm`, then `xm`, then the returned monadic function; each intermediate consistency premise is needed. |
| C18-027 | General application rule: `x ▷[R] xm` and `f ▷[R ⇒ (▷[S])] fm` imply `f x ▷[S] (fm · xm)`. | Preserve distinct source/result types and both relations. This rule is what allows curried function applications to be proved structurally. |
| C18-028 | Function-relator introduction from pointwise related outputs. | Existing `LiftFun` definition/introduction is adequate. The nested result relation must not collapse to equality of effectful functions. |
| C18-029 | Equation (18.2): for every `n`, `F n ▷ fib₄ n`, proved by the Fibonacci computation induction and the preceding rules. | Base pure cases, memo rule and two applications discharge the recurrence. Addition order in the printed proof is swapped relative to the program; mathematical commutativity is legitimate for the returned numbers but not an unproved reordering of state effects. |
| C18-030 | Equation (18.1): `(run(fib₄ n) empty).1=F n`, and the final store is consistent. | Derive from C18-029 and consistency of empty; do not use the empty-state theorem as an inadequate induction hypothesis. |
| C18-031 | General memory implementation contract supporting the same correctness relation. | AFP `mem_correct` permits lookup/update to discard entries: observed post-store is a submap of old store or old store updated at the new key, and the representation invariant is preserved. These weak laws suffice for value correctness; retained-cache and cost claims require a stronger explicit contract. |

## 18.3 Details of memoization, including the starred material: pp. 214–216

| ID | Source obligation | Exact scope |
|---|---|---|
| C18-032 | Alternative Fibonacci identity `F n = if n=0 then 0 else 1+Σ(k∈range(n-1)) F k`. | Natural truncated subtraction in `n-1`, so `n=1` has an empty sum and yields1. Reuse the existing Fibonacci prefix-sum theorem with a checked index bridge. |
| C18-033 | Define the alternative recursive evaluator by that equation and prove termination since each recursive argument in `range(n-1)` is less than `n` in the nonzero branch. | It is extensionally Fibonacci but is a different program from C18-001. Its recursion and costs cannot be inherited merely by equality. |
| C18-034 | `ifM bm xm ym` evaluates the Boolean computation and executes only the selected branch. | Use standard monadic conditional syntax with a run theorem. Do not pre-evaluate both branches. |
| C18-035 | Unconditional conditional rule: related Boolean/result computations for both branches imply consistency of the selected expression. | Preserve the arbitrary output relation `R`. |
| C18-036 | Refined conditional rule requires branch consistency only under the corresponding pure Boolean condition. | `b ▷ bm`, `(b→x ▷[R] xm)` and `(¬b→y ▷[R] ym)` imply consistency of `if b then x else y` with `ifM bm xm ym`. This guard-sensitive rule supports the well-founded recursive proof. |
| C18-037 | Direct `mapM' f []=pure []`; at `x::xs`, evaluate `f x`, then recursively map the tail, then cons the results. | Prove the exact left-to-right run recurrence. Standard `List.mapM` may be used after its semantic direct-recursion bridge; its accumulator implementation is an explicit cost adaptation. |
| C18-038 | Lifted two-argument `mapM = pure(fun f => pure(mapM' f))` with the book's nested monadic function type. | The wrapper layers make both arguments compatible with lifted application. Prove that applying it to pure `f` and pure `xs` yields `mapM' f xs`. |
| C18-039 | `list_all2 R xs ys` iff equal lengths and `R` at every corresponding valid index. | Reuse `List.Forall₂` and standard length/get characterizations. This is a relation between whole ordered lists, not membership/set equality. |
| C18-040 | Map reasoning rule: if `xs=ys` and `f x ▷[R] fm x` for all `x∈ys`, then `map f xs ▷[Forall₂ R] (mapM · pure fm · pure ys)`. | The premise is restricted to elements actually traversed, which is crucial for the decreasing-argument induction. No relation assumption on all possible inputs is necessary. |
| C18-041 | Memoized alternative Fibonacci uses the guard, lifted sum, lifted increment and mapped recursive calls over `range(n-1)`. | Repair the undefined `fibm'` printed in the map operand to the intended recursive memoized function, document that notational correction, and prove `F n ▷ fibM n`. Use corrected cache accumulation for intended efficiency. |
| C18-042 | The preceding construction generalizes from Fibonacci to any well-founded recurrence and suitable consistent memory implementation. | Provide a reusable theorem/interface with the needed recursion/lookup/update assumptions, and instantiate it for the chapter's algorithms. The book does not require reimplementing Isabelle's ML automatic transformation command in Lean. |
| C18-043 | Case combinators and higher-order functions can be handled by analogous relational rules. | A concrete sufficient scope is checked Option, product and list case rules plus the map/fold rules used below. Branch-dependent assumptions must be retained. The starred presentation is not an exemption from mathematical coverage. |

## 18.4.1 Weighted paths and Bellman–Ford recurrence: pp. 216–219

Let `V={0,…,n}` contain **`n+1` vertices**, with sink `t≤n`. Let `W u v`
take values in finite integers plus `⊤` and `⊥`. A missing edge has weight
`⊤`. The book prints `Int→Int→Extended Int` for `W` but then uses Nat
vertices; the companion consistently uses `Nat→Nat→Extended Int`.
Use that type or expose the Nat-to-Int restriction explicitly.

The source's addition is commutative and associative with `⊤` dominating
both finite values and `⊥`: if either argument is `⊤`, the result is `⊤`;
otherwise, if either is `⊥`, the result is `⊥`; otherwise add integers.
The negative-cycle correctness section assumes **no edge inside V has
weight `⊥`**. The bounded-path recurrence itself has weaker hypotheses.

| ID | Source obligation | Exact domain and proof requirements |
|---|---|---|
| C18-044 | Finite vertex interval, sink membership, edge-weight function and ordered three-way extended-integer carrier. | Preserve natural vertex numbering and signed finite edge weights. Restricting to nonnegative weights or undirected simple graphs changes the problem. |
| C18-045 | Make source addition/order explicit, including `⊤+⊥=⊤`. | Isabelle `Extended.thy` lines94–121 and `Example_Misc.Pinf_add_right` identify the operation. Verify a standard-carrier adaptation; the default addition on Mathlib `EInt` is a counterexample to an unrestricted operation-preserving bridge. |
| C18-046 | No-bottom finite-path closure and finite cancellation conditions. | Under `W u v>⊥` for vertices in V, every nonempty in-domain path weight is `>⊥`; a reachable-path weight may still be `⊤` only if it is not a real path. Cancellation `s≤s+c→0≤c` requires `⊥<s<⊤`, not arbitrary extended values. |
| C18-047 | `weight [v]=0`, `weight(v::w::xs)=W v w+weight(w::xs)`. | Empty-list weight is not specified by the book/source. Use a nonempty domain or a separately stated total extension. All OPT path arguments are nonempty, so no arbitrary default is needed. |
| C18-048 | Weight concatenation: `weight(xs++a::ys)=weight(xs++[a])+weight(a::ys)`. | This handles edge counts and cycle removal. An iterative fold is an extensional refinement with its own execution cost. |
| C18-049 | `OPT i v` is the minimum of path weights `weight(v::xs++[t])` with `length xs+1≤i` and `set xs⊆V`, together with `0` if `v=t` and `⊤` otherwise. | The singleton supplies the zero-edge path or unreachable sentinel and makes the minimization nonempty. Paths may repeat vertices; forbidding repetition would invalidate the dynamic recurrence with negative cycles. |
| C18-050 | The bounded candidate set is finite/nonempty, and the minimum is attained or equals the explicit singleton case. | Reuse finite bounded lists over a finite alphabet and finite min APIs. Bounded edge count and bounded intermediate vertices both matter. |
| C18-051 | `OPT 0 v = if v=t then 0 else ⊤`. | Immediate empty path-candidate family. Holds even if edge weights include `⊥`. |
| C18-052 | `OPT(i+1)v = min(OPT i v, min_{w≤n}(W v w+OPT i w))`. | Requires `t≤n`, as in companion `OPT_Suc`; no no-bottom edge premise is required for this bounded recurrence. Prove both inequalities, including a one-edge path and the `v=t` singleton case. |
| C18-053 | Executable `bf 0 v` is the same base; `bf(i+1)v` is `minList(bf i v :: map (fun w => W v w+bf i w) (range(n+1)))`. | The min input is always nonempty. Preserve the explicit old value at the head, all vertex candidates and evaluation order; this is not a sparse-edge relaxation algorithm. |
| C18-054 | `bf i v=OPT i v` for every `i,v`, under `t≤n`. | `bf_correct`, source lines256–270. No `v≤n` premise is needed for this value correspondence, although global graph conclusions concern vertices in V. |
| C18-055 | Monotonicity in the edge budget: `i≤j → OPT j v≤OPT i v`. | Follows from inclusion of candidate families; useful for row comparison and negative-cycle detection. Preserve the direction. |
| C18-056 | Figure18.2 and Table18.1 are checked examples. | Vertices0–4, sink4; finite edges `0→1:-1`, `0→2:2`, `1→2:5`, `2→1:-1`, `1→3:4`, `3→2:-2`, `2→3:2`, `2→4:3`, `3→4:2`; all others `⊤`. Rows0–4 are `[⊤,⊤,⊤,⊤,0]`, `[⊤,⊤,3,2,0]`, `[5,6,3,1,0]`, `[5,5,3,1,0]`, `[4,5,3,1,0]`. |

## 18.4.2 Negative cycles and the returned result: pp. 219–220

| ID | Source obligation | Exact hypotheses and conclusion |
|---|---|---|
| C18-057 | A negative reaching cycle is a closed walk `a::xs++[a]` of negative weight, with all vertices in V and a finite-weight path from `a` to `t`. | Source `has_negative_cycle` existentially quantifies that cycle and reaching suffix; it does not require the cycle to be simple. The source's shorter name still includes reachability to the sink. |
| C18-058 | Reachability admits a simple/shortened path with at most `n` edges when `t≤n`. | Pigeonhole/cycle removal supplies the bound for `n+1` vertices. For `v=t`, use the zero-edge path. Preserve the distinction between a path's number of vertices and edges. |
| C18-059 | The vertices on a negative reaching cycle all have finite `OPT n` under the no-bottom edge premise. | Upper finiteness follows from reachability/shortening; lower finiteness from C18-046. Both are needed before cancelling the cycle sum in the book's proof. |
| C18-060 | A negative reaching cycle implies some `v≤n` satisfies `OPT(n+1)v<OPT n v`. | `detects_cycle`, source lines592–638; requires `t≤n` and no `⊥` edge inside V. The contradiction proof sums relaxation inequalities around the cycle and cancels a finite sum. |
| C18-061 | If some `v≤n` improves strictly from row `n` to `n+1`, then a negative reaching cycle exists. | `detects_cycle_has_negative_cycle`; derive via the unbounded shortest specification and shortening. Keep the same well-formedness assumptions. |
| C18-062 | Exact detection equivalence: negative reaching cycle iff `∃v≤n, OPT(n+1)v<OPT n v`. | `bellman_ford_detects_cycle`, source829–831. This is the central unnumbered proposition on p.219, with its implicit no-bottom premise made explicit. |
| C18-063 | Define `shortest v` as the infimum of **unbounded-length** path weights plus the singleton sentinel. | It is an infimum, not a finite `Min`. It can be `⊥` when reachable negative cycling makes weights unbounded below; it is `⊤` when no path exists. No fixed arbitrary maximum path length may replace the specification. |
| C18-064 | With no negative reaching cycle, any finite path can be shortened without increasing its weight to a simple path, or to the zero-edge sink case. | `simple_paths` and `shorter_than_OPT_n_has_negative_cycle`; zero-weight cycles may be removed. These are the missing substantive arguments behind the printed short proof. |
| C18-065 | No negative reaching cycle implies `bf n v=shortest v` for every `v≤n`. | `bellman_ford_shortest_paths`, source833–842. Includes unreachable vertices, whose distance is `⊤`; it does not require global graph connectivity. |
| C18-066 | Stabilization: with no negative reaching cycle, `m≥n` implies `bf m v=bf n v` for every `v≤n`. | `bf_fix`, source848–861; combine bounded-budget monotonicity and C18-065. |
| C18-067 | Distinguish reaching and unreachable negative cycles. | Small example: vertices0,1, sink1, only finite edge `0→0=-1`; the negative cycle cannot reach1, and the correct result is `some [⊤,0]`, not failure. A checked example guards against replacing the predicate by existence of any negative cycle. |
| C18-068 | No-bottom edge assumption cannot be dropped. | Vertices0,1, sink0, weight `W 0 0=⊥`, all other weights `⊤`: a negative reaching self-loop exists, but rows1 and2 are both `[⊥,⊤]`. Thus strict improvement at `n+1` fails to detect it. Retain a checked counterexample and the corrected theorem. |
| C18-069 | Memoized `bfM` over keys `(budget,vertex)` computes `bf` and preserves consistent memory. | Instantiate the common recurrence/memory relation. Cache both arguments; using only a vertex key would conflate successive relaxation rows. |
| C18-070 | An actual row-by-row tabulator computes row0 through rown, vertices0 throughn within each row, retaining previously computed dependencies. | The natural forward iterator starts at `(0,0)`. Prove schedule coverage, termination by remaining positions, and consistency/availability of every preceding-row value. |
| C18-071 | Companion/book iterator discrepancy: AFP `iter_bf_unfold` moves **forward**, yet `bellman_ford` invokes `iter_bf(n,n)`. | Its explicit outer schedule visits only `(n,n)` before stopping; recursive memoized calls may fill dependencies, but this is not the advertised row-by-row traversal from `(0,0)`. Preserve the literal executable semantics and a checked schedule counterexample; separately certify the intended tabulation repair. |
| C18-072 | Printed `bellman_ford`: run its preliminary iterator; obtain `xs=mapM'(bfM n)[0…n]`; obtain `ys=mapM'(bfM(n+1))[0…n]`; return `some xs` if `xs=ys`, otherwise `none`. | Retain this output protocol and simultaneous pure row values. Source value correctness is unaffected by the ineffective starting index because the preparatory computation merely preserves consistency. |
| C18-073 | Final theorem: from empty, with `t≤n` and every `W i j>⊥` inside V, return `none` exactly for a negative reaching cycle; otherwise `some(map shortest [0…n])`. | `bellman_ford_correct`, source895–899. The source title promises shortest **weights**, not reconstructed paths. `none` is global cycle detection, while individual unreachable vertices remain `⊤` inside a successful list. |
| C18-074 | List-equality detection agrees with the pointwise strict-improvement criterion. | Both lists have the same fixed vertex order/length and each new entry is ≤ the previous entry. Establish this bridge rather than assume inequality of lists directly means a decrease. |
| C18-075 | The chapter's tabulation/memory-saving discussion needs an explicit scope. | A meaningful realization is a checked two-row tabulator using only the preceding row to compute the next, retaining two rows for the final comparison. Prove the same row/result specification and `O(n+1)` stored entries. The displayed unbounded mapping program itself retains `Θ((n+1)²)` possible budget/vertex entries and supplies no such space bound. |
| C18-076 | Efficient Bellman–Ford costs must refer to an actual implementation and primitive tariff. | With dense enumeration of all vertices, `n+1` relaxation rounds perform `Θ((n+1)³)` candidate edge/previous-row accesses. Constant-time arrays, logarithmic finite maps and recursive functional lookup have different total costs. The book states no exact time constant or sparse `O(VE)` theorem here; do not attach either to its dense recurrence without a separate adaptation proof. |

## 18.5.1 Optimal BST specification and recursive solution: pp. 220–223

Keys are the inclusive **integer** interval `[i,j]`; `p : Int→Nat` gives
nonnegative access frequencies. Empty intervals are allowed. Use the shared
node-labelled binary-tree carrier with an empty constructor. For successful
lookup comparisons the root contributes depth1. Dividing the weighted sum
by the total frequency yields an expectation only when that total is
positive; no probability normalization is needed by the optimization theorem.

| ID | Source obligation | Exact semantics and requirements |
|---|---|---|
| C18-077 | BST candidates have `inorder t=[i…j]`, including the empty tree when `j<i`. | This fixes every key exactly once in sorted order. It is stronger than set equality and directly gives the strict BST property. Int endpoints/subtractions must not be silently replaced by truncated Nat arithmetic. |
| C18-078 | Raw recursive cost: empty0; at root `k`, add `Σ_{x∈set left}p x`, cost left, `p k`, cost right and `Σ_{x∈set right}p x`. | Preserve the set-based subtree sums. Identifying this with a sum over node occurrences/depths requires distinct labels, supplied by the interval-inorder invariant. |
| C18-079 | Cost equals the sum over keys of `p k` times successful-lookup comparison depth, with root depth1. | Companion `OptBST.depth`, `cost'`, `weight_correct` use distinct inorder; duplicate raw labels need not satisfy the identity. Avoid calling edge-depth0 the same quantity without a +1 bridge. |
| C18-080 | Minimizing weighted cost is equivalent to minimizing expected successful comparison count for a fixed positive total frequency. | The common denominator is `Σ_{k=i}^j p k`. If all frequencies are0, every cost is0 and tree optimization remains defined, while a probabilistic expectation is not asserted by division through0. |
| C18-081 | Numerical example with frequencies `[10,30,15,25,20]` on1…5. | Printed first tree has root3, left child2 with left1, right child4 with right5: cost215, expected215/100=2.15. Printed optimum has root4, left root2 with children1,3, right leaf5: cost200, expectation2. Prove optimality through the general algorithm, not merely that these two trees differ in score. |
| C18-082 | Derived weight `WΣ i j = Σ_{k∈Icc i j}p k`, including0 on empty intervals. | Finite interval sums on Int; no positivity assumption on each frequency. |
| C18-083 | General weighted-path recurrence: `wpl W i j empty=0`; at `node l k r`, add `wpl W i (k-1) l`, `wpl W (k+1) j r`, and `W i j`. | Defined for any raw tree and any Nat-valued interval weight. Validity is needed for its relationship with the original cost. |
| C18-084 | `inorder t=[i…j] → wpl WΣ i j t=cost p t`. | `OptBST.inorder_wpl_correct`; split the inorder interval at the root and partition the frequency sum. |
| C18-085 | Basic optimum recurrences and correctness work for arbitrary `W : Int→Int→Nat`. | Preserve this generality in §18.5.1. The stronger assumptions for §18.5.3 are separate; do not impose them globally or omit them later. |
| C18-086 | Interval split at a valid root: `[i…j]=[i…k-1]++k::[k+1…j]`, with `i≤k≤j`, and the corresponding left/right inorder equalities. | The p.222 prose instead prints `[j+1…k]` for the last interval. Correct this typo and retain a small witness, e.g. `i=0,k=1,j=2`, where the printed last range is empty and drops key2. |
| C18-087 | `argmin f` on a nonempty list returns the **rightmost** minimal-scoring element. | Source recursion examines the tail and retains the head only when its score is strictly smaller; equality chooses the tail. Use the existing last-minimum API with checked correspondence and explicit empty failure/domain. |
| C18-088 | Selected argmin belongs to the input and has score `min(f '' set xs)`. | `argmin_forall`, `argmin_Min`, `argmin_in`; no arbitrary default allowed to satisfy a nonempty theorem. |
| C18-089 | On an increasing integer range, argmin is the maximal index among all minimizers. | `argmin_takes_last` and `argmin_Max_Args_min_on` are needed for Knuth root monotonicity, not just ordinary optimality. |
| C18-090 | `minWpl i j=0` if `j<i`; otherwise minimum over `k∈[i…j]` of `minWpl i(k-1)+minWpl(k+1)j+W i j`. | The book/older `OptBST` put `W` inside each mapped score. Newer `Optimal_BST.min_wpl` pulls it outside `Min`; prove value equality and keep the differing evaluation tariff explicit. |
| C18-091 | `optBst i j=empty` if `j<i`; otherwise take last argmin of `wpl W i j` over trees `node(optBst i(k-1)) k (optBst(k+1)j)` for ascending `k∈[i…j]`. | Building candidate trees and rescoring them is the literal source algorithm. A cost-cached variant is a checked refinement, not a definitionally identical replacement. |
| C18-092 | Termination of both recurrences uses `max(j-i+1,0)` as a natural measure. | Every candidate root is inside the nonempty interval, so both recursive child intervals decrease; endpoints may be negative. |
| C18-093 | Lower-bound theorem: `inorder t=[i…j] → minWpl i j≤wpl W i j t`. | `min_wpl_minimal` / `min_wpl_is_optimal`; uses optimal substructure of both children. |
| C18-094 | Inorder theorem: `inorder(optBst i j)=[i…j]`. | `opt_bst_correct`; last argmin selects an actual candidate, and every candidate has the same inorder. |
| C18-095 | Achieved bound: `wpl W i j(optBst i j)=minWpl i j`. | `wpl_opt_bst`; gives an actual optimizing tree, not merely a numeric lower bound. |
| C18-096 | Derived optimum tree theorem: every interval BST `t` has cost at least that of `optBst W i j`. | Combine C18-093–095. Keep arbitrary W for the weighted-path theorem. |
| C18-097 | Specialize to `WΣ`: `minWpl WΣ i j≤cost p t` under correct inorder, and `cost p(optBst WΣ i j)=minWpl WΣ i j`. | The two displayed p.223 propositions and `opt_bst_has_optimal_cost` follow from the cost bridge. |

## 18.5.2 Memoized weights and optimal trees: p. 223

| ID | Source obligation | Exact memory and evaluation behavior |
|---|---|---|
| C18-098 | Frequency-sum recurrence `WΣ i j = if i≤j then WΣ i(j-1)+p j else0`. | `W_rec`; give a terminating executable `W_fun` and prove it equals the set sum. Int lower endpoints handle empty bases `(i,i-1)` without truncation. |
| C18-099 | Memoize `W_fun` using keys `(i,j)` and prove `WΣ i j ▷ Wm i j`. | Instantiates the same state-consistency mechanism, with corrected cache retention for the intended preprocessing. |
| C18-100 | `Wc n` is the final store after left-to-right `mapM' (fun i => Wm i n) [0…n]` from empty. | `compute_W`; when `n<0`, the index list is empty. This store is a cache of values, not itself an executable function without lookup. |
| C18-101 | `cmem(Wc n)` and `lookup(Wc n)(i,j)=some x → x=WΣ i j`. | `compute_W_correct`; validity holds for every lookup hit, not only in the precomputation range. |
| C18-102 | For `0≤i≤j≤n`, corrected non-evicting recursion actually stores `(i,j)` in `Wc n`. | This is the cache-completeness theorem required by the efficiency explanation, beyond the source's consistency theorem. Base pairs `(i,i-1)` are also stored. No claim that all pairs of endpoints in0…n are stored is valid. |
| C18-103 | The printed assertion that a miss only occurs outside0…n needs qualification. | With `n=2`, `(i,j)=(2,0)` lies inside the square but is not visited by the described row recursion; it can miss. The valid guarantee is the upper triangle `0≤i≤j≤n` (plus visited empty bases). For literal stale-store memo the guarantee fails even on nonempty interior intervals. |
| C18-104 | Total fallback lookup `lookup(Wc n)(i,j).getD(WΣ i j)` equals `WΣ i j` for all endpoints. | `W_compute`; correctness of hits suffices and a miss computes the original sum. This equality does not prove the fallback branch is cheap or unreachable. |
| C18-105 | `optBst' i j`: precompute `M=Wc j`, use lookup-with-sum-fallback as the weight function, and call `optBst` with it. | Prove `optBst' i j=optBst WΣ i j`, including negative endpoints/out-of-precomputed-range calls. In-range performance has a narrower domain than this all-input semantic equality. |
| C18-106 | Memoized `minWpl` and `optBst` return the same numeric optimum/tree and consistent stores as their pure recurrences. | Preserve all interval keys and last ties. `OptBST.thy` supplies both older examples; newer `Optimal_BST_Memo.thy` memoizes only the cubic tree-building function and explicitly does not memoize weights. Do not attribute a complete quadratic cached-cost implementation to that source. |

## 18.5.3 Knuth optimization and actual cost scope: pp. 224–225

Write `R i j` for the **largest** root among optimizing trees of a nonempty
interval, equivalently last argmin of the root-score recurrence. The
monotonicity theorem needs properties of W that §18.5.1 intentionally did
not assume. For `i≤i'≤j≤j'`, the companion `Optimal_BST2` requires:

1. `W i' j ≤ W i j'` (interval inclusion monotonicity).
2. `W i j + W i' j' ≤ W i' j + W i j'` (quadrangle inequality).

Both hold for frequency sums with nonnegative frequencies. The second is
in fact equality for those sums. The more general AFP `Wpl` allows weighted
unsuccessful-search leaves as well; that extension is not the book's
successful-key model. Specialize its leaf frequencies to0 when reusing it.

| ID | Source obligation | Exact assumption, algorithm or count |
|---|---|---|
| C18-107 | `R i j = argminLast(fun k => W i j+minWpl i(k-1)+minWpl(k+1)j) [i…j]`. | Defined on `i≤j`; the printed lowercase `w` is the same interval weight, not an introduced second function. Empty intervals need a separate convention and may not enter a theorem unnoticed. |
| C18-108 | `R i j` is in `[i,j]`, is the root of the selected `optBst`, and is maximal among optimal roots. | Use last-tie selection and C18-095, including the singleton case `R i i=i`. |
| C18-109 | State the two W hypotheses above for the generic Knuth theorem. | `Optimal_BST2` lines130–132; preserve the inclusive middle condition `i'≤j`. Its abstract QI locale uses a shifted half-open convention, requiring a checked endpoint translation. |
| C18-110 | Prove frequency-sum weights satisfy interval monotonicity and the quadrangle equality. | Uses Nat nonnegativity and finite interval decomposition. This discharges the assumptions for the original problem rather than leaving them as unexplained new axioms. |
| C18-111 | Optimal-cost recurrence inherits the quadrangle inequality, then largest optimal roots obey monotonicity. | `Quadrilateral_Inequality.lemma_2`, `lemma_3_1`, `lemma_3_2`, `lemma_3`; these substantive lemmas cannot be omitted merely because the book refers their proofs to the literature. Port a reusable precise theorem or prove an equivalent specialized result. |
| C18-112 | For `i<j`, `R i(j-1)≤R i j≤R(i+1)j`. | Main displayed root bound on p.224. It needs C18-109, or the concrete frequency-sum instance. |
| C18-113 | Arbitrary nonnegative W does not suffice; preserve a small counterexample. | Let `W(0,1)=W(2,2)=1`, all other W=0. Then `(minWpl,R)` on `[0,1]` is `(1,1)`, on `[1,2]` is `(0,2)`, and on `[0,2]` is `(0,0)`. Thus the lower root bound fails; the restricted recursion on `[0,2]` selects root2 at cost1 although optimum cost is0. |
| C18-114 | `optBst₂ i j`: empty if `j<i`, singleton if `i=j`; otherwise first obtain roots from `optBst₂ i(j-1)` and `optBst₂(i+1)j`, then last-argmin candidate trees over the inclusive root interval. | Preserve both preliminary recursive calls and the dependency of the candidate range on their actual results. Root extraction occurs only for nonempty subintervals. |
| C18-115 | The computed left boundary is ≤ the right boundary, lies inside `[i,j]`, and every recursive candidate child interval decreases. | Source proves these on the partial-function domain before establishing total termination; Lean can use strong induction/well-founded recursion with corresponding bounds. Do not use an arbitrary root default or argmin-empty result to evade the proof. |
| C18-116 | Under the W hypotheses, `optBst₂ i j=optBst i j` as labelled trees, not merely equal scores. | `opt_bst2_opt_bst`, source241–283. Largest-root tie policy and interval restriction retaining the last minimum establish this stronger equality. |
| C18-117 | Consequently `inorder(optBst₂ i j)=[i…j]` and `wpl W i j(optBst₂ i j)=minWpl i j`; frequency-sum specialization is an optimal search tree. | Include both semantic validity and achieved optimum. |
| C18-118 | Cost-cached refinement returns `(optimalTree,optimalCost)` together, with each root candidate combining two already-returned costs and `W i j`. | AFP `opt_bst_wpl2_eq_pair` and `opt_bst_wpl2_eq_pair'` show exact equality to `(optBst₂, wpl optBst₂)` / `(optBst,minWpl)`. This is relevant support for the promised efficient realization, although not printed as a separate book algorithm. |
| C18-119 | Avoid repeatedly evaluating a score during argmin, while preserving the last-tie result. | `argmin2_argmin` stores `(candidate,score)`; `argmin_fold` scans with an incumbent score and updates on `≤`. Existing `argminLast` can supply semantic laws, but exact score-call/cell-allocation counts must follow the chosen executable refinement. |
| C18-120 | Correct telescoping identity: for `1≤d≤n`, sum over `j=d…n`, putting `i=j-d`, of `R(i+1)j−R i(j-1)+1` equals `R(n-d+1)n−R 0(d-1)+n-d+1`. | Integer arithmetic avoids truncated subtraction; interval bounds make each summand nonnegative. Here `d=j-i`, and the number of keys is `d+1`. The printed `d=i-j` is a sign error; the printed `d≤n` alone omits the nonempty-neighbour requirement `d≥1`. |
| C18-121 | Each fixed-diagonal candidate-root sum in C18-120 is at most `2n`. | Use root upper bound `≤n`, lower bound `≥0`, and `d≥1`. The `n=0` case has no nontrivial diagonals and is handled by a singleton base, not a call to undefined empty-interval R. |
| C18-122 | Across all nontrivial intervals in0…n, candidate-root evaluations are at most `2n²`; add `n+1` singleton entries and the two boundary queries per nontrivial interval. | With an actual retaining memoizer, each interval body is executed at most once. Therefore the total number of interval-call/query events is `O((n+1)²)` under a specified event observation. This is not yet a full runtime bound. |
| C18-123 | The unoptimized all-root recurrence has total candidate count `N(N+1)(N+2)/6` over all nonempty intervals of N keys. | Derive `Σ_{L=1}^N (N-L+1)L`. This makes the stated factor-N reduction in the candidate-work upper bound concrete; it is not an assertion about every isolated recursive invocation. |
| C18-124 | Separate unmemoized recursion, memoized tree-only recurrence, and memoized tree-plus-cost refinement. | Unmemoized recursion repeats intervals. Tree-only caching still recomputes `wpl` by traversing candidate trees. C18-122 supports the intended efficient method only after measured erasure/retention and stored-score obligations are discharged. |
| C18-125 | The printed literal `wpl` scoring prevents a blanket quadratic total-call bound, even after interval memoization. | For all frequencies0, last ties choose the rightmost root. Each interval with `L≥2` has two candidates, each containing L nodes; one `wpl` traversal has `2L+1` call entries. Across all N-key subintervals, these score traversals alone total `Σ_{L=2}^N(N-L+1)(4L+2)=N(N-1)(2N+11)/3`, cubic. Retain this measured counterexample family and the paired-cost correction. |
| C18-126 | Memory/primitive tariff for the intended quadratic realization. | A constant-time table and cached scores/weights support `O(N²)` unit-cost operations. The p.211 red-black-map choice entails extra lookup/update comparison work, typically a logarithmic factor. Arbitrary-precision arithmetic has its own bit cost. Prove the promised call count and state any stronger runtime theorem with its precise realization assumptions. |

## Source-defect dispositions and independent witnesses

The following are not silently repaired in the reconstruction map. Each
mathematical counterexample should later become a checked Lean example;
the independent finite calculations during this inventory are research
evidence, not completed formalization.

| Location | Defect or missing distinction | Required disposition |
|---|---|---|
| p.209 `memo₁` | Writes into a state captured before recursive execution, losing the recursive cache updates. | Preserve literal semantics and C18-012/018 witnesses; implement intended accumulation with a fresh state read and prove its correspondence to p.207 `memo` and AFP `checkmem`. For `fib₃ 3 empty`, literal final domain is `{3}`, corrected domain `{2,3}`, although both return2. |
| pp.211–213 consistency discussion | Correct result/consistent cache does not imply that memoization saves repeated work. | Separate the weak value relation from retention/coverage and measured-call theorems. The source's general memory laws intentionally allow eviction. |
| p.212 proof instruction | It refers to instantiating (18.3) with `a=fib₄ n` while removing the memo wrapper around the recursive body at the new index. | Use the rule at the actual key and body; retaining the completed `fib₄ n` as the body would not express the displayed proof step. This is an explanatory mismatch, not a new recursive definition. |
| p.213 displayed proof term | The two Fibonacci arguments appear in reverse order from the p.210 program. | Use commutativity only to match the pure sum, while preserving the program's state order or proving the particular value relation directly. No general commutation law for effects follows. |
| p.215 alternative `fibm` | Recursive map operand is printed `fibm'` with no definition. | Explicitly identify it with the intended recursive stateful function and prove the corrected formula, rather than invent a second unknown function. |
| p.216 W type | Declares Int arguments while paths and `bf` use Nat vertices. | Follow the companion Nat function or provide the restriction/coercion. This is a typing adaptation, not a new graph assumption. |
| p.217 extended addition | The omitted mixed-infinity case matters to full-domain equations. | State the source's top-dominant addition; demonstrate why nested Mathlib EInt default addition does not preserve it. A no-bottom theorem may use a restricted standard-addition bridge. |
| p.219 table discussion | Says the example stops at path length5/number of vertices; the table stops at budget4, and a simple path on5 vertices has at most4 edges. | Preserve the displayed table and state the n-edge bound for n+1 vertices. Do not shift the recurrence's stopping index. |
| p.219 negative-cycle proposition | Its no-bottom edge assumption is only displayed in the final theorem on p.220. | Carry the assumption into detection/cancellation; retain C18-068 as a counterexample to the unrestricted claim. |
| p.220 `iter_bf(n,n)` and AFP lines304–325 | Source forward iterator starting at its last index cannot be the advertised full forward table schedule. | At `n=1`, its outer schedule is `[(1,1)]`, whereas intended full row order is `[(0,0),(0,1),(1,0),(1,1)]`. Recursive cache filling does not identify those traces. Final value theorem survives; corrected scheduling needs its own correspondence. |
| pp.210–211 memory-saving promise | The later printed map retains subproblem entries and does not show a two-row algorithm. | Give a concrete checked rolling-row realization if claiming that promised space saving; label its schedule/memory theorem as an adaptation. Do not attribute linear space to the printed full map. |
| p.221 depth interpretation | Cost charges the root once; ordinary graph-theoretic root depth is0. | State comparison depth1, or prove the edge-depth+1 formula. Preserve the positive-denominator condition for expected values. |
| p.222 interval split | Last range printed `[j+1…k]`, dropping the right subtree's keys. | Correct to `[k+1…j]` and keep the `0,1,2` arithmetic witness. |
| p.223 miss explanation | A precomputed upper triangle does not contain every endpoint pair in the surrounding square. | Restrict the no-miss theorem to ordered relevant intervals; `(2,0)` at `n=2` is a simple missing in-square key. Fallback keeps the all-input value theorem correct. |
| p.224 root monotonicity | Arbitrary Nat-valued W from §18.5.1 does not imply the optimized root bounds. | Add the companion's interval monotonicity/quadrangle hypotheses, prove them for `WΣ`, and retain C18-113. Do not strengthen the basic arbitrary-W optimality theorem unnecessarily. |
| p.224 `w`, `d`, and sum domain | Lowercase weight name is undeclared; `d=i-j` has the wrong sign; empty neighbouring root ranges arise if `d=0`. | Identify `w=W`, use `d=j-i`, and state `1≤d≤n`; singleton intervals are separate. |
| pp.224–225 quadratic runtime language | The sum counts root candidates; uninstrumented map operations and recursive WPL scoring cost more. | Preserve the quadratic candidate theorem, a checked paired-score/table implementation where desired, and C18-125's cubic traversal witness. No semantic equality alone transports a resource bound. |

### Independently checked finite arithmetic during research

Two separate readers noticed the stale-state update and the missing Knuth
hypotheses directly from the PDF. A small standalone Python evaluation of
the displayed recurrences (no repository modification or Lean build) checked
the following values:

| n | Fibonacci value | Literal stale-store call entries | Corrected accumulating call entries |
|---:|---:|---:|---:|
| 3 | 2 | 5 | 5 |
| 4 | 3 | 7 | 7 |
| 5 | 5 | 11 | 9 |
| 6 | 8 | 15 | 11 |
| 10 | 55 | 53 | 19 |

The three-key W counterexample was evaluated independently from the source
definitions: full `[0,2]` root scores are `[0,1,1]`, so last-minimum chooses
root0; the restricted interval is `[1,2]`, whose tied scores choose root2.
The cost difference is0 versus1. The cubic WPL-call formula was also checked
at N=2,3,4,5,6, giving10,34,76,140,230. These are concrete targets for
later checked diagnostics, not evidence of a completed chapter.

## Implementation handoff and acceptance boundary

Formalize generic state/consistency and measured memory observations in
shared concept modules, then instantiate the book's Fibonacci, graph and
interval-BST examples. Reuse the existing state monad, relators, last-tie
selection, binary-tree carrier and measured interfaces. Preserve each
literal recurrence or a proved correspondence, including the displayed
defective program where a counterexample is needed. Correcting a source
error must be visible in its coverage row and witness, not hidden in a
stronger hypothesis or a renamed optimized implementation.

The chapter is not complete with only the value theorems. Completion also
requires the mathematical claims in the source discussion, the retained
source-error diagnostics, generic relation rules, all stated optimization
hypotheses, the exact stopping/tie/indexing behavior, and honest resource
theorems attached to the implementation they measure. Chapter closure still
requires the project's independent review axes on one immutable candidate
and its applicable validation. None of those acceptance steps occurred in
this source inventory.
