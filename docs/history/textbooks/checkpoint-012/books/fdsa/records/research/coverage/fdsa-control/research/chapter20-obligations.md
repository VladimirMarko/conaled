# Chapter 20: Queues — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-020`.

**State: queued; source preparation only.** This inventory covers printed
pp. 233–244 in the pinned July 27, 2026 book: the eight queue laws, two-list
implementation, its exact Appendix B.8 costs, Exercise 20.1, stepped
reversal, the complete Hood–Melville transition system and invariant, and
the mathematical generalizations in the chapter notes. No Lean, Git,
ticket or acceptance state was changed; no build or review loop was run.

## Sources and fixed identities

| Source | Inspected identity |
|---|---|
| Book | Alejandro Gómez-Londoño and Tobias Nipkow, Chapter 20 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; PDF pp. 239–250. Full text and the diagrams/proof lines on printed pp. 237–238 and 243 were inspected. |
| Isabelle pin | `f86f290225eebcc52c1ae7dba2e098f405f51c21`, <https://github.com/isabelle-prover/mirror-isabelle>. Supporting snapshot later than the manuscript. |
| `Queue_Spec.thy` | `src/HOL/Data_Structures/Queue_Spec.thy`, SHA-256 `f2d9365858dad006e30e1148bf62adceca1297c972c2efe3a56a64d756481282`. Direct book link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Queue_Spec.html>. |
| `Queue_2Lists.thy` | Same pinned directory, SHA-256 `cd2b22bce8aafcc93ec19ca5d18a8ff9dd83f533cfd231fe3642cf08274149c2`. Direct link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Queue_2Lists.html>. Contains all operations, locale interpretation and generated costs with `a_enq`, `a_deq`. |
| Cost support | `src/HOL/Library/Time_Functions.thy`, SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`; Appendix B inventory B-046–048 records the exact recurrences. |
| Hood–Melville entry | <https://isa-afp.org/entries/Hood_Melville_Queue.html>, Alejandro Gómez-Londoño, BSD-licensed. |
| Fixed Hood–Melville archive | <https://isa-afp.org/release/afp-Hood_Melville_Queue-2026-10-26.tar.gz>, 5,982 bytes, SHA-256 `7334636107ea70c6ff2da4a40261d670f5461d3d03c480bda48125fc6c30fa4b`. |
| `Hood_Melville_Queue.thy` | 29,721 bytes, SHA-256 `e591873fb17d0f5c71d837f30f6ff32fb1c6820341703b346482cceefba7e551`. Actual definitions, invariant and theorem statements were inspected; proofs use detailed status cases and list identities. No generated execution-cost functions occur in this theory. |
| Chapter-notes deque source | <https://isa-afp.org/entries/Real_Time_Deque.html>, Balazs Toth and Tobias Nipkow. Dated archive <https://isa-afp.org/release/afp-Real_Time_Deque-2026-10-26.tar.gz>, 27,931 bytes, SHA-256 `5de0dcd92035716afdcc2545b458508ed9fb1a6d81eb8f25dfbf0e34d40a14af`. Its `Deque.thy` interface and final interpretation were inspected for domain/scope; this is not a full inventory of that external development. |
| Selected deque files | `Deque.thy`: `76e18892869b419fb869dae42a1625d8e9618cdda11e836d8842d3ab1b5d5e2d`; `RealTimeDeque.thy`: `8a34fdfc5852b293ff4935d46126c6b89754b84da6421faaa0e5886e1f27cf96`; `RealTimeDeque_Proof.thy`: `df136792d062426c733796808fe01eaf2798b7c2415731376a0f6e1c329db2e6`. |
| Licenses | Isabelle BSD-3-Clause, `ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`; AFP BSD license text SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Retain relevant notices. |
| Lean reuse | Inspected conaled `1aabd512284fe86254278ac631eda061d311050b`; relevant existing APIs already in checkout `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`, Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

Pinned Isabelle raw URLs use
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/`
plus the revision and path. A scoped scan of `Queue_Spec`, `Queue_2Lists`
and `Hood_Melville_Queue` found no `sorry`, `oops`, `axiomatization` or
`admit`; no Isabelle build or proof audit is claimed. The min-queue exercise
is not solved in these inspected companion theories.

## Existing APIs, minimal assumptions and cost boundaries

| Existing API | Exact reuse and limits |
|---|---|
| `Sequences.AbstractFIFO.Ops` | Existing operation-only interface has empty, enqueue (`snoc`), total deletion (`tail`) and `Option` head. Reuse it; the source's unspecified empty `first` does not justify `Inhabited α`. Emptiness can be a separate observation/theorem or a small compatible interface extension. |
| `AbstractFIFO.Simulation`, `stepSquare`, `runSquare`, `run_preserves`, `client_eq`, `client_empty`, `representation_independent` | Exact reusable behavior layer. Relate concrete state `q` to list `xs` by validity and `decode q=xs`; instantiate eight source laws without a second FIFO theory. |
| `AbstractFIFO.lists`, `lists_correct` | Exact trivial list implementation, including total empty deletion and optional empty head. |
| `Resources.FIFOContracts.Instrumentation`, `Accounting`, `client_bound`, `sequential_bound`, `budget_abstract`, `run_erases` | Existing actual measured execution, behavior/resource separation and public amortized budgets. `Accounting.behavior` uses a pure decoding relation, so valid-state subtypes provide its existing route when concrete laws require an invariant. |
| `FIFOContracts.appendRun_exact`, `listMeasure`, `listProfile` | Already show list enqueue visits `length+1` append cases. Its deletion tariff is 1, while the source two-list empty deletion costs 0; do not equate the complete tariffs. |
| `Sequences.Symmetric.SymList`, `fromSL` | Standard pair-of-lists carrier and identical observation `front ++ reverse rear` can be shared. `Symmetric.Inv`, `snocSL`, `tailSL` implement a different two-ended balancing policy, including half splitting; they do not implement Figure 20.1. |
| `Resources.SymmetricCosts.reverseRun_value`, `reverseRun_work` | Exact accumulator-reversal bridge: result `reverse xs ++ acc`, work `length xs+1`. Reuse this actual traversal for source `itrev` inside `norm`. |
| `Resources.run_potential`, `run_constant_charge` | Sufficient for the two-list potential, which is natural. Prove additive local inequalities, then telescope. The source's natural subtraction can be bridged explicitly rather than used as a general signed potential operation. |
| `List.head?`, `tail`, `reverse`, `take`, `drop`, append/reversal lemmas | Standard operations and equations; reuse the Chapter 1/Appendix A checked correspondences. No new general list library is needed. |
| `Function.iterate`, `iterate_zero_apply`, `iterate_succ_apply`, `iterate_add_apply`, `iterate_succ_apply'` | Exact meaning and induction tools for repeated `rev_step` / `exec`. A custom function-composition exponent is unnecessary. |
| `List.min?`, `min?_eq_none_iff`, `min?_eq_some_min`, `min?_eq_some_iff`, `min_mem`, `min_le_of_mem` | Optional/nonempty minimum contracts for Exercise 20.1. The source assumes linear order; the operation alone uses `Min`, while its order-theoretic correctness needs the appropriate laws. See Appendix A's exact capability table. |
| Existing symmetric deque budgets | Supply amortized two-ended behavior, not the chapter-notes real-time deque theorem. An amortized budget or equality of list observations cannot establish a per-call worst-case bound. |

Both ordinary queue implementations work for arbitrary payloads, including
empty payload types; no comparison, equality test on payloads or default
element is needed. Empty-list tests should be constructor tests. Only the
min-queue adds the source's order capability. Existing `AbstractFIFO.Ops`
currently shares a universe for item and state; if a more general universe
is needed, improve that interface rather than introducing a duplicate.

Two separate metrics occur. Appendix B.8 counts recursive calls made by
the two-list operations: nonrecursive wrappers have no extra tick, and
`itrev [] []` costs 1. Hood–Melville's claim is a **worst-case constant
number of primitive steps per public call**, under the book's unit-cost
arithmetic/constructor model. Its abstraction function may traverse lists;
it is a specification, not part of every public execution. No companion
theory here supplies a complete measured primitive-step interpretation.

## 20.1 Queue interface: p. 233

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-001 | Queue operations are empty, enqueue at the rear, remove at the front, observe the first element, and test emptiness. | Reuse `AbstractFIFO.Ops` with optional/proof-domain head and a compatible emptiness observation. |
| C20-002 | Keep list observation and representation invariant separate from operations. | `Simulation` relation includes validity and list equality; no quotient or new universal ADT carrier is required. |
| C20-003 | Empty observes as `[]`. | Source `Queue.list_empty`. |
| C20-004 | Valid enqueue observes as `oldList ++ [x]`. | Source `Queue.list_enq`; direction/order is material. |
| C20-005 | Valid deletion observes as `oldList.tail`, including empty. | Source `Queue.list_deq` has no nonempty premise. Do not weaken this to nonempty deletion only. |
| C20-006 | On a valid nonempty queue, first equals the first list element. | Source `Queue.list_first`; strengthen to optional-head equality only after proving the empty behavior of the chosen Lean adapter. |
| C20-007 | Valid emptiness test agrees with `oldList=[]`. | Source `Queue.list_is_empty`; use executable constructor-based `Bool` observation. |
| C20-008 | Empty is valid. | Source `Queue.invar_empty`. |
| C20-009 | Enqueue preserves validity. | Source `Queue.invar_enq`. |
| C20-010 | Deletion preserves validity, including empty. | Source `Queue.invar_deq`. |
| C20-011 | The straightforward list implementation has linear enqueue work in current queue length. | `FIFOContracts.appendRun_exact`, with terminal call counted; other list operations are constant in this model. |
| C20-012 | The two-list implementation has constant amortized operations; the real-time implementation has constant worst-case operations. | Separate theorem targets. Neither follows solely from satisfying the same eight value laws. |

## 20.2 Two lists and exact amortized costs: pp. 233–235

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-013 | `norm(fs,rs)` is `(itrev rs [],[])` when `fs=[]`, otherwise the original pair. | Missing source-specific normalization on the existing pair carrier; use measured accumulator reversal. |
| C20-014 | `enq a(fs,rs)=norm(fs,a::rs)`. | Preserve normalization on enqueue as well as deletion. |
| C20-015 | `deq(fs,rs)` leaves the pair unchanged when the front is empty; otherwise returns `norm(fs.tail,rs)`. | The invalid raw state `([],[a])` is deliberately not normalized by deletion. Do not change the total definition merely because public clients satisfy validity. |
| C20-016 | Nonempty first is the front head. | Optional `fs.head?` or a valid-nonempty proof-domain projection; avoid traversing the abstraction. |
| C20-017 | Emptiness is front emptiness. | Correct only under the source invariant when compared with the whole queue; no payload equality capability. |
| C20-018 | Empty is `([],[])`. | Existing pair carrier; exact source boundary. |
| C20-019 | `decode(fs,rs)=fs ++ reverse rs`. | Same `Symmetric.fromSL`, without inheriting its different invariant/operations. |
| C20-020 | Validity is `fs=[] → rs=[]`. | This one-sided invariant differs from `Symmetric.Inv`. |
| C20-021 | Omitting enqueue normalization can leave all entries in rear and make first require a linear reversal. | Retain the concrete sequence witness `([], [x_n,…,x_1])`; first must remain a direct front observation in the intended implementation. |
| C20-022 | Normalization preserves the decoded list. | Standard accumulator-reversal correctness and append identities; no validity hypothesis is needed. |
| C20-023 | Normalization establishes the source invariant for every raw pair. | Direct cases on the old front and rear. |
| C20-024 | Enqueue has the required list observation. | In fact its observation law holds for all raw pairs by C20-022; retain minimal assumptions. |
| C20-025 | Dequeue has the required tail observation under validity. | Empty-front case uses validity; nonempty case uses append-tail and C20-022. |
| C20-026 | First and emptiness satisfy their observation laws under validity. | Optional-head equality handles both empty and nonempty in Lean; the source nonempty theorem is a consequence. |
| C20-027 | Empty satisfies its observation and validity laws. | No order/inhabitance assumptions. |
| C20-028 | Both updates preserve validity. | Enqueue uses C20-023; empty-front deletion retains its old valid pair. Instantiate the eight-law source interface. |
| C20-029 | `Tnorm(fs,rs)=length rs+1` if front is empty, otherwise 0. | B-046 and `reverseRun_work`. In particular `norm([],[])` costs 1, despite leaving the value unchanged. |
| C20-030 | `Tenq a(fs,rs)=Tnorm(fs,a::rs)`. | B-047; no wrapper tick. Exact values are `length rs+2` for empty front and 0 otherwise. |
| C20-031 | `Tdeq(fs,rs)=0` for empty front; otherwise `Tnorm(fs.tail,rs)`. | B-048; singleton front costs `length rs+1`, longer fronts cost 0. |
| C20-032 | Potential is `length rs : Nat`; it is nonnegative and zero at empty. | Simple natural potential, distinct from the symmetric deque's imbalance potential. |
| C20-033 | Enqueue satisfies `work + Phi(new) ≤ Phi(old)+2`. | Exact source `a_enq` after bridging its subtraction; the local law holds on all raw pairs. Actual amortized differences are 2 for empty front, 1 otherwise. |
| C20-034 | Dequeue satisfies `work + Phi(new) ≤ Phi(old)+1`. | Exact source `a_deq`; differences are 1 for singleton front and 0 otherwise, including invalid empty-front pairs. Thus no negative-charge issue arises for these particular equations. |
| C20-035 | A sequential run from empty costs at most twice its enqueue count plus its deletion count; arbitrary starts add initial rear length. | Reuse `Resources.run_potential` and `FIFOContracts`; relate the actual same trajectory to list semantics. Persistent reuse is governed by Chapter 19's boundary. |
| C20-036 | First and emptiness are constant-time observations. | Direct front constructors; do not implement them through `decode`, reversal or deletion. |

## Exercise 20.1: min-queues, p. 235

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-037 | Extend the queue interface, for linearly ordered payloads, with minimum and the valid-nonempty least-element contract. | Use an optional minimum that agrees with `List.min? (decode q)`, or a nonempty proof-domain result; the source `Min(set list)` has an invalid empty domain. |
| C20-038 | Implement the extra information promised by the hint while preserving FIFO order. | A concrete missing construction is two stacks whose every node caches the minimum of its suffix. The existing pair carrier can hold annotated lists; caches are not a new abstract queue meaning. |
| C20-039 | Cached push and pop preserve the per-stack minimum invariant. | Push compares the new value with the old cached minimum; pop exposes the tail's already cached minimum. Empty cache results are explicit Options. |
| C20-040 | Rear-to-front transfer reverses the values and rebuilds the minimum caches in the new direction. | A plain reversal of `(value,cache)` pairs is incorrect: suffixes change. Prove both value and cache correctness for the actual transfer. |
| C20-041 | Combining the two cached minima returns exactly the minimum of the decoded queue. | Handle zero, one or two nonempty stacks; use leastness/membership or standard minimum equations. Duplicates remain entries. |
| C20-042 | All ordinary FIFO laws still hold and the combined representation/cache invariant is preserved. | Compose the list-decoding simulation with cache erasure; reuse the existing client theorem. |
| C20-043 | All updates have constant amortized work in an explicit primitive comparison/cache-write/transfer model. | Instrument actual transfer; a fixed multiple of rear length supplies potential. The book specifies no exact numeric constant for this exercise, so define the tariff before deriving it. |
| C20-044 | First, emptiness and minimum take constant worst-case work. | At most two cached minimum reads and one payload comparison under the source unit-comparison model; no full-list minimum recomputation. |

## 20.3.1–20.3.3 Stepped reversal and scheduling: pp. 236–238

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-045 | `rev_step(x::xs,ys)=(xs,x::ys)`. | New small transition on a standard pair; do not duplicate accumulator reversal as a separate list API. |
| C20-046 | `rev_step([],ys)=([],ys)`. | Total terminal self-loop. |
| C20-047 | The three successive states starting at `([1,2,3],[])` are `([2,3],[1])`, `([3],[2,1])`, `([],[3,2,1])`. | Checked example target, including its ordering rather than just length. |
| C20-048 | Repeated steps use n-fold function iteration. | Existing `Function.iterate`; preserve its composition convention. |
| C20-049 | Lemma 20.1: after `length xs` steps, `(xs,ys)` becomes `([], reverse xs ++ ys)`. | Induction with `iterate_succ_apply`; a value bridge to existing accumulator reversal. |
| C20-050 | Starting with empty accumulator gives `([],reverse xs)`. | Direct specialization, including empty input. |
| C20-051 | Each individual step has constant primitive work. | Fixed constructor inspection and one cons; distinguish a per-step metric from the aggregate recursion/iteration count. |
| C20-052 | Phase 1 reverses old rear `r` into `r'`. | `r' = snd ((rev_step^[length r]) (r,[])) = reverse r`. |
| C20-053 | Phase 2 reverses old front `f` into `f'`. | Corresponding equation for `f' = reverse f`. |
| C20-054 | Phase 3 reverses `f'` onto `r'`. | Produces `reverse f' ++ r'`, preserving all old values and their FIFO order. |
| C20-055 | Independent phases 1 and 2 can advance together and require `max(length f)(length r)` data-moving rounds. | Product transition plus terminal self-loops; this is not simultaneous machine-thread execution. |
| C20-056 | The three-phase result is `f ++ reverse r`. | Lemma 20.1 and reverse involution; correct the extra-prime error on p. 237 explicitly. |
| C20-057 | Keep a live front for deletions and a fresh rear for enqueues while internal lists rebuild the next front. | Record observations must distinguish live queues from work lists. Copying a list reference at setup is not traversing/copying all elements. |
| C20-058 | Entries removed from live front must be invalidated in the work state; `ok` tracks retained entries of the reversed prefix. | Relate the informal deletion count to `ok` with a phase-aware invariant; `ok` is a natural counter with guarded uses, not an arbitrary signed counter. |
| C20-059 | Start a new reversal when the cached logical rear length exceeds the cached logical front length. | Use `lenr>lenf`. During an existing reversal, `lenf` is not generally `length(front)`. |
| C20-060 | At a new reversal, valid one-operation updates produce source lengths `n` and `n+1`. | Needs the prior balance invariant and proof that a previous reversal cannot be overwritten too early. |
| C20-061 | Rebuilding without deletions moves data in `2*n+1` rounds, but the concrete `exec` machine needs one further `App 0 → Done` step. | Exact initial `rem_steps` is `2*n+2`. Do not identify the informal data-moving count with actual `exec` invocations. |
| C20-062 | Two `exec` applications in the triggering operation and two in each subsequent update finish before the old front is exhausted. | Available budget `2*(n+1)` covers the actual count `2*n+2`; invalidations can shorten the work. |
| C20-063 | During completion there are at most `n` subsequent updates; new rear has length at most `n`, while rebuilt front has at least `n+1` remaining entries. | Bound enqueues and dequeues separately and then their total. This maintains balance at the next stable phase. |

## 20.3.4 Complete transition implementation: pp. 238–241

Use a dedicated queue record for the genuinely new scheduled representation,
with fields `lenf`, live `front`, `status`, new `rear`, `lenr`. The operation
interface and list observations remain the existing FIFO ones.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-064 | Record has two natural cached lengths, two live lists, and a status field; construction/update has ordinary product/record semantics. | A Lean structure is sufficient; no custom record machinery. |
| C20-065 | `lenr` counts current rear; `lenf` counts the logical front under construction. | The p. 239 statement that both are lengths of their physical fields is inaccurate during reversal; see the reachable witness below. |
| C20-066 | Status alternatives are `Idle`, `Rev ok f f' r r'`, `App ok f' r'`, `Done fr`. | New small inductive control state; all payload occurrences share the queue's payload type. |
| C20-067 | `exec` on `Rev ok (x::f) f' (y::r) r'` moves both heads to accumulators and increments `ok`. | Exact constructor equation; the two source lists shrink together. |
| C20-068 | `exec` on `Rev ok [] f' [y] r'` becomes `App ok f' (y::r')`. | Includes the final rear item and the phase transition. |
| C20-069 | `exec(App 0 f' r')=Done r'`. | This branch has priority over the next rule; it adds the scheduling step omitted from the informal move count. |
| C20-070 | For positive `ok` and nonempty `f'`, `exec` moves its head onto `r'` and decrements `ok`. | Pattern-match zero first, so saturation does not incorrectly move an invalidated item. |
| C20-071 | All remaining `exec` patterns return their input, including `Idle`, `Done` and malformed work states. | Preserve total raw behavior; progress theorems require `inv_st`. |
| C20-072 | Invalidating a `Rev` decrements its `ok` and leaves its four lists unchanged. | Natural predecessor; public invariants ensure the meaningful cases. |
| C20-073 | Invalidating `App 0 f' (x::r')` returns `Done r'`. | Removes the first already-built item; do not merely decrement zero. |
| C20-074 | Other `App` invalidation decrements `ok` and retains both lists. | Preserve the source's overlapping-pattern priority. |
| C20-075 | All remaining invalidations are identity. | Explicit malformed/Idle/Done behavior. |
| C20-076 | `exec2` applies `exec` twice; a resulting `Done fr` installs `front=fr` and `status=Idle`. | The second call still occurs if the first reaches Done, because Done is an exec self-loop. |
| C20-077 | Otherwise `exec2` only replaces status with the twice-stepped status. | Cached lengths and fresh rear remain untouched. |
| C20-078 | `check` calls `exec2` directly when `lenr≤lenf`. | No list-length traversal. |
| C20-079 | Otherwise `check` sets `lenf:=lenf+lenr`, status to `Rev 0 front [] rear []`, clears rear/lenr, then calls `exec2`. | Initial `Rev 0` is a transient state, not itself a public state satisfying the full queue invariant. |
| C20-080 | Empty record is `(0,[],Idle,[],0)`. | Exact constructor order and boundary. |
| C20-081 | First is the head of live `front`. | Optional/proof-domain adapter; validity proves it is available whenever logical queue is nonempty. |
| C20-082 | Enqueue adds at rear head, increments `lenr`, then calls `check`. | Exact source operation; observations see the new item at the end. |
| C20-083 | Dequeue decrements `lenf`, takes live front tail, invalidates status, then calls `check`. | Total on empty, using natural truncated predecessor. All intermediate updates matter to the proof. |
| C20-084 | Supply a constant-time emptiness observation compatible with the source ADT. | Book figure omits it; companion defines `list q=[]`. A Lean fast observer such as `front.isEmpty` or `lenf==0` needs an explicit validity-dependent equivalence, and its own cost statement. |
| C20-085 | Each public update performs exactly two calls to the nonrecursive `exec`, plus a bounded number of primitive field, constructor, arithmetic and comparison operations. | Formal per-operation worst-case bound remains missing. Unit-cost natural arithmetic/reference sharing is an explicit model assumption; no machine-word or arbitrary-precision runtime theorem is implied. |

## 20.3.5 Observations, all invariant clauses and correctness: pp. 241–244

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-086 | `inv_st(Rev ok f f' r r')` requires `length f+1=length r`, equal accumulator lengths, and `ok≤length f'`. | All three clauses are necessary source assumptions. |
| C20-087 | `inv_st(App ok f' r')` requires `ok≤length f'` and `length f'<length r'`. | Strict second inequality; distinct from `ok<length r'`. |
| C20-088 | Idle and Done satisfy `inv_st` unconditionally. | Done is permitted internally but excluded by the public queue invariant. |
| C20-089 | `front_list` at Idle is live `front`. | Observation only. |
| C20-090 | At Rev it is `reverse(take ok f') ++ f ++ reverse r ++ r'`. | Prefix selection and both orientations matter; `r'` is already in its final orientation. |
| C20-091 | At App it is `reverse(take ok f') ++ r'`. | Discards invalidated tail entries of `f'`. |
| C20-092 | At Done it is the completed list. | Needed for transient execution proofs even though public invariant excludes Done. |
| C20-093 | `rear_list=reverse ∘ rear`. | Pure observation; reversal is not performed by every enqueue. |
| C20-094 | Whole queue observation is `front_list ++ rear_list`. | Reuse FIFO list semantics. |
| C20-095 | Public invariant: `lenf=length(front_list)`. | Logical front length, not physical front length. |
| C20-096 | Public invariant: `lenr=length(rear_list)`. | Equivalent to physical rear length by reverse-length equality. |
| C20-097 | Public invariant: `lenr≤lenf`. | Scheduling/balance condition. |
| C20-098 | In Rev, `2*lenr≤length f'`. | Relates fresh rear growth to work already performed. |
| C20-099 | In Rev, `ok≠0`. | Required for public states; setup and some update intermediates temporarily fall outside it. |
| C20-100 | In Rev, `2*length f + ok + 2 ≤ 2*length(front)`. | Deadline uses **unprocessed** `f`, not processed `f'`; matches primary `rem_steps`. |
| C20-101 | In App, `2*lenr≤length r'`. | Bounds fresh rear while the replacement front is assembled. |
| C20-102 | In App, `ok+1≤2*length(front)`. | Includes the extra transition to Done. |
| C20-103 | Live front is a prefix of logical front: `∃rest, front_list=front++rest`. | Stronger than mere membership/subsequence; makes front-head and deletion contracts possible. |
| C20-104 | No public state has status Done. | Prove for public constructors/updates via `exec2`; do not assume all helpers preserve the full invariant at every intermediate point. |
| C20-105 | Status satisfies `inv_st`. | Last independent conjunction clause. |
| C20-106 | Remaining exec steps are `2*length f+ok+2` in Rev, `ok+1` in App, and 0 in Idle/Done. | Exact primary `rem_steps`, correcting the p. 243 explanatory prime error. |
| C20-107 | A well-formed non-Idle status reaches some Done after its remaining-step bound. | Primary `inv_st_steps`; `rev_steps_app` gives the first phase's exact result after `length f+1` steps. First-arrival minimality needs its own decrease argument if claimed. |
| C20-108 | Status validity is preserved by exec, two execs and invalidate. | Primary `inv_st_exec`, `inv_st_exec2`, `inv_st_invalidate`; these are status-only statements, not unqualified whole-queue invariants. |
| C20-109 | Empty satisfies the complete queue invariant. | Primary `invar_empty`. |
| C20-110 | Enqueue preserves the complete invariant. | Primary `invar_enq`, by detailed cases. Use explicit transient preconditions or direct case proofs; post-update input to `check` need not satisfy the original invariant. |
| C20-111 | Dequeue preserves the complete invariant, including empty. | Primary `invar_deq`; includes `App 0` invalidation and phase-completion boundaries. |
| C20-112 | Empty has empty list observation. | First of the eight source queue laws. |
| C20-113 | Valid enqueue appends its item to list observation. | Primary `queue_correct_enq`; maintain order and duplicates. |
| C20-114 | Valid dequeue takes the observation's tail. | Primary `queue_correct_deq`; no nonempty precondition. |
| C20-115 | Valid nonempty first returns the observation's head; valid logical emptiness forces live front empty, and conversely. | Primary `first_correct` contains the key empty-front argument. Optional-head equality and a fast emptiness adapter are useful strengthened Lean forms. |
| C20-116 | These laws instantiate the Queue ADT, including a verified emptiness observation. | Primary `HMQ: Queue` uses the slow definitional emptiness test. The intended fast Lean observer requires its explicit correspondence, not a cost transfer from this interpretation. |
| C20-117 | Arbitrary valid command histories preserve the list behavior and produce the same head client as lists/two-list queues. | Reuse `Simulation.runSquare`/`client_eq`, then separately the worst-case run budget. Companion `qfa` uses a right fold, while conaled `run` executes commands left-to-right; reverse the source action list if relating those exact definitions. |

## Mathematical scope of the chapter notes: p. 244

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C20-118 | Scheduled reversal extends to purely functional double-ended queues with constant worst-case operations. | Retain as a mathematical existence/implementation correspondence obligation, not historical prose merely because externally cited. The pinned `Real_Time_Deque` provides a primary witness; its Deque contract guards deletion on nonempty inputs, unlike the total Queue contract. Existing symmetric deque amortized results do not discharge its worst-case claim. A bounded adapter/statement selection from that external construction remains to be specified before acceptance. |
| C20-119 | Lazy evaluation permits alternative real-time single/double-ended queues, and lazy cost analysis needs its own execution model. | Preserve the costed-implementation claim separately from the subjective claim that it is simpler. The book gives no lazy code or complete tariff here; resolve the exact source statement/operational semantics before accepting it, rather than substituting a strict algorithm's output equality. The cited Pottier et al. 2024 work is *Thunks and Debits in Separation Logic with Time Credits*, listed on the primary author bibliography <https://pauillac.inria.fr/~fpottier/biblio/pottier.html>. Its proof-model transfer is not supplied by this inventory. |

Historical dates, attribution and the subjective difficulty/simplicity
comparisons are documentary context. C20-118–119 retain the mathematical
claims with their unresolved source/model boundaries; they are not counted
as formalized by mentioning the citations.

## Source corrections, concrete witnesses and cost cautions

1. **Extra prime in p. 237's displayed calculation.** After substituting the
   definition of `f'`, the text changes `reverse r` to `reverse r'`. That
   term must remain `reverse r`. For `f=[]`, `r=[1,2]`, the intended result
   is `[2,1]`, whereas the extra-prime expression gives `[1,2]`. This was
   visually checked and independently evaluated. The equations, rather
   than schematic diagram labels, must determine rear orientation; a
   useful concrete diagram/client has front `[1,2]`, rear `[4,3]`, and
   decoded queue `[1,2,3,4]`.

2. **Data-moving rounds and actual exec calls differ by one.** With no
   interleaved deletion, `Rev 0 f [] r []`, where lengths are `n,n+1`, has
   `2*n+2` remaining exec calls: `n` paired moves, one Rev-to-App move,
   `n` App moves, one App-to-Done transition. For `n=0`, the two statuses
   are `App 0 [] [y]` and `Done [y]`; one call does not finish. The book's
   `2*n+1` informal count omits the administrative completion step. Its
   scheduling budget `2*(n+1)` still suffices exactly.

3. **Wrong list in p. 243's remaining-step prose.** The prose uses
   `2*length f' + ok + 2` and says the Rev base is reached after
   `length f'` calls. The displayed invariant and primary `rem_steps`
   correctly use `f`. A well-formed status `Rev 0 [1] [] [3,2] []` needs
   four calls: it becomes `Rev 1 [] [1] [2] [3]`, then
   `App 1 [1] [2,3]`, then `App 0 [] [1,2,3]`, then Done. The printed
   prime formula would predict two. These exact status evaluations were
   independently checked without Lean builds.

4. **Cached front length is logical.** After enqueuing `1,2,3` from empty,
   the implementation reaches `lenf=3`, live `front=[1]`, status
   `App 1 [1] [2,3]`, rear empty and `lenr=0`. This is a valid public
   state and its logical front is `[1,2,3]`; the physical front has length
   1. Thus the p. 239 informal cache description cannot be formalized as
   `lenf=length front`. `check`'s later explanation and the formal
   invariant already use the right meaning.

5. **The companion emptiness operation has no proved constant strict cost.**
   Its exact definition is `is_empty q = (list q = [])`, and `list`
   computes reversals/append from work lists. In a strict value evaluation,
   this is not justified as a bounded primitive projection. Define a fast
   observer on front or a cache, prove its equality on valid states, and
   measure that implementation. Likewise, p. 243's claim that only
   `exec2` manipulates status is literally inaccurate: `check` installs
   Rev and `deq` calls invalidate. The correct public no-Done theorem
   follows from the full control flow.

6. **Use an explicit primitive model for real-time claims.** No recursive
   traversal appears in a public Hood–Melville update, but arbitrary
   natural-number arithmetic, physical allocation and garbage collection
   are not thereby proved constant-time. Under the book's primitive model
   a uniform syntactic call bound is appropriate; do not turn this into a
   machine-runtime or memory-allocation guarantee. Conversely, applying
   Chapter 1's recursive-function-only tariff to these nonrecursive
   wrappers can give zero and does not by itself explain actual constant
   primitive work.

## Minimal placement and connected acceptance examples

Keep both concrete implementations in the existing sequence/FIFO domain,
with their distinct representation namespaces and independent invariants.
Share the pair carrier/list observation for the two-list queue, not the
different symmetric balancing operations. The scheduled queue genuinely
needs its record/status carrier. Instantiate `AbstractFIFO` behavior
contracts and `FIFOContracts` resource clients instead of reproducing the
source locale hierarchy. Keep the abstract list construction out of the
public executable observer path.

The min-queue should share the two-stack queue mechanics and separate cache
correctness from FIFO observation. Order-dependent cached minima do not
belong in the generic FIFO interface. All measured operations need exact
value erasure and cost equations before any potential bound is claimed.

Connected examples should exercise: empty deletion; a two-list transfer
with at least two distinct rear values; a retained-version amortization
boundary; duplicate minima before/after removal and cache rebuilding;
each Rev/App/Done transition; the valid `lenf=3`/physical-length-1 state;
`App 0` invalidation; and a mixed command history through repeated
reversals. Compare the same history's list/head observation across the
implementations while asserting the appropriate separate cost budgets.
No chapter acceptance follows from this source inventory.
