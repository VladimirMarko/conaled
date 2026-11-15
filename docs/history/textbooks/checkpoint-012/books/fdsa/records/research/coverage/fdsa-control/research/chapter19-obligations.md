# Chapter 19: Amortized Analysis — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-019`.

**State: queued; source preparation only.** This inventory covers printed
pp. 227–232 of the pinned July 27, 2026 book, including the introductory
mathematical claims, the potential method, both counter/table examples and
all three exercises. No Lean source, Git state, ticket or acceptance status
was changed; no build or implementation/review loop was started.

## Source evidence and provenance

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 19 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; PDF pp. 233–238. The printed p. 230 equality, cost convention and real-division note were also visually inspected. |
| Direct companion entry | <https://isa-afp.org/entries/Amortized_Complexity.html>, Tobias Nipkow, *Amortized Complexity Verified*. The entry is a source locator, not a claim that the current website equals the manuscript revision. |
| Fixed AFP snapshot | <https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz>, SHA-256 `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`. This supporting snapshot is later than the manuscript. |
| `Amortized_Framework0.thy` | SHA-256 `905899004289e7a68601a2f416ba33926135f31288c2396a0ae1abcac7133eff`. Its unary `Amortized` locale, `BinCounter`, `DynTable1` and `DynTable2` match the chapter's real costs, zero initial potential and weak table invariants most closely. |
| `Amortized_Framework.thy` | SHA-256 `74376411045129de46686fae882364cda484ce0b3d8b5069b1b085c96ea7d681`. General arity/operation-tree framework, natural actual costs and real potential/upper bounds; exact value **and cost** homomorphism premises in `Amortized2`. |
| `Amortized_Examples.thy` | SHA-256 `598b2132e979743984491fc67f3dfc03d6523eae49b938646c2797bdcb9ae67d`. Contains `Bin_Counter.a_incr`, insert-only `Dyn_Tab1` and insertion/deletion `Dyn_Tab3`. These latter examples have stronger reachable-state invariants and, for deletion, a different zero-occupancy branch; do not silently substitute them for the book. |
| License | AFP entry is BSD-licensed; shared `AFP-LICENSE` SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Retain applicable source attribution/notices when adapting proofs. |
| Lean reuse | Inspected conaled baseline `1aabd512284fe86254278ac631eda061d311050b`; cited resource/counter APIs already exist at checkout `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`, Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

The three relevant AFP files were inspected for their actual definitions and
statements. A scoped scan found no `sorry`, `oops`, `axiomatization` or
`admit`; this is source preparation, not an Isabelle rebuild or proof audit.
The source archive's other examples and arbitrary growth-factor table
generalization are supporting material, not extra Chapter 19 requirements.
Reading copies remain reproducible inputs, not copied-manuscript deliverables.

## Domains and existing reusable contracts

Actual work, potential and amortized charge are three different things.
The book uses real-valued actual-cost functions in this chapter, but their
values are casts of nonnegative integer counts. An amortized charge can be
negative even though actual work and the permitted state's potential are
nonnegative. In particular, neither a natural subtraction nor a nonnegative
charge datatype represents equation (19.1) exactly in general.

| Existing declaration/module | Exact reuse or material boundary |
|---|---|
| `Resources.Measured`, `pure`, `bind`, `reweight` | Existing value-plus-observation carrier and execution-order composition. Use natural work and explicit additive casts into `Int`/`Real`; no second writer/state framework is needed. |
| `Resources.run`, `run_state`, `run_append` | The actual sequence of states is already explicit. `run_state` identifies the final state with a fold over executed transitions, so an amortized budget must follow this trajectory. |
| `Resources.reweight_run` | An additive cost map commutes with a run. This is the correct bridge from natural event counts to real costs, after proving that each selected cost model agrees. |
| `Resources.run_invariant`, `run_value_fusion` | Reuse validity preservation and observation transport over actual runs. The potential argument does not itself prove that the abstract data-structure operations are correct. |
| `Resources.budget`, `budget_append` | Existing state-dependent natural charge sums. Their current type is specifically natural; an exact signed amortized sum is not already this `budget`. |
| `run_potential`, `run_potential_exact`, `run_cost_le`, `run_zero_potential`, `run_constant_charge`, `budget_constant` | Exact reuse for natural potentials/charges expressed additively as `work + potential_after ≤ potential_before + charge`. Current declarations require the local law on all states; restricted-validity laws need a subtype or a small invariant-aware extension. |
| `Resources.charge_iff_signed` | Converts a natural additive inequality to an integer inequality. It does not create a general real-potential theorem or identify natural truncated subtraction with a signed difference. |
| `Resources.initial_potential_matters` | Existing checked boundary example demonstrates why a nonzero initial potential cannot be discarded. |
| Mathlib `Finset.sum_range_sub` | Generated by the inspected `@[to_additive]` theorem `prod_range_div` in `Algebra/BigOperators/Group/Finset/Basic.lean`: for an additive commutative group, consecutive differences sum to the final value minus the initial value. Direct exact reuse for the book's displayed telescoping equation. |
| `Resources.BinaryCounter.inc`, `value`, `value_inc` | Same least-significant-bit-first increment; `value_inc` gives its numeric meaning. No new binary-counter operation is needed. |
| `flipCost`, `incWithCost`, `incWithCost_eq`, `flipCost_eq_leadingOnes_add_one` | Same recursive-call count, with terminal cost 1, and actual measured execution. The book's `Tincr` is its real cast. |
| `ones`, `ones_le_length`, `flipCost_le_length_add_one`, `flipCost_potential` | `ones` is the source potential after a small equality with `length (filter id bs)`. The existing exact theorem is `flipCost bs + ones (inc bs) = 2 + ones bs`. |
| `totalCost_potential`, `totalCost_le`, `totalCost_from_zero`, `counter_potential`, `advanceWithCost_eq` | Already prove the exact boundary-potential identity and total cost at most `2*n + ones bs`, or `2*n` from `[]`. These are semantically exact reuse, not merely asymptotic analogies. |
| `numericSquare`, `observedCounter_value`, `observedCounter_writes` | Existing connected clients preserve both numeric result and actual measured count. Reuse them for the chapter's counter specialization. |
| Mathlib `Nat.ofDigits`, `ofDigits_cons`, `ofDigits_digits`, `digits_lt_base`, `digits_ofDigits` | Standard little-endian positional meaning for Exercise 19.1. A measured increment in arbitrary base and its potential proof remain missing; recomputing `digits (value+1)` is not the requested carry algorithm or its cost. |
| `Resources.isBigO_of_nat_bound` | Standard project bridge from an explicit natural linear bound to real-valued `IsBigO`. Keep the initial-potential parameter and the varying operation-count variable explicit. |
| `Sequences.ByteBuffer` / `Resources.ByteBuffer` | Existing fixed-capacity byte machine and separately modeled events are useful architectural examples, but they neither resize dynamically nor implement this table's copying tariff. No exact table-cost theorem transfers. |

The natural-potential counter can be reused immediately at the statement
level. Real-potential tables and later logarithmic tree potentials need the
smallest useful signed/real extension of existing resource accounting, with
explicit nonnegativity/validity hypotheses. The algebraic telescoping core
only needs additive-group laws; inequality results add order compatibility.
Do not bundle payload equality, order, inhabitance or a physical allocator
into the general resource interface.

## Introduction and the potential method: pp. 227–228

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C19-001 | Interpret the counter's head as the least significant bit; increments scan initial ones and stop after writing a zero position or extending the representation. | Existing `BinaryCounter.value`/`inc`. The subsequent executable definition is an unbounded list counter, not a fixed-width modular machine. |
| C19-002 | A counter state of length `k` has increment cost at most `k+1`, hence linear worst-case cost in its width. | Existing `flipCost_le_length_add_one`. The extra terminal call matters for exact costs. |
| C19-003 | The all-one state of length `k` attains cost `k+1`; the linear worst case is real. | Derive from `flipCost` on `List.replicate k true`; no canonicality premise is needed. |
| C19-004 | The coarse composition of `n` width-bounded increments gives `n*(k+1)` work. | State the bound under a width bound on every input state in the run; the unbounded-list algorithm need not retain its initial width. |
| C19-005 | Roughly half the consecutive increments stop immediately because the old least significant bit is zero. | Retain the mathematical observation: from numeric zero, the cheap increments occur at even old values, with `ceil(n/2)` such calls among the first `n`, counting the empty representation as zero. A parity/counting specialization is still needed if this claim is exposed independently. |
| C19-006 | From zero, `n` increments cost `O(n)`; with arbitrary initial state retain an additive initial-potential term. | Already `totalCost_from_zero` and `totalCost_le`. The unrestricted expression `O(n)` must not quantify a uniform constant over arbitrary, uncharged initial counter widths. |
| C19-007 | For `n>0`, the average actual cost of these `n` sequential calls is bounded by a constant. | Cast the `2*n` bound and divide by positive `n`; this is an average along a deterministic run, not an expectation over random inputs. |
| C19-008 | An amortized constant bound does not give a constant worst-case bound on every individual call. | C19-003 together with C19-006 is a concrete checked witness; no real-time conclusion follows from the average alone. |
| C19-009 | Repeatedly reusing the same all-one version spends `k+1` work each time and defeats charging its stored potential only once. | Required persistence boundary: `m` independent reuses cost `m*(k+1)`. Account for construction/reuse explicitly; they are not the trajectory represented by `run`. |
| C19-010 | Restricting operations to successive states supports the amortized theorem. | Existing `run` expresses the needed history. A monadic interface alone does not prove linear ownership or prevent external aliases; make any usage protocol explicit rather than asserting that arbitrary monads enforce it. |
| C19-011 | Choose potential nonnegative on the relevant valid states, usually zero at a designated initial state. | These are hypotheses, not consequences of defining a function named potential. Retain the initial boundary term in the general theorem. |
| C19-012 | Equation (19.1): `A_f(s) = T_f(s) + Phi(f(s)) - Phi(s)`, allowing extra operation parameters. | Signed/real subtraction with natural work cast explicitly. Existing natural additive accounting is equivalent only after the appropriate bridge. |
| C19-013 | Along `s_(i+1)=f_i(s_i)`, the sum of amortized costs equals the sum of actual costs plus `Phi(s_n)-Phi(s_0)`. | `Finset.sum_range_sub`, sum distributivity, and an actual state sequence; permit varying operations as in the source framework. |
| C19-014 | For arbitrary initial potential, total actual cost is at most total amortized charge plus initial potential when final potential is nonnegative. | General boundary form; existing natural `run_cost_le` supplies its natural specialization. |
| C19-015 | If initial potential is zero, summed amortized charges upper-bound total actual work. | Existing natural `run_zero_potential`; add the real/signed specialization without weakening its hypotheses. |
| C19-016 | Validity-preserving operations and local bounds `A_f(s)≤ub_f(s)` give a sum of bounds evaluated at the actual states. | Invariant-aware trajectory theorem. Constant budgets are a specialization; logarithmic budgets remain state dependent. Source unary `inv_state`, `aa1`, `ub` provide primary proof guidance. |
| C19-017 | A binary operation has amortized charge `T_g(s,t)+Phi(g(s,t))-Phi(s)-Phi(t)`. | Preserve both input potentials. This is the formula needed later for mergeable heaps. |
| C19-018 | Binary composition telescopes when each input occurrence is accounted for in the computation history. | Source general `Amortized` operation-tree theorem `t_sum_a_sum`/`t_sum_le_U_sum` supplies a precise witness. A DAG that reuses an already charged input needs separate accounting; the unary sequence theorem alone does not justify consuming two potentials. |
| C19-019 | An observer returning a value but leaving the state unchanged has amortized cost equal to actual cost. | Model its result and unchanged state separately; cancellation is immediate. A search operation that returns an updated tree is not such an observer. |

## Binary counter: p. 229

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C19-020 | Increment of `[]` is `[true]`. | Exact `BinaryCounter.inc` base equation. |
| C19-021 | Increment of `false::bs` is `true::bs`. | Exact non-carry equation. |
| C19-022 | Increment of `true::bs` is `false::inc bs`. | Exact carry equation; structural recursion proves termination. |
| C19-023 | The operation adds one to the represented natural number. | Existing `value_inc`; connect the concrete algorithm to its intended counter observation rather than treating the cost proof alone as correctness. |
| C19-024 | `Tincr []=1` and `Tincr(false::bs)=1`. | `flipCost` cast to `Real`; the terminal empty call is charged. |
| C19-025 | `Tincr(true::bs)=Tincr bs+1`. | Exact measured recurrence via `incWithCost_eq`. No cost for a Boolean constructor or the nonrecursive numeric observation is included. |
| C19-026 | Potential is the number of true bits, as a real. | Prove `ones bs = (bs.filter id).length`, then cast; do not define a second recursive counter potential unless needed as an observation alias. |
| C19-027 | Potential is nonnegative for all Boolean lists and zero at `[]`. | Natural cast and existing `ones` equations, with no canonical representation hypothesis. |
| C19-028 | Exact amortized increment cost is 2 on every Boolean list. | `flipCost_potential`, with casts and ring cancellation, directly matches `BinCounter.A_incr` / `Bin_Counter.a_incr`. |
| C19-029 | The exact local identity telescopes to `totalCost + finalOnes = initialOnes + 2*n`. | Existing `counter_potential` / `totalCost_potential`, including `n=0`. |
| C19-030 | Canonicality may support numeric interpretation/unique encodings, but is unnecessary for these local and cumulative potential laws. | Keep `canonical_inc` as a separate result; avoid strengthening C19-028 to canonical inputs only. |

## Dynamic tables: pp. 229–231

Write a state as `(n,l) : Nat × Nat`, with occupied count `n` and allocated
capacity `l`. In the formulas below `l/2` inside a potential is real division;
the capacity update `l div 2` is natural floor division. A pair transition
does not perform any copying: the assigned work is a declared abstraction
of a copying implementation, as the book explicitly says.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C19-031 | Represent an empty table by `(0,0)` and permit occupied count at most capacity. | The introductory strict `n<l` is erroneous: the empty and full states are both needed. Use `n≤l` plus the more specific invariant below. No payload or arbitrary default element is needed. |
| C19-032 | `ins(n,l)=(n+1, if n<l then l else if l=0 then 1 else 2*l)`. | New abstract resizing transition on a standard product; source `DynTable1.ins`. |
| C19-033 | Insert-only validity is `l/2≤n ∧ n≤l`, equivalently `l≤2*n ∧ n≤l`. | Use natural multiplication for the equivalent invariant and explicit casts for real inequalities. Do not interpret the source's real `/` as floor division. |
| C19-034 | Empty satisfies this invariant and insertion preserves it. | Required initialization/preservation laws; source `DynTable1.ins` interpretation proves them. |
| C19-035 | Nonempty reachable capacity has load between one half and one. | Derive under `l>0`; the ratio at `(0,0)` does not express an occupancy percentage. The multiplication invariant remains meaningful at empty. |
| C19-036 | Insertion's copying-model cost is 1 if there is space or `l=0`, otherwise `n+1`. | Exact `DynTable1.T_ins`; preserve the first-allocation case. It is not the generated recursive-call cost of C19-032, which has no recursive call. |
| C19-037 | Insert-only potential is `(2*n:Real)-l`, with zero value at empty. | A signed expression, not `Nat.sub` followed by a cast. On valid states the equivalent natural potential may be used after an equality proof. |
| C19-038 | This potential is nonnegative under C19-033. | Validity is needed: for example `(0,1)` has potential `-1`. |
| C19-039 | Insertion's amortized cost is at most 3 on valid states. | Corrected source claim; `DynTable1.ins` interpretation proves the upper bound. |
| C19-040 | More precisely the amortized cost is 2 at `(0,0)` and 3 at every other insert-only valid state. | Small boundary refinement demonstrates why the book's blanket `Ains=3` is false. |
| C19-041 | A run of `m` insertions from empty has assigned copying work at most `3*m`. | Apply the same actual-state trajectory theorem, retaining the cost model's declared status. This is not yet a byte-copy implementation theorem. |
| C19-042 | Deletion without shrinking leaves capacity fixed and can waste unboundedly much space relative to the remaining occupied count. | Keep this mathematical motivation and Exercise 19.2 separate from the shrinking variant; the same fixed capacity can remain after all entries are deleted. |
| C19-043 | Shrinking at a strict half-full threshold permits repeated expensive growth/contraction with only a constant number of operations in between. | Formal witness family described below; the total costs cannot have a uniform constant amortized bound for arbitrary lengths/sizes. |
| C19-044 | Quarter-threshold deletion: decrement `n` with natural truncation; if old `n=1`, set capacity to zero; otherwise if `4*(n-1)<l`, use `l div 2`; otherwise retain `l`. | Exact `DynTable2.del`. Do not change `n=1` to `n≤1` on the book's weak valid domain. |
| C19-045 | Deletion cost is 1 at old `n=1`, otherwise `n` when contracting and 1 otherwise. | Exact `DynTable2.T_del`; the cost `n` includes the stated copy/deletion model. At `(0,l)` with `l>0` this total abstract definition gives cost 0, unlike the stronger-domain AFP example. |
| C19-046 | For the combined operations the book uses only `n≤l` as its invariant. | Exact `DynTable2.invar`; do not silently require a quarter-full table for the local amortized inequalities. |
| C19-047 | Empty is valid and both insertion and this deletion preserve `n≤l`. | Retain all natural-floor and zero cases, including initially weak-valid `(0,l)` states. |
| C19-048 | States reachable from empty additionally satisfy `l≤4*n`, hence positive-capacity load at least one quarter. | A separate reachable-state invariant, not a consequence of C19-046 on arbitrary states. Check preservation and isolate the empty ratio boundary. |
| C19-049 | Combined potential is `l/2-n` when `2*n<l`, and `2*n-l` otherwise, computed in `Real`. | Exact `DynTable2.Phi`; at the boundary both branches give zero. For odd capacities half-integral values are real, not rounded. |
| C19-050 | This piecewise potential is nonnegative on every state and zero at `(0,0)`. | Unlike C19-038, no validity premise is needed for nonnegativity. |
| C19-051 | Insertion with the combined potential has amortized cost at most 3 under `n≤l`. | Source `DynTable2.tb` interpretation; equality 3 is not a general claim. |
| C19-052 | Quarter-threshold deletion has amortized cost at most 2 under `n≤l`. | Same interpretation; amortized charge can be negative, so do not model its exact value in `Nat`. |
| C19-053 | Any mixed valid trajectory from empty is bounded by `3*(number of insertions)+2*(number of deletions)`. | State-dependent telescoping specialized to per-operation constants, with natural actual costs cast to reals. Empty deletion must remain in the permitted operation language. |
| C19-054 | The explanatory credit values at `(l,2*l)` and `(l/2,2*l)` are 0 and `l/2`, respectively. | Treat the latter as a natural state only when `l` is even, or state the corresponding real algebra separately. These explain the slope of the potential; they do not replace C19-052's rounded-boundary proof. |
| C19-055 | Real `/`, natural `div`, signed subtraction and saturated natural predecessor have distinct meanings. | Required correspondence examples: odd capacity, empty table, last deletion, full insertion and deletion from weak-valid `(0,l)`. |

## Exercises: p. 232

The inspected companion files do not supply these three exercise solutions.
The concrete bounds below are proof targets, not newly checked Lean results.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C19-056 | Exercise 19.1: implement carry increment in arbitrary base `b≥2`, with head as least significant digit. | Use a list of bounded digits or natural digits with an explicit `<b` invariant; preserve the carry algorithm. |
| C19-057 | Prove that generalized increment preserves the digit domain and adds one to `Nat.ofDigits b`. | Reuse `ofDigits_cons` and positional arithmetic. No no-leading-zero premise is required for addition correctness; canonicality is a separate optional representation fact. |
| C19-058 | Define its actual cost by one charge per visited digit, including the terminal insertion/stop, matching the binary convention. | An exact measured execution and value erasure are missing. Merely giving a recurrence detached from execution is insufficient correspondence. |
| C19-059 | There exists one constant `c` valid for every base `b≥2`. | A concrete target is `c=2` with potential equal to the count of digits equal to `b-1`: each carry spends one credit; a stopping increment creates at most one. The existential constant must precede the quantifier over `b`. |
| C19-060 | Obtain a linear total bound from empty uniformly in the base. | Same resource theorem; specialize back to `b=2` and connect the existing Boolean representation and exact binary law. General bases give an inequality, not always amortized charge exactly 2. |
| C19-061 | Exercise 19.2: retain the same insertion, but define naive deletion as `(n-1,l)` with constant deletion work 1. | Specify the empty natural predecessor case and validity `n≤l`; capacity does not reset on the last deletion. |
| C19-062 | Find nonnegative potential supporting both operations. | A suitable target is `max 0 ((2*n:Real)-l)`; the original unrestricted linear potential becomes negative after sufficiently many deletions and cannot justify dropping the final potential. |
| C19-063 | Prove insertion amortized cost at most 3 and naive deletion at most 1. | Case analysis of the clipped potential, retaining the same copying-model insertion work. |
| C19-064 | Prove invariant preservation and the mixed sequential bound from `(0,0)`. | Reuse actual-state accounting; a fixed-capacity byte-buffer theorem is not an exact replacement. |
| C19-065 | Exercise 19.3: replace the contraction guard by `3*(n-1)<l` and contracted capacity by `(2*l) div 3`, retaining the last-element reset and corresponding copy cost. | Natural floor division is material. State the inherited `n=1` and empty branches explicitly. |
| C19-066 | Use potential `abs ((2*n:Real)-l)` and prove its nonnegativity/initial zero. | Absolute value must surround signed subtraction; `abs (Nat.sub …)` would be a different function. |
| C19-067 | Prove constant amortized bounds for both operations. | Concrete targets are insertion ≤3 and deletion ≤3 under `n≤l`. Deletion ≤2 is false here: `(3,6)` has old potential 0, no contraction, new potential 2 and work 1. |
| C19-068 | Show validity preservation and a mixed trajectory bound, uniformly over table sizes. | Handle floor residues modulo 3 and saturation at zero. Small exact-rational enumeration supports the target constants but is not their formal proof. |

## Checked source corrections and boundary evidence

1. **Strict occupancy typo, p. 229.** The prose's `n<l` excludes both
   `(0,0)` and every full `(l,l)` state. The displayed invariants and primary
   definitions use non-strict occupancy and have explicit overflow branches.
   Correct the correspondence explicitly to `n≤l`; do not make overflow
   unreachable through a strict invariant.

2. **Exact-charge typo, p. 230.** The printed assertion that the informal
   insertion cost 3 has formal counterpart `Ains s=3` is false. Starting at
   `(0,0)`, actual work is 1, the new state is `(1,1)`, old potential is 0 and
   new potential is 1, so the amortized charge is **2**. The exact source
   `Amortized_Framework0.DynTable1` uses the upper bound 3. With the later
   piecewise potential even nonempty states need not have charge 3:
   insertion at `(1,4)` has charge 0, and deletion at `(2,2)` has charge -1.

3. **Two AFP variants must not be conflated.** `Framework0.DynTable2`
   matches the book's `n=1` special case and weak invariant `n≤l`.
   `Amortized_Examples.Dyn_Tab3` instead uses `n≤1` and validity
   `if l=0 then n=0 else n≤l ∧ l≤4*n`. For example, `(0,4)` is valid in the
   book and is sent to `(0,2)` at assigned cost 0; the second variant sends
   it to `(0,0)` at cost 1, but excludes it from its valid domain. Agreement
   on states reachable from empty does not imply unconditional equality.

4. **Half-threshold fluttering is a theorem target, not just a warning.**
   For a positive even/power-of-two capacity `l`, start just after an
   overflow at `(l+1,2*l)`. Under the proposed half-threshold shrinking
   policy, two deletions and two insertions return to that state. With the
   same copying tariff their four costs are `1,l,1,l+1`, summing to
   `2*l+3`. Repeat the cycle. Its size-dependent cost per four operations
   rules out a uniform constant amortized bound, even after accounting for
   a prefix that builds the initial full table.

5. **Exercise 19.3 has a different constant from quarter-threshold deletion.**
   The state `(3,6)` is an independent counterexample to importing the
   preceding deletion bound 2. Exact-rational bounded enumeration over all
   `0≤n≤l≤150` found no validity failures and maxima 3/2 for quarter-policy
   insertion/deletion, and 3/3 for the third-policy variant. These finite
   calculations are evidence for the stated proof targets only; no build
   or infinite-domain proof was claimed.

## Implementation placement and connected acceptance examples

Extend the existing `Applications/Resources/Potential.lean` accounting only
where signed/real potentials and invariant-restricted local laws require it.
Reuse its natural clients and Mathlib's telescoping lemma; do not port the
whole AFP locale hierarchy merely to reproduce its syntax. A binary
composition/operation-history specialization should be driven by the later
merge client, preserving occurrence accounting.

Keep the binary chapter specialization beside existing
`Applications/Resources/BinaryCounter.lean`. An arbitrary-base extension
belongs to that same counter domain, with standard `Nat.ofDigits` as its
numeric observation. Put the abstract resizing transitions and declared
copying cost in a focused dynamic-table resource module; an actual array or
allocator implementation would require its own representation-and-cost
bridge and is not supplied by this abstract chapter.

Connected examples should include: a zero-start and arbitrary-start counter
run with both numeric result and measured work; an all-one retained-version
reuse witness; base 2 and a larger base with the **same** constant; a table
trajectory containing first allocation, growth, contraction and empty
deletion; odd capacities under the weak invariant; and the `(3,6)`
one-third-policy boundary. Each example should assert the observation and
the exact selected work/potential calculation, not just a final big-O label.

Historical attribution and the savings-account metaphor are explanatory
prose. The deterministic sequence bounds, persistence counterexample,
binary-composition formula and every mathematical assertion above remain
formal obligations even when their proof is delegated by the book to an
external source. No chapter acceptance is implied by this inventory.
