# Chapter 8 exercises 8.1 and 8.6: counter and workload qualifications

Read-only paper preparation by `/root/chapter08_exercise_readiness`, within
root's ongoing book/thesis union task. No Lean definition, test, candidate,
ticket, coverage row, compiler process, cache, resource setting or remote state
was changed. Chapter 2 remains earliest unaccepted. This report supplies
proposed arguments and independently specified cases for later implementation;
none is a kernel-checked result or an acceptance claim.

## Inspected source and scope

Read complete book printed pp99-114 (Chapter 8, including its blank last page)
and thesis printed pp49-60 (Chapter 5). Also read book pp28-30 for Exercise 3.9
and pp33-38 for the exact lazy stream operations used by the deque analysis.
Root's complete chapter report owns the other exercises, algorithm scope and
source variants; this report concentrates on 8.1 and 8.6.

The book is the user-supplied 232-page PDF, SHA256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
The thesis is the 162-page PDF, SHA256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.
Source identities and reacquisition guidance are in
`session/research/union-source-identities.json`. Printed page + 12 is PDF page
for both sources. No manuscript is reproduced in the deliverable.

Applied the PDF skill and read AGENTS, domain/architecture guidance, glossary
and ADR0001. Visual checks used the actual rendered book p101 to confirm the
qualification about estimates, and p110 to confirm Figure 8.3's rear-heavy
`drop(j,r)` and the two directions of Exercise 8.6. The extraction's apparent
`drop(i,r)` is not the printed formula. Relevant render identities:

| Render | SHA256 |
| --- | --- |
| `research-pfds/analysis-ch08-exercises/book-101.png` | `df9c90609bf71208ad25085b8153bb6e3ed9030e026e64ab51f392c8c822e735` |
| `research-pfds/source-assets/book-08-root-122.png` (printed 110) | `6f1861e2d230eb42b00a6f63433b790d82c46b2fdfc105924041887292826511` |

The thesis has the rebuilding/deque discussion but not these numbered
exercises. Its different odd-size split and the printed rotateDrop call-order
problem remain separately owned by root's chapter report. The c=4 comparison
below concerns **banker's deques**, whose parameter permits every fixed c>1;
it does not instantiate the later real-time deque, which permits only 2 or 3.

## Exercise 8.1: arbitrary set operations and estimated counts

### What the source actually requests

Book pp100-101 proposes tombstones with periodic rebuilding and asks for a
Boolean on each red-black node, estimates of valid/invalid counts, and
correction of those estimates at rebuilding. The statement says to assume
successful insertions/deletions **for purposes of the estimates**. It does not
state a precondition that clients never insert an existing key or delete an
absent/dead key. Book p28's original insertion explicitly has an equality
branch, so duplicate insertion is already a meaningful set operation.

A faithful main semantic contract should therefore remain ordinary set
insertion/deletion on arbitrary arguments. A useful stronger cost theorem may
have a successful-operation hypothesis, but that theorem alone would not cover
the requested estimated-count algorithm. The source supplies no complete code
for the new counter policy; the following is a concrete natural policy to fix
explicitly in the later requirements, not an attributed printed implementation.

### Required semantic changes

Keep search ordering over **all physical keys**, including tombstones. On an
equality match, membership returns the validity flag; it must not treat an
invalid internal node as permission to discard its children. Deletion changes
the matching flag to false, preserving colors and shape. Repeated deletion or
deletion of an absent key has no further set effect. Insertion at an existing
tombstone sets its flag true, while insertion of an already valid key has no
set effect. New physical nodes use the established red-black insertion.

Every balancing rotation must carry a validity flag together with its own key.
Resetting flags while moving nodes would silently resurrect deleted elements.
Rebuilding filters valid elements from the inorder sequence, preserves their
ordering and uniqueness, invokes the linear builder required by Exercise 3.9,
marks every rebuilt node valid and resets the counts to actual values.

Later connected cases should cover a deleted root with live descendants,
repeated deletion, absent deletion, duplicate insertion, tombstone
reactivation, rotations carrying both valid and invalid keys, rebuilding an
empty live set, and preservation of a retained pre-update version.

### A precise estimated-count phase

Immediately after a rebuild, let n0 be the actual physical/live node count.
Within the next phase let I and D count **all** insertion and deletion calls,
including duplicates and failures to find a valid key. A simple blind update
policy has estimated counts

    A = n0 + I - D       estimated valid count
    B = D                estimated invalid count
    A + B = n0 + I       estimated total physical count.

Use integer arithmetic for this identity, or prove an equivalent bounded Nat
representation without silently relying on truncated subtraction. The natural
half-deleted trigger is B >= A after an update. The exact equality convention
must be stated; a strict trigger only changes the boundary cases. A deletion
on an empty set can transiently make A negative under the integer policy, and
then immediately triggers rebuilding/reset. It must not require a false
nonnegative intermediate invariant. An implementation may handle the empty
case directly, but must record that chosen behavior and its cost.

Let N be the current number of physical nodes, before the rebuilding scan.
Because one insertion creates at most one physical node and marking does not
remove nodes,

    N <= n0 + I.

At B >= A, the counter identity gives n0 + I <= 2D, hence N <= 2D. Thus a scan
and linear rebuild costing at most K*N + K0 can still be charged to the D
deletion calls in that phase, even when some of those calls were ineffective.
The counter estimates need not be accurate for this **rebuilding-budget**
argument. Query/search/path-copy costs remain additional obligations.

For example, starting with four live nodes and no invalid ones, two deletions
of an absent key give (A,B)=(2,2) and can trigger a complete rebuild even though
no key was removed. The scan is unnecessary semantically but its four-node
cost is still paid by two deletion calls under the displayed estimate. This is
a proposed paper case, not a run of a tree implementation.

### Physical size is not current live size

The same policy does **not** maintain N <= 2V for the current live cardinality
V. Start from a valid tree with N live keys, choose a deepest key x, perform N
duplicate insertions of x, and delete each of the other N-1 keys once. The
final counters are

    A = N + 1,  B = N - 1,

so no half-estimate trigger occurs. The physical tree still contains N nodes,
but only x is live. Marking leaves its search path intact. A deepest key in an
N-node binary search tree has depth at least order log N, and a balanced
starting tree provides the matching upper bound.

Repeated membership queries for x therefore continue to traverse order log N
physical nodes while V=1. Alternatively, repeated duplicate insertions of x
keep the same shape and further inflate A. An arbitrarily long such suffix
cannot be paid by a fixed initial-potential allowance to obtain a uniform
O(log(V+1)) bound. This is a paper counterexample to the **unstated live-size
interpretation**, not a claim that physical-size red-black search is incorrect.

The faithful available statements are an O(log(N+1)) path bound in physical
nodes, plus the separate rebuilding account above. A bound in live cardinality
needs additional successful-operation/accuracy hypotheses, or a separately
identified exact-counter variant. Silently replacing the requested estimates
with exact counters would erase this exercise's control-flow distinction.
Likewise, the p100/thesis p50 motivation about approximately half the actual
nodes being marked must not be imported as an invariant of blind estimates.

### Persistent versions retain the batched-rebuilding limitation

This is strict batched rebuilding, not the lazy mechanism introduced later.
For an even physical size N, retain a phase state after N/2-1 genuine deletions,
with no insertion and accurate counters. Repeatedly deleting the same still
valid key from that **retained state** triggers the half threshold afresh in
every child version. Each child performs a new scan/rebuild of order N work;
the input data sharing does not memoize that whole function call.

Consequently an ephemeral phase account cannot be presented as a bound for
arbitrary persistent branching. The setup cost, fresh child computations and
repeated read-only starting version must be explicit in the eventual checked
counterfamily. This is the concrete boundary advertised on book p101/thesis
p50, rather than a universal axiom about every conceivable rebuilding method.

## Exercise 8.6: fix the observation before comparing c

The exercise asks for workloads favoring each of c=2 and c=4. The balance
invariant and asymptotic O(1) amortized result do not select a universal winner.
An honest comparison needs operation order, demands, setup, retained versions
and a work observer. A list-length recurrence alone is not a lazy execution.

Two observations are useful during development:

1. **Nominal complete rebuilding visits.** For a rotation whose total size is
   n and whose longer side is split at floor(n/2), count one visit for each
   source Cons processed by take, append, drop and reverse, excluding nil-case
   and fixed overhead. The count is n + floor(n/2). This is a logical complete
   charge, whether or not the suspended operations are subsequently demanded.
2. **Executed monolithic visits.** Count Cons-consumption iterations in the
   source `drop'` and `reverse'` bodies that are actually entered under the
   client demands. Memoized re-forcing of the same completed suspension adds
   no iterations of those bodies. Input-stream construction, cache lookup,
   append/take and ordinary operation overhead remain separate components.

Book pp34-36 makes append, take, drop and reverse lazy at function entry.
Append/take are incremental; drop/reverse execute their loops monolithically
when demanded. This distinction is essential below. The proposed monolithic
counts are **paper predictions** about those source operations, not measured
Haskell/Lean timings or established conaled execution theorems.

### Family favoring c=4: repeated fixed-size shifts

Build a deque with m elements in each stream using alternating cons and snoc,
and account for making the initial finite streams available. Choose m=15t,
t>=1. Repeatedly perform the cycle

    cons a fresh element at the front; init; observe last.

Each cycle retains total size 2m. The last query makes the new rear head's
demand explicit without changing lengths. Starting from (m,m), before a
rotation the lengths after j complete cycles are (m+j,m-j). For these chosen
m, the first threshold is reached by init, not by the preceding cons. The
periods in cycles are exactly

    k2 = 5t + 1,          k4 = 9t + 1.

Each rotation restores (m,m), so the periods repeat. The rotation has nominal
complete visits 3m and nominal monolithic visits m+k_c: drop consumes m cells
and reverse consumes the k_c moved cells. With L a common multiple of the
periods, the nominal totals are

    complete(c)  = 3m * L/k_c,
    monolithic(c) = (m+k_c) * L/k_c.

As t grows, the complete-charge density per cycle tends to 9 for c=2 and 5 for
c=4. The monolithic-charge densities tend to 4 and 8/3. These compare explicitly
chosen source counters, not wall-clock constants.

There is a useful demand argument still to formalize. A newly built rear is
its old remaining rear prefix, of length m-k_c, followed by the fresh reverse
block. Later cycles delete from that prefix, while additional rebuilding only
appends new blocks behind it. With the last query after every cycle, the first
force of that reverse block is predicted at exactly m-k_c cycles after its
creation. Thus the paper prediction for executed monolithic visits by cycle L
is

    (m+k_c) * max(0, floor((L-(m-k_c))/k_c)).

The semantic prefix preservation, exact forcing time, fresh allocation and
memoization facts are required to turn this into a theorem. They have not been
proved in this investigation. In particular, the last unfinished blocks cannot
be counted as already executed merely because the length recurrence created
them. The bounded delay suggests the same limiting comparison for actual
selected work, with only a boundary term for pending blocks.

The following **arithmetic** checks used the book's two length transitions and
confirmed all rotation times, sides and sizes. The last two columns simply
evaluate the paper formula above; no lazy evaluator was executed.

| m | L cycles | rotations c=2 / c=4 | nominal complete c=2 / c=4 | nominal monolithic c=2 / c=4 | predicted executed monolithic c=2 / c=4 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 60 | 10 / 6 | 450 / 270 | 210 / 150 | 168 / 125 |
| 30 | 209 | 19 / 11 | 1710 / 990 | 779 / 539 | 697 / 490 |
| 150 | 4641 | 91 / 51 | 40950 / 22950 | 18291 / 12291 | 17889 / 12050 |

These rows and the exact observation label are retained in scratch
`research-pfds/analysis-ch08-exercises/length-simulation.json`, SHA256
`505308f63f1ce1a60f4b85487dc40b94bb2826dc370c321ac411aca10ae8e67c`.
The recurrence is fully specified above and the numerical rows are preserved
here, so the disposable scratch file is not required for recovery.

### Family favoring c=2: fresh branches from warm retained inputs

For any m>=1, first build balanced streams (m,m) by alternating cons and snoc,
then perform 3m+1 more snocs. Both implementations denote the same ordered
sequence of length 5m+1. For c=4 the resulting lengths are exactly (m,4m+1),
on its allowed boundary, without a further rotation. For c=2 the balance law
alone implies its actual front length F satisfies

    5m+1 <= 3F+1, so F >= ceil(5m/3) > m.

Warm the input streams once, retaining the corresponding queue version. The
warmup and its cost must be part of the final workload. A proposed public route
is draining a branch while retaining the starting queue; its claim to memoize
the relevant original cells needs proof. A representation-level full-force
observer is another precisely stated model, but is not silently an ordinary
deque operation.

From each retained warm input, independently execute m tails followed by head.
For c=4, the first tail leaves (m-1,4m+1) and triggers a rotation of total size
5m. Put j=floor(5m/2). Its new front is the remaining old front, of length m-1,
followed by reverse(drop(j,oldRear)). The remaining m-1 tails exhaust that old
prefix, and the final head demands the new reverse block. Its selected work is

    j drop iterations + (4m+1-j) reverse iterations = 4m+1.

The rest of the branch causes no second c=4 rotation. For c=2, the original
front has more than m cells. Any rear-heavy rotations caused by these tails
append new work after the still-present original front suffix. Consequently
the observed prefix remains inside the warm original front, and the paper
prediction is **zero fresh drop/reverse iterations** during the branch. New
incremental append wrappers may still be evaluated and must be counted in a
complete resource vector.

Repeating this experiment M times from each retained input is predicted to give
M*(4m+1) versus 0 selected monolithic visits, after the one-time setup/warmup.
The c=4 reverse computations are newly allocated by each tail call; they are
not a single retained child thunk whose later force would hit the same cache.
No function-result memoization is assumed. Proving this identity distinction
is part of the persistent execution correspondence.

A small literal case is m=1. A common setup produces six ordered elements.
The c=4 representation has front length 1 and rear length 5; c=2 has lengths
3 and 3. On warm inputs, head(tail q) in c=4 demands drop(2) and reverse(3),
while c=2 simply reads its second existing front element. The expected semantic
answer is the same second element in both cases. This discriminates the demand
paths before attempting the general family.

This comparison establishes a useful prospective **work-component** separation.
Both branches have order m ordinary operations, so it does not establish a
different asymptotic complexity class. To assert a total-cost inequality or a
quantitative speed ratio, retain all selected primitive weights and the
remaining overheads and prove the corresponding sum. No machine timing,
benchmark or universal faster implementation is claimed here.

## Remaining proof and integration obligations

* Fix the exact optimistic counter policy and half-threshold convention, prove
  set semantics for arbitrary calls, and carry flags through existing
  red-black balancing. Prove physical search/path-copy cost and scan/builder
  cost separately. State live-size refinements only under adequate hypotheses.
* Connect the arithmetic phase charges to the same measured operations and
  distinguish the ephemeral account from the retained-version failure case.
* Implement the banker deque through the existing semantic/measurement
  interfaces with the book's split convention, then retain the thesis variant
  separately where its rounding changes the trajectory. Correct source errors
  explicitly; do not use the appendix's missing singleton cases as a working
  reference implementation.
* For the c comparison, prove state lengths, occurrence-preserving denotation,
  source demand/force timing, logical work allocation and cache identities.
  Keep setup/warmup costs, pending terminal blocks and query demands explicit.
  A count of physical body entries alone does not count all loop iterations.
* Preserve independent expected values for the small six-element branch and
  periodic rotation cases. A proof of a nominal charge must not be relabeled
  as a measured execution. No statement here substitutes for the later
  chapter's full build, proof audit, independent reviews and final verification.

The requested chapter ranges and relevant stream/builder source were fully
read. The unresolved portions are the explicitly named mathematical and
operational proofs above, not uninspected numbered exercise subparts. Root's
chapter-level report remains the complete source/coverage inventory.
