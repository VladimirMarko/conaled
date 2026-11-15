# Adjacent-pair construction: bounded cost argument to formalize

Prepared by root during the prerequisite validation recovery on 2026-11-02.
This is mathematical preparation, not Lean implementation, a checked theorem,
an acceptance review, or advancement past Chapter2. Source obligation:
book printed p19 Exercise3.3, B3-E3.3 in chapter03-union-inventory.md.
The source identity and visual inspection are retained there. No manuscript
text is reproduced here.

The existing first-slice plan leaves linear paired construction open. The
following accounting avoids a loose per-level bound whose extra unmatched
heap would obscure linearity. It should be proved through the actual paired
rounds, after the six-operation interface and measured meld are available.

## Exact structural recurrence

Let N_i be the number of heaps at the start of round i, beginning with n
singletons. Pair adjacent heaps and carry an unmatched last heap. Then
N_(i+1) = ceil(N_i/2), and M_i = floor(N_i/2) is the number of actual melds.
For n>0 stop at the first k with N_k=1; for n=0 perform no rounds. In each
nonterminal round, M_i = N_i - N_(i+1). Thus the total number of melds is n-1
for positive n, with zero for empty input.

Define W(n) = sum over i<k of (i+1)*M_i, with W(0)=W(1)=0. Summation by
parts gives W(n) = sum over i<k of (N_i-1). An equivalent recursive proof is
more convenient in Lean: for n>1, q=ceil(n/2) is smaller than n, and shifting
the remaining rounds' weights gives

    W(n) = floor(n/2) + W(q) + (q-1) = (n-1) + W(q).

Since q-1=floor((n-1)/2), strong induction proves W(n) <= 2*(n-1). The
induction uses 2*(q-1) <= n-1. This includes every odd-tail round without an
additional logarithmic error term. Sanity cases to connect to the actual
round operation are n=0,1,2,3,4,5,8, with W=0,0,1,3,4,7,11 respectively.
These calculations are proposed expectations, not compilation evidence.

## Connect actual heap costs, rather than counting melds alone

After i rounds every heap has unfolded size at most 2^i, because each comes
from a consecutive block of at most 2^i original singleton occurrences.
Retaining this block/size invariant also handles the unmatched last heap.
For a Ranked leftist heap, the existing rank-size inequality gives rank at
most i+1 under that size bound. Consequently the first-slice planned
comparison theorem gives at most 2*(i+1) priority comparisons per meld in
round i. This is a sufficient upper bound; no equality or physical-allocation
claim is intended.

More generally, if the measured actual meld cost for these inputs is bounded
by A*(i+1)+B for fixed natural coefficients, then all meld work is bounded by

    A*W(n) + B*(n-1) <= (2*A+B)*(n-1).

Singleton formation, round-list traversals, termination checks and returning
the result need their own declared counts. They can be charged to n plus
the actual round-list lengths; for n>0 their excess over one retained heap
per round is exactly the sum above. An implementation that rescans all
original elements per round would not satisfy this intended linear model.
Do not hide such traversals inside an assumed constant-cost round operation.

The source round bound also needs the exact ceiling-log convention, with
n=0/1 handled explicitly. Existing Nat.clog halving lemmas were identified
by the reuse inventory, but their precise statements must be checked before
use. The generic resource bound is conditional on the measured realization;
ExactQueue laws alone do not imply a logarithmic meld or linear construction.

## Required checked connections

Prove actual round length, flattened occurrence permutation, validity and
block sizes; prove termination and the actual round/meld counts; derive the
weighted recurrence from those executions; finally transport the source
leftist meld bounds and account for list/singleton work. Retain empty, one,
odd-tail and non-power-of-two examples. Counting n-1 melds alone remains
insufficient. This note resolves no Chapter3 coverage item by itself.

## Closing the traversal charge explicitly

Further preparation by root,2026-11-03; still not a checked Lean result.
For positive n, every nonterminal round performs at least one meld. Hence its
round count k is at most the total meld count n-1. The exact earlier identity
sum_i(N_i-1)=W(n) then yields

    sum_i N_i = W(n)+k <= 3*(n-1).

Thus a declared per-round traversal/dispatch charge a*N_i+b contributes at
most (3*a+b)*(n-1), without relying on a logarithm estimate for this part.
Combining singleton formation c*n, meld work A*W(n)+B*(n-1), and constant
return work d gives the explicit envelope

    c*n + (2*A+B+3*a+b)*(n-1) + d

for positive input. Empty and singleton execution still need their separately
observed constants. The logarithmic round theorem remains a required source
claim, but it need not be used to hide or discharge linear traversal work.
The constants must come from the actual instrumented implementation, including
any repeated pass over the round list; they are not supplied by the heap laws.
