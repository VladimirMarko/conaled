# Probability source preflight: quicksort, selection and treaps

Prepared 2026-11-02. **Bounded source/design preparation only.**
No algorithm, probability implementation, compiler run, ticket, frozen
requirement, source inventory or acceptance state is changed by this note.
No chapter is accepted. The existing full validation gate remains separate.

The source-reading side coordinated directly with the architecture agent,
which inspected the existing conaled/Mathlib probability APIs. This note
identifies common mathematical obligations and algorithm-specific bridges;
it does not create a probability carrier, executor or new chapter scope.
All primary reading inputs were already saved locally. No new browsing or
paper-recovery campaign was needed.

The companion **probability-api-preflight.md**, SHA-256
**eacc4181f3cb9e49598521be8149c65fab306a5c288ddd04e5bfeff6cccfe396**,
records the inspected declarations and the more general nonnegative-integral
route for the shared analytic result.

## 1. Exact scope and inspected evidence

| Existing obligation | Random experiment and retained conclusion |
|---|---|
| Chapter 2, C02-024; book §2.3 p.16 | First-pivot quicksort averaged over a uniform permutation of distinct ordered keys, and separately randomized occurrence-pivot quicksort on a fixed distinct-key input. Both retain the stated expected/average \(O(n\log n)\) bound with actual algorithm/distribution/cost correspondence. |
| Chapter 3, C03-059–077; book p.35 | Fix an arbitrary list and valid zero-based rank. Draw an occurrence uniformly at every active call, conditional on its execution history. Retain quadratic worst-case paths, linear expected work, and the precise natural-parameter scan-volume tail already inventoried. Duplicates are allowed. |
| Chapter 10, C10-112–118; book Chapter Notes p.125 | Fix two finite key sets before drawing one uniform distinct priority ranking of their union. Use its restrictions for both treaps, including identical priorities for shared keys. Semantic laws are pointwise; union/intersection/difference work is \(O(m\log(n/m+1))\) in expectation. |

The selection query lower bound C03-081–083 concerns a separate deterministic
query model. It is not a probabilistic lower bound supplied by this preflight.
The treap paper's high-probability parallel span theorem is not added to the
book's retained expected-work obligation.

### Stable source pins

- FDSA, July 27, 2026 PDF:
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>,
  SHA-256 **9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645**.
  Rechecked printed pp.16,35,125; p.17 begins merge sort.
- Isabelle companion revision:
  **f86f290225eebcc52c1ae7dba2e098f405f51c21**.
  Source tariff and partition differences remain those already recorded
  in the chapter inventories and quicksort proof plan.
- AFP *The number of comparisons in QuickSort*, Manuel Eberl:
  <https://isa-afp.org/release/afp-Quick_Sort_Cost-2026-10-26.tar.gz>,
  SHA-256 **cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457**.
  Rechecked the saved Randomised_Quick_Sort and Quick_Sort_Average_Case
  theories at the algorithm/distribution/expectation correspondence points.
  Exact theory pins and BSD provenance remain in
  **../provenance/afp-quicksort-cost-source.json**.
- Sun, Fu, Chatterjee and Goharshady, *Automated Tail Bound Analysis for
  Probabilistic Recurrence Relations*, immutable
  <https://arxiv.org/pdf/2305.15104v1>, SHA-256
  **00838dc1f49ec407ec170a131d804bb8d306257c1204afee29cac9ba92952773**.
  Rechecked Example17 on PDF p.24 and AppendixG.2 on pp.42–43.
  The book's Karp1994 §2.5 remains inaccessible as recorded in Chapter3;
  this later primary paper and an independent elementary derivation are
  not described as direct inspection of Karp.
- Blelloch, Ferizovic and Sun, *Joinable Parallel Balanced Binary Trees*,
  TOPC9(2), Article7,2022, DOI
  <https://doi.org/10.1145/3512769>; saved author copy
  <https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>,
  SHA-256 **c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057**,
  CC-BY-4.0. Rechecked priority semantics pp.7:4–5, treap join/cluster
  discussion pp.7:17–19, and expected bulk-work proof pp.7:24–28.

These external PDFs remain reading inputs; this original note is the
deliverable. No rights or license is transferred between sources.

### Inventory snapshots preserved unchanged

| Existing note | SHA-256 at this preflight |
|---|---|
| chapter02-obligations.md | a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2 |
| chapter03-obligations.md | eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed |
| chapter10-obligations.md | f3703190c2c5591a8b8685e88205652ca412e90fedb3b467ceb5d4bfd55eac0b |
| quicksort-average-proof-plan.md | ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46 |
| selection-proof-plan.md | 4683072c5b47f168f81d0f35b727e247bc2c36af6922c76ab8eaac4fb542d18b |

## 2. Common probability facts, with different executions

All three analyses need a normalized probability law, a measurable or
finite observation of the **actual execution**, and justified finite-sum
expectation calculations. Linearity and the tower law do not require
independence. Each algorithm must separately establish the law of its
next state, the relation of its observed work to the source recurrence,
and the premises needed for any conditional argument.

| Reasoning obligation | Quicksort | Selection | Treaps |
|---|---|---|---|
| Uniform finite sampling | Input permutation, or a valid occurrence index per active subproblem | Valid occurrence index, including repeated values | One uniform ranking of all distinct keys in the operand union |
| Conditional law | Given the pivot/history, suitable recursive relative-order marginals remain uniform; or fresh recursive occurrence draws have their specified law | Given the entire past, each active occurrence is equally likely | Restrictions of one common ranking; reveal only justified information and retain the resulting joint law |
| Accumulated work | Add both recursive calls and the actual local toll | Add only the selected strict branch, with a positive scan toll at each active state | Sum actual split, join and dispatch work over the recursive set operation |
| Contraction | A single search path may shrink, but the algorithm executes both branches | Conditional expected next size is at most \(3m/4\) | Conditional progress/cluster arguments can support sublemmas; bulk work still needs its separate rank/charging analysis |
| Tail requirement | No new quicksort tail theorem is requested here | Exact retained excess-multiple tail | No new high-probability bulk-work or span milestone |
| Main analytic calculation | Harmonic recurrence or comparison-indicator sum | Geometric expected sizes, shifted sums and Markov | Conditional priority-rank/depth estimates, weighted sums and logarithmic concavity |

Uniform marginals do not determine a joint law. A one-time random environment
can realize fresh conditional choices only after an appropriate coupling
theorem. Conversely, a valid unconditional expectation recurrence is enough
for some aggregate inequalities, but does not certify that an algorithm
has the claimed conditional pivot law.

### Index and rank conventions

| Quantity | Convention and boundary |
|---|---|
| List occurrence index | Zero-based \(i:\mathrm{Fin}(m)\). An active draw requires \(m>0\). |
| Stable sorted occurrence rank | Zero-based \(r<m\), with ties broken by occurrence identity for counting only. It is a bijective relabeling of occurrences. |
| Book selection request | Zero-based \(k<m\). |
| Existing public selection API | One-based rank \(k+1\), with the existing Option failure behavior. This task does not alter that API. |
| Treap priority position | The one-based position \(t\in\{1,\ldots,U\}\) in the global priority ordering; position1 has strongest priority, represented by the smallest numeric priority. |
| Treap structural rank | A separate real/logarithmic size statistic used in the join analysis. It must not be confused with either a selection rank or priority position. |

The uniform permutation space of an empty key set has one element, so the
average-input quicksort law still makes sense at \(n=0\). Sampling an
element of an empty active list does not. Empty quicksort and treap
operations take their actual base branches; valid selection starts with
positive length.

## 3. Algorithm-specific correspondence that remains mandatory

### 3.1 Quicksort: two distributions and two recursive branches

For the first-pivot average, use a uniform permutation of a fixed set of
distinct ordered keys. Conditioned on the head pivot, the remaining order
is uniform. Filtering it into fixed lower and upper key sets gives uniform
relative-order marginals. Those marginals suffice for an expectation
recurrence. Equality of the entire recursive cost distribution needs
the stronger joint law; it cannot be inferred from the two means.

For randomized pivots, use a uniform occurrence at each nonempty
subproblem, remove that occurrence, partition the rest, and run both
recursive calls. Distinctness makes the chosen occurrence's key rank
uniform. Its actual conditional execution law, or a proved equivalent
random-priority representation, must precede the numerical recurrence.
No full distribution-equivalence theorem is necessary merely to prove
both expected bounds if separate correct expectation proofs suffice.

The displayed book sorter puts equal keys on the right. The AFP proof
uses the reflexive ordering side on the left; these partitions coincide
after removing the pivot only on the distinct-key domain. The AFP's
separate three-way variant does not discharge the displayed two-way
algorithm's repeated-key behavior.

Let \(Q\) charge \(m-1\) at a nonempty call and zero at an empty call.
Let \(T\) be the supplied Exercise2.4 observation, including the two
filter traversals and empty-call charges, but excluding append. The
already-retained pointwise bridge on the same execution is

\[
T=4Q+4n+1.
\]

Its expected recurrence has \(A_0=1\) and, for \(n>0\),

\[
A_n=4n-1+\frac2n\sum_{j=0}^{n-1}A_j,
\qquad
A_n=8(n+1)H_n-12n+1.
\]

The formula remains a future connected theorem, not a definition of
algorithm cost. At zero use the base equation; in natural arithmetic
the positive-size toll may be written \(4(n-1)+3\) before casting.
The harmonic implementation/bounds already exist in Mathlib.

Whole-call claims still require the actual append association and
pivot-selection/removal work bridge. Abstract random choice is not a
claim about the number of random bits, rejection-sampling time, or
physical runtime.

**Why selection's drift cannot certify all quicksort work:** the sum of
the two child sizes is \(m-1\), regardless of pivot. At \(m=5\) that sum
is4, exceeding \(3m/4=15/4\). A bound on the larger child follows one
path; it omits the other recursive computation. The \(n\log n\) proof
needs both branches.

### 3.2 Selection: occurrences, history and the actual retained branch

At state \((xs,k)\), let \(m=|xs|>0\). Uniformly choose an occurrence,
partition the entire list into strict-lower/equal/strict-upper blocks,
and recurse only into the rank-selected strict block; stop in the equal
block. The chosen occurrence is present in the equal block, so every
recursive length decreases strictly. All outcomes terminate within \(n\)
active calls and have the same correct selected value.

Let \(X_j\) be the active list length, padded with zero after termination,
and \(W=\sum_jX_j\). This is the retained scan-volume observation.
It is neither comparison count nor an automatically verified runtime.

After assigning stable distinct ranks to occurrences for the proof,
the actual next size satisfies

\[
X_{j+1}\le\max(r,m-1-r).
\]

Uniform occurrence sampling makes \(r\) uniform even with duplicates.
The exact finite average of the right side is

\[
\frac1m\sum_{r<m}\max(r,m-1-r)=
\begin{cases}
3m/4-1/2,&m\text{ even},\\
3m/4-1/2-1/(4m),&m\text{ odd},
\end{cases}
\quad (m>0),
\]

and hence is at most \(3m/4\). The parity expressions are real/rational
arithmetic. With natural indices the subtractions in the summand use
the domain \(r<m\).

This establishes the conditional drift only after proving the uniform
law at the current history. The majorant is not the actual selected
branch law: on five distinct keys, requested rank0 and pivot rank1
retain one element, while the larger-side bound is3. The actual mean
also depends on the requested rank and duplicate pattern, so a single
exact length-only recurrence cannot simply replace it.

The retained conclusions are

\[
n\le \mathbb E W\le4n,\qquad
\mathbb E X_j\le(3/4)^j n,\qquad
\mathbb E R_w\le4(3/4)^w n,
\]

where \(R_w\) is the actual residual scan volume after \(w\) stages.
Every path has \(W\le n(n+1)/2\). On distinct inputs, a specified
endpoint-pivot sequence that preserves the target until singleton
has probability \(1/n!\) and attains that maximum. The probability of
the entire maximum-cost event can exceed this one-path probability.

For the tail, retain **\(n>0\) and \(w\in\mathbb N\)**:

\[
\Pr[W\ge(4+w)n]\le(3/4)^w.
\]

The first \(w\) scans cost at most \(wn\); the event therefore forces
\(R_w\ge4n\). Markov applies with the positive denominator \(4n\).
Independence of the sizes is unnecessary.

At \(n=0\), the padded work is0 and the non-strict event is certain;
for \(w=1\), \(1\le3/4\) is false. Do not erase the positive-input
premise. A separately stated strict-event result can handle zero,
but is not a silent replacement of C03-071. At \(n=1\), \(W=1\)
and the retained tail event is empty for every natural \(w\).

Sun et al. reproduce a strict-tail expression and use a larger-side
recurrence; their Example17 also describes \(n-1\) comparisons while
charging a size-\(n\) toll. The inventory's scan-volume theorem is an
independent, precisely specified route, not a verbatim import of that
recurrence or the inaccessible Karp proof. A natural \(w\) theorem
does not automatically prove the same formula for every real \(w\).

Finally prove the pathwise source-observation bridge
\(\alpha W\le T_{\rm actual}\le\beta W+\gamma\), with fixed
\(\alpha,\beta>0,\gamma\ge0\). It yields the retained expectation
and affine-threshold tail bounds. The actual partition passes, pivot
retrieval, length traversals and branch work determine those constants.
For fixed \(w\) the tail upper bound is constant in \(n\); it does not
assert failure probability tending to zero for a fixed linear threshold.

### 3.3 Treaps: shared priorities and conditional charging

Fix key sets \(A,B\) first. Let \(U=|A\cup B|\), sample one uniform
permutation of those keys as the strongest-to-weakest priority order,
and use its restrictions to build both canonical treaps. Shared keys
have the same priority. After that sampling, the set operations are
deterministic. Distinct priorities and BST/heap invariants give semantic
correctness for every assignment; they do not give a pointwise logarithmic
work bound.

The expected-work target retains
\(m=\min(|A|,|B|)\), \(n=\max(|A|,|B|)\), \(1\le m\le n\), fixed
input-independent constants, and separate empty-operand cases.
The actual direction of set difference is preserved; sorting two
cardinalities does not permit swapping its arguments.

The probability steps in the saved paper require more than a uniform
root marginal:

1. Restrictions to fixed subsets have the appropriate uniform relative
   orders, while overlapping operand restrictions remain jointly
   correlated. Random recursive subproblems require a compatible
   conditional statement for what the execution has revealed.
2. For a fixed nonempty subset \(S\) of size \(s\) in a uniform ranking
   of \(U\) keys, the one-based global position \(T\) of its first key
   has mean \((U+1)/(s+1)\). In the union proof, when
   \(|A|\ge|B|\), this gives at most2 for the root of \(A\), since
   \(U\le|A|+|B|\le2|A|\). This is a statement about one shared
   ranking, not fresh priorities on each recursive call.
3. The join-depth estimate must be conditioned on the actual priority
   information. To use tower and Jensen, establish the needed
   conditional expected cost bound in \(1+\log T\), then apply
   \(\mathbb E\log T\le\log\mathbb E T\). Do not treat an expected
   depth bound as a pointwise bound for every priority assignment.
4. The rank-cluster argument on p.7:18 needs geometric continuation
   justified under the relevant history. A local unconditional
   positive chance of shrinkage does not by itself justify multiplying
   survival probabilities. Exact finite rounding and small-node cases
   must replace informal equal-probability/approximation language.
5. The bulk split-work proof weights cluster lengths by split-size
   logarithms. On pp.7:27–28 the printed manipulation suppresses
   variable indices and the probabilistic conditioning. A uniform
   unconditional \(\mathbb E[d(v)]\le C\) alone does not justify
   factoring a correlated weight from \(\mathbb E[d(v)Z(v)]\).
   Prove suitable conditional cluster control or an actual charging
   bound before the layer sum. This is a proof bridge still to supply,
   not a claim that Theorem9 is false.

The already-recorded Theorem12 wording discrepancy remains: p.7:28
reverses the size inequality and omits the treap expectation
qualification. Theorem9, Table3 and the qualified preceding analysis
remain the precise target. No new paper-wide obligations are created.

## 4. Smallest useful shared results

### Recommended now: geometric expectation and finite accumulated-work tails

Use ordinary random variables over an existing probability measure,
not a new process datatype. For example, let \(X_j:\Omega\to\mathbb R\)
be nonnegative almost everywhere and integrable. Suppose

\[
N\ge0,\qquad 0\le\rho<1,\qquad
\mathbb E X_0\le N,\qquad
\mathbb E X_{j+1}\le\rho\,\mathbb E X_j.
\]

These are **integrated drift hypotheses**. They do not assert a
conditional distribution. Prove

\[
\mathbb E X_j\le N\rho^j,\qquad
\mathbb E\!\left[\sum_{j=w}^{w+L-1}X_j\right]
\le N\rho^w\sum_{i<L}\rho^i
\le\frac{N\rho^w}{1-\rho}.
\]

This uses finite-sum integration, nonnegativity and geometric arithmetic.
These real-valued equations describe a finite source-client specialization.
The architecture handoff's preferred core may instead use ordinary
\(\mathbb R_{\ge0}^{\infty}\)-valued observations, nonnegative integrals
and shifted infinite sums on any measure. Finite source executions extend
by zero, and existing geometric-series/Markov lemmas apply directly.
Prove finiteness before taking real expectations: totalized Bochner
integration or the conversion of infinity to zero is not a valid resource
observation. No duplicate real expectation interface is needed.

For actual finite work \(W_H=\sum_{j<H}X_j\), let the prefix and residual
be the sums before \(\min(w,H)\) and over \([w,H)\). Their equality
with \(W_H\) is an explicit finite-sum decomposition. If the actual
prefix is at most \(wN\) almost everywhere and \(N>0\), Markov gives

\[
\Pr\!\left[W_H\ge
N\left(w+\frac1{1-\rho}\right)\right]\le\rho^w.
\]

For \(w\ge H\), the residual is empty and the positive-threshold event
is empty under the prefix bound. No infinite sum, almost-sure
termination theorem or independence assumption is needed.

The expectation bound allows \(N=0\); the displayed non-strict tail
requires \(N>0\). Keep \(\rho=0\) valid: at \(w=0\), the natural power
is \(0^0=1\), and positive \(w\) gives zero right-hand side. A finite
horizon of0 is another valid empty-sum case.

Selection supplies \(N=n,\rho=3/4,H=n\) after its own pivot/length
correspondence. Treap cluster continuation indicators can reuse the
same finite expectation/sum tools if their conditional continuation
bound is established, but this does not prove bulk treap work by
itself. Quicksort may reuse the additive expectation infrastructure;
its whole two-branch work does not satisfy the selection drift merely
because individual paths shrink.

An affine observation corollary is useful without introducing a
separate resource model: if the actual observed cost satisfies
\(T\le aW_H+b\) almost everywhere, \(a>0\), then expectation monotonicity
and event inclusion transport the bound with threshold
\(aN(w+1/(1-\rho))+b\). The probability-measure premise is what makes
the expectation of the constant \(b\) equal to \(b\).

The architecture inspection reports existing conaled finite stochastic
tables, kernel interpretation and random-environment execution, with
Mathlib integral/conditional-expectation/Markov foundations. The shared
addition should be this finite accumulated-work argument and its
connected uses, rather than another sampler, executor or Markov-chain
hierarchy. Source-specific conditional laws remain separate goals.

### Useful later, explicitly queued: uniform restriction/minimum of a finite ranking

A small combinatorial result should express that restricting a uniform
permutation of a finite set to a **fixed** subset gives a uniform
relative order, together with the head/remaining-order conditional
law needed by its clients. Useful corollaries include

\[
\Pr[\text{first element of }S\text{ belongs to }D]
=\frac{|D|}{|S|}\quad
(\varnothing\ne S,\ D\subseteq S)
\]

and, for a subset of size \(s>0\) in \(U\) keys,

\[
\Pr[T>t]=\frac{\binom{U-t}{s}}{\binom Us},
\qquad
\mathbb E T=\frac{U+1}{s+1},
\]

with integer \(0\le t\le U\). Empty subset restrictions still have the
unique empty order, but no minimum key or first-position variable.

This genuinely connects the quicksort permutation/filter law and treap
priority restrictions. For example, a quicksort pair-comparison
indicator can use the first priority among a key interval; a treap
ancestor indicator uses a related interval-minimum event. Each
indicator characterization is algorithm-specific and must be proved.
Neither is supplied by the uniform restriction lemma alone.

This combinatorial work can remain queued while the analytic
accumulation unit proceeds. Do not infer an overlapping joint law
from marginal restrictions or claim conditional uniformity after
arbitrary extra observations. A full partition independence theorem
is a stronger optional route, not necessary for every mean calculation.

### Existing foundations to reuse

Architecture's bounded API inspection identified:

- conaled's exact rational finite stochastic Table, its composition,
  deterministic maps and kernel interpretation;
- the existing ProbabilityProgress random-environment execution and
  termination/hitting-time observations;
- Mathlib finite sums/integrals, kernel composition integrals, tower
  laws, Markov and logarithmic concavity/Jensen;
- current finite uniform measures, including uniformOn and
  Measure.uniformOfFinset; PMF bind/map if a finite recursive-result
  presentation is appropriate.

Avoid the remembered PMF.uniformOfFintype constructor name: at the pinned
Mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679** it is a deprecated
alias to a measure constructor, not the assumed PMF API. The companion
architecture handoff owns exact declaration/signature selection.
Jensen for positive priority positions can use a closed finite range
\([1,U]\) with its integrability/positivity facts; do not silently
drop the domain conditions of an integral Jensen theorem.

## 5. Independent connected-example targets

The following exact rational calculations were made by direct finite
enumeration of pivots/permutations and the stated recurrences. They are
independent expected-value evidence and future connected-case targets,
**not kernel validation**.

### Quicksort

On the six permutations of three distinct keys, the comparison
observation \(Q\) is2 on two permutations and3 on four. Hence
\(\mathbb E Q=8/3\). The Exercise2.4 observation is21 and25 on those
same cases, with mean \(71/3\), agreeing with \(T=4Q+13\).
The empty case has \(Q=0,T=1\); singleton has \(Q=0,T=5\).

For three equal keys every pivot occurrence gives \(Q=3,T=25\).
The full constant-list family remains quadratic. Its behavior is
not the three-way selector's behavior on equal keys.

### Selection

Each row charges the full active length, including singleton calls.
All requested ranks below are zero-based.

| Input; rank | Scan-volume law | Exact mean |
|---|---|---:|
| [0]; 0 | 1 with probability1 | 1 |
| [0,1]; 0 | 2 with probability1/2; 3 with probability1/2 | 5/2 |
| [0,1,2]; 0 | 3:1/3; 4:1/3; 5:1/6; 6:1/6 | 25/6 |
| [0,1,2]; 1 | 3:1/3; 5:1/3; 6:1/3 | 14/3 |
| [0,0,1]; 0 | 3:2/3; 5:1/3 | 11/3 |
| [0,0,1]; 2 | 3:1/3; 4:2/3 | 11/3 |
| [7,7,7]; 1 | 3 with probability1 | 3 |

Uniform **distinct-value** choice would instead give mean4 on
[0,0,1] at rank0, and mean7/2 at rank2. This is a different algorithm.
The distinct-input rows show that the exact selected-branch mean cannot
be a function of length alone.

The larger-side arithmetic average at lengths1 through6 is respectively
\(0,1,5/3,5/2,16/5,4\), all at most \(3m/4\).
For the equality boundary of the retained tail, distinct input of length7
at rank0 has
\(\Pr[W\ge28]=1/5040\) but \(\Pr[W>28]=0\).
At length9, rank0, \(w=1\), the threshold45 is the maximum:
\(\Pr[W\ge45]=1/362880\) while \(\Pr[W>45]=0\).
These are the unique successive-maximum pivot paths for selecting
the minimum. They demonstrate that changing the event comparator
changes the exact event, even where both proposed bounds hold.

### Treap priorities and correlations

Take ordered keys \(0<1<2\), with all six priority rankings equally
likely. For \(A=\{0,1\}\) and \(B=\{1,2\}\), each two-key treap's root
is uniform on its own keys, but

\[
\Pr[\operatorname{root}(A)=1
\land\operatorname{root}(B)=1]=1/3,
\]

whereas the product of the marginals is \(1/4\). The input treaps
cannot be independently sampled and treated as the intended joint law.
The first global priority position of \(A\)'s root is1 with probability
2/3 and2 with probability1/3, giving mean4/3.

For joining singleton key0, pivot1 and singleton key2, the pivot's
resulting depth is0,1 or2, each with probability1/3. Under the explicit
observation charging one entry per actual pivot-join call, the counts
are1,2,3 and the expected count is2. The later recurrence bridge must
establish this entry observation; it is not automatically the paper's
full primitive-work count.

Distinct uniform priority **marginals** are also insufficient. Give
the three cyclic rankings (0,1,2), (1,2,0), (2,0,1) probability1/3
each. Every key's numeric priority is uniform on positions1,2,3,
but key0 precedes key1 with probability2/3, not1/2. Thus the joint
ranking is not uniform despite distinct priorities and uniform
individual marginals.

### History, weighting and the analytic shared case

One fair bit reused at two stages has fair marginals at both stages,
but after the first bit is revealed, the second is determined. The
probability of two specified equal outcomes is1/2 rather than1/4.
This refutes the inference from marginal progress chances to a
product/geometric survival law without the required conditional bound.

Likewise, on two equiprobable outcomes let \((d,Z)=(1,0)\) or (3,2).
Then \(\mathbb E d=2\), \(\mathbb E Z=1\), but
\(\mathbb E[dZ]=3>2\). This is the finite counterexample to the
unjustified factorization discussed for weighted treap clusters.
It is not itself a counterexample to the treap algorithm.

Root's separate exact calculations are preserved in
**probability-work-calculations.json**, SHA-256
**5eae4c4c905978d1866d9a950971cd0591c54471ad5e67282aabf2f725e4a600**.
Under uniform probability on
Fin8, the four stage means are \(1,1/2,1/4,1/8\); expected accumulated
work is \(15/8\le2\). The stages are dependent. At \(w=1\), the
non-strict threshold3 has probability1/4, below the bound1/2.
The shifted residual mean is7/8, below1. This is a suitable direct
client of the proposed analytic unit without any algorithm-specific
uniform-permutation theorem.

That file also records the \(\rho=0\) boundary and a zero-cap
counterexample to the non-strict tail without positive \(N\).
For the affine observation \(2W+3\), the Fin8 mean is27/4 and the
threshold9 tail has probability1/4. These calculations exercise the
actual accumulated observation, the shift, dependence and constants
without claiming a new probability implementation.

## 6. Handoff boundary

The immediately useful shared result is the finite geometric
expectation/shifted-work/tail argument over existing probability
interfaces. Uniform permutation restriction and subset-minimum
combinatorics are separately queued. All algorithm-specific sampling,
conditional history, measured recurrence, rank convention and source
tariff bridges remain required.

This note changes no existing source requirement and makes no
implementation or acceptance claim. The treap weighted-conditioning
point is recorded as detail within its existing expected-work proof
obligation, not as a new whole-paper goal. No additional inventory
audit, source campaign or repository edit was performed.
