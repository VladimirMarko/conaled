# Shared affine recurrence bound: source and API preflight

Prepared 2026-11-02. **Read-only preparation, not Lean implementation,
compilation, final review, or chapter acceptance.** This note changes no chapter
order, ticket, Git state, or acceptance record. It extends the analysis in
[selection-proof-plan.md](selection-proof-plan.md), without replacing its
algorithm-to-cost correspondence obligations.

## Recommendation

Add one ordinary upper-bound theorem for a scalar function and **two abstract
natural child-size functions**. Its essential hypothesis is that the sum of
child sizes is eventually at most `rho*n+K`, with `rho<1`; its toll is at most
an affine function. Keep ceiling arithmetic in the source specialization.
Prove the result by strong induction after enlarging a finite base prefix.
No new recurrence record, executor, timing class, worst-case supremum, or
finite-branch framework is needed for the present consumers.

The useful output is a single pair of constants chosen before the input size:
`exists A B, forall n, f n <= A*n+B`. It is stronger than an eventual bound and
does not exclude `n=0`. Preserve the book's real-valued one-sided statement;
obtain natural-cost/Big-O conclusions through explicit casts and nonnegativity
where appropriate.

Strict fractional contraction is not a necessary hypothesis for every linear
tree algorithm. Ordinary traversals and the prefix balancer have child sizes
summing to `n-1` and constant local work. Braun conversion uses a consumed-size
or forest measure. Those existing source arguments should remain direct
inductions, with their exact constants, rather than be forced through this
different sufficient theorem.

## 1. Pins and primary statements

The book is the July 27, 2026 [official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Printed pp. 41–43, including Theorems 3.9–3.10 and formulas (3.15)–(3.19),
were inspected against the pinned companion theory. Later-tree comparisons
use the chapter inventories and the actual theories listed below.

All these theory paths are under `src/HOL/Data_Structures/` at Isabelle
[`f86f290225eebcc52c1ae7dba2e098f405f51c21`](https://github.com/isabelle-prover/mirror-isabelle/tree/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures).
The source pin postdates the PDF; it is a checked statement reference, not
proof that this exact revision generated the book. Isabelle's pinned top-level
`COPYRIGHT` is BSD-3-Clause; retain relevant attribution in translations.

| Theory | SHA-256 | Inspected role |
|---|---|---|
| `Selection.thy` | `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8` | `akra_bazzi_light_aux1`, `akra_bazzi_light_aux2`, `akra_bazzi_light`, `akra_bazzi_light_nat`, `T'_mom_select_le'`; Manuel Eberl. |
| `Tree23_of_List.thy` | `dcb3ef5eff58d65a4bb95b915870dd527d0bb9dcffd13c9c41e9fb5421ba7240` | `T_join_adj`, `T_join_all`, `T_tree23_of_list`; Tobias Nipkow. |
| `Balance.thy` | `6d14341de140a4cf5d811798aa1796c143a9127aedfeae0b600f8d174e6bb3fc` | Actual sequential prefix-consumption algorithm and height recurrences; Chapter 4 inventory owns its cost exercise. |
| `Array_Braun.thy` | `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f` | `T_brauns_simple`, `T_brauns_ub`, `sum_tree_list_children`, `T_list_fast_rec_ub`; Tobias Nipkow with Thomas Sewell. |

Conaled interfaces were inspected at the frozen Chapter 1 candidate
`1aabd512284fe86254278ac631eda061d311050b`; the shared draft is
`c28ba71863d2a35ee1c3a089caa90464e4cca692`. Dependency pins are Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries
`66e469188fe07963e5cf666c7d4433f45b8131c5`, and Lean
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

### Exact source theorem

For fixed `f : Nat -> Real`, `n0 : Nat`, and real parameters, the assumptions
of Theorem 3.9 are

```text
0<a, 0<c, a+c<1, 0<=C1,
forall n>n0,
  f n = f ceilNat(a*n+b) + f ceilNat(c*n+d) + C1*n+C2.
```

The conclusion is

```text
exists C3 C4 : Real, forall n : Nat, f n <= C3*n+C4.
```

`b,d,C2` may be negative; `f` need not be nonnegative or monotone. The ceiling
is the source's integer ceiling followed by conversion to Nat, hence truncates
negative results to zero. In Lean this is `Nat.ceil`, not an unspecified
rounding operation. The source's natural-valued corollary casts the recurrence
and rounds the final constants upward.

The printed coefficient prose on p.41 wrongly names `a,b` where the recursive
coefficients are `a,c`. Its introductory necessity claim must not be read into
Theorem 3.9, which proves only sufficiency and even allows zero linear toll.
The p.43 strict slope condition is stronger than its subsequent `max` choice
ensures; non-strict slope suffices and is what the pinned proof uses.

## 2. Small reusable Lean statement

The following is a proposed signature, not a declaration already present or
checked by Lean. After root's suggestion to clear a factor of two in the
contraction margin, the core can use a **commutative ring rather than a field**.
Its typeclasses use the actual unbundled names at this pin:

```lean
theorem exists_affine_bound_of_two_branch
    {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Archimedean R]
    (f : Nat → R) (left right : Nat → Nat) (n0 : Nat)
    (rho K C D : R) (contract : rho < 1)
    (sizes : ∀ n, n0 < n →
      (left n : R) + (right n : R) ≤ rho * n + K)
    (step : ∀ n, n0 < n →
      f n ≤ f (left n) + f (right n) + C * n + D) :
    ∃ A B : R, 0 ≤ A ∧ ∀ n : Nat, f n ≤ A * n + B
```

This uses an upper recurrence because source costs usually arrive as bounds.
An equality is immediately usable through its `le` direction. Child sizes need
not be monotone, and no monotonicity of `f` belongs here. The theorem is about
an already given total function: it neither defines that function nor proves
termination of an algorithm that lacks an appropriate base cutoff.

Even `0<=C` is unnecessary in this abstract upper-bound version: use the
positive parts of the toll coefficients when choosing the slope below.
The source specialization retains and uses
`0<=C1` when verifying the book's particular displayed constant choice. Likewise
the core needs no separate `0<=rho` or `0<=K`; only the asserted size bound and
`rho<1` enter the proof. This is a useful weakening, not a change to the book's
claim. No total-order or field assumptions are transferred to payloads.

The stated scalar classes support finite maxima and sufficiently large natural
multiples of every positive scalar. Division and floor/ceiling are unnecessary
in the core. Neither completeness, topology, norms, measure theory, real
logarithms, nor differentiability is required. Once the threshold and candidate
constant inequalities are supplied, even the Archimedean assumption is no longer
used by the induction. Its quantitative calculation can remain an internal
helper unless a concrete caller needs that lower-level interface.

This ordered-ring formulation also covers exact integer bounds on already
supplied child maps. For the source's fractional coefficients, a concrete second
scalar setting is rational arithmetic: the coefficients and natural ceilings can be handled
exactly in `Rat`, then the final natural bound can use the existing Real Big-O
bridge. The source Theorem 3.9 specializes to Real. This avoids hard-wiring
analysis imports into a finite arithmetic proof.

### Quantifier order and uniformity

All maps and recurrence parameters are fixed before `exists A B`; the same
constants cover every `n`, including the enlarged base prefix. This is not
`forall n, exists A B`, which would provide no growth information.

For a family `f p n`, applying the theorem separately gives
`forall p, exists A B, forall n`, not automatically
`exists A B, forall p n`. A common recurrence and common finite-prefix bound
would be required for that stronger result. For example, the family
`f p n = p` with natural parameter `p`, zero child maps and zero toll satisfies
a contracting upper recurrence; its values at `n=0` have no common constant
intercept. For selection, the separately proved scalar `F(n)` is the common
majorant, independent of list values and requested rank. Apply this theorem
once to `F`, then compose `Tmom k xs <= F(length xs)`.

## 3. Division-free proof route, including base cases

Let `delta=1-rho>0`. `Archimedean.arch (2*K) delta_pos` gives a natural `M`
with `2*K<=M • delta`. Rewrite the natural scalar multiplication using
`nsmul_eq_mul` and commutativity, and set `N=max n0 (max 1 M)`. Thus
`2*K<=delta*N`, `1<=N`, and the recurrence applies whenever `n>N`.

Let

```text
prefixMax = (Finset.range (N+1)).sup' nonempty f
B = max 0 prefixMax
S = max 0 C + max 0 D + B.
```

The finite prefix contains zero. `Finset.sup'` avoids a complete-lattice
supremum and a separate image construction. The **generic construction chooses
`B>=0`**; that is needed for the compact absorption estimate below. This does
not mean the source's different prescribed prefix maximum must be nonnegative.

Use `Archimedean.arch (2*S) delta_pos` once more to choose a natural `a` with
`2*S<=a • delta`. Set `A=(a:R)`. Then `A>=0` and `A*delta>=2*S`, without
division, floors, or an inverse for `delta`.

Prove `f n<=A*n+B` by `Nat.strongRecOn`:

1. If `n<=N`, `Finset.le_sup'` gives `f n<=prefixMax<=B`; nonnegative `A`
   gives `B<=A*n+B`. This covers **all** `0..N`, including zero and the
   enlarged prefix beyond the original `n0`.
2. For `n>N`, the size bound and cutoff give
   `2*(left n+right n)<=2*rho*n+2*K<=(1+rho)*n<2*n`.
   The final strict inequality uses `rho<1` and `n>0`. Both children are
   nonnegative, so each is strictly below `n`. Reflect these cast inequalities
   back to Nat before applying the induction hypotheses.
3. Because `n>=1`, the slope choice gives

```text
A*delta*n >= 2*S*n >= 2*C*n + 2*D + 2*B.
```

Here `max 0 C>=C`, `max 0 D>=D`, and the nonnegative `max 0 D` and `B`
can be multiplied by `n>=1`. This is why no sign premise on `f,C,D` is needed.
Double the recurrence and use the induction hypotheses and the size bound:

```text
2*f n <= A*(2*(left n+right n)) + 4*B + 2*C*n + 2*D
      <= A*((1+rho)*n) + 4*B + 2*C*n + 2*D
       = 2*A*n - A*delta*n + 4*B + 2*C*n + 2*D
      <= 2*(A*n+B).
```

Cancel the positive scalar two using ordered-ring multiplication laws.
Multiplication monotonicity supplies the displayed inequalities explicitly;
`ring`/`linarith` normalize the remaining expressions. An arithmetic tactic
should not be expected to invent the natural threshold, slope witnesses, or
these multiplication premises.

For sharing the proof with the source's more precise constants, an internal
induction calculation can accept arbitrary `A>=0`, arbitrary `B`, decreasing
children, the size/step bounds, and

```text
0 <= A*delta-C,
A*K+D+B <= (A*delta-C)*N,
forall n<=N, f n<=B.
```

Its step is the equivalent undoubled expression
`A*n+B + (A*K+D+B-(A*delta-C)*n)`. The division-free choices above imply these
conditions because `N>=1`; the source's quotient choices imply them directly.
This calculation needs no field or Archimedean assumption. Keep it internal
unless a checked quantitative consumer justifies exporting it. In either case,
**C03-041/042 and the source's explicit constant-choice argument remain formal
obligations**; a different generic proof does not erase them.

## 4. Exact declarations available at the pin

| Existing API | File and role |
|---|---|
| `Nat.strongRecOn` | Used directly by the pinned Akra–Bazzi development, e.g. `AkraBazziRecurrence.T_pos`. It supplies induction over every smaller natural. |
| `Archimedean.arch`, `exists_lt_nsmul` | `Mathlib.Algebra.Order.Archimedean.Defs`; `arch` supplies a natural multiple of a positive scalar above a prescribed value, without division. Its non-strict form suffices here. |
| `nsmul_eq_mul` | `Mathlib.Algebra.Ring.Defs`; rewrites `m • delta` as `(m:R)*delta`, with commutativity supplying the desired orientation. |
| `exists_nat_gt`, `exists_nat_ge` | `Mathlib.Algebra.Order.Archimedean.Defs`; useful in field/source corollaries and counterexamples, but unnecessary for choosing the ring core's multiples. |
| `Finset.sup'`, `Finset.le_sup'`, `Finset.sup'_le_iff` | `Mathlib.Data.Finset.Lattice.Fold`; a nonempty finite maximum of `f` over `range (N+1)` needs only a semilattice supremum. A linear order supplies it. |
| `Finset.max'`, `Finset.le_max'` | `Mathlib.Data.Finset.Max`; also valid for the image of the finite prefix, but `sup'` avoids that intermediate image. |
| `Nat.ceil_le`, `Nat.lt_ceil` | `Mathlib.Algebra.Order.Floor.Defs`; natural ceiling's characterizations, including negative arguments. |
| `Nat.le_ceil`, `Nat.ceil_mono`, `Nat.ceil_le_ceil`, `Nat.ceil_eq_zero`, `Nat.ceil_lt_add_one`, `Nat.ceil_add_one` | `Mathlib.Algebra.Order.Floor.Semiring`; rounding bounds and comparison. `ceil_lt_add_one` requires a nonnegative argument. |
| `FloorRing.toFloorSemiring`, `Int.ceil_toNat` | `Mathlib.Algebra.Order.Floor.Defs`; the exact bridge from the source's integer-ceiling/convert-to-Nat notation. |
| `FloorRing.archimedean` | `Mathlib.Algebra.Order.Archimedean.Basic`; an ordered field with `FloorRing` already supplies `Archimedean`. The rounded source wrapper need not ask for both independently. |
| `Archimedean.floorRing` | Same file; a construction, not an automatically installed instance. Do not silently replace an existing computable floor instance. |
| Rat `FloorRing` instance | `Mathlib.Data.Rat.Floor`; exact rational source coefficients can use the same rounding laws. |
| `Real.instArchimedean` and Real `FloorRing` instance | `Mathlib.Algebra.Order.Archimedean.Real.Basic`; the simple `Mathlib.Basic.Real.Basic` import deliberately defers these structures. |
| `Nat.instCeilDiv`, `Nat.ceilDiv_eq_add_pred_div`, `ceilDiv_le_iff_le_mul` | `Mathlib.Algebra.Order.Floor.Div`; integer execution formulas `(n+4)/5` and `(7*n+39)/10` have exact ceiling-division bridges. |
| `Resources.isBigO_of_nat_bound` | `Applications/Resources/Growth.lean`; from `forall n>=N, f n<=C*g n` derives Real-cast `IsBigO atTop`. It is already used by `Resources.TreeFlattening.recursive_flatten_theta` and `stack_flatten_theta`. |
| `Nat.log_of_one_lt_of_le`, `Nat.log_pow` | `Mathlib.Data.Nat.Log`; separate floor-halving/logarithmic recurrences. |
| `Nat.clog_of_one_lt`, `Nat.clog_of_two_le`, `Nat.clog_mono_right`, `Nat.clog_pow` | Same file; exact ceiling-halving logarithm and its properties. Use these actual names rather than inventing a logarithm recurrence wrapper. |
| `Real.natFloor_logb_natCast`, `Real.natCeil_logb_natCast` | `Mathlib.Analysis.SpecialFunctions.Log.Base`; bridges between the natural logarithms and the book's real-log notation. |

The suggested core imports start with `Mathlib.Algebra.Order.Archimedean.Defs`,
the needed ordered-ring lemmas, `Mathlib.Data.Finset.Lattice.Fold`,
`Mathlib.Data.Finset.Range`, and the specific arithmetic tactics used. The
broader Archimedean `Basic` file is not needed merely to call `arch`; it imports
rational-floor material. The source rounding/constant-choice adapter adds
ordered-field and floor-semiring facts and the chosen scalar instance.
Real/logarithmic/asymptotic imports should remain in the corresponding clients.

### Why not use a similarly named existing framework directly?

`AkraBazziRecurrence` in `Computability/AkraBazzi/SumTransform.lean` is a genuine
existing general divide-and-conquer framework. Its main results in
`AkraBazzi.lean` are `isBigO_asympBound`, `isBigO_symm_asympBound`, and
`isTheta_asympBound`. The hypotheses include positive weights, contractions,
positive base values, nonnegative polynomially growing toll, decrease, and
`o(n/log^2 n)` perturbations. Its bound uses a critical exponent and an
asymptotic sum transform. The file itself lists common power-toll
specializations as unfinished work. It is available for later analyses but
does not directly supply this signed-base, upper-recurrence, all-input affine
statement. Porting a parallel full Akra–Bazzi structure would be duplication.

`LinearRecurrence.IsSolution` in `Mathlib.Algebra.LinearRecurrence` concerns
fixed-lag sequences `u(n+d)=sum_i a_i*u(n+i)`; it is a different notion of
linear recurrence. `LinearGrowth.linearGrowthInf` and `linearGrowthSup` in
`Analysis/Asymptotics/LinearGrowth.lean` concern limit inferior/superior of
`u(n)/n`, mostly in `EReal`; they do not prove the required induction bound.
Neither is a reason to rename or reproduce existing APIs.

## 5. Recover the rounded source theorem precisely

Set

```text
left n  = ceilNat(a*n+b)
right n = ceilNat(c*n+d)
rho = a+c
K = max 0 b + max 0 d + 2.
```

For each branch, ceiling monotonicity first replaces its offset by its
nonnegative maximum. Since `a,c>0`, the resulting affine arguments on natural
`n` are nonnegative; `Nat.ceil_lt_add_one` then bounds each rounded size by
the corresponding argument plus one. Adding gives the core size hypothesis.
The source recurrence equality supplies the upper recurrence.

The original proof's sufficient child thresholds
`N >= (max 0 b+1)/(1-a)` and `N >= (max 0 d+1)/(1-c)` can be recovered from
the larger combined threshold, but the core proof can show each child is
smaller directly from their sum. Retain these displayed inequalities as checked
source corollaries if needed by the obligation ledger; they do not require a
second recursion principle.

The source's `N=max n0 ceilNat(K/(1-a-c)+1)` and printed alternative
`max n0 (ceilNat(K/(1-a-c))+1)` agree because this ratio is nonnegative and
`Nat.ceil_add_one` applies. The source chooses `B` as the finite prefix maximum
and `A=max(C1/(1-a-c), (C1*N+C2+B)/((1-a-c)*N-K))`. This is a distinct,
quantitatively sharper choice than the division-free existence construction.
With `C1>=0`, `A>=0`; the denominator is positive, and multiplying the two
defining inequalities by their positive denominators gives exactly the
nonnegative-slope and absorption hypotheses in the internal calculation above.
Thus the source's displayed witness, **including possibly negative `B`**, has
its own checked-bound target. Retain C03-041/042 explicitly rather than
substituting the generic construction's nonnegative intercept or larger threshold.

For a natural cost, cast the recurrence into Rat or Real, obtain `A,B`, and
use `Nat.le_ceil` to bound them by `ceilNat A`, `ceilNat B`. Multiplication by
the nonnegative natural input preserves the inequality. A natural affine bound
`f n<=A_nat*n+B_nat` then gives, for `1<=n`,
`f n<=(A_nat+B_nat)*n`. Apply `Resources.isBigO_of_nat_bound` with threshold
`1`. The zero input remains covered by the original affine theorem.

A one-sided bound for an arbitrary signed function is not alone a norm bound:
`-n^2<=0` demonstrates the distinction. For the book's natural work, nonnegative
casts make the Big-O bridge valid. If a future signed client needs a norm bound,
bound its absolute-value recurrence explicitly rather than silently treating
one-sided order as a norm estimate.

## 6. Connected clients and exact constants

### Median-of-medians: source constants, not only an asymptotic label

Use the actual scalar recurrence

```text
F n = 483                                             if n<=20
F n = F ((n+4)/5) + F ((7*n+39)/10) + 19*n+54          if n>20.
```

Its executable definition still needs both child arguments `<n` for `n>20`.
Its separate monotonicity proof is used when actual partition lengths are
replaced by upper bounds; the generic recurrence lemma does not assume or
supply that property. The shared helper-cost and pivot-balance proofs must
establish `Tmom k xs<=F(length xs)` uniformly over valid ranks before applying
the affine conclusion.

The source coefficients give `rho=9/10`, `K=5`, `C=19`, `D=54`. The
division-free generic proof admits concrete witnesses

```text
N=100, B=F 100=10930, A=220060.
```

Indeed `2*K=delta*N=10`, and
`A*delta=22006=2*(19+54+10930)`. Monotonicity of `F` supplies the common prefix
bound. This yields a connected generic-theorem target
`F n<=220060*n+10930`; the same constants then bound every valid measured
selection through its already established scalar majorant.

An additional explicit choice following the source's sharper quantitative
argument is

```text
N=51, B=F 51=6341, A=73640.
```

Monotonicity supplies the prefix bound through `F 51`. The denominator is
`(1/10)*51-5=1/10`, and the chosen slope is the source maximum
`max 190 ((19*51+54+6341)/(1/10))=73640`. Its absorption inequality holds with
equality: both sides are `374595`. Thus a proposed concrete client can prove
`F n<=73640*n+6341`, then the same uniform selector bound. These constants are
deliberately loose; optimizing them is unnecessary for coverage.

The exact finite values `F 0=F 1=483`, `F 21=1419`, `F 51=6341`, and
`F 100=10930`, plus both constant calculations, were independently recomputed
using integer/rational arithmetic in a local Python model. A bounded check
through `n=2000` was only
a sanity check; it is not a universal proof or Lean validation. Future Lean
clients should derive the universal bound from the theorem, not from testing.

The generalized grouping exercise is a genuine second use of the same core.
For fixed positive group size `l`, the smaller recursive input contributes
fraction `1/l`, while the retained strict partition contributes
`(l+floor(l/2))/(2*l)` plus a proved rounding constant. Their sum is below
one for odd `l>=5` and even `l>=6`. The appropriate size bounds, cutoff,
per-group insertion cost, and finite base bound still have to be supplied.
The generic lemma does not manufacture those algorithm-specific premises.

### Later trees: retain the strongest relevant source arguments

| Source case | Exact recurrence boundary | Reuse decision |
|---|---|---|
| Chapter 7 `join_all` | One recursive joined sequence; slot count halves and the pass costs at most `floor(m/2)`, plus one entry. Singleton base costs one. The source proves `T_join_all<=2*m`, then total conversion `<=3*n+3`. | Direct computation induction proves the displayed constant more simply. A scalar one-branch halving majorant is a related affine example, but adding a dummy second branch or a new arity framework is unnecessary. |
| Chapter 4 `bal`, Exercise 4.9 | On valid prefix domains, `T(0)=1`, `T(n)=T(n/2)+T(n-1-n/2)+1`; child sizes sum to `n-1`. | Prove exact `2*n+1` by natural strong induction. The sum has no fixed contraction factor below one. The sequential suffix/value domain remains separate. |
| Chapter 4 accumulator inorder | Two structural child calls and one entry; exact `2*nodes+1` in the stated tariff. | Structural induction, preserving value correspondence. Direct append-based inorder has different shape-dependent costs. |
| Chapter 11 shared Braun initialization | One actual recursive pair computation at `(n-1)/2`, with constant local work. | Use existing natural log recurrences for the logarithmic bound. Expanding the shared pair into separate recursive calls changes the execution. |
| Chapter 11 `brauns` | Remaining input is `drop (2^k) xs`; local cost is at most `4*min(2^k,n)+5`; index `k` increases. Source `T_brauns_ub` is `<=9*(n+1)` uniformly in `k`. | Induct on remaining length while generalizing `k`; use consumed-size identity `min(m,n)+(n-m)=n`. No fixed fractional shrink holds uniformly at `k=0`. |
| Chapter 11 `list_fast_rec` | Forest list length can grow; total child node count drops by the count of nonempty roots. Source bound is `14*sum nodes + forestLength + 2`. | Preserve this two-observation induction. A bound in forest length alone, or scalarizing away the additive forest term, would lose the base cost for empty-tree entries. |
| Existing conaled tree flattening | `fromTWithCost_perfect_exact` has `2*cost+2=(p+4)*2^p`; stack traversal has `cost=2*2^p`. | Reuse `recursive_flatten_theta`, `stack_flatten_theta`, and the existing natural-to-Real growth bridge as composition examples. They already distinguish different executions with equal output. |

## 7. Boundary counterexamples to preserve

### Removing strict contraction permits superlinear cost

Define a natural recurrence with valid decreasing children:

```text
H n = 1                                      if n<=1
H n = 2*H ((n+1)/2) + n + 1                  if n>1.
```

It has positive bases and positive linear and constant toll, and corresponds
to source parameters `a=c=1/2`, `b=d=0`, `C1=C2=1`. Each child is smaller
for `n>1`, but `a+c=1`. At powers of two, induction gives

```text
H (2^k) = (k+2)*2^k - 1 >= (k+1)*2^k.
```

Hence no constants `A,B` bound every `H n` by `A*n+B`: choosing a natural
`k+1>A+max(0,B)` contradicts that inequality at `n=2^k`, since `2^k>=1`.
The first values at powers `1,2,4,8,16` are `1,5,15,39,95`, independently
checked arithmetically. The universal powers formula and unbounded-ratio
argument, not those values, are the future formal counterexample.

This does not assert contraction is necessary for every linear recurrence:
the constant-toll tree balancer in the table is linear at total asymptotic
child fraction one. The source theorem is a sufficient result; an asserted
converse requires its separate positive-toll and other source hypotheses.

### Ignoring natural-ceiling truncation is false

For `x=-2`, `Nat.ceil x=0`, whereas `x+1=-1`; therefore the unrestricted claim
`(Nat.ceil x:R)<=x+1` is false. Replace negative offsets by their nonnegative
maxima before invoking `Nat.ceil_lt_add_one`, or handle the negative argument
case using `Nat.ceil_eq_zero`. Dropping this boundary would invalidate the
source's allowed negative offsets.

### Enlarging a proof cutoff does not repair a recursive definition

For the median-of-medians scalar bound, `B(13)=(7*13+39)/10=13`.
A recurrence definition that begins recursing at that size cannot justify
termination with strict size decrease merely because the later affine proof
chooses `N=51`. The actual source uses cutoff `20`, whose recursive arguments
do decrease. Prove definition-level decrease before applying the theorem to
the resulting total function.

## 8. Minimal integration boundary

A focused `Applications/Resources/AffineRecurrence.lean` can hold the ordinary
generic theorem and its rounded/natural source specializations if they have
checked consumers. This keeps real analysis out of value-only selection and
sequence modules and avoids swelling the existing small `Growth.lean` helper
with unused analytical machinery. Use the existing asymptotic bridge in clients.
Do not export a renamed copy of `Nat.ceil`, a second logarithm, an alternative
Akra–Bazzi record, or a generic induction wrapper without a demonstrated need.

The acceptance evidence should connect an actual scalar source recurrence,
its all-base-case bound and exact rounding to the theorem, and then connect
that scalar bound to the measured selector. Include the rational/real
specialization and the contraction counterexample. Later tree exact bounds
remain their chapter obligations. The research calculations here are proof
targets and design evidence only; root owns implementation, compilation, audit,
and the already established review process.
