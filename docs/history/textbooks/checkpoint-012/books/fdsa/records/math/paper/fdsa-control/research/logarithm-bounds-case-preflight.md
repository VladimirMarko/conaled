# XL01: logarithm bounds — independent case preflight

Prepared 2026-11-03 for `FDSA-XL01`. This is a **report-only mathematical and
source-level assessment**, within the existing root workflow. The complete
ticket was read first and this path was absent before writing. Only this report
is writable in this assignment. No source scope, implementation base, public
name, executor, tariff, worktree, compiler or acceptance is selected here.
Chapter 1 attempt 3 remains the sole authorized validator; its active output
was not inspected. All original obligations and earlier outcomes are retained.

## 1. Conclusion and intended use of the cases

The positive-input sharp base-two sum inequality is a real shared dependency:
the pairing first-pass proof uses it directly, and the splay proof uses its
strict `+1` consequence. The same mathematical fact can be tested meaningfully
at external-leaf counts and at the pairing arguments `(n1+n2+1, m+1)`. The
all-zero size instance also distinguishes the retained correct `+2` sum from
the manuscript's already-recorded `+1` error. These are connected scalar
clients, not substitute algorithms or coverage of the later chapters.

The smallest plausible shared implementation is the sharp result and its
strict corollary, using ordinary `Real.logb` and existing arithmetic APIs.
The nonnegative shifted-product result and skew's weaker general-base result
can be direct clients of those existing primitives; a new public wrapper for
each source name is not established by these cases. The final shifted-minus-one
helper has an exact source statement but no named consumer in the source
author's bounded retained-theory search. Preserve its statement and the book
inventory; do not promote it solely because the containing theory is imported.

All calculations below are exact. No floating-point logarithm, Lean execution,
generated test, new tree operation or new resource interpretation was used.
Some boundary cases deliberately violate a hypothesis and are marked as such.
They test the proposed *statement*, rather than providing additional valid
instances of the source algorithm.

## 2. Exact source claims

Write `L(x) = Real.logb 2 x` and `Lb(x) = Real.logb b x`. Variables in this
table are Real. The tags are local descriptions, not new ticket obligations.

| Tag / actual source | Exact conclusion | Exact source domain |
|---|---|---|
| A — `Lemmas_log.thy:5–16`, `ld_sum_inequality` | `L(x)+L(y)+2 ≤ 2*L(x+y)` | `0<x`, `0<y` |
| B — `Lemmas_log.thy:18–20`, `ld_ld_1_less` | `1+L(x)+L(y) < 2*L(x+y)` | `0<x`, `0<y` |
| C — `Lemmas_log.thy:32–41`, `ld_le_2ld` | `L(1+x+y) ≤ 1+L(1+x)+L(1+y)` | `0≤x`, `0≤y` |
| D — `Lemmas_log.thy:43–53`, `ld_ld_less2` | `1+L(x)+L(y) ≤ 2*L(x+y-1)` | `2≤x`, `2≤y` |
| E — `Skew_Heap_Analysis.thy:52–54`, `plus_log_le_2log_plus` | `Lb(x)+Lb(y) ≤ 2*Lb(x+y)` | `1<b`, `0<x`, `0<y` |

A follows from `4*x*y ≤ (x+y)^2`, itself the nonnegativity of `(x-y)^2`.
B follows by removing one from A's left side, so the strictness is essential
and does not need a second concavity theorem. C's source proof first bounds
`1+x+y` by `(1+x)*(1+y)`. In fact the same nonnegative domain proves C without
its extra `1`; the recorded source constant is retained. D uses
`2*x*y ≤ (x+y-1)^2`. E bounds each summand by the logarithm of the sum and
does not assert a base-independent AM–GM constant of `2`.

These exact claims were read in the retained source rather than inferred
from theorem names. The source-file identities and the reading limits
are recorded in section 10. Lines 21–30 of `Lemmas_log.thy` are a commented
alternative proof, not an additional result.

## 3. Compact scalar cases and missing-premise witnesses

### 3.1 Sharpness, strictness, and positive arguments below one

The same two equal-input cases establish three different boundaries.

| Inputs | A, sharp `+2` | B, strict `+1` | Meaning |
|---|---|---|---|
| `x=y=1` | `2 = 2` | `1 < 2` | The additive constant `2` is attained. Replacing A's `≤` by `<`, or replacing `+2` by any larger real constant, is false. |
| `x=y=1/4` | `-2 = -2` | `-3 < -2` | Both inputs are positive, but their logarithms and both sides of A are negative. The valid domain is not restricted to arguments at least one. |

The second row uses `L(1/4)=-2` and `L(1/2)=-1`, obtained from the power and
inverse laws at base two. There is no numerical approximation. More generally,
at every positive equal input `t`, `L(2*t)=1+L(t)` makes A an equality; the
single `t=1` case already refutes every proposed larger uniform constant.

These cases have different roles. The unit case is also the external-leaf
count of an empty tree, and the pairing first-pass all-zero size substitution.
The quarter case is a scalar-domain case. It is not a possible unweighted
external-leaf count, and it must not be advertised as a source splay-tree
fixture. Section 8 separately discusses the genuinely weighted paper domain.

### 3.2 Zero and totalization do not remove positivity

In the pinned Lean library `Real.logb b 0 = 0`. Thus the proposed extension of
A from positive to merely nonnegative inputs fails at `x=0,y=1/4`:

`L(0)+L(1/4)+2 = 0`, whereas `2*L(1/4) = -4`.

The required comparison would be `0≤-4`. At `x=0,y=1`, A and B would instead
assert `2≤0` and `1<0`. E also fails on a zero input at base two: the quarter
instance would say `-2≤-4`. It is useful to retain the quarter witness because
E happens to be true at `x=0,y=1`; that single accidental equality would not
test its positivity premise.

The pinned library also gives `logb b (-x)=logb b x`. This totalization is not
a permission to state the source inequalities over all Real inputs. For
example `x=1,y=-1` would make A say `2≤0`. These are explicit counterexamples
to proposed Lean overclaims, not assertions about equality of Isabelle and
Lean logarithm totalizations outside the intended positive domain.

### 3.3 Nonnegative child sizes and shifted products

C must admit zeros: at `x=y=0` it says `0≤1`; at `x=0,y=1` it says `1≤2`.
These are real source cases for empty child forests. Replacing its premises by
strict positivity would unnecessarily exclude actual nonempty heaps whose
children are empty. The stronger zero-slack bound has equality in both cases,
since the product difference is exactly `x*y`.

Conversely, requiring only the three displayed log arguments to be positive
does not justify C. Set `x=-3/4,y=1`. Then

`1+x+y=5/4`, `1+x=1/4`, `1+y=2`,

all strictly positive, but C becomes `L(5/4)≤0`. This is false because
`5/4>1`. The counterexample isolates the lost nonnegative-factor condition;
it does not rely on log zero or log of a negative value.

The source `+1` is slack, not an executed operation or a claim of sharpness.
Proving the stronger scalar inequality does not authorize changing a stated
pairing-heap cost bound, changing its tariff, or bypassing its potential
cancellation and representation hypotheses.

### 3.4 The real subtraction in D

At the source lower corner `x=y=2`, D says `3≤2*L(3)`. Applying monotonicity
to the exactly equivalent product comparison `8≤9` proves it, without a
decimal estimate. At positive `x=y=1`, the shifted argument is still positive
but D would say `1≤0`. Thus positivity of the original and shifted arguments
alone is insufficient, and even `x,y≥1` is insufficient.

At `x=0,y=2` the shifted argument is `1`, yet the conclusion would say `2≤0`.
Conversely, at `x=y=1/2` the shifted argument is zero and the totalized formula
happens to say `-1≤0`. An accidental true zero-log instance cannot justify
using a rank outside the source lemma's stated domain as though it satisfied it.

The hypotheses `x,y≥2` are sufficient source hypotheses, not individually
minimal. Indeed

`(x+y-1)^2 - 2*x*y = (x-1)^2 + (y-1)^2 - 1`.

If `x≥2` and merely `y>0`, this is nonnegative and `x+y-1>0`, so the same
inequality already follows; `x=2,y=1` gives equality `2=2`. This observation
prevents a false minimality claim. It is not a request to add an optimized
domain theorem or extend the unit without a selected consumer.

### 3.5 Increasing base and its constant

E at base two and `x=y=1/4` gives `-4≤-2`, another valid negative-log case.
For a decreasing base, choose `b=1/2,x=y=1`: `log_(1/2)(2)=-1`, so E would
say `0≤-2`. This refutes the omission of `b>1` even with positive inputs and
a positive base different from one.

At `b=4,x=y=1`, the *actual weak* E says `0≤1` and is true. Copying A's `+2`
unchanged to that base would say `2≤1` and is false. The corresponding sharp
general-base constant would be `2*logb b 2`, not uniformly `2`; no such new
generalization is required by the source uses under assessment.

At bases `0` and `1`, the pinned Lean `logb` is identically zero. E's bare
formula therefore has accidental true instances there. They do not supply
the source's monotone logarithm or justify dropping its base premise. No
general-base wrapper should conflate these cases with the increasing domain.

## 4. Connected substitutions into actual tree observations

Let `ell(t)=t.numLeaves` for the existing ordinary `BinaryTree` carrier. The
pinned public laws give `ell(t)=t.numNodes+1` and `0<ell(t)` even for `nil`.
After casting to Real, `ell(t)≥1` is available without a search-tree invariant,
heap validity, cached summary, balance hypothesis, payload order or inhabitance.

For `l : BinaryTree α` and `r : BinaryTree β`, in independent universes, A and
B can be instantiated at `x=(ell(l):Real)`, `y=(ell(r):Real)`. This is already
a useful actual-API composition. If the labels share a type and a root label
`a` is supplied, the existing node recurrence identifies their sum with
`ell(BinaryTree.node a l r)`. Neither the scalar claim nor the independent-type
version needs a newly invented common tree carrier.

The compact expected values are:

| Existing shape inputs | Leaf counts | A | B |
|---|---:|---|---|
| `nil`, `nil` | `1,1` | `2=2` | `1<2` |
| Two singleton children, as in `TreeCacheExamples.balancedThree` | `2,2` | `4=4` | `3<4` |

For `α=Empty`, the existing `nil : BinaryTree Empty` still supports the first
row. There is no default payload and no claim that a nonempty tree or a node
at every natural size exists for an empty payload type. Label mapping retains
the same counts by the existing arbitrary-map laws, so the numerical claims
are insensitive to changing labels; no injectivity premise is needed.

The actual splay `zig_zig` calculation at `Splay_Tree_Analysis.thy:24–44`
uses B with `x=size1 lb`, `y=size1 A'` after an induction estimate and exact
potential cancellation. Its surrounding premise includes `lb≠Leaf`, so the
`nil,nil` scalar case is not a complete instance of that branch. The `2,2`
row tests a permitted size substitution, but does not establish all of that
branch's subtree-membership, reconstruction, query or timing premises.

The saved XT02 `ShapeLog` already proves raw
`minHeight t ≤ log₂(ell(t)) ≤ height t` after Real casts, and exact rounded
identities under `AlmostComplete`. It does not provide A or B. Conversely,
the scalar inequalities do not establish balance: the reused `balancedThree`
and `leftThree` both have three nodes and four external leaves, hence the
same logarithm `2`, while their heights are respectively `2` and `3`.
No complexity or worst-case path bound follows from the new arithmetic alone.

## 5. Pairing first-pass connection and the retained correction

`Pairing_Heap_List2_Analysis.thy:101–117` uses actual child-forest sizes
`n1,n2` and remaining-forest size `m`. Its A substitution is

`x=(n1:Real)+(n2:Real)+1`, `y=(m:Real)+1`.

Both arguments are positive for every natural `n1,n2,m`, including zero.
Their sum is exactly `n1+n2+m+2` after the same casts. Therefore the connected
scalar conclusion is

`L(n1+n2+1)+L(m+1)+2 ≤ 2*L(n1+n2+m+2)`.

At `n1=n2=m=0`, corresponding to two singleton heads and an empty suffix,
the correct instance is `2≤2`. In the full intermediate expression at source
lines 110–113, the remaining logarithms are `L(1)=0` and the remaining suffix
term is zero, so the left side is exactly `2`, and the correct right side is
`2*L(2)=2`. Replacing the final sum by the printed `n1+n2+m+1` instead gives
`2≤0`. This independently recovers the already-retained `C23-052` witness.
It is not a new finding, a new obligation, or permission to weaken the
unchanged Lemma 23.2 target. The actual companion source uses `+2`.

A second source connection tests C's zero domain without inventing a new
algorithm. In `Pairing_Heap_Tree_Analysis.thy:47–65`, the two arguments are
the node counts of the possibly empty children of two nonempty whole roots.
When both children are empty, the displayed exact potential difference is

`L(1)+L(2)-L(1)-L(1) = 1`.

The source upper estimate is `L(2)+1=2`. Its `1≤2` slack is compatible with
C at `x=y=0`; using the stronger zero-slack scalar bound would make this
particular estimate `1≤1`. This does not establish a new runtime constant.
The source still assumes whole-root shapes `Node hs1 x1 Leaf` and
`Node hs2 x2 Leaf`; arbitrary forests are not interchangeable with these
binary heap values. List2 uses its own forest potential, including later
siblings, and its own merge estimate. Similar logarithms do not identify
the two potentials or prove their representation/cost bridge.

## 6. Skew composition and casts

The actual skew merge analysis first bounds a signed Int charge using three
spine counts. Only after that does it cast to Real and use logarithms
(`Skew_Heap_Analysis.thy:59–110`). Its potential counts right-heavy nodes;
it is not a sum of real logarithmic ranks. E is one final arithmetic step,
applied at positive `ell(t1),ell(t2)` with base two.

The exact size observation is

`ell(merge t1 t2) = ell(t1)+ell(t2)-1`.

The external-leaf lower bounds imply the Real shifted argument is at least
one, so the separate monotone comparison
`L(ell(t1)+ell(t2)-1) ≤ L(ell(t1)+ell(t2))` is justified. For two empty
trees, the two input counts are `1,1`, the output count is `1`, and this
comparison is `0≤1`; E contributes `0≤2`. These are scalar and size
observations, not a claimed exact `T_merge` measurement.

Nat subtraction must be handled before rewriting the cast. On the actual
leaf-count domain `1≤ell(t1)+ell(t2)`, the predecessor cast agrees with the
Real subtraction. Without that premise, `((0+0-1 : Nat):Real)=0`, whereas
`(0:Real)+(0:Real)-1=-1`. The two expressions are not definitionally or
universally equal. Likewise, signed potential differences must not be moved
into truncated natural subtraction; the source's Int charge and subsequent
Real cast have substantive roles.

Neither A nor E proves the three spine estimates, the actual recursive
merge/potential relation, or the coefficient `3` in the final bound. The
source framework's wrapper tariffs and outside-log constants also remain
separate. No operation is charged here for evaluating a mathematical Real
logarithm or traversing all subtrees to recompute a potential.

## 7. Exact existing library connections

The following are the actual pinned interfaces directly read for this report,
not proposed replacement definitions. Implicit base arguments and section
premises are stated explicitly in this table to prevent accidental omission.

| Existing public interface | Meaningful connection and limitation |
|---|---|
| `Real.logb_mul (hx : x≠0) (hy : y≠0)` | Expands `logb b (x*y)`. Positive inputs discharge the nonzero premises, but the product identity itself does not prove the monotone inequality. |
| `Real.logb_pow b x k` | Gives `logb b (x^k)=k*logb b x` for natural `k`. It supplies the square in A/D and exact dyadic values; its broad totalized domain must not be confused with the source inequality's domain. |
| `Real.logb_self_eq_one hb`, `Real.logb_one`, `Real.logb_inv b x` | Normalize base-two powers and inverses and the unit leaf count. The `hb` here is `1<b`. |
| `Real.logb_le_logb_of_le hb hx hxy` | Uses `1<b`, `0<x`, `x≤y`. Directly gives E's two comparisons and C's product comparison. |
| `Real.logb_lt_logb hb hx hxy` | Uses `1<b`, `0<x`, `x<y`. Certifies `L(5/4)>0` and exposes the missing-premise counterexample without decimals. |
| `Real.logb_nonneg hb hx` | Requires `1≤x`, not merely `0<x`. Exactly the scalar domain fact needed for the actual unweighted potentials. |
| `Real.logb_le_logb_of_base_lt_one` | Under `0<b<1`, reverses the ordering of positive arguments; explains the base-one-half counterexample. |
| `BinaryTree.numLeaves_pos`, `BinaryTree.numLeaves_eq_numNodes_succ`, existing count/map/node laws | Discharge the actual structural positivity and Natcast premises without an order, cache, or balanced-tree assumption. |
| `Trees.minHeight_le_logb_numLeaves`, `Trees.logb_numLeaves_le_height` | Reuse existing raw tree-height inequalities at XT02; exact floor/ceiling results retain their own `AlmostComplete` premise. |

An elementary proof of A can compare `4*x*y` with `(x+y)^2`, apply the
existing monotonicity result, and expand products/powers. B is then strict
linear arithmetic. E needs only two applications of monotonicity and addition.
C uses `(1+x)*(1+y)-(1+x+y)=x*y≥0`. These are source-level proof routes, not
claims that a particular uncompiled Lean script elaborates. A broader Jensen,
rank, logarithm, expectation or cost framework is unnecessary for these uses.

## 8. Actual potentials, the weighted boundary, and XP01

### 8.1 Similar shapes do not identify potentials

For the same ordinary singleton shape, the inspected source recurrences give
different potentials:

| Source potential | Singleton value | Reason |
|---|---:|---|
| Splay Base `Φ` | `1` | The root contributes `L(numNodes+1)=L(2)`; empty-child potentials are zero. |
| Binary pairing `Φ` | `0` | The root contributes `L(numNodes)=L(1)`. |
| Skew `Φ` | `0` | Equal empty child sizes make the right-heavy indicator zero. |

The splay Base rank arguments are external-leaf counts at least one. The
binary pairing rank is called at nonempty nodes with node count at least one.
List2's forest-node argument also has a `+1`. Their log nonnegativity follows
from those facts, and empty potentials are supplied by actual base equations.
A heap-order or BST premise is not needed just to prove these shape-based
potential nonnegativity statements.

The file `Splay_Tree_Analysis_Optimal.thy` is not a weighted-key analysis.
Its locale fixes a base `α>1` and a coefficient `β`, assumes three product
inequalities on variables at least one, and uses
`β*log_α(ell(l)+ell(r))`. The inspected `α=cuberoot(4),β=1/3` instance has
improved unweighted coefficients. Its title does not establish Static
Optimality, and it has no named use of the four `Lemmas_log` helpers. The
separate original `C21-098–101` obligations remain intact.

### 8.2 What the separate weighted paper actually permits

The retained Sleator–Tarjan primary paper, printed p.658, defines an arbitrary
fixed positive weight per item, weighted subtree size as their sum, rank as
the binary logarithm of that size, and tree potential as the sum of node ranks.
Printed p.659 uses weights `1/n` or `q(i)/m` and separately bounds the net
potential decrease. These are different source definitions from the saved
companion's unweighted external-leaf ranks.

In that positive-weight domain, a singleton of weight `1/4` has weighted size
`1/4`, rank `-2` and summed potential `-2`. Hence positivity of weights does
not imply potential nonnegativity. This is a counterexample to a *proposed
overgeneralization* of the unweighted argument and a boundary for the separate
weighted/static-optimality work. It is not a new weighted implementation,
required XL01 tree fixture, or counterexample to the unweighted source theorem.
The primary paper's rotation-based cost and its net-decrease accounting are
not silently identified with the companion's recursive tariff.

For Static Optimality, the retained inventory explicitly preserves positive
access frequencies, the initial/final potential contribution, the actual
algorithm/cost bridge and the separate static-BST comparison. The scalar
quarter example proves none of those claims and does not license evaluating
`log(m/0)` or discarding startup terms.

### 8.3 Reuse the actual accounting API without hiding its premises

At retained XP01 revision `c28ba71863d2a35ee1c3a089caa90464e4cca692`,
`Resources.run_potential_map_of_invariant` proves, along the actual
state trajectory,

`h(totalWork)+potential(finalState) ≤ potential(initialState)+actualBudget`.

It takes the preserved-domain closure and each actual local inequality.
`run_potential_map_exact_of_invariant` gives the equality version;
`budget_amortized` expresses signed-group telescoping. They do not require
the potential to be nonnegative. By contrast,
`run_cost_le_map_of_invariant` requires
`∀ s, P s → 0≤potential s` before dropping the final term. It still retains
the initial potential. The existing examples use `Nat.castAddMonoidHom Real`
and distinguish raw work from signed/fractional accounting values.

An exact scalar boundary demonstrates why this matters: let initial potential
be `L(1)=0`, final potential `L(1/4)=-2`, and raw work zero. The exact local
accounting charge is `-2`, so `0+(-2)=0+(-2)` is a valid boundary equality.
Dropping the final potential would assert `0≤-2`. This is an algebraic
counterexample to the omitted nonnegativity premise, not a claimed transition
of the fixed-weight splay algorithm and not a newly proposed executor.

The existing XP01 `InitialCredit` example already shows why the initial term
cannot be discarded: its actual two-step raw work is `2`, while its actual
budget is `0`. The `Fractional` example already supplies an invariant-local
Real accounting client. Reuse those interfaces rather than creating a second
log-specific potential framework. XP01 remains an unaccepted draft.

For skew/pairing merge, the actual source expression subtracts the potentials
of both inputs. A scalar inequality does not choose how both input occurrences
are represented or consumed in a history. Unary XP01 does not authorize
repeatedly spending the potential of a persistent old heap. That multi-input
configuration/ownership and actual-cost work remains with the chapter.

## 9. Minimum connected evidence and preserved scope

A later root-selected pure unit could keep the following compact connections,
rather than a family of per-helper fixtures:

1. A and B at independent-type external-leaf counts, with the nil/Empty and
   singleton-child exact values, using existing count laws.
2. The actual pairing first-pass substitution for arbitrary natural
   `n1,n2,m`, plus the retained all-zero `+2`/`+1` counterexample.
3. The quarter-domain case and the zero-quarter counterexample, which jointly
   distinguish positivity, sign, sharpness and target totalization.
4. If C or E is included as a client, its real source substitution and the
   needed zero-child/base premise, using the existing logarithm API directly.

The other calculations in this report document statement limits; they do not
automatically become new exports or required formal fixtures. In particular,
the weighted singleton, accounting scalar boundary, D's domain comparison and
base-four overclaim are review evidence, not a request to implement more
algorithms, a general potential library, or every optional source theorem.

Actual shared consumers are `C21-074` and `C23-046`, with the retained
`C23-052` substitution correction. Direct primitive reuse also supports the
arithmetic component of `C22-056` and the shifted binary-pairing estimate.
The splay/tree/pairing algorithms, source tariff reconstructions, invariants,
exact cancellation, heap/BST semantics, history bounds, allocation models,
exercises and separate static-optimality claims remain chapter obligations.
No theorem here establishes asymptotic complexity from a few examples.

There is no basis to narrow the book, accept a chapter, change any obligation,
or rewrite the exact initial C2 prefix
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. Root owns any later scope decision,
checkpoint and author release. The existing unknown/failed validation outcomes
and the sole active C1 gate are unaffected.

## 10. Inputs, source correspondence and limits

### 10.1 Directly inspected retained source

Paths in this table are under `book-source/`. Hashes identify the exact reading
copies; reading limits are stated separately so that a scoped search is not
presented as a complete source review.

| File | Bytes / lines | SHA-256 | Direct reading boundary |
|---|---:|---|---|
| `Lemmas_log.thy` | 1,768 /55 | `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41` | Complete file. |
| `Splay_Tree_Analysis_Base.thy` | 4,591 /119 | `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17` | Complete file. |
| `Splay_Tree_Analysis.thy` | 20,301 /432 | `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012` | Lines 1–45; scoped logarithm/helper search elsewhere. |
| `Splay_Tree_Analysis_Optimal.thy` | 21,840 /495 | `511162539e9b8cab7bf804db673c82d2d534d6365098cc81525914506df0b73d` | Lines 10–38, 293–340; scoped logarithm/helper search elsewhere. |
| `Pairing_Heap_Tree_Analysis.thy` | 9,817 /251 | `0e7f8008a2d06c7dbc2f8647b05f87324dafab5ff96daa96097bb2722cfdc368` | Lines 19–65 and scoped helper/potential search. |
| `Pairing_Heap_Tree_Analysis2.thy` | 9,180 /236 | `a04e140d2ff71d11bafd9e16e39359bcf132b194d7cbfe9a27206f261e53d191` | Scoped helper/potential search; complete source correspondence supplied by the stopped source report. |
| `Pairing_Heap_List2_Analysis.thy` | 9,794 /271 | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` | Lines 101–117 and scoped size/potential/helper search. |
| `Skew_Heap_Analysis.thy` | 7,443 /199 | `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b` | Lines 1–112 and scoped logarithm search. |

The complete stopped source report was then read for correspondence, followed
by its sole namespace-citation correction. Final
`fdsa-control/research/logarithm-bounds-source-preflight.md` is 30,310 bytes /427
lines, SHA-256
`f7891e3ccbe07e56499f36c52d2024246758ff6a127cdf9b576f7445e5e4ae73`.
It confirms these exact statements, the active versus commented splay uses,
the representation-specific pairing domains, the retained C23 correction,
and the absence of a named D consumer in its scoped search. The independent
expectations above were calculated before that final correspondence read.
The fully read preceding source snapshot was
`2fb3d6fbe19b5a3954df573efd7ecf8f823041d486725e118c56107eee74f6ed`; its
only later change corrects the cited concavity theorem to the root namespace.

The complete stopped API report was also read:
`fdsa-control/research/logarithm-bounds-api-preflight.md`, 32,941 bytes /322
lines, SHA-256
`d013d148aea4b7949f7e8c66a7fed3ef32456565073453d1d3cabdf8fa357a5c`.
Its actual public signatures, scoped absence finding and minimal A/B
recommendation agree with this case assessment. Its proposed path/names are
proposals, not existing declarations or a scope freeze. This report uses
the actual `Resources` namespace for XP01, as checked in the retained file.

The source author also records equality of these reading copies with members
of the retained dated `afp-Amortized_Complexity-2026-10-26.tar.gz` (31,633
bytes, SHA-256
`d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`).
That archive comparison and its licensing/provenance assessment are credited
to the source report; this case task did not repeat the archive operation.
The archive postdates the retained July 27 manuscript and is not asserted to
be the manuscript's generating revision. AFP provenance must not be replaced
by the unrelated Isabelle tree-theory revision.

The separately inspected retained primary paper is
`book-source/sleator-tarjan-1985-self-adjusting.pdf`, 6,073,769 bytes, SHA-256
`33fe18c5aec145c30bd32fe155d05e25ffa9999f043c3422d0ea66de6ce14364`.
Printed pp.657–659 supply the accounting/weighted-rank/static-optimality
context; printed p.654 was read for background. Text extraction was read in
memory, with no saved extraction or new retrieval. This report paraphrases
only that bounded context; it does not claim a complete paper review,
implementation proof, or reuse of the AFP license for the ACM paper.

### 10.2 Pinned Lean and retained project inputs

Mathlib pin: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`Mathlib/Analysis/SpecialFunctions/Log/Base.lean` is 25,117 bytes /632 lines,
SHA-256 `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf`.
The actual ranges 37–96, 120–130, 178–240 and 267–289 were read, with scoped
declaration searches elsewhere. The related zero/negative/inverse declarations
in `Log/Basic.lean` were searched; that file is 28,165 bytes /713 lines,
SHA-256 `11c6334aeb0f1a4919fce9e9b4b3a4cc65d53e3f19e65b02ae79d215f07aee4d`.

| Exact retained revision / path | Bytes / lines | SHA-256 | Use |
|---|---:|---|---|
| XP01 `c28ba71863d2a35ee1c3a089caa90464e4cca692`, `Applications/Resources/Potential.lean` | 11,523 /238 | `fa33b209a7c8cd700e7a33a6d3ee11ef9ad572c2d2e8406dfbabf6468ebf7d8c` | Actual lines 43–165: invariant-local boundary, exact boundary, terminal nonnegativity and signed budget. |
| Same XP01, `Examples/MappedPotentialAccounting.lean` | 6,726 /165 | `aa57790203c7dbc800586464c46366fcd7e6da6965fdbc3c260285e9c8d693c3` | Actual lines 60–139: InitialCredit and Fractional examples; scoped names elsewhere. |
| XT02 `974a97321a8ec174b56104c7e6efaaca881b6639`, `Applications/Trees/ShapeLog.lean` | 2,796 /69 | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` | Complete file reread; raw Real bounds and conditional rounded identities. |
| XT01 `64c6b777d828ecfe83234fc2aed94600a1f24297`, `Applications/Trees/Observations.lean` | 4,119 /107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` | Existing count/map observations already read in this workflow, retained unchanged. |
| Same XT01, `Examples/TreeCache.lean` | 16,307 /363 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` | Existing balancedThree/leftThree fixtures, already read in this workflow. |

The current XL01 ticket is 2,422 bytes /39 lines, SHA-256
`5fd712cf74d2fbd0aaae5246054c7087a1e9081592da0e9a8f8b4daae4bf3758`.
The XP01 ticket was read in full to preserve its draft/unaccepted status.
Relevant rows, source-error sections and source provenance of these current
inventories were read; this was not a new whole-inventory acceptance review:

| `fdsa-control/research/` input | Bytes / lines | SHA-256 |
|---|---:|---|
| `chapter21-obligations.md` | 36,555 /324 | `e9ec73c1de2835060646f62fd7d675b192b4f1960742f917952a4fbf78265a51` |
| `chapter22-obligations.md` | 24,825 /213 | `805b5d297ee9088a01ed4adf7f3816debd7e9a4f02777364fc85f522a1935939` |
| `chapter23-obligations.md` | 33,222 /271 | `01c1184e372e574b0487822e844ff5f2abecd6c7e05fa3d59961972d785ea700` |

The governing AGENTS, architecture/domain guidance and EDD instructions had
already been fully read in this assigned workflow. Their existing discipline
is applied here: independently expected observations, exact assumptions,
actual public-law composition and concrete false-overclaim witnesses. This
is not a new implementation or final-review loop.

### 10.3 Final assessment boundary

The report identifies no mathematical obstruction to the small shared A/B
boundary. It does identify concrete false stronger statements: strict/sharper
A, nonnegative-input A/B/E, sign inference from positivity, C without its
nonnegative factor condition, D from positivity alone, E at a decreasing
base, the unchanged sharp constant at base four, and the retained pairing
sum typo. The source-specific counts and potential offsets remain explicit.

All proposed connections remain source-level. No elaborated Lean type,
compiled theorem, validator success, algorithm-cost equivalence or chapter
acceptance is claimed. No source, inventory, earlier report, Git ref/index,
worktree, cache, active-output, compiler/checker, project hash helper, remote
service or upload was changed or invoked by this report-only assignment.
Ordinary content identities are for recovery and correspondence, not proof
validation. Root owns the next decision and durability capture.
