# FDSA shared logarithm bounds

## Status and purpose

This is the **uncompiled, unaccepted FDSA-XL01 shared draft**, prepared against
`07e480f6ec9958d4975bb90151005b84f2907614` on 2026-11-03. It supplies a small
arithmetic dependency used by the splay and pairing-heap analyses in
*Functional Data Structures and Algorithms: A Proof Assistant Approach*.
Chapter 1 remains the active sequential prerequisite. Neither these source
files nor this note accepts a chapter, appendix, shared unit or inventory row.

The two core claims concern ordinary real logarithms at base two. Their
meaning is independent of a data-structure representation, potential function
or resource tariff. Connected examples specialize the claims to canonical
Mathlib `BinaryTree.numLeaves` and natural size observations. They also use
existing logarithm primitives directly for the weaker Skew and shifted-product
calculations. The core and examples have no dependency on the unaccepted
shared-tree or generalized-potential drafts.

The frozen requirements and complete source/API/case assessments are retained
in the checkpoint's companion `fdsa-control` directory. They preserve the full
book request and all prior findings. This note records the selected source
correspondence, domains and limits; it is not a substitute for those requirements
or the eventual compilation, integrity, audit and independent review gates.

## Two shared public claims

Write \(L(x)=\operatorname{Real.logb}(2,x)\) in this note. This is explanatory
notation only; Lean reuses `Real.logb` rather than defining a second logarithm.
For arbitrary positive real numbers \(x,y\), the core statements are

\[
L(x)+L(y)+2\le 2L(x+y),
\qquad
1+L(x)+L(y)<2L(x+y).
\]

The authored [core module](../../Applications/Arithmetic/LogarithmBounds.lean)
contains these exact public statements in namespace `Arithmetic.LogarithmBounds`:

```lean
theorem logb_two_sum_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 x + Real.logb 2 y + 2 ≤ 2 * Real.logb 2 (x + y)

theorem logb_two_sum_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 + Real.logb 2 x + Real.logb 2 y < 2 * Real.logb 2 (x + y)
```

The sharp inequality permits equality, attained whenever the positive inputs
are equal. The strict statement follows by reducing its left side by one;
it needs no unequal-input premise. Both statements permit positive values
below one. Neither assumes that inputs are natural numbers, at least one,
subtree sizes, ordered payloads or valid heaps.

The direct mathematical certificate is
\((x-y)^2\ge0\), hence \(4xy\le(x+y)^2\). Positivity justifies applying the
increasing base-two logarithm and expanding the product and square. Their
logarithms are respectively \(2+L(x)+L(y)\) and \(2L(x+y)\).
Ordinary linear arithmetic then gives the strict consequence. This route uses
existing multiplication, power and monotonicity laws; no new Jensen, rank,
weighted-mean, probability or resource interface is selected.

The complete stopped core has been read. `logb_two_sum_bound` compares
`(2*x)*(2*y)` with `(x+y)^2`, using the square certificate and the existing
`Real.logb_mul`, `Real.logb_pow` and base-two identities. Its positive factors
explicitly discharge the product and monotonicity premises.
`logb_two_sum_strict` calls that public sharp theorem directly. The core exports
only these two claims. The complete stopped [example module](../../Examples/LogarithmBounds.lean)
has also been read; its actual declaration map appears below. This inspection
establishes the source-level connections, without claiming elaborated types
or successful validation.

## Source identity, attribution and licensing

The manuscript reference is the official [July 27, 2026 PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
retained from the [author-maintained book site](https://fdsa-book.net/).
It is 1,742,029 bytes, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Relevant printed pages are Chapter 19 pp.227–228, Chapter 21 pp.249–252,
Chapter 22 pp.254–255 and Chapter 23 pp.260–263. Physical PDF page numbers are
printed page numbers plus six. Manuscript downloads and extracts remain
research inputs outside the source deliverable.

The supporting primary formal source is the dated
[AFP Amortized_Complexity archive of October 26, 2026](https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz):
31,633 bytes, SHA-256
`d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`.
The source preflight read all eight complete theories below and compared each
retained reading copy with its archive member; all eight byte comparisons were
equal. The member prefix is `Amortized_Complexity/`.

| Theory / member suffix | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| `Lemmas_log.thy` | 1,768 /55 | `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41` |
| `Splay_Tree_Analysis_Base.thy` | 4,591 /119 | `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17` |
| `Splay_Tree_Analysis.thy` | 20,301 /432 | `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012` |
| `Splay_Tree_Analysis_Optimal.thy` | 21,840 /495 | `511162539e9b8cab7bf804db673c82d2d534d6365098cc81525914506df0b73d` |
| `Pairing_Heap_Tree_Analysis.thy` | 9,817 /251 | `0e7f8008a2d06c7dbc2f8647b05f87324dafab5ff96daa96097bb2722cfdc368` |
| `Pairing_Heap_Tree_Analysis2.thy` | 9,180 /236 | `a04e140d2ff71d11bafd9e16e39359bcf132b194d7cbfe9a27206f261e53d191` |
| `Pairing_Heap_List2_Analysis.thy` | 9,794 /271 | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` |
| `Skew_Heap_Analysis.thy` | 7,443 /199 | `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b` |

The [AFP entry](https://isa-afp.org/entries/Amortized_Complexity.html) identifies
Tobias Nipkow, its July 7, 2014 entry date and BSD licensing. Its retained
13,056-byte page has SHA-256
`597605ac570e8d13a00d100c3cd3ba72718f5c259bc6c4c819a102c57205b70b`;
lines 212–215 identify the selected release for Isabelle2026. The binary
pairing analyses attribute Hauke Brinkop and Tobias Nipkow. List2 attributes
Tobias Nipkow, based on Hauke Brinkop's tree proofs. `Lemmas_log.thy` has no
individual author header; its attribution must not be invented from a filename.

**The archive postdates the manuscript.** It is a fixed supporting snapshot,
not an established generating revision of the July manuscript. The current AFP
browser pages are mutable theory locators. The separate Isabelle mirror pin
used for ordinary tree theories does not identify these AFP files. Their
functional imports have separately pinned archives in the chapter records;
reading the analysis files does not establish every functional algorithm or
generated timing correspondence.

The complete applicable [AFP notice](https://isa-afp.org/LICENSE) is reproduced
at the end of this note. Its retained identity is 1,842 bytes /36 lines,
SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`.
The entry advertises BSD and the inspected analysis files are not marked for
another license. Attribution, conditions and disclaimer are retained for the
source-oriented adaptations. This notice does not license redistribution of
the book or separately copyrighted papers. Pinned Mathlib reuse remains
under Mathlib's separate Apache 2.0 licensing and author notices.

## Exact source statements and treatment

All variables in the following source statements are Real. Subtraction inside
`L(x+y-1)` is Real subtraction. The table accounts for all four `Lemmas_log`
statements and the Skew helper; importing a support theory is not evidence
that every declaration in it is used by every consumer.

| Source declaration and exact location | Statement and premises | Selected treatment |
| --- | --- | --- |
| `Lemmas_log.ld_sum_inequality`, lines 5–16 | `0<x`, `0<y` imply `L(x)+L(y)+2 ≤ 2*L(x+y)`. | The shared sharp public law; supports `C23-046` and the scalar first-pass step. |
| `Lemmas_log.ld_ld_1_less`, lines 18–20 | The same positive domain implies `1+L(x)+L(y) < 2*L(x+y)`. | The shared strict corollary; supports `C21-074`. Lines 21–30 are a commented alternative proof. |
| `Lemmas_log.ld_le_2ld`, lines 32–41 | `0≤x`, `0≤y` imply `L(1+x+y) ≤ 1+L(1+x)+L(1+y)`. | A direct example at arbitrary natural child counts after Real casts derives the stronger zero-slack product inequality using existing Mathlib and retains the source's `+1` conclusion. No core alias or claim that this scope formalizes the full Real-domain helper. |
| `Lemmas_log.ld_ld_less2`, lines 43–53 | `2≤x`, `2≤y` imply `1+L(x)+L(y) ≤ 2*L(x+y-1)`. | Exact source statement retained, but not formalized by this unit. No named consumer was found in the bounded retained-theory search. The sufficient source hypotheses are not claimed individually minimal. |
| `Skew_Heap_Analysis.plus_log_le_2log_plus`, lines 52–54 | `1<b`, `0<x`, `0<y` imply `log_b x+log_b y ≤ 2*log_b(x+y)`. | Direct monotonicity example and source-size substitution; no new general-base core API. |

For the shifted product, `(1+x)*(1+y)-(1+x+y)=x*y≥0`, so the same nonnegative
domain proves the conclusion without its extra `1`. Child sizes may both be
zero. This scalar improvement does not change an advertised heap constant or
an operation tariff.

For the shifted-minus-one helper, the source argument proves
`2*x*y≤(x+y-1)^2`, with the shifted argument at least three. Merely positive
inputs do not suffice: `x=y=1` gives the false `1≤0` despite a positive shifted
argument. Conversely, the source hypotheses are sufficient rather than an
optimized boundary. No new wrapper, improved-domain theorem or entire optional
analysis is required solely because this helper occurs in an imported file.
All original book assertions and recorded helper obligations remain mandatory.

## Actual source consumers and what the scalars mean

### Splay external-leaf ranks

`Splay_Tree_Analysis_Base.thy:14–18` defines the root rank using
`log₂(size1 t)` and sums those ranks over labelled nodes. Here
`size1 t = numNodes t + 1`, the external-leaf count. It is at least one for
every tree; the empty tree contributes rank zero and a nonempty tree has count
at least two. These facts, rather than positivity alone, justify the actual
unweighted rank's nonnegativity.

The live strict-helper calls in `Splay_Tree_Analysis.thy` are at lines
40, 113, 143, 164 and 313. They enter zig-zig/zig-zag and splay-max estimates
after the relevant recursive bound, exact sizes and potential cancellation.
The occurrence at line 187 is inside the commented alternative at 177–192;
the active mirrored case invokes `zig_zig` at 175–176. A leaf-count
specialization below is the common scalar step, not a proof of the surrounding
query, nonempty-subtree, reconstruction or recursive-cost premises.

The insertion calculations at 247–252 and 263–268 use a separate ordinary
identity: for `s≥1`, `L(s+1)≤L(s)+1` follows from `s+1≤2*s` and the product
law. The source's sum of two external-leaf counts is at least two. The empty
and equality branches remain separate. The retained printed-p.251 recursive
cost typo, `Tsplay x A` where the actual zig-zag recurrence uses B, remains the
`C21-076` correction with its original counterexample. A correct scalar law
cannot validate a wrong recursive argument.

`Splay_Tree_Analysis_Optimal.thy` is an **unweighted** alternative analysis.
Its locale at 14–24 fixes a Real base `alpha>1` and coefficient `beta`, assumes
three product/`powr` inequalities on inputs at least one, and uses
`beta*log_alpha(ell(l)+ell(r))` at 35–43. The instance at 296–305 chooses
`alpha=cuberoot(4)`, `beta=1/3`; 317–339 obtains improved unweighted coefficients.
The file has no named use of the four helper declarations. Its title does not
establish Static Optimality. Key frequencies, weighted access, exact algorithm
costs and comparison with a static BST remain the separate `C21-098–101`
obligations; `C21-102` remains an open-conjecture statement rather than a
promised proof of that conjecture.

### Pairing forest offsets and the retained intermediate correction

`Pairing_Heap_List2_Analysis.thy:30–38,50–58` defines forest/tree/optional sizes
and potentials. A forest node's logarithm includes both its children and its
later siblings: `L(size(children)+size(laterSiblings)+1)`. This is not generally
the sum of potentials of isolated whole heaps. All node arguments are at least
one, and empty optional/forest potentials are explicitly zero.

At List2:101–118, particularly line 113, the first-pass sharp-helper arguments
are `x=n1+n2+1` and `y=m+1`, after casting the natural child and remaining-forest
sizes into Real. Their sum is **`n1+n2+m+2`**. The scalar cancellation expressed
by the selected examples keeps an arbitrary Real suffix-length scalar `k`:

\[
\begin{aligned}
&L(n_1+n_2+1)-L(n_2+m+1)+2L(m+1)-k+2\\
&\quad\le2L(n_1+n_2+m+2)-L(n_2+m+1)+L(m+1)-k\\
&\quad\le2L(n_1+n_2+m+2)-k.
\end{aligned}
\]

The second step uses `m+1≤n2+m+1`, with positive log arguments. No positivity
premise on the already-cast scalar `k` is needed for this arithmetic. The
actual list-length interpretation, recursive pass and potential equation
remain with the chapter implementation.

Printed p.261 puts `+1` in the intermediate sum where the source calculation
requires `+2`. Two singleton heads and an empty suffix give `n1=n2=m=0`.
The correct sharp step is `2≤2`; the printed replacement would require `2≤0`.
List2:112–113 and `Pairing_Heap_Tree_Analysis2.thy:75–76` use the correct sum.
This preserves the existing `C23-052` counterexample and corrected intermediate
step. Lemma 23.2's final target is unchanged.

The older binary analysis at `Pairing_Heap_Tree_Analysis.thy:89–97` uses a
positive **unshifted** suffix size because that suffix is explicitly nonempty.
Its first-pass/deletion bounds differ from the simplified analysis at
`Analysis2:65–81`, which shifts the suffix size by one and covers empty forests.
Their older coefficient-three and later coefficient-two routes cannot be
identified by a common import.

The shifted-product helper is used at binary `Analysis:47–65` and
`Analysis2:45–63`. Both have whole nonempty root forms
`h1=Node hs1 x1 Leaf`, `h2=Node hs2 x2 Leaf`; the helper's nonnegative inputs
are the possibly empty child sizes. Those root/representation premises remain
necessary for the whole-operation claim. List2's own merge estimate at
87–88 and 200–206 uses its forest potential and does not call this helper.

### Skew monotonicity, signed charge and subtraction

`Skew_Heap_Analysis.thy:17–50` defines natural spine counts and an Int-valued
right-heavy-node potential. In 96–111, the actual merge charge is first bounded
in Int by three spine counts, then cast to Real and bounded by logarithms.
The output leaf-count identity is `ell(merge t1 t2)=ell(t1)+ell(t2)-1`.

Both input leaf counts are at least one. Their sum minus one is consequently
at least one; this justifies transporting the Nat predecessor to Real and
comparing its logarithm with that of the sum. The weak helper at line 109
bounds the other two logs. The full source conclusion includes the remaining
charge constant, `3*L(ell(t1)+ell(t2))+1`. The selected example handles only the
three-log arithmetic. It neither proves the heavy-spine estimates nor creates
an exact merge execution, signed-cost theorem or final `+1` charge.

## Selected independent mathematics

The declaration table below connects these expectations to the actual
public results. These are exact identities and inequalities, with no
floating-point estimates. Source-like successful specializations must consume
the intended core result or the stated existing library route. Counterexamples
to a dropped premise have their own purpose and cannot invoke a theorem whose
premises they violate.

| Selected case | Independently fixed conclusion and domain |
| --- | --- |
| Arbitrary `l : BinaryTree α`, `r : BinaryTree β` | Their Real-cast `numLeaves` are positive in independent universes. Both public laws apply without order, cache, balance, inhabitance or decidable payload equality. |
| Same-label node with supplied root label | The sum of child leaf counts is the actual node's `numLeaves`; no new tree carrier or summary is introduced. |
| Two nil trees over `Empty` | Leaf counts `1,1`: sharp equality `2=2`, strict `1<2`. No default payload or nonempty `BinaryTree Empty` is assumed. |
| Two singleton children | Leaf counts `2,2`: sharp equality `4=4`, strict `3<4`. A supplied label supplies each singleton. |
| Pairing sizes `n1,n2,m : Nat` | Positive shifted arguments and exact sum `n1+n2+m+2`; the displayed cancellation works for every Real `k`. |
| Pairing zero-size boundary | Correct sharp step `2≤2`; printed `+1` replacement false `2≤0`. This is the retained `C23-052` disposition. |
| Equal positive inputs `x=y=1` | Sharp equality `2=2`, strict `1<2`. Strict `+2` and every uniformly larger additive constant are false. |
| Equal positive inputs `x=y=1/4` | `L(1/4)=-2`, `L(1/2)=-1`; sharp `-2=-2`, strict `-3<-2`. This is a scalar-domain case, not an unweighted size. |
| Zero/quarter boundary | Lean's `L(0)=0` makes the extended sharp claim `0≤-4`, which is false. |
| Zero/unit boundary | Dropped positivity makes the sharp and strict claims `2≤0` and `1<0`, both false. |
| Skew weak sum | For arbitrary `b>1`, positive inputs, two monotonicity applications give the weak general-base inequality without a new core alias. |
| Skew leaf-count combination | `L(ell1+ell2-1)+L(ell1)+L(ell2) ≤ 3*L(ell1+ell2)`. At two nil trees it is `0≤3`; the component shifted-log and weak-sum bounds are `0≤1` and `0≤2`. |
| Binary pairing natural child sizes | Zeros are allowed. The product bound without the source's extra `1` is proved directly; both zero gives `0≤0`, and the retained weaker source conclusion gives `0≤1`. |
| Nat/Real subtraction | `((0+0-1 : Nat) : Real)=0`, while Real `0+0-1=-1`. A transport equality requires the actual non-underflow bound. |
| Base four at unit inputs | Copying the sharp additive constant `2` to this base gives false `2≤1`. |
| Base one-half at unit inputs | The increasing-base weak-sum overclaim gives false `0≤-2`. |

The nil/nil leaf-count substitution does not satisfy every nonempty premise of
the source splay zig-zig branch. Likewise, the quarter case does not identify
an actual unweighted tree with fractional size. These examples establish useful
scalar connections and precise limits, not complete source algorithm instances.

## Actual declaration and connection map

All example names in this table are in `LogarithmBoundsExamples`. Both complete
stopped source files were read before constructing this map. The statements and
visible derivations have been compared with the independent mathematics above;
this is a source-level connection assessment, not compilation evidence.

| Actual declaration(s) | Public connection and precise observation |
| --- | --- |
| Core `Arithmetic.LogarithmBounds.logb_two_sum_bound` | The sharp positive-Real source claim, through the square/product certificate and existing log algebra. |
| Core `Arithmetic.LogarithmBounds.logb_two_sum_strict` | Calls the sharp public result and derives the strict `+1` conclusion. |
| `leaf_count_bounds` | Supplies canonical count positivity to both public laws for trees over independent payload universes. |
| `node_leaf_count_bounds` | Reuses `leaf_count_bounds` and the actual node's leaf recurrence; the root label is an explicit argument. |
| `nil_empty_bounds`, `unit_values` | Instantiate the public-law connection with two `BinaryTree Empty` nils, then independently identify the values `2`, `1`, `2`. |
| `singleton_leaf_bounds`, `singleton_values` | Supply actual labels for two singleton children, consume `leaf_count_bounds`, and identify `4`, `3`, `4`. |
| `quarter_bounds`, `quarter_values` | The bound case invokes both public results at positive quarter inputs; separate exact power/inverse calculations identify `-2`, `-3`, `-2`. |
| `sharp_bound_cannot_be_strict`, `no_larger_uniform_margin` | The unit pair refutes strict `+2` and every larger Real margin `c>2`; these are counterexamples, not applications under false premises. |
| `zero_quarter_boundary`, `zero_unit_overclaims_fail` | Preserve the actual totalized zero values and refute dropped-positivity claims. |
| `pairing_sum_bound` | Discharges positivity after casting arbitrary natural `n1,n2,m`, calls the sharp law and proves the exact `+2` sum identity. |
| `pairing_cancellation_steps`, `pairing_zero_boundary` | Reuse `pairing_sum_bound` plus the actual monotone comparison, retaining arbitrary Real `k`; the zero case consumes this chain and separately refutes the printed `+1` transition. |
| `skew_scalar_sum_bound`, `skew_leaf_sum_bound` | Two existing `Real.logb_le_logb_of_le` calls establish the weak arbitrary-base bound, then canonical leaf positivity specializes it. No sharp-constant generalization is asserted. |
| `skew_shifted_leaf_bound`, `leaf_predecessor_cast` | Actual leaf-count lower bounds establish positive Real shift, monotonicity and the three-log estimate; the separate Nat-cast identity proves its no-underflow premise. |
| `skew_empty_bounds`, `skew_empty_values` | Instantiate the preceding bound with actual nil trees and identify the empty scalar values. |
| `pairing_child_product_bound`, `pairing_child_source_bound` | Existing product/monotonicity laws handle arbitrary natural child counts including zero; the second result retains the source's extra unit of slack. |
| `pairing_empty_children_bounds`, `pairing_empty_children_values` | Consume those two child-size results at zero and identify `0≤0` and `0≤1`. |
| `nat_subtraction_boundary` | Explicitly distinguishes truncated Nat subtraction and Real subtraction at zero; it does not supply a missing non-underflow premise. |
| `base_four_boundary`, `decreasing_base_overclaim_fails` | The base-four case retains a valid application of the weak arbitrary-base result and refutes the copied sharp margin; the base-one-half case refutes increasing-base reasoning by exact inverse-base values. |

The examples' only project import is the new arithmetic core. Their other
imports are pinned Mathlib tree, cast and tactic modules. Private exact-value
and leaf-positivity helpers stay implementation details; the successful shared
specializations visibly call the public sharp/strict declarations, and direct
library clients are identified separately. No expected numerical value was
changed to fit a proof, and no additional algorithm or resource observation
was introduced by these connections.

## Existing Mathlib interfaces and domains

The dependency pin is Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean 4.35.0. The principal
existing module is `Mathlib/Analysis/SpecialFunctions/Log/Base.lean`
(25,117 bytes /632 lines, SHA-256
`85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf`).
These names refer to the inspected pin, not assumptions about a later API.

| Existing interface | Actual role and premise |
| --- | --- |
| `Real.logb_mul` (line 85) | Expands a product with both factors nonzero; positive source inputs discharge the premises. |
| `Real.logb_pow` (line 125), `Real.logb_inv` (line 92) | Power/inverse identities for the square and exact dyadic values. Their totalized domains do not weaken the inequality's premises. |
| `Real.logb_self_eq_one` (line 65), `Real.logb_one` (line 54) | Base-two and unit normalizations. The self-log law used here has `1<b`. |
| `Real.logb_le_logb_of_le` (line 194) | Explicit `1<b`, positive lower argument and an ordinary argument inequality. Supplies the sharp proof's monotone step and the direct Skew/product calculations. |
| `Real.logb_lt_logb` (line 198) | Strict monotonicity on positive arguments. Actual proper-subtree size comparisons remain separate obligations. |
| `Real.logb_nonneg` (line 237) | Requires argument at least one; positivity alone is insufficient. |
| `BinaryTree.numLeaves_pos`, `numLeaves_eq_numNodes_succ`, node recurrence | Canonical structural positivity and count observations. No shared-tree draft or label-law assumptions are needed. |
| `Nat.cast_add`, `Nat.cast_succ`, `Nat.cast_sub` | Transport sizes into Real. The subtraction theorem retains its bound; it does not identify arbitrary truncated and signed subtraction. |

Mathlib defines `Real.logb b x` by `Real.log x / Real.log b`. It totalizes zero
arguments and bases zero/one, and has equal values at opposite nonzero arguments.
The source inequalities here use positive arguments and valid bases. No
cross-system equivalence of Isabelle and Lean outside those domains is claimed.
Those totalized values explain the false-overclaim examples; they are not valid
replacement premises for a source rank or a nonempty-forest theorem.

The existing root-namespace `strictConcaveOn_log_Ioi` is an alternative source
of concavity reasoning. It is not `Real.strictConcaveOn_log_Ioi`; the retained
source-report citation correction is preserved in the control records. The
selected elementary product proof does not require that theorem or a new
Jensen framework. Natural floor/ceiling logarithms from other work do not
replace these exact Real-valued ranks.

## Potential and work boundaries

The same shape can have different source potentials: an ordinary singleton
has splay potential `L(2)=1`, binary-pairing potential `L(1)=0`, and Skew
right-heavy-node potential zero. List/forest pairing also depends on the later
sibling suffix. Similar recursion shapes or shared logarithms do not prove
these potentials equal.

Positive Real rank arguments can have negative logarithms, as the quarter
case demonstrates. The separate weighted splay/static-optimality work must
retain its actual weight, cost and boundary-credit hypotheses. The scalar
quarter case is not a counterexample to the companion's unweighted
external-leaf analysis and does not select a weighted implementation here.

Chapter 19's accounting relation retains both endpoints: actual work plus
final potential is bounded by the accumulated charge plus initial potential.
Dropping the final term requires its nonnegativity; dropping the initial term
requires zero initial credit or an explicit bound. The retained XP01 draft
prepares invariant-local actual-trajectory accounting and signed telescoping
through the existing `Resources.run`. It remains unaccepted and is not imported
by this arithmetic unit. No new log-specific accounting framework is introduced.
A two-input merge must account for both actual input occurrences; a unary run
law cannot justify spending the same persistent heap's potential repeatedly.

Source tariff distinctions also remain unchanged:

- Splay Base:20–48 uses actual `splay_code` time equations. Nonrecursive branches
  cost one; insertion has no extra wrapper and costs zero at empty. The looser
  `+3` operation budgets in Analysis:382–386 do not add an executed tick to the
  local `+2` bounds.
- Skew:117–135 manually defines raw Int insertion/deletion costs. Its later
  framework at 150–160 adds one to those wrappers and charges empty operations
  one; the resulting outside-log `+2` bound is a different tariff from the
  book's `+1` presentation.
- Pairing List2:176–195 gives selected nonrecursive link/insert/merge cost zero;
  recursive pass invocations still contribute. Whole-root representation,
  ordinary runtime, selected-call zero, fused-pass savings and allocation
  observations remain distinct.

A mathematical Real logarithm is an observation used in a proof. These files
do not charge for computing logarithms, traverse a source heap to recompute
all potentials, or transfer mathematical equality into a runtime/caching claim.

## Preserved original obligations and eventual validation

| Chapter / original rows | Support supplied by this bounded draft | Work still required |
| --- | --- | --- |
| 19, including `C19-011–018` | Future scalar local bounds may be inputs to the existing accounting design. | The actual algorithms/exercises, invariant closure, tariffs, histories and initial/final-credit conditions. No new Chapter 19 log theorem is inferred merely from an import. |
| 21, especially `C21-074` | The strict shared scalar fact, with external-leaf specializations; it can support the arithmetic parts of `C21-075`, `C21-077`, `C21-087`. | Splay/splay-max recurrences and mirrored branches, membership and returned-state correctness, exact potential cancellation and costs, insertion/deletion, aggregate bounds, Exercise 21.1, weighted/static optimality and the conjecture statement. |
| 22, arithmetic within `C22-043–044`, `C22-055–057` | Existing-library weak-sum and shifted-log calculations, including casts and the empty scalar boundary. | Heavy-spine estimates, actual merge and signed charge, heap/PQ semantics, wrapper tariffs, operation histories, Exercise 22.1 and worst-case distinctions. |
| 23, `C23-046` and scalar `C23-052` | The sharp common bound, actual shifted size/cancellation arithmetic and retained `+2` correction; direct binary child-size product support. | Every representation, tie rule, pass/merge/deletion recurrence, invariant, exact size/potential bridge, cost/allocation observation, Exercise 23.1, two-input history and cited improved aggregate estimate. |

No inventory row is accepted by an isolated scalar proof or example. All 27
chapters, Appendices A–C, source mathematical assertions and exercises remain
required. Preserving these exclusions does not impose an additional generic
framework, auxiliary statistic or full port of an imported optional analysis
beyond the original book obligations. Prior source-error dispositions and the
exact Chapter 2 first-integration prefix remain unchanged.

The complete stopped core and examples were read, followed by this complete
note and the additive reconstruction-map section. No concrete mathematical,
source-domain or selected-coverage discrepancy was found in that bounded
statement/connection assessment. Positivity, strictness, exact shifts, casts,
independent universes, Empty cases, actual public-law calls and direct-library
clients were checked at the source level.

The source draft has not been compiled or audited; elaboration, warning checks,
kernel validation and all project gates remain unrun for it. This author-side
reading is neither independent Standards nor Spec approval. The local original
base and this draft are unaccepted. When root selects an
integrated candidate after Chapter 1 acceptance, the matching candidate still
needs the applicable focused and full guarded verification, both integrity
phases, complete import coverage, exhaustive transitive axiom audit, both
independent review axes and immediate final identity verification. A source
assessment, local commit or durable checkpoint does not replace those gates.

## Complete applicable AFP notice

The following block preserves all 1,842 bytes of the retained `AFP-LICENSE`,
including its attribution, conditions and disclaimer. The new Lean module
links to this note for its source provenance.

```text
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors 
                    (see author notice in individual files)

All rights reserved.

All files in the Archive of Formal Proofs that are unmarked or marked
with 'License: BSD' are released under the following license. Files
marked with 'License: LGPL' are released under the terms detailed in
LICENSE.LGPL


Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Archive of Formal Proofs nor the names of its contributors may be
used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
