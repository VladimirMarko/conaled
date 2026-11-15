# XL01: logarithm bounds — bounded source and scope preflight

Prepared 2026-11-03 for `FDSA-XL01`. **Report-only preparation; no implementation,
scope freeze, compilation, final review, chapter activation or acceptance.** The
ticket was read first and this report path was absent before authoring. This is
the sole file written by this task. Chapter 1 attempt 3 remains the sole
authorized validator; its active output was not inspected here. All chapters,
appendices and shared drafts retain their existing unaccepted status. The
initial Chapter 2 prefix remains `c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

## 1. Source conclusion and smallest justified boundary

There is a genuine common mathematical dependency: the sharp positive-input
base-2 inequality

\[
\log_2 x+\log_2 y+2\le 2\log_2(x+y)
\]

is used by the pairing-heap first-pass analysis, and its strict `+1` consequence
is used by the splay analysis. These are already explicit book obligations
`C23-046` and `C21-074`; shared preparation does not add a new coverage goal.
One small theorem and its strict corollary are a justified common boundary.
The bounded API-author handoff reports no existing named sharp result in its
pinned Mathlib Analysis search; the direct proof uses the existing primitives
listed in section 6. They should use ordinary `Real.logb`, not a new logarithm,
rank type, potential hierarchy, or algorithm executor.

The other source helpers should not automatically become four new public
wrappers. Skew heaps' weaker sum bound is a direct monotonicity calculation.
The shifted-product helper used by the two binary pairing analyses follows
from an even stronger elementary product bound. The fourth `Lemmas_log` helper
has no named consumer in the inspected sources or the scoped retained-theory
search. Its exact statement is preserved below, without treating the mere
import of its theory as a demonstrated need for a separate shared API or a
new whole-paper obligation.

The source statement and the choice of a shared implementation are separate.
Every original algorithm, helper proposition required by the book, numerical
constant, exercise and retained source-error disposition remains mandatory.
This report recommends no chapter implementation and selects no base/worktree.

## 2. Primary sources, exact identities and reading boundary

The manuscript is the retained **July 27, 2026** version of *Functional Data
Structures and Algorithms: A Proof Assistant Approach*. Its official URL is
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>. Local
`book-source/functional_data_structures_algorithms.pdf` is 1,742,029 bytes,
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The relevant text is Chapter 19 pp.227–228, Chapter 21 pp.249–252, Chapter 22
pp.254–255, and Chapter 23 pp.260–263; PDF page numbers are printed page +6.
The complete retained Chapter 21–23 text extracts and the Chapter 19 potential
method passage were read for this preflight. No new paper/source campaign or
remote retrieval was performed.

The analysis source is the dated archive
<https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz>, local
`book-source/afp-Amortized_Complexity-2026-10-26.tar.gz`, 31,633 bytes, SHA-256
`d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`.
All eight reading copies below were compared with their exact archive member
bytes using a read-only archive reader; every comparison was equal. No archive
was extracted or modified. Every member has prefix `Amortized_Complexity/`.

| Local `book-source/` file / archive member suffix | Bytes / lines | SHA-256 |
|---|---:|---|
| `Lemmas_log.thy` | 1,768 /55 | `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41` |
| `Splay_Tree_Analysis_Base.thy` | 4,591 /119 | `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17` |
| `Splay_Tree_Analysis.thy` | 20,301 /432 | `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012` |
| `Splay_Tree_Analysis_Optimal.thy` | 21,840 /495 | `511162539e9b8cab7bf804db673c82d2d534d6365098cc81525914506df0b73d` |
| `Pairing_Heap_Tree_Analysis.thy` | 9,817 /251 | `0e7f8008a2d06c7dbc2f8647b05f87324dafab5ff96daa96097bb2722cfdc368` |
| `Pairing_Heap_Tree_Analysis2.thy` | 9,180 /236 | `a04e140d2ff71d11bafd9e16e39359bcf132b194d7cbfe9a27206f261e53d191` |
| `Pairing_Heap_List2_Analysis.thy` | 9,794 /271 | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` |
| `Skew_Heap_Analysis.thy` | 7,443 /199 | `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b` |

All eight complete files were read. The entry
<https://isa-afp.org/entries/Amortized_Complexity.html>, retained as
`afp-Amortized_Complexity-entry.html` (13,056 bytes /331 lines, SHA-256
`597605ac570e8d13a00d100c3cd3ba72718f5c259bc6c4c819a102c57205b70b`), identifies
Tobias Nipkow, the entry date July 7, 2014, and BSD licensing; lines 212–215 list
this October 26 release for Isabelle2026. The two binary pairing analyses name
Hauke Brinkop and Tobias Nipkow; List2 names Tobias Nipkow based on Hauke
Brinkop's tree proofs. `Lemmas_log` itself has no individual author header.

The archive postdates the manuscript. It is a fixed supporting snapshot, **not
an inferred generating revision of the July manuscript**. The mutable browser
URLs under `https://isa-afp.org/browser_info/current/AFP/Amortized_Complexity/`
identify theories, not immutable versions. These AFP files must not be assigned
the separate Isabelle mirror revision used elsewhere for `Tree.thy`.

The AFP entry's functional imports (`Splay_Tree`, `Pairing_Heap`, `Skew_Heap`)
have separate retained archives, already pinned by their chapter inventories.
This task did not reread all functional implementations: it read the actual
analysis definitions, size/potential recurrences and their cited operation
interfaces. It does not newly certify algorithm correspondence or generated
time functions. The book and external reading copies remain source material,
not manuscript deliverables to redistribute.

## 3. Exact five inequalities and their domains

Here every variable in a logarithm inequality is **Real**, and `L(x)` means
`Real.logb 2 x`. These are source descriptions, not new frozen requirement IDs.

| Source location | Exact statement | Domain and proof significance |
|---|---|---|
| `Lemmas_log.thy:5–16`, `ld_sum_inequality` | `L(x)+L(y)+2 ≤ 2*L(x+y)` | `0<x`, `0<y`. From `(x-y)^2≥0`, hence `4xy≤(x+y)^2`, followed by positive-argument logarithm algebra and monotonicity. The constant 2 is sharp: equality holds at every positive `x=y`. |
| `Lemmas_log.thy:18–20`, `ld_ld_1_less` | `1+L(x)+L(y) < 2*L(x+y)` | Same positive domain. The live proof derives it from the preceding weak `+2` inequality. Lines 21–30 are a commented alternative proof, not another required result. Strict `+2` would be false at equality. |
| `Lemmas_log.thy:32–41`, `ld_le_2ld` | `L(1+x+y) ≤ 1+L(1+x)+L(1+y)` | `0≤x`, `0≤y`, including both zero. All three arguments are≥1. The source first proves `1+x+y≤(1+x)(1+y)`; its displayed `+1` is slack. The stronger bound without that `+1` follows directly, but this does not silently change an algorithm's advertised constant. |
| `Lemmas_log.thy:43–53`, `ld_ld_less2` | `1+L(x)+L(y) ≤ 2*L(x+y-1)` | `2≤x`, `2≤y`; these are sufficient source hypotheses, not a claim of a minimal domain. The shifted argument is≥3. The source reduces to `2xy≤(x+y-1)^2`; the subtraction is Real. No named consumer was found in the scoped retained `.thy` search. |
| `Skew_Heap_Analysis.thy:52–54`, `plus_log_le_2log_plus` | `log_b x+log_b y ≤ 2*log_b(x+y)` | `1<b`, `0<x`, `0<y`. Bound each summand by `log_b(x+y)` separately. It does not require AM–GM and does not have the sharp base-2 `+2` constant. |

The sharp base-2 constant must not be copied to an arbitrary base unchanged:
at base 4 and `x=y=1`, that assertion would say `2≤1`. A natural general-base
sharp version would contain `2*log_b 2`, but the sources do not require adding
that generalization to the minimum common unit. Likewise, replacing strict
positivity by nonnegativity is not harmless: at `x=y=0`, Lean's totalized
logarithm makes the first statement read `2≤0`.

## 4. Actual consumers, without importing their entire proofs

### 4.1 Splay: external leaves, strict helper, actual recursive branch

`Splay_Tree_Analysis_Base.thy:14–18` defines root rank
`phi t = log₂(size1 t)` and total potential as its sum over labelled nodes.
Write `ell(t)=numNodes(t)+1`: `ell≥1` on every tree, including the empty tree;
a nonempty tree has `ell≥2`. Consequently the rank is nonnegative, and the
empty rank is 0. These conclusions need the stronger lower bound 1, not just
positive arguments. No BST premise is needed for potential nonnegativity.

The live `ld_ld_1_less` uses in `Splay_Tree_Analysis.thy` are lines 40, 113, 143,
164 and 313. They supply the zig-zig/zig-zag and splay-max potential estimates
after exact size and recursive-potential cancellation. The arguments include
`size1 A` and `size1 BC`, or the two reconstructed subtrees' leaf counts, so
positivity is structural. The line 187 occurrence is inside the commented
alternative at 177–192; the active mirrored case invokes `zig_zig` at 175–176.
The book states the strict helper explicitly on pp.250–251. Relevant original
rows are `C21-062–079` and `C21-087`.

The same file's insertion proof at 247–252 and 263–268 uses a different small
step: `log₂(s+1)≤log₂ s+1` for `s≥1`, from `s+1≤2s` and `log₂(2s)=1+log₂ s`.
This is `C21-085`, an ordinary log-product/monotonicity client. Its source
`s=ell(l)+ell(r)` is at least2. Equality branches and empty insertion are
handled separately; a generic log lemma does not discharge those branches.

The already retained p.251 typo remains: its first zig-zag recurrence says
`Tsplay x A`, but the algorithm and actual proof (`Analysis:129–136`) use B.
That is `C21-076`, with its original counterexample in the inventory. The
new common scalar fact does not repair an incorrectly chosen recursive cost.

### 4.2 `Analysis_Optimal` is a different, unweighted analysis

The complete `Splay_Tree_Analysis_Optimal.thy` was read rather than inferring
its contents from its title. Its locale at 14–24 fixes Real base `alpha>1`
and coefficient `beta`, and assumes three specific product/`powr` inequalities
on variables≥1. Lines 35–43 define
`phi(l,r)=beta*log_alpha(ell(l)+ell(r))`, then the total potential and actual
splay charge. These remain **unweighted external-leaf counts**.

Lines 242–291 prove polynomial side bounds, lines 296–305 instantiate
`alpha=cuberoot(4)`, `beta=1/3`, and lines 317–339 obtain improved `3/2`
logarithmic access/splay-max coefficients and corresponding operation budgets.
The file has no named use of the four `Lemmas_log` helpers. Its base import is
not evidence that all four are used. This analysis does not introduce key
frequencies or prove the book's Static Optimality Theorem. `C21-098–101`
still need their separate weighted access/algorithm-cost/static-BST bridge;
`C21-102` remains an open-conjecture statement. No port of the entire optional
parameterized locale is justified merely to obtain the common scalar lemma.

### 4.3 Pairing: actual first-pass shift and representation-specific potentials

The book's principal representation and constants correspond to
`Pairing_Heap_List2_Analysis.thy`. Lines30–38 define forest/nonempty-tree/optional
sizes, and 50–58 define their potentials. A forest node contributes
`log₂(size(children)+size(laterSiblings)+1)`. This includes the later siblings;
it is not generally the sum of the isolated heaps' potentials. Every node
argument is≥1, and the empty optional/forest potential is 0. Heap order is
unneeded for this shape-only nonnegativity (`C23-038–045`).

The actual first-pass call of `ld_sum_inequality` is List2 lines 101–118,
specifically 113. With child-forest sizes `n1,n2` and remaining forest size m,
its two Real arguments are

\[
x=n_1+n_2+1,\qquad y=m+1,\qquad x+y=n_1+n_2+m+2.
\]

Both arguments are positive even when all three natural sizes are 0. Thus the
sharp `+2` cancels the induction estimate's `+2` while leaving the correct
`log₂(n1+n2+m+2)` term. The unchanged obligations are `C23-046`, `C23-050–052`.

**Retained source error, not a new weakened target:** printed p.261 has `+1`
inside this intermediate sum instead of `+2`. Two singleton heads with empty
suffix have `n1=n2=m=0`, so the printed intermediate transition requires
`2≤0`. List2:112–113 and the simplified binary analysis:75–76 both use the
correct `+2`. The statement of Lemma 23.2 remains unchanged, as does the
mandatory counterexample/corrected-step obligation `C23-052`. This report does
not claim to have newly rendered the PDF; it rereads the retained exact text
and formal source and preserves the earlier visually checked disposition.

The original binary `Pairing_Heap_Tree_Analysis.thy:89–97` also uses the sharp
lemma, but with `x=size lx+size ly+1`, `y=size ry`. Here `ry` is explicitly a
nonempty node, so its unshifted size is positive. A further monotonicity step
enlarges the sum. Its first-pass estimate requires a nonempty forest and its
older deletion budget has coefficient 3. The simplified binary analysis at
65–81 instead shifts the suffix size by 1, covers empty forests, and obtains
the coefficient 2 route used in the book. These proof boundaries cannot be
merged simply because both import `Lemmas_log`.

The shifted-product helper `ld_le_2ld` is used at binary Analysis:47–65 and
Analysis2:45–63. Both explicitly assume whole nonempty roots
`h1=Node hs1 x1 Leaf`, `h2=Node hs2 x2 Leaf`; it bounds their potential change
by `log₂(size h1+size h2)+1`. The nonnegative x,y in that helper are the two
possibly empty child sizes. List2's own merge estimate at 87–88 and 200–206 is
`2*log₂(combinedSize+1)` after empty cases; it does not call `ld_le_2ld`.
Preserve `is_root`/whole-heap representation premises when transferring binary
operations. These facts support `C23-049` and `C23-062–072` only after the
actual representation and cost correspondence is proved.

### 4.4 Skew: signed charge, three spine bounds, elementary monotonicity

`Skew_Heap_Analysis.thy:17–50` defines natural indicators/spine counts, proves
`2^(lrh t)≤numNodes t+1` and its right-spine counterpart, and converts them
to Real log bounds. Its potential is Int-valued. In lines 96–111 the exact
merge charge is first bounded in Int by three natural spine counts, then cast
to Real, and only then bounded by logarithms. The output identity is
`ell(merge t1 t2)=ell(t1)+ell(t2)-1`.

The two input leaf counts are≥1, hence their sum minus1 is≥1. This justifies
both the cast of natural subtraction and the monotone step from the output
logarithm to the logarithm of the input sum. The weak generic helper at 109
bounds the other two terms; the final result is
`3*log₂(ell(t1)+ell(t2))+1`. This is `C22-041–044` and `C22-054–057`, including
the actual spine/merge bridge. The scalar lemma alone is not that bridge.

## 5. Domain, cast and totalization boundaries

| Boundary | Required treatment |
|---|---|
| Real log of a positive value below 1 | It may be negative. At `x=y=1/4`, the sharp lemma is equality `-2=-2`, and the strict helper gives `-3<-2`. Potential nonnegativity comes from the actual size argument≥1. |
| Empty source structures | Splay uses `ell(E)=1`; optional/forest pairing potential is explicitly 0; a binary pairing node always has positive node count. A sharper unshifted forest-log theorem has an explicit nonempty premise (`C23-053`). Do not use the numerical value of log 0 as its semantic substitute. |
| Nonnegative shifted-product variables | Child sizes may both be 0, giving the legitimate source inequality `0≤1`. Requiring positive child sizes would exclude real leaf cases. |
| The `x+y-1` helper | Preserve its `x,y≥2` domain if quoting it. Merely positive inputs are insufficient even when the shifted argument remains positive: `x=y=1` would give `1≤0`. No minimal-domain theorem is claimed. |
| Nat size versus Real arithmetic | Cast size observations before logarithms and signed potential subtraction. A displayed `size1+size1-1` must first have the natural predecessor bound proved if transported from Nat. `Nat.sub` is not general Real subtraction. |
| Int skew potential and indicators | `rh≤1` permits moving the natural `1-rh` into Int. Subsequently cast the entire signed amortized charge into Real. Casting unsigned truncation after the fact changes the source calculation. |
| Different potential offsets | Splay sums `log₂(numNodes+1)` at each node; binary pairing sums `log₂(numNodes)` at each nonempty node. Similar tree folds do not prove identity. `C23-072` retains the explicit bridge obligation. |

Pinned Mathlib `Analysis/SpecialFunctions/Log/Base.lean:41–88` defines
`Real.logb b x = Real.log x / Real.log b`, with log 0=0, equal values at x and
-x, and zero functions at bases 0 and 1. The source lemmas above use positive
arguments and valid bases. This report does not assert cross-system equality
of Isabelle and Lean totalizations outside that intended domain. Those total
definitions must not be used to drop hypotheses or make an invalid empty-case
interpretation appear meaningful.

## 6. Existing library reuse and a bounded possible follow-up

The detailed pinned-API assessment is separately owned in
`logarithm-bounds-api-preflight.md`; the independent examples are separately
owned in `logarithm-bounds-case-preflight.md`. This source report does not
replace either assessment or prescribe a new hierarchy. The following exact
Mathlib declarations were additionally inspected directly here, at pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

| Existing declaration / location | Direct use |
|---|---|
| `Real.logb_mul`, `Base.lean:85`; `Real.logb_pow`, line 125 | Expand the positive product/square in the AM–GM proof; the product law asks for nonzero factors, discharged by positivity. |
| `Real.logb_le_logb_of_le`, line 194 | Under the enclosing `1<b` premise, only the lower argument needs explicit positivity and the arguments' ordinary inequality. Supplies the Skew two-summand bound and shifted-product estimate directly. |
| `Real.logb_lt_logb`, line 198 | Proper-subtree size inequalities imply strict ranks; the subtree/size premise remains algorithm-specific. |
| `Real.logb_nonneg`, line 237 | Needs argument≥1, not merely positive; supplies the scalar component of source-potential nonnegativity. |
| `Real.logb_self_eq_one`, line 65; `logb_one`, line 54 | Base 2 and empty-leaf normalization, without replacing real ranks by rounded natural logarithms. |
| `Real.strictConcaveOn_log_Ioi`, `Analysis/Convex/SpecificFunctions/Basic.lean:66` | An alternative existing route to two-term log concavity. No new Jensen/expectation framework is required for this deterministic scalar use. The direct square/product proof more closely follows the actual source. |

A minimal source-faithful proof route for the common lemma is: establish
`0<4*x*y` and `4*x*y≤(x+y)^2`; apply base 2 log monotonicity; expand the two
sides as `2+log₂x+log₂y` and `2*log₂(x+y)`. Linear arithmetic gives the strict
`+1` consequence. This is proof preparation, not a checked Lean term.

Use the skew weak bound and the shifted-product source bound directly from
these APIs or as small clients if a later scoped unit needs them. A new
public wrapper is not justified by source name similarity alone. The unused
fourth helper should remain documented with its exact assumptions; no
current book row is discharged or removed by declining to create a wrapper.
If an implementation later genuinely uses that helper, it must establish the
actual shifted domain and prove the stated inequality rather than assuming
an imported theory supplied it automatically.

The smallest meaningful connected uses would instantiate the same positive
lemma at actual external-leaf counts and at the pairing first-pass arguments
`(n1+n2+1,m+1)`, together with the retained `+1` versus `+2` error witness.
Empty-shifted cases and an example with positive input below 1 test distinct domains.
These are source-oriented examples of the scalar law, not surrogate splay or
heap implementations or a request to add every optional example to a unit.

## 7. Costs, potentials and XP01 must stay separate

The full prior reports `potential-generalization-preflight.md` and
`potential-draft-preflight.md` were read. XP01 already prepares generalized
actual-trajectory budgets, additive raw-work maps, validity-local potential
laws and signed-group telescoping over the existing `Resources.run`.
It does not need another log-specific accounting API. Its immutable draft
`c28ba71863d2a35ee1c3a089caa90464e4cca692` is source evidence, not acceptance.

Chapter 19 p.228 / `C19-011–018` separates the local inequality from the
trajectory theorem: actual work plus final potential equals summed charges
plus initial potential. Dropping the final term needs its nonnegativity;
dropping the initial term needs an initial-zero premise or a separate bound.
For a two-input merge subtract both input potentials and account for both
input occurrences in the actual history. Unary XP01 does not authorize
spending an old persistent heap's potential repeatedly. These requirements
are unaffected by proving a pure logarithmic inequality.

| Source cost boundary | Original obligations that remain |
|---|---|
| Splay Base:20–48 selects the actual `splay_code` time equations; nonrecursive branches cost 1, insertion has no extra wrapper and costs 0 at empty. Analysis:382–386 uses looser `+3` budgets for insert/delete while local book bounds use `+2`. That slack is not an additional executed tick. | `C21-055–061`, `C21-084–093`, exact erasure, recursive/result dependency, BST/shape premises and actual retained-state traces. |
| Skew:43 selects merge timing;117–135 manually define raw Int insertion/deletion costs. Later 150–160 changes the framework tariff by adding 1 to insert/delete and charging empty creation/deletion 1. Its upper budgets consequently use `+2` outside the log. | `C22-025–031`, `C22-045–065`. Do not transfer a book `+1` bound unchanged to the larger wrapper tariff. |
| Pairing List2:176–195 gives selected nonrecursive link/insert/merge cost 0, while recursive passes pay their entries. Its deletion bound combines real potential with actual pass work; binary analyses have additional whole-root representation premises. | `C23-028–037`, `C23-047–061`, `C23-069–078`. Ordinary constant-time root operations, selected-call 0, fused-pass savings and improved-history tariffs remain distinct. |

Logarithms here observe mathematical sizes; no operation is charged for
computing a real logarithm or recomputing all subtree sizes. A tree fold can
describe a potential, but that does not insert a traversal into the source
program or prove a cache bound. Existing tree count/fold observations may be
reused when their exact carrier and offset agree; pure scalar XL01 has no
reason to force a tree-framework dependency.

## 8. Complete original scope is retained

| Chapter | What the possible scalar common fact can support | What it does not complete |
|---|---|---|
| 19 | A future state-dependent logarithmic local upper charge can feed existing XP01 accounting. | Counter/table algorithms and exercises, invariant preservation, exact tariffs, multiple-input history/ownership and original boundary-credit obligations. There is no independent logarithm lemma asserted in Chapter 19 merely because its framework is imported. |
| 21 | `C21-074`, and the scalar step within `C21-075`, `C21-077`, `C21-087`; ordinary reuse for `C21-063–064`, `C21-079`, `C21-085`. | The splay/splay-max algorithms, all mirrored correctness and cost cases, actual query/result relation, proper membership state, insertion/deletion, exact potential cancellation, aggregate bounds, Exercise 21.1, Static Optimality and the conjecture statement. |
| 22 | The arithmetic component of `C22-043–044`, `C22-055–057`; direct weak-sum/monotonicity reuse. | The size-sensitive heavy-spine proofs, actual merge recurrence/tariff and Int charge, heap/PQ semantics, insertion/deletion and history bounds, Exercise 22.1 and linear-height/worst-case distinctions. |
| 23 | `C23-046` and the scalar substitution in `C23-052`, supporting the unchanged first-pass target. | Every heap/forest/optional representation, strict tie behavior, pass recurrence, preservation, exact size/potential bridge, cost and allocation observation, Exercise 23.1, two-input histories, and the cited improved aggregate bound with its retained estimate gap. |

No original inventory was edited. Optional better constants in a companion
analysis are not substituted for the exact book constants, and the book's
cited mathematical assertions are not demoted merely because their proof is
elsewhere. Conversely, an imported but unused support lemma or the title of
an optional companion file does not require importing an entire additional
analysis. The retained C21 and C23 source errors remain explicit, with their
corrected statements/steps and counterexamples, rather than being hidden by
weaker conclusions.

## 9. Retained record identities and assessment limits

| Unmodified input record | Bytes / lines | SHA-256 |
|---|---:|---|
| `tickets/FDSA-XL01.md` | 2,422 /39 | `5fd712cf74d2fbd0aaae5246054c7087a1e9081592da0e9a8f8b4daae4bf3758` |
| `research/chapter19-obligations.md` | 29,453 /235 | `1d9d22ca8d801d7c0ba47910d0f6519dd7c76acd787164be3a382ad818c220c6` |
| `research/chapter21-obligations.md` | 36,555 /324 | `e9ec73c1de2835060646f62fd7d675b192b4f1960742f917952a4fbf78265a51` |
| `research/chapter22-obligations.md` | 24,825 /213 | `805b5d297ee9088a01ed4adf7f3816debd7e9a4f02777364fc85f522a1935939` |
| `research/chapter23-obligations.md` | 33,222 /271 | `01c1184e372e574b0487822e844ff5f2abecd6c7e05fa3d59961972d785ea700` |
| `research/potential-generalization-preflight.md` | 18,738 /321 | `c47864985fc8c1c6baffa5601d2610268b7f5c2cd895073966eb214e365226ae` |
| `research/potential-draft-preflight.md` | 6,519 /90 | `fba713681c8eb3a80720b10d9ed0d0a33b46d2dddd883b7bd2ca0bc263f254f2` |

Exact retained text-extract identities: `chapter19.txt` 11,630 bytes /189
lines, SHA-256 `ec24f793ae9de72c1e2a59c372410592515c05f18f5f4d37e3be594d88691de6`;
`chapter21.txt` 12,645 /296,
`264723480de11639b091cb53f4a30c32b8bcfced06ef7c55005d4363cd6d0a12`;
`chapter22.txt` 4,289 /91,
`1dd43d2b3b93595d36bd344a235e926faeeaa03782fb04a183bce09e3556e2d1`;
`chapter23.txt` 10,424 /226,
`bc041e90844d53dac7a326a1bc2bfa9fdd873bc350573bae2dc7669912a8830b`.

The directly inspected Mathlib `Log/Base.lean` is 25,117 bytes /632 lines,
SHA-256 `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf`;
`Convex/SpecificFunctions/Basic.lean` is 10,888 /239,
`809d8e40e5ab931ec4254ae9068e9fb5a4a7c19e95d3fddcc9f4ad81028faef1`.
Only their relevant declaration ranges were reread here; the separate API
author owns the broader exact-library search. The relevant inventory rows,
source correction sections and provenance sections were read, not a new
whole-book inventory. Text reads, scoped search and ordinary content hashes
were the only verification operations; no proof checker, project hash helper,
Git/ref/index, build/cache, active-output or remote action was performed.

This report supplies source-level mathematics and a bounded recommendation.
It does not claim elaboration, theorem audit, source-runtime equivalence,
independent final approval or closure of any obligation. Root owns the next
scope decision and any subsequent checkpoint/release. The original Chapter 1
attempt histories and all prior reports remain unchanged.

## 10. Applicable AFP notice

The retained `book-source/AFP-LICENSE`, from <https://isa-afp.org/LICENSE>, is
1,842 bytes /36 lines, SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`.
The entry advertises BSD and these inspected analysis files are unmarked for
another license. Any source adaptation must preserve applicable attribution,
conditions and disclaimer. This is distinct from the manuscript's copyright
and from other libraries' licenses. The complete retained notice follows.

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
