# Braun shape — pinned API and reuse preflight

Date: 2026-11-03 UTC. Ticket: `FDSA-XT09`.

**Report-only preparation. No implementation scope, base, worktree, source
release, validation result or acceptance is selected.** C1 attempt 3 remains
the sole authorized compiler/checker; this task did not inspect its outputs or
control its execution. The original initial C2 prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847` after repaired Chapter 1 acceptance.
Only this new report is written.

## 1. Recommendation

A small ordinary Braun structural unit is justified: Chapter 11 arrays and
Chapter 16 heaps use the **same recursive shape predicate** on the same
node-labelled tree, independently of their different observations, ordering
invariants and operations. The missing common mathematics is the left-biased
sibling-count condition, its invariance under arbitrary label maps, uniqueness
of the label-erased shape at a given size, and the bridge to the existing
almost-complete shape results.

Reuse `BinaryTree`, the saved XT01 count/map/erasure laws, and the saved XT02
minimum-height, almost-complete and logarithm results. No second tree carrier,
canonical-tree generator, array index framework, heap hierarchy, execution
model or new cost observation is needed. The public structural interface
should not require payload order, equality, inhabitance, finiteness, or map
injectivity. Different label types may inhabit different universes.

The economical proof spine uses a symmetric **local constructor theorem**:
two almost-complete children whose node counts differ by at most one form an
almost-complete parent. Braun supplies a particular orientation of that
condition recursively. A theorem with these explicit child hypotheses does
not require a new balancing framework. The source also states the recursive
`wbalanced → acomplete` theorem; it remains an explicit C11-018 obligation if
the first unit exposes only the local constructor and Braun consequence.
Defining a second ordinary recursive Prop predicate is an optional scope
choice for that full source statement, not a requirement of arrays or heaps.

Exercise 11.1 has an independent proof-route requirement: prove the power
bound and exact logarithmic height **without first proving Braun trees almost
complete**. A feasible direct induction is described in section 6. Reusing the
almost-complete height theorem alone cannot be credited as that exercise.
The index characterization, array/heap algorithms and all other exercises
remain separately queued unless later explicitly selected.

## 2. Reading boundary and exact retained inputs

The complete 48-line XT09 ticket was read before investigation. Its identity
is 2,921 bytes, SHA-256
`66a33e78146023b718ee7a999b10be612f6b47efb5e9ea76f6c6f83379c620a5`.
The prior shared-tree shape preflights were reused, with current declarations
verified directly from the retained Git revisions below. Relevant Chapter 11
and 16 inventory rows and their source passages were read; no inventory was
edited. The source author owns the separate full chapter/source assessment.

The complete stopped `research/braun-shape-source-preflight.md` was also read
before this report was closed: 28,163 bytes/401 lines, SHA-256
`5a11f1e66cf45870d7b0e0651445459457bdca5cf4c8ddd599c7c5ddb40d5931`.
Its exact model, source-tariff and independent-exercise boundaries agree with
the API routes below. No source discrepancy or inventory correction is proposed.

Project Git reads used the pinned Nix shell with optional Git locks disabled.
No ref, index, source checkout, dependency or build artifact was changed. The
following complete files were read from their exact saved revisions:

| Revision | File | Bytes / lines | SHA-256 |
|---|---|---:|---|
| XT01 `64c6b777d828ecfe83234fc2aed94600a1f24297` | `Applications/Trees/Observations.lean` | 4,119 / 107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| Same XT01 | `Applications/Trees/Cached.lean` | 5,668 / 135 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| XT02 `974a97321a8ec174b56104c7e6efaaca881b6639` | `Applications/Trees/Shape.lean` | 11,019 / 267 | `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3` |
| Same XT02 | `Applications/Trees/ShapeLog.lean` | 2,796 / 69 | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` |

These remain saved **unaccepted drafts**. Reading a complete proof does not
establish its elaboration or the validity of a later combined candidate.
The original XT01 and XT02 identities are preserved; this report selects
neither a descendant nor an integration base.

The Mathlib pin is `56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean
v4.35.0 / `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Complete reads covered
`Mathlib/Data/Tree/Basic.lean`, `Get.lean`, `Traversable.lean` and the Catalan
tree module; relevant Nat/Real logarithm declarations and proofs were inspected.
A scoped search for `braun` found no Lean declaration at project `07e480f...`,
XT01 or XT02, or in pinned Mathlib, Lean Init/Std and Batteries. This establishes
the local reuse gap, not an absence claim about other libraries or future pins.

Applicable AGENTS, architecture/domain guidance, glossary and ADR 0001/0010
were read. The design keeps the canonical carrier and ordinary mathematical
laws; it does not change a preservation family or interpretation interface.
No general framework retrofit or upstream language comparison is needed.

Primary source reads included the entire `Braun_Tree.thy` and `Tree_Real.thy`,
the ordinary `wbalanced` definition in `Tree.thy`, the actual array invariant
and relevant recurrences, and the direct Braun height proof in the priority
queue companion. Exact sources and licenses are recorded in section 9.

## 3. Existing carrier, mapping and shape APIs

Mathlib's `BinaryTree.{u} (α : Type u) : Type u` has constructors
`nil` and `node (value : α) (left right : BinaryTree α)`. The order is
**label, left, right**, unlike the Isabelle source's printed left-label-right
notation. Nil has no payload; the existing `Inhabited (BinaryTree α)` instance
chooses nil without `Inhabited α`.

The complete pinned `Data/Tree/Basic.lean` is 6,679 bytes/188 lines, SHA-256
`43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d`.

| Existing declaration | Exact useful contract |
|---|---|
| `BinaryTree.numNodes` (108–110) | Nil is 0; node is `l.numNodes + r.numNodes + 1`. This is the source's node size, not `sizeOf`. |
| `BinaryTree.numLeaves` (118–120) | Nil is 1; node is the sum of child external-leaf counts. |
| `BinaryTree.height` (128–130) | Nil is 0; node is `max l.height r.height + 1`. |
| `BinaryTree.numLeaves_eq_numNodes_succ t` (136) | `t.numLeaves = t.numNodes + 1`, including nil. |
| `BinaryTree.numLeaves_pos t` (139) | Every external-leaf count is positive. |
| `BinaryTree.height_le_numNodes t` (143) | Raw structural bound, with no balance or payload assumptions. |
| `BinaryTree.map f` (79–81) | Maps labels and preserves child positions; no injectivity or payload capability. |
| `BinaryTree.comp_map f g t` (92–96) | `t.map (g ∘ f) = (t.map f).map g`. The orientation is explicit. |
| `BinaryTree.id_map t` (87–90) | `t.map id = t`. |
| `BinaryTree.left`, `right` (151–163) | Total child projections; both return nil on nil. |
| `BinaryTree.unitRecOn` (174–176) | Ordinary induction on `BinaryTree Unit`; no tree enumeration is required for erased-shape uniqueness. |

XT01 already supplies `Trees.numNodes_map label t`, `numLeaves_map label t`,
`height_map label t`, and `fold_map` for independent input/output label
universes. Its `inorder_length` observes node count and `inorder_map` maps the
labels of the inorder list. These are value laws, not constant-time erasure
or array-index-order laws.

`Trees.Cached.erase t := t.map Prod.fst` has `numNodes_erase`,
`numLeaves_erase` and `height_erase` without cache validity. The actual
`annotate empty combine t` satisfies `erase_annotate empty combine t = t`
and `annotate_valid`. `read_eq_fold` requires recursive `Cached.Valid`;
`read_annotate` establishes that observation for the actual annotation output.
A Braun map law can compose with these without inventing another cache API.

### Existing XT02 declarations to consume directly

All statements below are in namespace `Trees`:

| Declaration and argument order | Exact statement |
|---|---|
| `minHeight t` | Fold of nil value 0 and node `min left right + 1`. |
| `minHeight_map label t` | `minHeight (t.map label) = minHeight t`. |
| `AlmostComplete t` | `t.height ≤ minHeight t + 1`. There is no left-packing premise. |
| `almostComplete_map label t` | `AlmostComplete (t.map label) ↔ AlmostComplete t`. |
| `almostComplete_children a l r ht` | Almost-complete parent implies both children almost complete. |
| `pow_minHeight_le_numLeaves t` | `2 ^ minHeight t ≤ t.numLeaves`. |
| `numLeaves_le_pow_height t` | `t.numLeaves ≤ 2 ^ t.height`. |
| `minHeight_eq_log_numLeaves t ht` | Under `ht : AlmostComplete t`, `minHeight t = Nat.log 2 t.numLeaves`. |
| `height_eq_clog_numLeaves t ht` | Under the same premise, `t.height = Nat.clog 2 t.numLeaves`. |
| `clog_numLeaves_le_height t` | `Nat.clog 2 t.numLeaves ≤ t.height` for every raw tree. Its proof uses the universal capacity bound, not almost-completeness. |
| `height_optimal s t hs hsize` | For `s : BinaryTree α`, `t : BinaryTree β` in independent universes, `AlmostComplete s → s.numNodes ≤ t.numNodes → s.height ≤ t.height`. |
| `minHeight_eq_floor_logb_numLeaves t ht` | From `ShapeLog`: `minHeight t = ⌊Real.logb 2 (t.numLeaves : Real)⌋₊`. |
| `height_eq_ceil_logb_numLeaves t ht` | From `ShapeLog`: `t.height = ⌈Real.logb 2 (t.numLeaves : Real)⌉₊`. |

These existing general results need applications after the new predicate
bridge, not renamed Braun-specific wrappers for every logical presentation.
The complete-tree definitions/equality/strictness results in XT02 remain
available but need not be reproved for Braun trees.

### Nearby APIs do not already supply Braun structure

`BinaryTree.get : PosNum → BinaryTree α → Option α` (`Get.lean:51–55`)
follows `one` at the root, `bit0` left and `bit1` right. This is useful later
for the book's least-significant-bit path convention. The file has no Braun
contiguity or index-cardinality theorem. `indexOf` is an order-directed search,
not an array-index invariant. `getOrElse` takes an explicit default value;
it is not needed for pure shape and must not impose `Inhabited α` on it.

`treesOfNumNodesEq` in the Catalan module enumerates **all** Unit-labelled
trees of a size. It provides neither Braun uniqueness nor a reason to enumerate
trees in its proof. The ordinary map suffices for label erasure. The
`Traversable` instance likewise adds no missing shape law and need not be
imported merely to write the direct `BinaryTree.map` already available.

Current `RandomAccess.Tree` is a different, leaf-labelled carrier with cached
sizes, no empty tree, and `Perfect 0 (.leaf x)`. Its `size_eq_pow` and
`fromT_length` concern complete leaf blocks, not the Braun node-count condition.
Likewise, the existing leftist queue's rank/short-path invariant is not Braun
balance. No carrier substitution or queue replacement follows from this task.

## 4. Smallest proposed structural statements

All names in this section are **proposals**, not a frozen API. They can live in
the existing `Trees` namespace and ordinary files, without a new typeclass or
record. For arbitrary `α : Type u`, a direct source-shaped definition is:

```text
Braun nil = True
Braun (node a l r) =
  (l.numNodes = r.numNodes ∨ l.numNodes = r.numNodes + 1) ∧
  Braun l ∧ Braun r.
```

Expose the constructor equation and its equivalent inequality form
`r.numNodes ≤ l.numNodes ∧ l.numNodes ≤ r.numNodes + 1 ∧ Braun l ∧ Braun r`.
The disjunction/inequality equivalence is Nat arithmetic. No integer absolute
value, payload equality, `Fintype`, or decision about labels is involved.
There is no need to pair the specification with a new executable checker or
to assign a cost to evaluating this recursive predicate.

The core map statement should be an **iff**:

```text
(label : α → β) (t : BinaryTree α) :
  Braun (t.map label) ↔ Braun t.
```

Its structural induction uses `Trees.numNodes_map` and the two child induction
hypotheses. Reflection does not require injectivity because Braun depends only
on shape. Consequently arbitrary annotations, projections, constant maps and
noninjective relabellings all preserve and reflect it. A relabelling cannot
repair an invalid shape.

The reusable uniqueness statement can retain independent universes directly:

```text
(s : BinaryTree α) (t : BinaryTree β)
(hs : Braun s) (ht : Braun t) (hn : s.numNodes = t.numNodes) :
  s.map (fun _ : α => ()) = t.map (fun _ : β => ()).
```

This is an observation in `BinaryTree Unit`, not equality of payload-bearing
trees. A proof can first establish the source Unit theorem privately and apply
the map/count laws, or perform the same induction on the erased trees. At two
nonempty roots, write child counts `l₁,r₁,l₂,r₂`. Equality of parent counts and
`rᵢ ≤ lᵢ ≤ rᵢ+1` force **both corresponding child counts equal** by linear Nat
arithmetic. Apply induction to both children; Unit labels are equal. Nil versus
node is excluded by the count equation. No division, parity enumeration,
finite-set cardinality or generic tree equivalence relation is needed.

This states at most one erased Braun shape per size. It does not construct one
for every Nat, assert a canonical labelled tree, or imply equal inorder values.
In particular, `BinaryTree Empty` still has nil but has no positive-size member;
there must be no hidden payload witness in an existence claim.

The constructor inequalities also give immediate domain facts used later:
in a Braun node, empty left implies empty right, while empty right allows an
empty or singleton left child. These can be derived by constructor/count cases
where the actual client needs them. Do not replace them by the false symmetric
empty-child equivalence or add a generic shape-pattern framework.

## 5. Braun-to-almost-complete proof spine

The genuinely new common bridge is `Braun t → AlmostComplete t`.
The supporting local theorem can use only:

```text
AlmostComplete l, AlmostComplete r,
l.numNodes ≤ r.numNodes + 1, r.numNodes ≤ l.numNodes + 1
    → AlmostComplete (node a l r).
```

This is symmetric **local** size balance. It is weaker than Braun orientation
and still requires both children almost complete. It is not a theorem that any
root with balanced counts is almost complete. A proof splits Nat arithmetic
into equal sizes, left one larger, or right one larger; no integer absolute
value import is needed in the natural core. The source's absolute-difference
presentation is equivalent and can be connected in the source witness.

### Equal counts

`numLeaves_eq_numNodes_succ` gives equal child leaf counts. The exact XT02
`height_eq_clog_numLeaves` and `minHeight_eq_log_numLeaves` then give equal
child maximum and minimum heights. The parent's two successor equations
preserve the children's gap of at most one. This consumes actual child
almost-completeness, not a claimed height determination for arbitrary trees.

### Left child one larger — source Lemma 11.1

Put `k := r.numLeaves`, with `0 < k` from the existing raw positivity theorem.
Then `l.numLeaves = k+1`. Monotonicity of Nat log/clog and the two child exact
formulas yield the source's important intermediate identities:

```text
(node a l r).height = Nat.clog 2 (k+1) + 1
minHeight (node a l r) = Nat.log 2 k + 1.
```

Let `i := Nat.log 2 k`. The pinned standard power bounds give
`2^i ≤ k < 2^(i+1)`, hence `2^i < k+1 ≤ 2^(i+1)`. The two clog equivalences
below imply `Nat.clog 2 (k+1) = i+1`. Thus the parent's maximum height is
exactly one more than its minimum height. Empty `r` is included: `k=1`.
There is no logarithm-at-zero side case to discard.

The right-one-larger case follows by swapping the two child roles in the
min/max equations; no new mirror operation is necessary. Braun's recursive
child hypotheses and either permitted size case then prove its bridge by
ordinary induction.

### Exact pinned numerical API

All Nat declarations below are from `Mathlib.Data.Nat.Log` and were inspected
at the pin. In the table, unspecified Nat variables are implicit.

| Call shape | Contract used |
|---|---|
| `Nat.pow_log_le_self 2 hk` | For `hk : k ≠ 0`, `2 ^ Nat.log 2 k ≤ k`. |
| `Nat.lt_pow_succ_log_self (by decide : 1 < 2) k` | `k < 2 ^ (Nat.log 2 k).succ`. |
| `Nat.log_mono_right h` | `n ≤ m → Nat.log b n ≤ Nat.log b m`; base implicit. |
| `Nat.clog_mono_right b h` | `n ≤ m → Nat.clog b n ≤ Nat.clog b m`; base explicit. |
| `Nat.clog_le_of_le_pow h` | `x ≤ b^y → Nat.clog b x ≤ y`; no extra base premise in this direction. |
| `Nat.clog_le_iff_le_pow hb` | For `hb : 1 < b`, `Nat.clog b x ≤ y ↔ x ≤ b^y`. |
| `Nat.lt_clog_iff_pow_lt hb` | For `hb : 1 < b`, `y < Nat.clog b x ↔ b^y < x`. |
| `Nat.le_pow_clog hb x` | For `hb : 1 < b`, `x ≤ b ^ Nat.clog b x`. |
| `Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂` | From `b^i ≤ k` and `k < b^(i+1)`, `Nat.log b k = i`. |
| `Nat.log_one_right b`, `Nat.clog_one_right b` | Both return zero at argument 1, covering nil's leaf count. |

No new logarithm or rounding theory is needed. For C11-015's displayed real
expressions, use the actual bridge declarations from
`Mathlib.Analysis.SpecialFunctions.Log.Base`:

```lean
Real.natFloor_logb_natCast (b n : Nat) :
  ⌊Real.logb b n⌋₊ = Nat.log b n
Real.natCeil_logb_natCast (b n : Nat) :
  ⌈Real.logb b n⌉₊ = Nat.clog b n
```

They have no additional premise; the structural use still explicitly retains
`k ≥ 1`. These connect the actual intermediate parent identities to the source
floor/ceiling formulas. If C11-015 is selected in a later scope, preserve those
identities as checked statements, not merely an assertion that some proof of
almost-completeness exists. Real analysis need not enter the natural Braun
predicate or uniqueness proof.

Once the bridge is proved, C11-017's exact log heights and cross-type optimum
are applications of the existing XT02 declarations. Retain `numNodes+1` when
converting leaves, including nil. No claim about machine time or optimality
of a concrete array/queue algorithm follows from height optimality.

For full C11-018, the optional ordinary recursive symmetric predicate is true
at nil and requires both child predicates and the two sibling-count inequalities
at a node. The same local theorem proves its almost-completeness by induction.
Braun implies it, but the converse fails. Merely stating the local constructor
does not by itself formally cover that recursive source statement; retain it
as a named remaining obligation if the first unit omits the predicate.

## 6. Independent exercise routes remain distinct

### Exercise 11.1 / C11-122

The retained `Priority_Queue_Braun.thy:25–36` already gives primary-source
support for a direct tree induction proving
`Braun t → 2 ^ t.height ≤ 2*t.numNodes + 1`. Its preceding comment explicitly
distinguishes this proof from the almost-complete argument. That source theorem
is evidence for a feasible route, not an imported Lean proof.

A particularly explicit Lean induction can strengthen the induction result
to `t ≠ nil → 2 ^ t.height ≤ 2*t.numNodes`, handling nil separately with
`1 ≤ 1` for the requested weak bound. At a node with two nil children the
strong bound is `2 ≤ 2`. Otherwise choose a child `c` of maximum height. It is
nonempty: a nonempty tree has positive height by its constructor equation.
The induction hypothesis gives `2^height(c) ≤ 2*n(c)`. The sibling-size
difference at most one gives `2*n(c) ≤ n(parent)`. Doubling and `Nat.pow_succ`
give `2^height(parent) ≤ 2*n(parent)`. This proof uses only recursive shape,
counts and heights; it never invokes almost-completeness or its exact log law.

To derive the exact ceiling height independently, retain the universal XT02
capacity theorem `numLeaves ≤ 2^height` and its `clog_numLeaves_le_height`
consequence. These were proved without almost-completeness. For a nonempty
tree, write `height = j+1`. The direct source bound becomes
`2*2^j ≤ 2*n+1`, so Nat arithmetic gives `2^j ≤ n < n+1 = numLeaves`.
`Nat.lt_clog_iff_pow_lt` yields `j < clog 2 numLeaves`, hence
`height ≤ clog 2 numLeaves`. Combine the two directions; nil is the
`clog 2 1 = 0` case. The Real ceiling bridge then gives the printed formula.
Using this route would honor the exercise; citing `height_eq_clog_numLeaves`
with the new Braun-to-AC theorem would not.

Whether this independent proof is included in the first unit is not selected
here. It can later share the same predicate and carrier without a second
executor, metric or alternative definition of Braun.

### Other exercises and structural consequences

C11-123 still requires an actual left-spine-height observation and proof that
it equals maximum height on Braun trees. C11-124 requires the child-height
analogue `h l = h r ∨ h l = h r + 1`, with the requested readable proof.
The existing exact height formulas give a concrete route: size bias gives
`h r ≤ h l` by clog monotonicity; `L l ≤ L r + 1 ≤ 2*L r` and
`L r ≤ 2^clog(2,L r)` give `h l ≤ h r+1` by `clog_le_of_le_pow` and
`Nat.pow_succ`. The left-spine equality then follows by tree induction.
These consequences are not automatically covered merely by a general height
upper bound, nor do they hold for arbitrary symmetric size-balanced trees.

C11-125 concerns the **actual** prefix-consuming `Balance.bal` from Chapter 4
and its split sizes. A shape theorem is not a substitute for its return-value,
size and consumption proofs. Its inorder traversal is also not the array's
Braun index-order list. Index/trie, initializer, flexible-array and fast-list
exercises remain separate. No algorithm is introduced by this report.

## 7. Connected uses and failure boundaries

The independent cases are coordinated separately; the following are direct
mathematical expectations that a selected future source unit should make useful.

| Case / connection | What it tests |
|---|---|
| Nil at payload `Empty` | Braun, almost-completeness, node count 0, leaf count 1 and both logarithmic heights 0; no default payload or excluded empty domain. |
| Arbitrary noninjective `label : α → β` | Braun holds iff it held before mapping, with equal count/height. The output universe may differ. |
| XT01 `Cached.erase` and actual `annotate` | Braun erasure is an iff without `Cached.Valid`; `erase_annotate` transports Braun to the actual annotated tree. A size-reader interpretation additionally uses `annotate_valid`, `read_eq_fold`/`read_annotate`, and `fold_numNodes`. Shape alone cannot certify a cached number. |
| Two differently labelled Braun singletons | Equal erased shape and count do not imply equality of payload-bearing trees or their inorder lists. |
| Two-node right chain | Symmetric recursive size balance and almost-completeness hold; Braun fails because the left child is smaller. It has minimum possible height without Braun shape. |
| Left and right two-node chains | Equal counts and symmetric size balance do not give erased-shape uniqueness. Left bias matters for the Braun uniqueness theorem. |
| Parent with a complete three-node left child and singleton right child | It is almost complete (`h=3`, `minHeight=2`) but its child counts differ by two. Almost-completeness does not imply even symmetric sibling-size balance. |
| Root with equally sized children, one a malformed three-node chain | A balanced root equation does not imply recursive Braun validity or almost-completeness. Child hypotheses cannot be dropped. |

There are actual retained fixtures to reuse rather than inventing all cases
again. `TreeShapeExamples.rightTwo` and `rightTwo_almostComplete` are in the
XT02 example file. `TreeCacheExamples.sample` has child sizes 1/2 and is already
shown almost complete by `TreeShapeExamples.sample_almostComplete`, while its
actual `sizeSample` has `sizeSample_valid`. Those facts do not give Braun bias.
Conversely, the existing `TreeCacheExamples.corrupt.left` is a singleton with
stored size 2: its raw shape is Braun but that size cache is wrong. The actual
definitions and referenced existing statements were read at their retained
XT01/XT02 revisions; their earlier validation limits remain unchanged.

These cases need no broad enumeration campaign. The exact shape/count laws
are reusable by the two actual source models:

- Chapter 11 array validity is `Braun t ∧ cachedSize = t.numNodes`. Its list
  observation is `x :: splice (list l) (list r)`, not XT01 inorder; its valid
  numeric range and update domains still need the index/list proofs.
- Chapter 16 queue validity is `Braun t ∧ heap t`. Minimum correctness needs
  heap order and nonemptiness; neither is implied by Braun. Its size and
  height facts use the same shape predicate independently of labels. The
  source has no queue merge operation to infer from that shared invariant.

The array and heap source predicates justify the shared structural boundary;
they are not a claim that their full Lean realizations already exist. No
surjectivity, payload equality or total order is imported into Braun merely
because a later heap operation compares values.

The LSB-first Braun index set and its interval equivalence remain C11-009–013.
Conventional breadth-first heap numbering is a different convention. Shape
uniqueness does not prove index contiguity, and `BinaryTree.get` by itself
does not establish which indices succeed. A complete `get`/Nat conversion or
index-set framework would materially enlarge this proposed unit.

All costs remain attached to actual operations. A logarithmic height can only
be substituted into a separately proved height-based operation cost. The
source array's higher-order callbacks and specialized wrappers, and the heap's
insertion/sift/deletion recurrences, retain their own exact tariffs and domains.
In particular, Braun heap `del_left` swaps the returned left remainder with
the old right child; it is not the ordinary XT08 leftmost extractor. No
whole-fold, path executor, cache-read tariff or machine-runtime claim is added.

## 8. Minimal dependency and placement assessment

If root later selects a bounded unit, the natural dependency is the existing
`Applications.Trees.Shape` interface, which already imports XT01 observations.
A possible ordinary module is `Applications/Trees/Braun.lean`. Generic
almost-complete constructor lemmas have a natural home as additive statements
in the existing `Shape.lean`; the Braun-specific predicate/map/uniqueness/
induction belongs in the Braun module. Alternatively the small constructor
proof can stay locally with the new development if no independent public use
is selected. These are placement proposals, not authorization to change the
old draft or choose its commit as a new base.

Source real-log witness statements or connected examples can import the
existing `ShapeLog`; the natural core does not need Real analysis. Annotation
composition examples may import `Cached`. There is no dependency on XT03–XT08,
resources, priority-queue adapters, arrays, ordering/search, selection or
probability. A general tree-size abstraction, shape quotient, finite tree
enumerator, or balance/typeclass hierarchy would add work without serving
these contracts.

All earlier public statements and proof bodies remain unchanged. Any later
implementation needs root's frozen requirements, selected base and saved
pre-code checkpoint/release, then the existing matching validation/review
sequence. No earlier unaccepted draft gains validation through this proposal.

## 9. Provenance, exact support identities and limits

The official July 27, 2026 book PDF is retained at SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`:
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
The inspected Isabelle mirror revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It postdates the book and pins
the supporting formal source, not an asserted manuscript build revision.

| Retained support | Bytes / lines | SHA-256 |
|---|---:|---|
| `book-source/Braun_Tree.thy` — complete read; predicate/inequalities 12–18, Unit uniqueness 22–31, AC bridge 35–40, later index layer 42–181 | 6,544 / 183 | `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1` |
| `book-source/Tree_Real.thy` — complete read; one-larger constructor 61–82, symmetric constructor 87–104, recursive weight balance 106–112 | 4,280 / 114 | `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` |
| `book-source/Array_Braun.thy` — relevant operation/invariant and observation ranges | 26,980 / 713 | `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f` |
| `book-source/Priority_Queue_Braun.thy` — direct proof 22–36 and relevant source/height-bound ranges | 10,740 / 292 | `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e` |
| `fdsa-control/research/chapter11-obligations.md` — relevant structural, index and exercise rows | 51,829 / 386 | `ec4a0763833c45d4ff3cd0a06b90cb3fd270a245b61bab2c52608066554213fc` |
| `fdsa-control/research/chapter16-obligations.md` — shared invariant, operation/domain and cost boundaries | 19,617 / 166 | `180865d8315609bd24687b5ce0c2cbf7e75995769ac10db74e621cc693585108` |
| `Mathlib/Data/Nat/Log.lean` — relevant actual declarations and proofs | 20,607 / 511 | `66bb65d1a1cabeb2ee3d8c88c55fd3cf6e48e910ea40322173d79e5ed66a0c3e` |
| `Mathlib/Analysis/SpecialFunctions/Log/Base.lean` — exact Nat floor/ceil bridge | 25,117 / 632 | `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf` |
| `Mathlib/Data/Tree/Get.lean` — complete read | 2,536 / 72 | `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` |

Primary paths are `src/HOL/Data_Structures/Braun_Tree.thy` and
`Array_Braun.thy`, and `src/HOL/Library/Tree.thy`/`Tree_Real.thy` at
<https://github.com/isabelle-prover/mirror-isabelle> with the revision above.
The priority-queue companion is pinned by
<https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz>, archive
SHA-256 `e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b`.
No new retrieval or enumeration was performed.

Mathlib/Lean source carries Apache-2.0 notices. The Isabelle/AFP sources credit
Tobias Nipkow, with Thomas Sewell's cited contributions to the index proof and
array theory; their applicable BSD notices remain in
`book-source/ISABELLE-COPYRIGHT` and `book-source/AFP-LICENSE`. Any later source
adaptation must retain those notices and algorithm attributions. This original
report neither redistributes the whole manuscript nor introduces copied code.

No concrete mathematical/API obstruction was found for the small structural
boundary. Remaining source construction would need to elaborate the explicit
min/max rewrites, Nat arithmetic in the child-count uniqueness proof, and the
different explicit argument orders of log/clog monotonicity. Those are proof
tasks under the stated hypotheses, not reasons to strengthen public domains.
No proposed Lean proof was compiled, and this is not a prediction of linter
or compiler success. All source algorithms, exercises, original scopes,
unknown gate outcomes and acceptance conditions remain unchanged.
