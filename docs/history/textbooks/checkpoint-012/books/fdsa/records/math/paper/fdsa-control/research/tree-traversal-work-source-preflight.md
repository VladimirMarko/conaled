# Tree traversal work: bounded source and mathematical preflight

Prepared 2026-11-02. **Planning only; possible XT05 scope is not frozen.**
All existing shared units remain unaccepted, and Chapter 1 remains the strict
prerequisite. The old gate 80227 is unchanged. This path was checked absent;
this is the sole new file written by the task. No existing inventory, requirement,
repository source, worktree/ref, cache or review result is changed.

The current AGENTS, architectural-quality and domain guidance, glossary, ADR
index and relevant ADRs 0001/0010 were read. This source preparation does not
start a new implementation/review loop. The user's local-ticket and durability
instructions continue to override GitHub tracker/publication defaults.

## 1. Conclusion and smallest useful scope

The remaining direct-inorder part of Exercise 4.1 can be handled with one small
shape calculation connected to the **existing actual measured programs**.
Let `A(t)` sum each node's left-subtree size, counting occurrences. Then:

```text
A(E) = 0
A(N l a r) = A(l) + A(r) + n(l)
0 <= A(t) <= choose(n(t), 2).
```

An explicit left chain has `A = choose(n,2)`; an explicit right chain has
`A = 0`. Exact cost formulas for the retained append callbacks therefore give
a universal quadratic upper bound, a matching quadratic family and a linear
family. That suffices for the source's **worst-case** quadratic claim and its
contrast with the accumulator. A maximum over all labelled trees, a
classification of every extremizing shape, a general history framework and a
source-language cost translator are unnecessary for these conclusions.

This statistic is a proposed proof device, not a requirement named by the book.
An equally precise proof of the actual work bounds by another route would
satisfy the same source obligation. It is useful here because the saved XT03
single/right/left append recurrences and full list-cache example all expose
the same left-subtree-size term. The saved XT04 suffix programs supply connected
linear comparisons without another traversal implementation.

## 2. Exact source evidence and provenance limits

### Original mathematical obligations

| Source / inventory | Required meaning |
| --- | --- |
| Book printed p. 48; `Tree.thy` lines 76–78; C04-004 | The literal direct inorder is `I(l) @ [a] @ I(r)`, with empty result at `E`. |
| Book printed p. 5, §1.4 | Append associates to the right, so the literal expression contains `I(l) @ ([a] @ I(r))`. This is settled parsing evidence, not an associativity-based cost rewrite. |
| Book printed p. 49, Exercise 4.1; C04-017/018 | Direct inorder has quadratic complexity in the usual worst-case sense; implement a cons-only accumulator, prove its arbitrary-suffix equation and its linear resource behavior. A right chain rules out a quadratic lower bound on every shape. |
| `Tree.thy` lines 81–83 and 430–431 | The companion accumulator is `I2 l (a :: I2 r suffix)` and its value theorem quantifies over every suffix. No generated timing declaration accompanies it. |
| `Tree.thy` lines 415–416; C04-015 | `length (inorder t) = size t`, needed to charge append on the actual returned left traversal. |
| Book printed p. 56; `Tree2.thy` lines 18–20 and 39–40; C04-063/064 | Augmented-tree inorder ignores annotations and uses **one append to a cons**; its length is the input's node count. The stated map/erasure alternatives are value equalities, not equal-cost algorithms. |
| Book printed pp. 57–58; C04-069–073 | Generic cache validity and root-reader correctness; bounded local overhead retains the work of the actual combine function. It does not make an arbitrary combine constant-time or a whole annotation pass linear. |
| Book §1.5, pp. 6–8, and Appendix B.1, pp. 347–348 | Recursive entry charges, zero constructor/primitive work, and actual append/callback charges. `Time_Functions.thy` lines 38–41 proves append work `length(left)+1`; lines 63–76 retain higher-order callback costs. |

The official retained PDF is
`book-source/functional_data_structures_algorithms.pdf`, July 27, 2026,
downloaded from <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
Its recorded SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Printed pages are six less than PDF page numbers. The passages on pp. 5,
48–49 and 56–58 were reread for this task; the established source tariff and
prior preflight remain the evidence for the timing convention.

The retained Isabelle mirror pin is
`f86f290225eebcc52c1ae7dba2e098f405f51c21` from
<https://github.com/isabelle-prover/mirror-isabelle>. Previously recorded source
identities, not newly computed digests, are:

| Exact original path | Retained SHA-256 |
| --- | --- |
| `src/HOL/Library/Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `src/HOL/Data_Structures/Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` |
| `src/HOL/Library/Time_Functions.thy` | `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01` |

Applicable BSD-3-Clause notices remain in the source inventories. The mirror
postdates the book and is not asserted to be its build revision. The retained
`Tree.thy` and `Tree2.thy` have no `time_fun`, `T_inorder` or `T_inorder2`
declaration. No generated compiler expression, normalization or closure
conversion evidence was inspected. The exact formulas below are mathematical
targets derived from the **declared measured recurrences**; they are not
attributed to absent Isabelle timing theorems or to Lean's physical runtime.

The earlier append-association uncertainty and Chapter 1's intermediate
constructor-charge irregularity are already retained and resolved/qualified
in their original records. Nothing here silently changes those records or
opens a new source-error campaign.

## 3. What the saved XT03/XT04 contracts already expose

The following local files were read in `conaled-tree-accumulator`; these are
saved source drafts, not accepted dependencies. The corresponding full notes
are `docs/research/fdsa-tree-fold-resource.md` and
`docs/research/fdsa-tree-accumulator-invocation.md`.

| Current declaration / location | Exact usable contract |
| --- | --- |
| `Examples/TreeFold.lean`, lines 52–85: `rightStepRun`, `leftStepRun`, three step value/cost laws | Actual callbacks return `left ++ (a :: right)` with respective work `length(left)+1`, `length(left)+3`, and `2*length(left)+3`. The two-append implementations bind the actual intermediate list. |
| Same file, lines 87–118: `single_value`, `right_value`, `left_value`, corresponding node-cost laws | Returned traversal is ordinary inorder. The actual returned-left length is replaced by `n(l)` only through the value/length bridge. |
| `Examples/TreeFoldCache.lean`, lines 117–146: `list_value`, `list_read`, `list_nil_cost`, `list_node_cost` | Actual list annotation returns `Cached.annotate`; recursive validity/erasure connects child root reads to inorder. The node callback costs `n(l)+4`, and nil costs structural entry `e`. |
| `Applications/Resources/TreeCache.lean`, lines 19–26 and 30–64 | A root read costs one. The actual smart node performs two reads, the supplied callback and one entry charge, with total callback work plus three. |
| `Applications/Resources/TreeAccumulator.lean`, lines 92–118 | Actual all-suffix invocation has work `e*(2*n+1)` and returned list `I(t) ++ suffix`; the proportional linear bound retains its positive-size premise. |
| `Examples/TreeAccumulator.lean`, lines 19–74 | Actual construction and one/two applications have separate entry parameters; construction returns the function into measured results, so its value equality retains inner invocation work. |
| Same file, lines 162–175: `materializeAppend` and its value/cost laws | First run actual single-append inorder, then append its actual returned prefix to the supplied suffix. Work is that inorder work plus `n+1`. |

No existing executor needs to be replaced by a closed-form tally. The new
proofs should consume these public actual-execution laws. Their generic
reweight/value statements alone do not establish the shape-dependent sums.

## 4. One optional shape statistic, exact costs and sharp bound

Let `n = t.numNodes` and let `A` have the recurrence in §1. It counts ordered
ancestor/descendant occurrences whose first edge below the ancestor goes left.
It is not a set sum over distinct subtree values. Repeated equal children and
equal labels retain both occurrences. It depends only on shape, so arbitrary
label maps, including noninjective maps and annotation erasure, preserve it.

One economical implementation route would use the existing ordinary fold to
return the pair `(nodeCount, A)`. No new size carrier is needed. This is an
analysis observation; evaluating it must not be silently inserted into an
algorithm whose resource theorem is being proved. An explicit general
recurrence framework is not required merely to share this calculation.

The actual public node-cost recurrences suggest the following exact targets
for natural structural entry `e`:

| Existing execution | Exact all-tree work target | At entry one |
| --- | --- | --- |
| Single append to cons | `e*(2*n+1) + n + A` | `3*n+1+A` |
| Literal right-associated two appends | `e*(2*n+1) + 3*n + A` | `5*n+1+A` |
| Left-associated comparison | `e*(2*n+1) + 3*n + 2*A` | `5*n+1+2*A` |
| Actual full inorder-list annotation, positive helper tariff | `e*(2*n+1) + 4*n + A` | `6*n+1+A` |

These follow by tree induction from the respective current node laws and
`A(N l a r)=A(l)+A(r)+n(l)`. The first three return the same inorder list.
The annotation returns a different object, an annotated tree; its **root read**
equals inorder and its erasure equals the input tree. Do not assert equality
of these full return values merely to compare work.

The cache coefficient four already contains append's terminal call and the
three positive helper charges. It must not receive another implicit read or
constructor charge. Conversely, the source leftist zero-helper tariff cannot
be substituted for those positive charges by a value equality. At `e=0` the
append/helper work remains; only the structural entry component disappears.

For the sharp bound `A(t) <= choose(n,2)`, write `l=n(left)`, `r=n(right)`.
After applying the two induction hypotheses, use the identity

```text
choose(l+r+1,2) = choose(l,2) + choose(r,2) + l*r + l + r.
```

The recurrence needs only the first two terms plus `l`, leaving nonnegative
surplus `r*(l+1)`. This proves the bound for every tree without a label premise.
The familiar formula `choose(n,2)=n*(n-1)/2` is valid also at `n=0,1` with
natural arithmetic, but using the binomial coefficient can avoid premature
subtraction/division manipulation in the formal proof. No assumption that
`A` itself is an operational cost is needed.

## 5. Explicit chains suffice for worst-case work

For a supplied label `a`, define the usual families mathematically:

```text
L(0) = E                 R(0) = E
L(n+1) = N L(n) a E      R(n+1) = N E a R(n).
```

Both have `n` labelled nodes, height `n` and inorder `replicate n a`. The
recurrences give

```text
A(L(n)) = choose(n,2)
A(R(n)) = 0.
```

The left identity uses `choose(n+1,2)=choose(n,2)+n`; the right identity is
immediate induction. A concrete `Unit` label gives witnesses at every size
without imposing `Inhabited` on the universal tree theorems. For `Empty`
payloads only the empty tree exists, so do not demand a positive-size family
uniformly over all payload types.

At entry one the literal printed traversal therefore has

```text
W_right(L(n)) = 5*n+1+choose(n,2)
W_right(R(n)) = 5*n+1.
```

The universal bound and the left family are enough to certify quadratic
worst-case growth once formally proved. For example, a completely explicit
integer formulation is:

```text
for every t with n(t)>0: W_right(t) <= 6*n(t)^2
for every n>0:          n^2 <= 2*W_right(L(n)).
```

Thus the upper bound quantifies over all shapes, while the lower bound has an
actual size-`n` witness for every positive `n`. They do not state that every
shape has quadratic work. A maximum operator over labelled trees would add
unnecessary finiteness/choice questions. Existing asymptotic interfaces may
package these proved estimates, but a new framework is not needed.

The right family is linear under the same tariff, and both families have the
same node count, height and inorder. This shows why output value, node count
or height alone cannot identify the exact work. The same argument gives
quadratic left-chain and linear right-chain behavior for the other retained
append/cache executions, using their own constants. All asymptotic claims
must fix the tariff parameter: allowing `e` to grow arbitrarily with `n` is
not a uniform quadratic statement. Nil retains its exact cost `e`; a positive
entry does not satisfy a pointwise `K*n^2` bound at `n=0`.

## 6. Accumulator and cache comparisons without lost work

XT04 already gives the invocation count `2*n+1` for every suffix at entry one.
That is independent of `A`. Its right-first dependency and all-suffix theorem
must remain unchanged. Its function construction is a separate measured
program, not a hidden free phase of a new comparison.

Two particularly small connected consequences use programs already present:

```text
cost(materializeAppend t suffix) = 4*n+2+A(t)
cost(buildOnce 1 1 t suffix)       = 4*n+2.
```

Both return `I(t) ++ suffix`; their exact work difference is `A(t)` in these
declared models. Right chains give equality; left chains give a quadratic
excess. This comparison includes construction on the staged side, unlike a
comparison with invocation alone. It neither measures physical closure
allocation nor claims a compiler transforms one program into the other.

The full list-cache construction offers another consequential use of the same
calculation. Reading an already supplied valid root cache is constant local
work, but constructing all those annotations can be quadratic on a left
chain. Its read/validity bridge is essential before replacing the actual
left summary's length by `n(l)`; arbitrary corrupt caches cannot use that step.

Distinguish three source/model operations:

1. `Tree2.inorder` traverses an annotated tree while ignoring annotations.
2. XT03's list annotation builds a tree whose node annotations are whole
   inorder lists, an explicit specialization of the generic source pattern.
3. A later root read returns an already stored summary under its local tariff.

The book does not print a whole-pass timing theorem for operation 2. Its
all-tree work formula is a new connected result of the declared measured
model, not a missing book quotation. A single visit to each tree node is not
enough to make the actual append callback constant. Neither the sum of all
mathematical cache lengths nor `A(t)` by itself determines physical allocation
or sharing: even a right chain can have quadratic total cache-list lengths
while this construction's invocation count is linear. No memory claim is
needed or implied.

## 7. Independent small expectations

These values follow from the displayed recurrences; no enumeration or compiler
run was performed. All columns below use entry one. The asymmetric saved
sample has root 1, left singleton 0, right root 3 with left singleton 2, so
`n=4`, `A=2` and inorder `[0,1,2,3]`.

| Tree | `n` | `A` | Single | Literal right | Comparison left | List-cache build | Accumulator invocation | Materialize + append | Construct + invoke |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Empty | 0 | 0 | 1 | 1 | 1 | 1 | 1 | 2 | 2 |
| Singleton | 1 | 0 | 4 | 6 | 6 | 7 | 3 | 6 | 6 |
| Saved sample | 4 | 2 | 15 | 23 | 25 | 27 | 9 | 20 | 18 |
| Four-node left chain | 4 | 6 | 19 | 27 | 33 | 31 | 9 | 24 | 18 |
| Four-node right chain | 4 | 0 | 13 | 21 | 21 | 25 | 9 | 18 | 18 |

For the last two columns, use the same arbitrary suffix and retain the actual
returned lists. For the cache column, compare the root observation and erasure,
not the full returned tree with a list. Repeated payloads and a noninjective
map should preserve `A` and all these work counts; they do not collapse
occurrences. This compares given trees and does not include the work of
computing a separate map or erasure pass. A repeated-child case additionally has
`A(N u a u)=2*A(u)+n(u)`.

## 8. Recommended boundary for a future freeze

The smallest useful candidate can consist of:

- The shape observation, its constructor/map laws, sharp binomial upper bound,
  and two explicit chain families. This is proposed shared mathematics, not a
  book-mandated statistic or a new runtime analysis pass.
- Exact all-tree work laws connected to the saved actual traversal and
  list-annotation recurrences, retaining their independent value/read laws.
- Explicit worst-case upper and witness lower estimates for the literal source
  traversal, the linear right family, and reuse of XT04's accumulator theorem.
- One or two connected comparisons, preferably the existing
  `materializeAppend` versus construction-plus-invocation and the full list
  annotation, so the shared statistic is consumed by actual compositions.

Any common recurrence lemma should remain a small proof convenience over
these existing operations; no replacement evaluator, abstract history library,
general translator or new tree type is justified. Keep source-independent tree
mathematics and cross-component compositions in the locations prescribed by
ADRs 0001/0010. The architecture/API preflight owns the exact declaration and
placement proposal; this note freezes neither.

This would address the remaining direct-traversal resource claim in C04-018
and extend the shared evidence for generic augmentation. It would not accept
Chapter 4, solve its balancing/enumeration/level exercises, prove an actual
balanced wrapper linear merely from its balancer's cost, or settle later
AVL/Braun/search/heap algorithms. Those original obligations remain in their
owning chapters. Excluded mechanisms do not become additional framework
requirements. No compiler, checker, project hash helper, Git/ref/cache/gate
change, remote research or final-review action was performed.
