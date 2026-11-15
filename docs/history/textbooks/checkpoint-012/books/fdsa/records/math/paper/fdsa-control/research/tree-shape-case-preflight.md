# Binary-tree shape bounds: independent mathematical cases

## Status and scope

This note retains the completed hand-calculated expectations for a possible
later shared `BinaryTree` shape-bound unit. It is source preparation, not frozen
scope, implementation, either final review axis, or accepted/compiled coverage.
Chapter 1 remains the active chapter. The previously retained 626-shape check
is historical only and was **not repeated**. No new enumeration, compiler,
checker, project hash helper, Git/ref, cache, gate, or remote operation was used
to prepare this note.

The statements below concern the existing node-labelled `BinaryTree` carrier.
Labels can repeat and need no equality, ordering, or inhabitance assumption.
The cost of computing observations is outside this mathematical preparation.

## Conventions and general expectations

Write `E` for `nil` and `N(l, r)` for a node with the indicated children; node
labels are suppressed. Let `n`, `L`, and `h` denote `numNodes`, `numLeaves`, and
`height`. Thus an empty tree has `(n, L, h) = (0, 1, 0)`, and every tree satisfies
`L = n + 1`. Leaves here are external `nil` occurrences.

Define minimum external-leaf height `d` by

```text
d(E)       = 0
d(N(l,r))  = 1 + min(d(l), d(r)).
```

The existing maximum height has the analogous `max` equation. For every tree:

\[
0\le d\le h,\qquad 2^d\le L\le 2^h.
\]

Use **complete** to mean that all external leaves have the same depth (the
perfect-tree convention), not the heap convention of filling levels from left
to right. The expected equality characterizations are

\[
\operatorname{Complete}(t)
\iff d=h
\iff L=2^d
\iff L=2^h.
\]

Both endpoint equalities are substantial: equality in either inductive leaf
bound forces both children to attain the relevant bound at the same height.
The empty tree is complete. An incomplete tree has both strict inequalities
`2^d < L < 2^h`; those strict inequalities do not require its two heights to
differ by only one.

## Almost completeness and the exact logarithm offset

Use **almost complete** to mean `h - d <= 1`, equivalently `h <= d + 1` because
`d <= h`. This is a global condition on external-leaf depths.

For positive integer `L`, let `floorLog₂ L` be the greatest integer `k` with
`2^k <= L`, and `ceilLog₂ L` the least integer `k` with `L <= 2^k`. These are
mathematical descriptions, not commitments to particular Lean API names.
Almost completeness gives

\[
d=\lfloor\log_2 L\rfloor,
\qquad h=\lceil\log_2 L\rceil.
\]

The equivalent integer bounds are `2^d <= L < 2^(d+1)` and, when `h > 0`,
`2^(h-1) < L <= 2^h`. At `h = 0`, use `L = 1` separately; natural subtraction
must not turn the latter strict inequality into the false statement `1 < 1`.
If the almost-complete tree is incomplete, then `h = d + 1` and
`2^d < L < 2^(d+1)`. If it is complete, `L = 2^h = 2^d`.

In node-count form the height statement is

\[
h=\lceil\log_2(n+1)\rceil.
\]

For `n > 0`, this is also `h = floor(log₂ n) + 1`. The latter formula needs its
positive-node premise; the empty tree has height zero. Replacing `n + 1` by `n`
inside the ceiling is wrong. In particular, an almost-complete tree with four
nodes has height three, whereas `ceil(log₂ 4) = 2`.

For an arbitrary tree, the general rounded bounds are only

\[
d\le\lfloor\log_2 L\rfloor
\le\lceil\log_2 L\rceil\le h.
\]

The two endpoint equalities together do characterize almost completeness,
since the ceiling and floor of the same logarithm differ by at most one. The
upper endpoint equality alone does not; see `X` below.

## Compact hand-calculated fixtures

All displayed nodes can carry the single `Unit` label. Define

```text
P1 = N(E, E)
P2 = N(P1, P1)
Q  = N(E, P1)
A4 = N(Q, P1)
X  = N(E, P2)
Y  = N(A4, Q).
```

| Tree | Nodes `n` | External leaves `L` | Minimum height `d` | Height `h` | Purpose |
| --- | ---: | ---: | ---: | ---: | --- |
| `E` | 0 | 1 | 0 | 0 | Empty complete tree; logarithm endpoint |
| `P2` | 3 | 4 | 2 | 2 | Complete nonempty tree; both leaf equalities |
| `Q` | 2 | 3 | 1 | 2 | Almost complete and incomplete; right-heavy shape is allowed |
| `A4` | 4 | 5 | 2 | 3 | Almost complete and incomplete; exact node-count offset |
| `X` | 4 | 5 | 1 | 3 | Minimum possible height at four nodes, but not almost complete |
| `Y` | 7 | 8 | 2 | 4 | Every node has sibling heights differing by at most one, but the tree is not almost complete |

These values follow directly from the `min`, `max`, node-count, and leaf-count
recurrences. For `Y`, the root's child heights are `3` and `2`; inside `A4` they
are `2` and `1`; inside each `Q` they are `0` and `1`; all remaining nodes have
equal child heights. Thus the local balance condition holds at **every** node.

### Three groups of tempting implications that fail

1. **Strictness and rounding.** Strict real bounds do not stay strict after
   rounding: `Q` has `1 < log₂ 3 < 2`, but `floor(log₂ 3) = 1 = d` and
   `ceil(log₂ 3) = 2 = h`. Nor do the two strict leaf bounds force almost
   completeness: `X` has `2 < 5 < 8` but `h - d = 2`. Strictness of the general
   leaf bounds detects incompleteness, not a one-level depth spread.
2. **Power counts.** A power-of-two external-leaf count does not imply
   completeness. `Y` has `L = 8 = 2^3` and `n = 7 = 2^3 - 1`, yet `d = 2` and
   `h = 4`. The valid completeness criteria require the power's exponent to be
   this tree's `d` or `h`, rather than merely some integer.
3. **Height optimality and local balance.** Minimum possible height does not
   imply almost completeness: `X` has four nodes and height three, and height
   two permits at most three nodes. Consequently
   `h = ceil(log₂(n+1))` alone is insufficient. Local sibling-height balance
   everywhere is also insufficient: `Y` satisfies it but has `h - d = 2`.
   These are separate failed converses, witnessed by separate trees.

The right-heavy `Q` also separates this definition of almost completeness
from any additional left-to-right filling convention.

## Height optimality, label types, and empty labels

For given values `t : BinaryTree α` and `s : BinaryTree β`, where `α : Type u`
and `β : Type v` may be unrelated and in different universes, the expected
comparison is

\[
\operatorname{AlmostComplete}(t)\ \land\ n(t)\le n(s)
\quad\Longrightarrow\quad h(t)\le h(s).
\]

Indeed, almost completeness identifies `h(t)` with `ceil(log₂(n(t)+1))`;
monotonicity of that ceiling and the general leaf upper bound for `s` finish
the comparison. No map or equivalence between label types is needed. Taking
equal node counts gives the usual height-minimum consequence, and `X` shows
that consequence does not characterize almost completeness.

For an empty label type, every `BinaryTree` value is `nil`: a node would require
an unavailable label. Thus all existing-value statements still apply, with
`n = d = h = 0` and `L = 1`; no inhabitance hypothesis should be added to those
statements. An existence claim providing an almost-complete tree of every
positive node count is different: it needs an available label, such as a
`Nonempty α` premise or an explicitly supplied label. Likewise, comparison
against trees of a positive size over an empty label type must not be treated
as an existence or optimality witness. The `Unit` fixtures avoid that issue.

## Limits of this note

This is an independent mathematical case set for later source and API work.
It does not freeze a unit, choose formal definitions or theorem names, supply
Lean proofs, extend accepted chapter coverage, or assert any successful build
or audit. No new exhaustive evidence is claimed; the historical 626-shape
check was not rerun. Only this new note was written for the retention task.
