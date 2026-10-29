# Free-word prefix circuit lower bounds

Issue #244 connects the [measured scan circuits](../../Applications/Parallel/MeasuredScan.lean)
to independent lower bounds. The original
[scan and FFT assessment](scan-fft-optimality.md) distinguished semantic
correctness, resource counts, and global optimality. The new
[PrefixBounds module](../../Applications/Parallel/PrefixBounds.lean) proves

```text
W >= n - 1
n <= 2^D
W + D >= 2*n - 2.
```

The competitors are arbitrary finite collections of raw `Wire` outputs using
binary concatenation, independent input letters, and identity constants. Wiring
and copying are free. Work counts distinct reachable binary nodes; depth counts
binary gates on the longest output dependency path. Identity multiplications
may remain, and no scan-plan origin or normalization hypothesis is required.
The required outputs are all inclusive prefixes, including the total. Adding
the free empty prefix recovers the exclusive-prefix-plus-total convention.
Additional output ports are permitted.

`ComputesPrefixes` tests words on the distinct letters `0,...,n-1`.
`prefix_eval` proves that this implies the required output values under every
monoid interpretation. It does not assume commutativity. Arbitrary constant
words are excluded: otherwise a test at fixed generator inputs could be
satisfied by hardcoding the answers. The empty and singleton cases use natural
subtraction, so the bounds remain valid at those sizes.

## The mixed bound

The proof uses two finite sets of gates. Let `T` be the gates reachable from
the total whose symbolic words are nonempty. There are at least `n-1` such
gates. Let `P` be the `n-1` distinct output gates for prefixes of lengths
`2,...,n`. Every member of `P` contains the first input letter.

The total word has no repeated letters. At each concatenation node, a given
letter can occur in at most one child. Induction therefore bounds the number
of total gates containing the first letter by the total's depth. In particular,
`|T ∩ P| <= D`. Since `T ∪ P` is contained in the circuit's retained gates,
finite-set cardinality gives

```text
2*(n-1) <= |T| + |P| = |T ∪ P| + |T ∩ P| <= W + D.
```

Empty-word gates are omitted from `T` so arbitrary identity subexpressions
cause no difficulty. Their presence can still increase charged work or depth.
The separate depth proof uses binary fan-in: word length at depth `d` is at
most `2^d`, even for words with repeated letters.

This is a specialized free-word proof motivated by
[Snir's prefix lower bound](https://snir.cs.illinois.edu/listed/J16.pdf).
It does not formalize Snir's broader theorem for self-reducible function
families using arbitrary unary and binary operations. No lower-bound axiom
or assumption about a complete recipe search is used.

## Named DAGs and attained bounds

[PrefixDAG](../../Applications/Parallel/PrefixDAG.lean) provides a second
representation: an arbitrary finite sequence of named binary gates, each
referencing inputs, identity, or earlier gates. Its output references determine
the retained node IDs; dead nodes are excluded and duplicate named gates are
counted separately. Topological indexing enforces acyclicity and permits
unrestricted fan-out.

Compilation to structural wires preserves monoid evaluation and every output
arrival time. The compiled gate set is the image of the retained node IDs.
Consequently structural sharing can decrease work but cannot increase it.
All three lower bounds therefore hold for these named DAGs as well.

The [checked applications](../../Examples/ScanOptimality.lean) use the actual
four-by-four block circuit and its established `(W,D)=(24,6)` count to prove
membership in `Optimization.minimizers` for `W+D` and in `Optimization.pareto`
for the work/depth pair, over all admissible structural circuits. They also
compare its cost directly with every admissible named DAG. These results are
independent of the bounded scan-plan search in #243.

Further cases establish a work-optimal sequential scan, a depth-optimal
sixteen-input tree, the three sixteen-input dominance comparisons, and
noncommutative semantics. Raw identity gates, empty/singleton inputs, and a
named DAG with duplicate and dead nodes exercise the model boundaries. A
singleton-monoid example computes every required value with zero binary gates,
showing why the lower bound cannot apply to every fixed monoid interpretation.
