# Exact finite tables from kernel equality

[#335](https://github.com/VladimirMarko/conaled/issues/335) adds an equality
facade to the existing finite stochastic-table interpretation. The semantic
relation `tableEquiv` is retained and now proved equivalent to both entrywise
equality and equality of the actual table structures. No global category
instance or new probability assumption is introduced.

[FiniteKernelEquality](../../Applications/Probability/FiniteKernelEquality.lean)
uses the existing singleton observation theorem. Equality of the kernels gives
equality of `mass (entry x y)` for every input and output. Each table entry is
nonnegative by the existing table contract. On that domain, applying `toReal`
and rational-cast injectivity recovers the rational entry. Table extensionality
then recovers the structure; its proof fields carry no additional data.

The domain restriction is necessary. `mass` uses `ENNReal.ofReal`, which clips
negative values. The checked example `mass (-1) = mass (-2)` rules out a global
injectivity claim. The finite table theorem retains the existing finite-space
and measurable-singleton hypotheses, so singleton observations recover the
whole table. It does not claim reflection for arbitrary measures or observations.

## Law transport and iteration

`tableMeaning_equality_laws` exposes operation preservation with actual table
equality as the source relation. `tableMeaning_reflects` supplies reflection.
`tableEqualityLaws` applies the existing `RawMap.transportLaws` to Mathlib's
stochastic category, exactly as the semantic-equivalence facade does. No
independent matrix-sum associativity proof is added.

The resulting identity and associativity theorems quantify over arbitrary
tables between the existing finite-space objects. `Table.steps_add` derives
exact concatenation of finite iteration from those laws. Its order is explicit:
`steps (n + m)` equals `steps m` after `steps n`, matching `Table.comp`'s
right-argument-first convention. The existing kernel iteration theorem remains
the connection to the full output law.

## Caller consequences and negative control

[FiniteKernelEquality examples](../../Examples/FiniteKernelEquality.lean)
recover exact two-step Boolean negation from the existing kernel computation.
The caller applies kernel injectivity and reuses that computation, instead of
reproving table entries. This is an additional equality result; the old kernel
proof is retained, and no reduction in its proof length is claimed.

The same examples exercise arbitrary-table associativity, concatenation of the
retained asymmetric Metropolis–Hastings client's iterations, and agreement of
that concatenation with the established kernel interpretation. Equality can
now be used to rewrite exact entries and subsequent table computations. Clients
that only need kernel behavior keep their existing semantic API unchanged.

Two deterministic tables output `(false, false)` and `(false, true)`. They have
the same first marginal but different tables and different full kernels. This
rejects replacing whole-kernel equality by a weaker observation while retaining
the existing full-joint-law contract.

## Statement review

Numeric reflection explicitly assumes both inputs are nonnegative. Kernel
reflection quantifies over every entry, and table extensionality equates the
actual data structures. Transport uses equality preservation and reflection,
not an injectivity assumption supplied by a caller. The iteration theorem's
composition order agrees with the original executable definition. The negative
examples establish actual distinct data, rather than failure of a tactic.

The facade adds theorem-level access without changing existing objects,
operations, semantic equivalence or instances. Full build, proof audit and
independent Standards/Spec review are recorded with the issue's candidate.
