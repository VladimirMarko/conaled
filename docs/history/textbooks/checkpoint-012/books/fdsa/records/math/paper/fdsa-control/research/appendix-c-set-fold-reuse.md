# Appendix C follow-up: unrestricted set-fold convention

Prepared 2026-11-02. Short read-only API check; no Lean implementation, build,
acceptance change or review loop. Mathlib pin:
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The source convention is already
pinned in `appendix-c-obligations.md`: Isabelle's ordinary set sum/product is
the finite-index-set fold, with neutral result on an infinite indexing set.

## Finding

No matching unrestricted operation was found in the inspected pinned Set,
Fintype and BigOperators interfaces. **Use the standard finite APIs directly
for finite domains; a small explicit adapter is appropriate if the unrestricted
source notation itself must be represented.** There is no need for a new set
carrier, folding framework or notation system.

The adapter's mathematical definitions are simply:

```text
setSum s f  = if hs : s.Finite then hs.toFinset.sum f  else 0
setProd s f = if hs : s.Finite then hs.toFinset.prod f else 1
```

These are proposed convention adapters, not existing declaration names or
compiled code. They are noncomputable for arbitrary sets: deciding finiteness
is classical, and `Set.Finite.toFinset` chooses a finite representation. The
branch decision can remain local to the definition. No global equality or
membership decision, `Fintype`, or inhabitance assumption belongs on the index
type. Index and value types may inhabit independent universes.

## Exact existing interfaces

| API | What it provides |
|---|---|
| `Set.Finite.toFinset {s : Set ι} (hs : s.Finite)` | Noncomputable `Finset ι`, with no public `DecidableEq ι` requirement. |
| `Set.Finite.mem_toFinset`, `coe_toFinset` | Exact membership and set equality of the chosen finite representation. |
| `Set.Finite.toFinset_eq_toFinset` | Agreement with `Set.toFinset` when `[Fintype s]` is available. The latter is not an unrestricted infinite-set conversion. |
| `Finset.sum` | Fold with `[AddCommMonoid M]`; no order, cancellation or field structure required. |
| `Finset.prod` | Fold with `[CommMonoid M]`; no additional value capabilities required. |
| `finprod_mem_eq_finite_toFinset_prod f hs` | Finite-domain agreement between `finprod` and the selected finite representation. |
| `finsum_mem_eq_finite_toFinset_sum f hs` | The generated additive counterpart; its name is also used by pinned Mathlib's set-cardinality code. |

The definition-level imports are
`Mathlib.Data.Set.Finite.Basic` and
`Mathlib.Algebra.BigOperators.Group.Finset.Defs`.
`Finset.sum_empty`/`prod_empty` are available there. Add the corresponding
`Finset.Basic` module for singleton/insertion or other finite-fold laws when
actually used. The finite/infinite branch equations follow directly from the
chosen definition; proof irrelevance removes any choice between proofs of
the same finiteness proposition. This import recommendation was not compiled.

## Why `finsum`/`finprod` do not already implement the source convention

`Mathlib.Algebra.BigOperators.Finprod` defines `finsum` through
`HasFiniteSupport (f ∘ PLift.down)`, and `finprod` through
`HasFiniteMulSupport`. The restricted-set versions use the intersection of the
index set with that support. Their neutral branch concerns **infinite support**,
not an infinite original indexing set. Its introductory phrase about infinite
sums must be read together with these actual definitions.

Over the infinite set of naturals, take `f n = if n=0 then 5 else 0`.
The book's set sum is 0, but `finsum f` is 5. For products,
`g n = if n=0 then 2 else 1` gives source result 1 and `finprod g = 2`.
The existing `finsum_eq_single` and `finprod_eq_single` provide simple future
proof routes for these contrasting observations. These are mathematical
checks here, not newly verified Lean examples. A counterexample client can
import `Finprod` without imposing that heavier dependency on the adapter.

Preserve finiteness hypotheses on insertion/union decomposition laws. For
example, adding a new nonzero term to an infinite set still leaves the source
sum 0; an unrestricted `sum_insert = term + oldSum` statement would therefore
be false. Empty/singleton and explicit finite-domain clients use the ordinary
standard laws. No execution-cost or decidable-enumeration claim follows from
this classical notation bridge.
