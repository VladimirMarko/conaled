# Color finite-palette API leads

Prospective source reconnaissance only, 2026-11-04; no new Lean proof or
algorithm was written or compiled. Use with specs/1017-Color.md and
POSITIVE-KEY-REUSE.md only when preceding chapter gates permit implementation.
Mathlib pin:56a005855ea17e0b0958f73ec801ae140b0a1679. The independent advisor
inspected these APIs; root additionally read the exact declarations below.

## Optional lookup colors without a default

Mathlib/Data/Finset/Option.lean supplies `Finset.eraseNone`, an order-preserving
map from Finset (Option α) to Finset α, with no equality/order/inhabitance class
on α in these public declarations:

- `mem_eraseNone : x ∈ eraseNone s ↔ some x ∈ s`.
- `card_eraseNone_le : s.eraseNone.card ≤ s.card`.
- `card_eraseNone_of_mem (h : none ∈ s) : s.eraseNone.card = s.card - 1`.
- `card_eraseNone_of_notMem (h : none ∉ s) : s.eraseNone.card = s.card`.

For a finite neighbor observation S and optional lookup f, `(S.image f).eraseNone`
is a prospective independent used-color observation. Forming image requires
DecidableEq (Option Color), supplied by DecidableEq Color. `mem_image` then
provides the actual neighbor witness, and `card_eraseNone_le` followed by the
plan's existing `card_image_le` bounds distinct used colors. Prove the source
colors_of bridge before using this as source coverage. No arbitrary default or
collapse of absent lookup into an actual color is justified.

## Witness and exact availability boundary

Mathlib/Data/Finset/Card.lean supplies:

- `Finset.exists_mem_notMem_of_card_lt_card (h : s.card < t.card) :
  ∃ e, e ∈ t ∧ e ∉ s`; its declaration explicitly omits DecidableEq α.
- With DecidableEq α, `card_sdiff : (t \ s).card = t.card - (s ∩ t).card`.
- With that class and h:s⊆t, `card_sdiff_of_subset h :
  (t \ s).card = t.card - s.card`.

The existence result is a proposition-level witness, not an implementation or
identification of source choose. For palette P and used colors U, the exact
available count is P.card minus (U∩P).card. The separate palette-membership
invariant U⊆P gives the simpler subtraction of U.card. A degree bound is a
sufficient route to availability; distinct used palette colors determine actual
availability. Equal degree and palette size alone does not settle it. Preserve
the source's strict low-degree test, stopping behavior and selection semantics;
these lemmas do not prove optimal coloring or justify changing the algorithm.

## Local degree bridge on an infinite vertex carrier

Mathlib/Combinatorics/SimpleGraph/Finite.lean only needs
Fintype (G.neighborSet v), not Fintype V, for:

- `G.neighborFinset v : Finset V`.
- `SimpleGraph.mem_neighborFinset : w ∈ G.neighborFinset v ↔ G.Adj v w`.
- `card_neighborFinset_eq_degree : (G.neighborFinset v).card = G.degree v`.
- `card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v`.

After the planned graph-observation bridge, these can connect finite adjacency
to standard degree notation while keeping the source positive-key carrier
infinite. In a selected-support argument use the proved residual/already-colored
neighbor observation; do not silently replace it with the original graph's
degree. These are uncompiled implementation leads and confer no chapter credit.
