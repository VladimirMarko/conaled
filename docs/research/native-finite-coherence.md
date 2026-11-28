# Finite native coherence for pointed endomorphisms

Issue #701 implements the finite diagrams specified by [the coherence contract](native-coherence-contracts.md), using the whole-path sethood result from #700. The constructions retain independently supplied complete equivalence witnesses. Carrier sethood makes the relevant whole-path family a set; its identity types are propositions. This compares two already constructed 2-cells by a native 3-path. It does not construct an arbitrary missing 2-cell.

## Operations and selected paths

`NativePathWhiskering` and its Cartesian counterpart construct family morphisms for left and right concatenation. Their action on native paths gives whiskering of whole 2-cells. The implementation uses generalized arguments, substitution and the concatenation boundary equations; a function on global terms alone would not supply this family morphism.

`Coherence.Finite` supplies whole-path concatenation, vertical composition, whiskering, associators and unitors. Transport along a concatenation is compared with composite transport, then recovered as a comparison of whole structure paths. The Cartesian model uses its own lawful fillings and reflexive-transport orientation. Neither implementation takes associativity, unit or pentagon conclusions as fields.

`selected e` is exactly `Coded.path e`, as proved by `selected_eq`. A private opaque value with this equality prevents the kernel from repeatedly unfolding the complete selected path during dependent conversion. It adds no axiom or alternative selection. `selected_carrier` recovers the actual `ua` path of `e.map` and its complete supplied witness. The binary faces transport the existing `Coded.composition` comparison through these equalities.

## Finite boundaries

`TripleWitnesses e f g` retains witnesses for `ef`, `fg`, `(ef)g` and `e(fg)`. `selectedAssociator` compares the two actual selected outer composites. If `μ` denotes the binary comparison, the two normalization routes are

```text
L = μ(ef,g) · (μ(e,f) ▷ Pg)
R = μ(e,fg) · (Pe ◁ μ(f,g)).
```

`compatibility` compares `L · α` with `selectedAssociator · R`, using those fixed parentheses and common endpoints. The intermediate carrier sethood needed by `μ(e,f)` is supplied separately. Selected identity paths and unitors retain arbitrary complete identity and composite witnesses; their compatibility cells compare the direct and binary-derived routes.

The ordinary triangle compares `α(p,refl,q) · (p ◁ λq)` with `ρp ▷ q`. The ordinary pentagon compares

```text
((α(p,q,r) ▷ t) · α(p,qr,t)) · (p ◁ α(q,r,t))
α(pq,r,t) · α(p,q,rt).
```

`FourWitnesses` retains the three pair witnesses, four triple witnesses and five outer witnesses. Its five normalization faces are built from binary comparisons and whiskering. Each selected edge is `(N_T · ordinaryEdge) · reverse N_U`; `selectedPentagon` compares the long and short composites. No equality of supplied witnesses, fillers or 2-path terms is assumed.

## Substitution and checked applications

`selectedReindexWith` uses the existing `Coded.pathReindexWith` comparison and retains equality of the complete map/witness pair. `reindexCell` transports native 2-cells along substitution and aligns their endpoints through the structure-object reindexing isomorphism. The resulting `reindexComparison` is a 3-path between `K · δR` and `δL · reindexCell H`, where `H` and `K` are constructed original and fresh 2-cells.

The interval-projection clients reindex all four supplied witnesses. Fresh outer composites may use independently supplied lawful preservation fillers. The direct associator is constructed from associativity of the actual maps and complete equivalence recovery. The binary route is constructed from the fresh binary faces, whiskering and the ordinary associator. The applications retain their whole endpoints and 3-path through the existing `PathData` interface.

The integer translation clients use actual admitted carriers. The two triple maps send point 0 to 6 and point 1 to 7. All five fourfold maps send them to 10 and 11. Complete equivalence and whole-path recovery are checked alongside the cells, including recovery of the actual left-associated concatenation of three whole paths. Separate instances use witnesses obtained from composed isomorphisms and from composition of complete homotopy-equivalence witnesses; no inequality between these witnesses is claimed. Negative controls reject unchanged endpoints after both the triple and fourfold translations. Integer shifts commute, so these examples do not distinguish the order of translations.

## Validation and limits

The integrated application entrypoint imports the finite-coherence clients in both models. Acceptance requires the integrated build and exhaustive proof audit, including the existing composition, inversion and lattice clients.

Unannotated dependent wrappers repeatedly exhausted the default elaborator or kernel conversion budgets. Explicit binary-face result types, explicit code parameters and a shared selected-path boundary removed those failures for the finite diagrams. A local 800000-heartbeat experiment was stopped and is not validation evidence; no resource override is retained. Fully expanded generic reindex wrappers also timed out. The usable substitution interface retains the same full map/witness equalities while separating constructed fresh cells from their comparison.

A focused build overlapped a source rewrite during development. Its receipt was discarded and the occurrence recorded under [#272](https://github.com/VladimirMarko/conaled/issues/272#issuecomment-7231675650). Frozen-source checks and the required guarded/fresh acceptance must establish the final result independently of that receipt.

These results concern finite diagrams of structures over native set carriers with proposition-valued preservation. They do not establish coherence for non-set carriers, dependent descriptions, proof-relevant laws, an unbounded hierarchy or a 4-cell relating the substitution comparisons. Existing composition, inversion, lattice and frozen-trial clients retain their original contracts.
