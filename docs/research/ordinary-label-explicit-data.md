# Explicit principal data for ordinary labels

Issue #367 separates fiber descriptions from their selection in
`SquareKit/SmoothConstantComparison.lean`. `PrincipalLabelData G U l` supplies
smooth functions `defining k` and the local contract
`defining k x ≠ 0 ↔ l x = k`. The label `l` is specified independently.
No field assumes the resulting section or its comparison with an existing
section. Coverage follows by taking the index `l x`; distinct fibers have
empty overlap, so their constant sections are compatible.

`gluedSection` selects a gluing from `sheaf_exists_unique`. Its restriction law
proves `label_section`. The sheaf-specific `ordinaryLabel_injective` then proves
uniqueness and independence of supplied functions. The classical inverse is
now the specialization `selectedPrincipalLabelData.gluedSection`. Both inverse
laws, restriction naturality, and group compatibility remain; `natural` and
`mul` also expose these laws directly for independently supplied descriptions.
Equality is equality of actual sections, including their non-real restrictions.
Point detection is proved only for the sheafified constant group.

This is an API refactoring. It removes the need to call `labelDefining` when
constructing the supplied-data record, but establishes no reduction of the
transitive Lean axiom set and no constructive theorem in another metatheory.
Unique existence in Prop does not provide a choice-free Type-valued gluing in
Lean. The existing smooth sheaf, real field, localization, and Yoneda machinery
remain in the construction's types and terms.

## Pinned dependency ledger

The unchanged dependency baseline is commit
`f6329edf700f6b151ba9c0be1866701c4f2c8cc1`, with Lean/Mathlib pinned by the
repository manifests. The modified source snapshots have SHA-256:

- `SquareKit/SmoothConstantComparison.lean`: `2b01f5ba16336900d01aaf9315b3d10be780457649f548c5eccea13bac906979`
- `Examples/SmoothOrdinaryComparison.lean`: `572c5c32402aaab814415bd172916e646aab449f6543962b1c539ec0844b4428`

Every declaration below was checked with `#print axioms` after importing
`Examples.SmoothOrdinaryComparison`. **Every row has exactly the same transitive
axiom set: `propext`, `Classical.choice`, `Quot.sound`.** This includes the record
constructor, whose types already reference the classical analytic development.
It is not an assertion that each source body directly invokes all three.
Prefixes are `E = SquareKit.EuclideanOpen`, `S = SquareKit.SmoothOpenSite`, and
`D = S.PrincipalLabelData`. Each row names the supplied data, selector or immediate
dependency, and its uniqueness contract or replacement boundary.

| Declaration | Inputs and selector/dependency | Contract or replacement |
|---|---|---|
| `E.openDefining` | Open ambient subset; chooses `IsOpen.exists_contDiff_support_eq` | Supply a smooth defining function instead |
| `E.openDefining_locus` | Same selected function; `choose_spec` | Equality of its nonzero locus with the open subset |
| `E.function_isUnit` | Smooth function, pointwise negative nonzero; real reciprocal | Proves `IsUnit`; no constructive apartness claim |
| `E.element_isUnit` | Localization element; `function_isUnit`, `openEquiv` | Transfers invertibility through the existing equivalence |
| `E.local_unit` | Element and nonzero value at a point; `inverseDefining`, hence `openDefining` | Existential principal neighborhood and unit; unchanged |
| `E.covering_local_inclusion` | Covering sieve and point; induction and `local_unit` | Existential ordinary local refinement; unchanged |
| `E.sheaf_exists_unique` | Cover, sheaf, compatible arrows; sheaf condition and Yoneda | Unique gluing in Prop; retained |
| `E.empty_domain_hom_ext` | Empty domain, two arrows to a sheaf; empty cover | Arrow equality; retained |
| `S.labelDefining` | Locally constant label and index; `openDefining` on fiber image | Replaced at the explicit API by `D.defining` |
| `S.labelDefining_iff` | Selected fiber function; `openDefining_locus` | Local nonzero/fiber equivalence |
| `S.label_covers` | Selected data; `D.covers` | Coverage, not selected cover member data |
| `S.fiberLabel` | Selected data and index; `D.localLabel` | Constant local section |
| `S.fiberLabel_compatible` | Selected data; `D.compatible` | Matching family equality |
| `S.ordinaryLabel_injective` | Two sections with equal point labels; chooses local refinement and lift witnesses from `covering_local_inclusion` | Section equality, only for this sheaf; unchanged |
| `S.selectedPrincipalLabelData` | Label; `labelDefining` and its law | Classical specialization of supplied data |
| `S.ofOrdinaryLocallyConstant` | Label; selected data and `D.gluedSection` | Retained inverse |
| `S.ordinaryLocallyConstantEquiv` | Ordinary domain; inverse and point injectivity | Both inverse laws |
| `S.ordinaryLocallyConstantEquiv_natural` | Smooth ordinary map; point-label naturality | Restriction/comap equality |
| `S.ordinaryLocallyConstantEquiv_mul` | Two sections; point-label multiplication | Group compatibility |
| `S.ofOrdinaryLocallyConstant_natural` | Map and label; equivalence injectivity | Inverse restriction law |
| `D.mk` | Functions and local fiber iff | No section or global comparison input |
| `D.covers` | Supplied data; index `l x` | Cover proof derived from fiber iff |
| `D.localLabel` | Supplied data and label index; `constantSection` | No fiber-function selector |
| `D.compatible` | Supplied data; equality case split and empty-domain extensionality | Compatible local sections |
| `D.gluedSection` | Supplied data; chooses `sheaf_exists_unique`, then Yoneda | Gluing selector remains |
| `D.restrict` | Supplied data and index; gluing `choose_spec` | Restriction is designated constant |
| `D.label_section` | Supplied data and point; explicit point lift, `restrict` | Independent label recovered |
| `D.unique` | Data, section with specified label; `ordinaryLabel_injective` | Unique actual section |
| `D.independent` | Two descriptions of the same label; `unique` | Equality independent of supplied functions |
| `D.eq_ofOrdinaryLocallyConstant` | Data; independence against selected data | Comparison proved, not assumed |
| `D.natural` | Smooth map and two admitted descriptions; old inverse naturality | Independent descriptions after restriction |
| `D.mul` | Data for two labels and their product; point multiplication and uniqueness | Product of sections equals supplied product section |

To reproduce a row, run `#print axioms` on its fully qualified name in a temporary
Lean file importing `Examples.SmoothOrdinaryComparison`, through
`direnv exec . lake env lean <file>`. The exhaustive project audit separately
checks every integrated declaration.

The remaining analytic obstruction is concrete: point injectivity obtains local
refinements via `covering_local_inclusion` and `local_unit`, whose
`inverseDefining` chooses a smooth function for an open inverse image.
`function_isUnit` uses the classical real inverse from a negative nonzero
hypothesis. Positive apartness or supplied inverse data would be different
contracts; this change proves no equivalence with a constructive real model.
Supplying fiber functions alone does not replace those dependencies or the
sheaf gluing selector. A future constructive result needs a named metatheory,
analytic model and gluing interface; no such port is claimed here.

## Checked clients and statement review

`constantData` supplies 0/1 defining functions using a caller's decidable group
equality, without `openDefining`. `constant_supplied_label` proves their expected
point labels. `squaredData` supplies squared defining functions and proves their
fiber law. `supplied_sign_values` uses that path for the independent sign label
on the punctured line; its two values are 1 and the quarter turn.
`supplied_sign_not_constant` rules out collapse to a global constant.
This disconnected client still starts with classically selected fiber functions;
it tests reuse and data independence, not constructive analytic existence.
`squared_data_independent` proves equality of the resulting sections.

`emptyData` admits arbitrary functions on the empty domain, and
`empty_supplied_independent` compares zero and one functions with even different
constant labels. The old `empty_inverse_unique` remains. `zero_not_sign_data`
rejects all-zero descriptions for the inhabited sign fiber. Existing transition,
refinement, nontrivial-torsor and quotient clients remain checked.

Statement review checked quantifiers over arbitrary groups and ordinary domains,
the restriction to admitted full fiber descriptions, actual section equality,
and the dependence of uniqueness on this particular sheaf. The supplied data
are inhabited by the classical selector, by elementary constant descriptions,
and by arbitrary functions on empty domains. No global comparison is an input.
The original inverse laws remain fields of `ordinaryLocallyConstantEquiv`;
`natural` and `mul` derive preservation rather than assume it. A plausible shared
blind spot is counting removed selectors while ignoring classical dependencies
in types: the measured axiom set explicitly prevents that inference here.
