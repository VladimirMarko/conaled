# Original-cover parameter sections

This partial #447 construction defines `CoverSectionFamily f` on the original
sheaf map `f : Y ⟶ X`. It supplies full deformation sections at every parameter
into Y, naturality under further restriction, and matching for maps with equal
composites to X. Its inputs contain no global quotient object or glued section.

`toSplit` and `fromSplit` use the actual `SplitSheaf.displayIso f` and its inverse.
Both round trips recover complete sections, including their context-arrow maps.
`glue` applies the existing split-display theorem only after this transfer.
`recover_local_section` recovers sections on arbitrary local quotient objects,
without assuming they extend globally. `glue_restrict_section` compares the
glued result along the original cover map; `glue_natural_section` retains the
parameter-restriction comparison to the split pullback.

`Examples.ArbitraryCoverSections` constructs the actual coproduct sheaf cover
`X ⨿ X → X`, proves local surjectivity, supplies compatible constant deformations
and exercises full-section recovery and selected-arrow retention. It also uses
the existing nontrivial doubled-origin torsor with ineffective action. The
cover's two inclusions have the same composite to X, and `sheet_matching`
derives equality of their supplied deformation values from the actual input
contract.

Statement review keeps the fiber boundary explicit: these are discrete
deformation sections. Their equality does not establish equality of arbitrary
groupoid-valued families. Quotient context arrows remain data in the lifted
sections; the examples retain distinct arrows even when they act identically.
Neither a section of the cover nor invertibility of parameter restriction is
assumed.

Focused Lean checking passed for the new library module and its examples using
the pinned shell and unchanged heartbeat/trust settings. Full candidate
validation and independent review remain pending. This is not completion of
#447: matching objects/arrows across the two cover presentations, generated
family/section closure from #445/#446, full pullback identity/composition,
uniqueness and the instantiated incompatible two-sheet deformation regression
remain required.
