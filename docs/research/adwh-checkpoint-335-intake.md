# Checkpoint 335 source identity and reconstruction

The recovered ADWH work extends conaled with finite search counting, Chapter 1
list and numeral foundations, and selected Chapter 2 resource and recurrence
results. [The integration record](adwh-recovered-integration.md) identifies the
maintained modules and scope. GitHub issue [#149](https://github.com/VladimirMarko/conaled/issues/149)
continues to own the textbook reconstruction. Neither these slices nor the
source archive establish whole-book completion.

## Source identity

The external compact archive has 11,799,703 bytes and SHA-256
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Its outer ZIP contains a README, restorer, manifest, and `sources.tar.xz`.
The payload contains 4,096 files. Neither it nor the external agent's recovery
archives are stored in Git or required by the conaled build.

The [metadata](../history/algorithm-design-haskell/checkpoint-335.json) records
the source identity. The [inventory delta](../history/algorithm-design-haskell/checkpoint-335.inventory.json)
reuses the checked-in checkpoint-233 inventory for 1,238 unchanged files and
records the two changed and 32 added sources. Overlay its
`changed_or_added_sources` by path and remove `removed_paths` to reconstruct
the 1,272-file inventory. The baseline inventory's digest binds that operation.
The changed sources are `ADWH.lean` and
`ADWH/Chapter15/QueensBitsPrimitives.lean`; all additions are in Chapter 15.
All ordinary chapter sources outside Chapter 15 retain their predecessor bytes.

The source uses Lean 4.35.0 and Init/Std. Its aggregate's local closure contains
1,271 modules and excludes `ADWH.Chapter15.QueensSixteen`. Conaled retains its
own pinned Mathlib dependencies, public entrypoint, build and exhaustive audit.
Source identity alone does not establish statement correctness or integration.

## Source and trust limits

The supplied material identifies Bird and Gibbons, *Algorithm Design with
Haskell* (Cambridge University Press, 2020), DOI `10.1017/9781108869041`.
It includes extracted official Haskell/literate files, errata, chapter companions
and coverage ledgers. The textbook PDF and complete extracted text are absent;
book-page and erratum attributions remain supplied-source claims.

The Chapter 6 groups-of-three qualification remains: ordinary algorithm
superlinearity is neither proved nor refuted by the source recurrence
countermodel. Execution results, modeled work bounds, and kernel-checked proofs
remain separate claims. The concrete queens-16 numeral proof and generated
witness families are excluded from this integration.

No blanket original-project license was located in the inspected source
metadata. Component notices do not establish a license for the whole archive.
This record preserves that unresolved provenance item.
