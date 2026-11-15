# Myers checkpoint 129

The owner supplied this checkpoint on 2026-11-15. The [archive](myers-129.tar.gz)
and [conaled handoff](conaled.md) are preserved byte-for-byte. The latter equals
`myers/math/conaled.md` inside the archive.

| File | SHA-256 |
| --- | --- |
| `myers-129.tar.gz` | `947dac685ec31c14bd357a9eedc3cdf4c32a8dc5c61310aa3b3b9986088b3d12` |
| `conaled.md` | `cc24988b13dd8f5017dede90806b64c8c9eb76426e2a922700673296305baf68` |

Local inspection checked all 2,808 payload entries against the archive's
`manifest.json`, including byte lengths and SHA-256 hashes. The only unlisted
file is the manifest itself. All 2,809 archive members are regular files with
unique relative names, no traversal, and no links. The Agda compiler was not
replayed. Retained receipts are external evidence; the integrated Lean build
does not validate this archive.

After extraction, `myers/README.md`, `environment.json`, and `state.json` locate
the external project's scope, pins, and checking evidence. Its continuation
instructions govern that external project, not conaled agents. The finite-branch
account is in `myers/math/finite-presentations.md`; its source correspondence
must be checked against actual Agda declarations and their evidence.

The handoff inspected conaled at `08dbb2a71c8c9236ef2a1283e66f17b5622c3b9e`.
At the local intake base `8e68f4434e3b1dd367c2f6d14fbda057765a5e52`, no subsequent
commits changed `SquareKit/Internal/Cubical/` or the cubical examples.

[#529](https://github.com/VladimirMarko/conaled/issues/529) retains its existing
arbitrary-context constructor and dependent-transport requirements.
[#565](https://github.com/VladimirMarko/conaled/issues/565) tracks the additional
Myers finite-label chart-family consumer and depends on #529. The owner requested
this separation without weakening #529. Neither task supplies ordinary Agda Id/J
admission, source judgmental conversion, a classification of the Dedekind sheaf
families, or a smooth/cohesive model. The separate unchanged-source obligations
remain under [#422](https://github.com/VladimirMarko/conaled/issues/422).
