# Exact foundation public-type inventory

Foundation candidate: `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`. Review base: `07e480f6ec9958d4975bb90151005b84f2907614`.
Each complete source blob is byte-identical at Chapter2 candidate `f673ee87195e4aaeef4b41767a7468c70ad6214f`.

**145 explicit public named declarations; zero secured printed-type matches; all 145 remain pending.** This is an inventory and evidence-gap record, not a compiler run or acceptance.

| Source | Public named | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/InsertionSort.lean` | 19 | 7257 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| `Applications/Resources/ListCalls.lean` | 34 | 7939 | `bce039ed24b88dcb7fc2496acede9e5118cadc0a9e76da8c4a166f93e5b46488` |
| `Examples/FunctionalNotation.lean` | 30 | 8277 | `fe4b585a6753110dee67c1942ce68d16d9bf00feb5946f32791682c634c42eef` |
| `Examples/InsertionCosts.lean` | 16 | 3862 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |
| `Examples/ListCalls.lean` | 16 | 4333 | `24d0809f51d04b0a9cadb5a349141e7327a5f7721f63c1021113527917487d5d` |
| `Examples/ListLibrary.lean` | 30 | 6761 | `036cf4c12ddf5d25ce433d9f7dbedfcbb96dfc3c7f602d10605388d2791e47ad` |

All six paths are absent at the accepted review base, so this inventory adds no unchanged Chapter1 declaration. There are no explicit inductives/constructors, named or anonymous instances, or private named declarations in these six files. Namespaces, complete declaration headers, and named definitions/theorems were independently reconciled against the immutable source blobs. The TSV supplies the exact missing names and their source locations; JSON records all identities and the read-only evidence search.

The retained foundation Standards assessment remains a completed source assessment. Its focused build evidence demonstrates elaboration but does not contain the requested printed types. The search across available provenance `.log` and `.txt` files found no type-output header in these six namespaces (actual `rg` exit 1, empty stdout/stderr). This does not claim that earlier source review was absent, nor does it invalidate the accepted Chapter1 baseline.

Root owns any later recorded type execution at exact F and must wait for the live full check to close before using shared project outputs. No Lean/Lake/compiler invocation, source/ref/cache mutation, or acceptance action was performed for this inventory.
