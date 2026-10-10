# Primary sources and dependency provenance

Reviewed for this delivery on **2026-10-10**. The Lean code is an independent
reconstruction. Manuscripts, research downloads and dependency caches are not
bundled in the deliverable. Original sources and their status are distinguished
from the scope of the new checked implementation.

## S1. Categorical compilation and the square formulation

* Conal Elliott, [Compiling to Categories, full author PDF](https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf), ICFP 2017.
* [ConCat implementation](https://github.com/compiling-to-categories/concat), source-code companion; this project does not port its GHC plugin.
* [Haskell Interlude 62](https://haskell.foundation/podcast/62/), discussion of four-arrow squares around 35:48–39:35.
* [Felix](https://github.com/conal/felix), foundation reference pinned in the original delivery to `6f36d28097db7ea5f5df3263db3e8be08f74e490`, especially `src/Felix/Construct/Comma/Type.agda`, `Homomorphism.agda`, and `MakeLawful.agda`.

Felix's underlying comma-category formulation is general. Hardware timing is
one application, not an assumption imposed by this project's square kernel.

## S2. Generic parallel algorithms

* [Full author PDF](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf), *Generic Functional Parallel Algorithms: Scan and FFT*, 2017.
* [Complete literate manuscript at reviewed revision](https://github.com/conal/generic-parallel-functional/blob/9a94c8343ede7f96b3b05a47d0e839bd585333eb/generic-parallel-functional.lhs).
* Source revision: `9a94c8343ede7f96b3b05a47d0e839bd585333eb`.

The reconstruction proves the structural scan and FFT semantics; paper-level
work/depth and optimized circuit-count analyses are not claimed.

## S3. Automatic differentiation

* [Complete literate manuscript](https://raw.githubusercontent.com/conal/essence-of-ad/master/essence-of-ad.lhs), *The Simple Essence of Automatic Differentiation*, 2018.
* [Manuscript repository](https://github.com/conal/essence-of-ad).
* **[Author's errata and clarifications](https://conal.net/papers/essence-of-ad/#errata-and-clarifications)**, read with the manuscript.

The source contains superseded definitions. The implementation uses the
corrected `onDot` result type and the corrected variance for the continuation
and opposite-category constructions. ADR 0003 gives the exact decisions.

## S4. Stack compiler calculation

* [Full July 2018 draft PDF](https://conal.net/papers/calculating-compilers-categorically/ccc.pdf), *Calculating Compilers Categorically*.
* [2020 Compiling Gracefully literate source](https://raw.githubusercontent.com/conal/talk-2020-calculating-compilers-categorically/master/compiling-gracefully.lhs).
* [Talk repository](https://github.com/conal/talk-2020-calculating-compilers-categorically).

The paper is an incomplete draft. The port formalizes its completed
first-order stack operations, with an explicit arbitrary-tail preservation
theorem in place of an informal parametricity appeal.

## S5. Convolution and language recognition

* [Author-maintained repository](https://github.com/conal/convolution-paper/tree/4a466d2344daf78d1edb515d4d6fe23d7bba3e67), *Generalized Convolution and Efficient Language Recognition*, 2019.
* [Extended literate manuscript at that revision](https://raw.githubusercontent.com/conal/convolution-paper/4a466d2344daf78d1edb515d4d6fe23d7bba3e67/convolution.lhs).
* [Author's extended PDF](https://conal.net/papers/convolution/convolution-long.pdf).
* Source revision: `4a466d2344daf78d1edb515d4d6fe23d7bba3e67`.

The checked coefficient convolution specializes the indexing monoid to finite
words, so split sums are finite for arbitrary semiring weights.

## S6. Higher-order, higher-order AD

* [Full literate manuscript](https://raw.githubusercontent.com/conal/paper-2020-higher-order-ad/master/hoad.lhs).
* [Repository](https://github.com/conal/paper-2020-higher-order-ad).
* [Author's landing page](https://conal.net/papers/higher-order-ad/), which describes an **early, incomplete draft dated November 2019**.

The repository name contains 2020; the author dates the draft 2019. Both
meanings of higher order are represented in this development, with the exact
completed fragments and remaining general constructions stated in ADR 0003.

## S7. Language derivatives

* [Complete Agda/manuscript repository](https://github.com/conal/paper-2021-language-derivatives/tree/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4), *Symbolic and Automatic Differentiation of Languages*, 2021.
* [Manuscript entrypoint](https://raw.githubusercontent.com/conal/paper-2021-language-derivatives/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4/paper.tex).
* Source revision: `fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4`.

The complete repository was read, including the incorporated `.lagda` modules;
`paper.tex` alone is not the full source. The Lean port uses total finite
observations and a total parser, without copying termination overrides from
the Agda automatic implementation.

## S8. Timely computation

* [Full author PDF](https://conal.net/papers/timely-computation/paper.pdf), *Timely Computation*, 2023.
* [Felix supporting category library](https://github.com/conal/felix).

The PDF is the complete paper source used here; Felix alone is not presented
as a complete artifact bundle for the paper. The port preserves independent
value/timing maps, setup/hold bounds, and the adder hazard calculation.

## Content fingerprints of downloaded manuscripts

These SHA-256 hashes identify the exact text snapshots inspected, including
the branch-addressed AD and talk manuscripts. They are provenance, not build
inputs; no network read of a manuscript is needed to check the Lean project.

| Manuscript | SHA-256 |
|---|---|
| `essence-of-ad.lhs` | `c6e775f71a3e2c893682b76f26a0e463d1d0c4d3b755de8db8fd5ea2d5a80018` |
| `hoad.lhs` | `a2b36e3854c7829aeb1a14decd7eeed3721526e7cf6295cdfb127917890627e3` |
| `compiling-gracefully.lhs` | `139c2b3b7179e88243c9a51992d94ada3ef51cc71af9ad97f6e40a6962e6814f` |
| `generic-parallel-functional.lhs` | `e24b7507af6baa9aed24bc8b94a1e1cc2c81d89241c05430d64e7b057f43addb` |
| `convolution.lhs` | `a212ea819ca2e975f33bf1d07aa677186c4ff4d08d7692f6dd71e50051d94c7d` |

## Proof dependencies

* Lean: `leanprover/lean4:v4.19.0`, recorded in `lean-toolchain`.
* Mathlib: [v4.19.0](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b), exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
* Transitive package revisions: `lake-manifest.json`.
* Axiom dependency audit: `ProofAudit.lean`, with the actual output in `verification.txt`.

The final check uses the unmodified official Lean compiler and the pinned
Mathlib cache. The hosted checking environment needed a small local launcher
compatibility shim to locate that compiler without `/proc/self/exe`; it was
not a source/proof modification and is not needed in a normal Lean installation.

Further primary sources concerning the original dependent model and the
LCCC/type-theory qualifications remain in the historical `DESIGN.md`.
