# ADR 0009 — Compile the linear fragment to coordinates over a semiring

**Status:** Accepted.

## Context

The 2017 paper interprets categorical programs as linear maps and their matrix
representations. The same coordinate construction is useful for reverse
accumulation and for the semiring-valued timing analysis in *Timely
Computation*. An interface specialized to real matrices would miss this reuse.

## Decision

Use matrices indexed by explicit finite types over an arbitrary commutative
semiring. The decoder is Mathlib's coordinate equivalence from matrices to
linear maps. Prove both inverse laws, and export squares for composition,
identity, addition, scaling, application, and transpose. Prove that transpose
reverses composition and gives the dual action under coordinate pairing.

Provide a second module that instantiates the existing first-order compiler
with actual matrices as its hom type. A source type has an explicit finite
coordinate type: one slot for a scalar, no slots for unit, and the disjoint
union of slots for a product. Encoding and decoding are inverse by proof.
The primitive vocabulary consists of zero, addition, and constant scaling;
the compiler therefore accepts exactly the chosen linear fragment. It emits
finite matrices directly, including when source terms contain `let`.

## Alternatives

* Retain a semantic function inside a record named "matrix": this would not
  establish a coordinate implementation.
* Admit variable-by-variable multiplication or nonzero constants as linear
  primitives: these do not preserve the claimed algebraic structure.
* Require a field or real inner product everywhere: unnecessary for the
  coordinate compiler and incompatible with tropical timing semirings.
* Give every target an exponential: the finite linear-map category here only
  needs the cartesian source interface used by the first-order compiler.

## Consequences

The same matrix representation applies to ordinary scalar arithmetic and
commutative timing semirings. Transpose is a coordinate dualization; no norm,
Hilbert-space adjoint, or conjugate-transpose convention is silently assumed.
The AD library separately proves the appropriate analytic adjoint theorem.

Matrix generation is executable when scalar arithmetic and the source
primitive values are executable. No sparse-storage, multiplication-cost,
machine-arithmetic, or floating-point-error theorem is claimed.

## Checked evidence

`MatrixBackend.decode_encode`, `encode_decode`, `compositionSquare`,
`transpose_pairing`, `dual_reverses_composition`,
`MatrixCompiler.decode_encode`, `encode_decode`, `compile_correct`,
`compileSquare`, `two_x_three_y`.

## Sources

* Elliott, [Compiling to Categories](https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf), linear-map interpretation.
* Elliott, [Timely Computation](https://conal.net/papers/timely-computation/paper.pdf), semiring-linear timing maps and matrix representations.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/ToLin.lean`, pinned in `lake-manifest.json`.
