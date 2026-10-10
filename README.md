# Compiling with commutative squares

A checked Lean reconstruction of the categorical compiler, explicit
representation squares, and a first dependent extension. The mathematical
development and its proof boundary are in [DESIGN.md](DESIGN.md).

## Build

Use **Lean 4.19.0**. No Mathlib or downloaded Lean packages are required.
With Lean on your path, run from this directory:

```sh
./check.sh
```

The script checks the source files in dependency order and prints the axiom
dependencies of the main results. It accepts `LEAN=/absolute/path/to/lean`.
Generated `.olean` files are build products, not required source files.

## Modules

| File | Purpose |
|---|---|
| `Squares.lean` | Representations, squares, two directions of pasting, products, the actual arrow-category exponential, and a function-decoding impossibility example. |
| `Compiler.lean` | An intrinsically typed simply typed source; target-parametric compilation; its general denotation theorem; raw categorical syntax; certified rewrites and examples. |
| `SquareCompiler.lean` | Connects that compiler to explicit, possibly noninvertible representation maps. |
| `FirstOrder.lean` | A separate cartesian compiler, with a verified additive-map backend and a proof that the backend is not cartesian closed. |
| `Dependent.lean` | A concrete split family model; dependent substitution and context-extension squares; dependent Π/Σ certificate combinators and examples. |
| `Verification.lean` | Collects the modules and reports the foundational dependencies of representative theorems. |

There are no admitted proofs or user-declared axioms. Lean's ordinary
foundational principles, including function extensionality and proof
irrelevance, are used. See the recorded check output for the actual
dependencies; “no additional axioms” does not mean an axiom-free foundation.

## Scope

The simply typed and first-order source compilers are structural compilers
over explicit syntax. The dependent module is a **shallow**, compositional
certificate library for indexed families, not a parser or compiler for all
Lean/Agda source, nor a formalization of the LCCC/type-theory biequivalence.
The runtime function representation in `Squares.lean` contains a semantic
function as data; erasing that component requires a separate argument.

This code is independent of Felix. It uses the repository's general
comma-category formulation as a mathematical reference, not as a dependency.
Source snapshot examined:
`conal/felix@6f36d28097db7ea5f5df3263db3e8be08f74e490`.

## References

- Conal Elliott, [Compiling to Categories](https://conal.net/papers/compiling-to-categories/), ICFP 2017.
- [Haskell Interlude 62](https://haskell.foundation/podcast/62/), especially the discussion of four-arrow squares around 35:48–39:35.
- [Felix](https://github.com/conal/felix), particularly `Construct/Comma/Type.agda`.
- Further primary references and exact mathematical qualifications appear in `DESIGN.md`.
