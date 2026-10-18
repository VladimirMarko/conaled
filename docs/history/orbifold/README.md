# Historical orbifold artifacts

Imported on 2026-10-18 from `/home/vlad/Downloads/orbifold/`. Both supplied
files are preserved byte for byte. This README supplies later annotations;
the chat's proposals and numerical results are not checked Lean claims.

| File | Contents | Status |
|---|---|---|
| [orbifold-simulator-chat.md](orbifold-simulator-chat.md) | Two prompts and responses: synthetic orbifolds and simulation; generalizations of gyrovector geometry | Historical motivation and research leads |
| [orbifold_gyro_probe.py](orbifold_gyro_probe.py) | Standard-library Python probe of framed disk motions and the hyperbolic cone orbifold with quarter-turn symmetry | Numerical experiment, outside the Lean build |

## Reading the chat

Response 1 discusses Myers' [*Orbifolds as microlinear types in synthetic
differential cohesive homotopy type theory*](https://arxiv.org/abs/2205.15887).
Sections 1–3 distinguish intrinsic geometry, explicit quotient presentations,
and equivariant dynamics. Sections 4–7 discuss atlases, geometric algebra,
representation proofs, and possible foundations. Section 8 proposes a first
Euclidean quotient example. The producing session explicitly lacked Lean;
none of its proposed formalizations was type-checked there.

Response 2 is the source for the gyrovector research direction. Sections 1–2
separate displacement from orientation and explain why independent orbit
representatives do not support naive gyroaddition. Section 3 surveys geodesic
loops, matrix gyrostructures, and post-Lie integration. Section 4 proposes
framed homogeneous and general Riemannian presentations; sections 5–6 describe
the probe and possible proof interfaces. The proposed “orbifold displacement
calculus” is a working design, not an established implementation.

The [current research note](../../research/orbifold-geometry.md) checks selected
claims against primary sources and the local architecture. It distinguishes
an explicit Lean/Mathlib presentation from the paper's synthetic type theory.
The archive's `sandbox:` attachment URL refers to the original session; the
Python file above is the supplied local attachment. Other chat citations are
research leads, not an assertion that every linked claim has been verified.

## Probe scope and reproduction

Run from the repository root:

```sh
direnv exec . python3 docs/history/orbifold/orbifold_gyro_probe.py
```

The import run passed every existing assertion with the default 1,000 samples
and seed 1729. It checked the gyroassociative identity, framed composition,
agreement with projective complex matrices, action composition, and quarter-turn
relabeling. The maximum sampled framed associativity residual was about
`7.45e-16`; the deliberately wrong position-only relabeling produced a residual
of about `0.112`. A 40-step diameter geodesic passed through the cone apex and
agreed with its analytic coordinate formula to about `3.89e-16`.

These are floating-point coordinate residuals, not intrinsic error bounds or
proofs. The matrices are projective complex 2×2 matrices; the probe does not
implement a Lorentz-matrix backend. It has no general atlas engine, force law,
certified ODE integrator, or renderer. The exact quarter-turn labels do not
make the floating-point geometric calculations exact.

No orbifold Lean modules have been added. Future checked implementations belong
to the orbifold workstream and must meet the repository's usual
statement-review, checked-example, and proof-audit requirements.

## Follow-up work

- [#32: Myers' theory in Lean](https://github.com/VladimirMarko/conaled/issues/32)
  asks for a Mathlib-compatible formalization or a justified reformulation.
- [#33: Generalized gyrovector geometry](https://github.com/VladimirMarko/conaled/issues/33)
  compares the proposed geometric operations and their assumptions.
- [#34: Verified orbifold simulator](https://github.com/VladimirMarko/conaled/issues/34)
  tracks the long-term simulator and its geometric and numerical contracts.
