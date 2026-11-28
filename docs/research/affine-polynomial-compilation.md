# Affine polynomial compilation

Issue #740 connects the cartesian source language to polynomial coordinate maps and actual affine scheme morphisms over a commutative ring R. `compile_realize` identifies the independently assembled geometric compiler with realization of the coordinate compiler for every source term and context, including let bindings. `recover_compile` recovers the complete coordinate map from the compiled scheme morphism.

The [polynomial library](../../Applications/AlgebraicGeometry/Polynomial.lean) exposes `PolynomialMap.Map`, `coordEquiv`, composition and evaluation without compiler syntax. Each output coordinate is a multivariate polynomial in the input coordinates. `coordEquiv` uses Mathlib's polynomial universal property to identify these tuples with R-algebra homomorphisms in the opposite direction. In particular, a followed by b induces the coordinate homomorphism of a composed after that of b. `evaluate_natural` proves compatibility with algebra maps, and `evaluate_generic` recovers a polynomial map by evaluation on the polynomial-ring generators.

The [geometric library](../../Applications/AlgebraicGeometry/AffineCompiler.lean) defines `GeometricHom` as all scheme morphisms between the selected affine spaces that commute with their maps to Spec R. `geometricEquiv` combines polynomial freeness with Mathlib's `Spec.homEquivAlgHom`; `realize` and `recover` are its inverse maps. The construction retains arbitrary polynomial morphisms between these objects. It does not restrict geometric arrows to a stored source term or an assumed code-generation witness.

## Cartesian objects and compilation

Source coordinates reuse `MatrixCompiler.Slots`, `encode` and `decode`: one coordinate for the ground type, none for unit, and disjoint union for products. This shares the existing coordinate/value round trips without changing the matrix fragment. Polynomial primitives admit constants, addition and variable multiplication; the linear compiler keeps its own vocabulary and contracts. The root `FirstOrder.lean` remains Std-only.

`affineSpaceIso` compares each selected spectrum with Mathlib's affine space over Spec R and proves the base-map comparison. The zero-coordinate object has `unitIso` to Spec R. `isPushout_polynomial` constructs the polynomial-ring pushout from the universal property of polynomial evaluation; Mathlib's contravariant Spec construction gives `product_isPullback`. This pullback property quantifies over all scheme test objects. `geometricPair_first`, `geometricPair_second` and `geometricPair_unique` identify the compiler's actual pairing with its universal solution.

The geometric target uses actual identity and composition of scheme maps. Its primitive maps and projections are realized coordinate maps; its pairing is constructed using exact recovery and polynomial pairing. `realizationMap_laws` and `realization_preserves` supply the local preservation obligations. `compile_realize` then uses `SquareKit.FirstOrderNaturality.naturality`, without another induction proving geometric soundness constructor by constructor.

The general polynomial-map API allows independent coefficient and index universes. The compiler and scheme specialization use `R : Type`, `A : Type` and `Scheme.{0}`, matching the existing small first-order source/target and coordinate encodings. No nontriviality or field assumption is imposed on R. Extending this source specialization to larger coefficient universes would require a universe-polymorphic source/target or a selected small literal vocabulary; it is not supplied by this implementation.

## Points and checked applications

`Points R A a` consists of actual morphisms Spec A to the selected affine object over Spec R. `pointEquiv` identifies these with coordinate vectors. `realize_point` and `compile_points` connect the geometric action to evaluation in every commutative R-algebra A in the stated universe, reusing the original compiler's Set-valued soundness through `sound` and `compile_correct`. `pointEquiv_change` identifies change of the point algebra with precomposition by Spec of the algebra map, and `mapPoint_natural` proves compatibility with arbitrary geometric arrows.

The [applications](../../Examples/AffinePolynomialCompiler.lean) retain:

- f(x,y) = (x+y, xy), g(u,v) = (u²+v, u+v), their explicit composite coordinates, and agreement of actual composed scheme maps. `source_composite_scheme` connects the compiled let-based composition to this independent direct-library calculation.
- Equality of coordinate and scheme interpretations for duplicated `(x+2)*(x+2)` and `let z := x+2; z*z`, with their A-valued point formula.
- Empty-context constants, the unit source, the zero-coordinate base isomorphism and the actual scheme pullback property.
- Equal functions on F₂-points for x² and x, but distinct polynomials and scheme morphisms. Their generic polynomial-ring-valued points remain distinct.

Statement review retains the contravariant order, all contexts and coefficient algebras, actual maps over the base, and the full scheme pullback property. Equality on points over a single finite field is deliberately insufficient for coordinate or scheme recovery. Equal semantic maps make no claim about execution cost, emitted binaries or speed.

## Scope and next work

This delivers the specified affine polynomial fragment. Ring base change and its identity/composition coherence belong to #741; the naturality above changes A as an R-algebra while retaining R. Higher-order ambient interpretation and geometric endpoint recovery remain #739. Scheme-site descent and non-affine clients remain #742. No new sheafification, stackification or F₁ geometry is required for this fragment.

The ordinary mathematical comparison is the contravariant affine-scheme correspondence in [Stacks, Section 26.6](https://stacks.math.columbia.edu/tag/01HX), and the fibre-product universal property in [Section 26.17](https://stacks.math.columbia.edu/tag/01JO), inspected on 2026-11-28. Lean proofs reuse the pinned Mathlib `MvPolynomial`, `GammaSpecAdjunction`, `AffineSpace` and `Pullbacks` interfaces. These source references explain the mathematical contract; candidate build/audit and independent review receipts are retained with the implementation handoff.
