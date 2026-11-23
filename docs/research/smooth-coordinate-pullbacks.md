# Coordinate pullbacks in the smooth sheaf model

Issue #673 supplies coordinate product and zero-fiber squares for the local
comparison used by #97. Coordinates split as `Fin (n+k)`, with `n` free and `k`
constrained coordinates. The ordinary objects are the principal domains
`EuclideanOpen.full n`, and their manifold objects are the inherited open
submanifolds `ordinaryOpen (full n)`.

`SmoothCoordinateAlgebra` defines the actual free-algebra inclusions, zero
insertion and constant maps. Its product and zero-fiber universal properties
quantify over arbitrary smooth algebras. Both equations, uniqueness and
postcomposition naturality are retained. No reducedness or presentation
hypothesis is required.

`SmoothCoordinatePullbacks` constructs the corresponding scalar-power maps
through the existing tuple interface. `product_isPullback` and
`zeroFiber_isPullback` quantify over arbitrary sheaf test objects. `fiberLift`
keeps the free block; its two projection equations and uniqueness justify the
inverse. Named component equations identify the coordinate projections with
the free-algebra maps. Restriction laws use every presentation-stage arrow,
including identity and composition.

`SmoothOpenCoordinatePullbacks.coordinateMap_comparison` identifies an actual
ordinary tuple of smooth operations with the scalar-power tuple under
`fullPowerIso`. This gives the ordinary coordinate squares and their principal
restrictions. `restricted_zeroFiber_isPullback` has ambient open defined by an
arbitrary `q`; the fiber open consists exactly of coordinates where
`q(x,0) ≠ 0`. `restrict_isPullback` and
`twice_restricted_zeroFiber_isPullback` retain the composite actual inclusions.
`inverse_localization_square` compares those inclusions with the localization
bases through `subdomainIso`. These proofs use the existing inverse-image and
overlap interfaces; they do not identify independently chosen smooth support
functions.

`SmoothManifoldCoordinatePullbacks` transports the squares to the actual
manifold realization via `principalIso_naturality`. Its `realize` abbreviation
is the existing manifold map applied to the ordinary principal-open map with
its proved `ContMDiff` witness. No general product-preservation premise is
introduced.

The examples retain two independent free coordinates, then reconstruct the
nonzero square-zero element `d` of `dual (free 0)`. Nonidentity stage maps double
and kill that element, exercising composite restriction. The same reconstructed
coordinate survives the principal opens `1+x ≠ 0` and `1-x ≠ 0`, their overlap
and the two successive inverse-image restrictions. Empty principal domains and
their inverse images are initial by empty-cover gluing. This does not assert
that their sections are empty at zero-ring stages. The cases `n=0` and `k=0`
also use the public universal square.

All proofs use the repository's default heartbeat, recursion and kernel
budgets. The zero-insertion component and ordinary comparison proofs use
declaration-local elaborator transparency settings for the scalar-power carrier.
No resource or toolchain defaults change.

#97 can use these actual local squares after conjugating through the
derivative-derived normal forms of #674. #675 owns construction of the ordinary
transverse equality-subtype manifold. Compatibility across its chart overlaps,
the final all-stage gluing and the realized transverse pullback theorem remain
with #97. General Weil KL, microlinearity, full well-adaptedness and higher or
cohesive comparisons do not follow from this coordinate result.
