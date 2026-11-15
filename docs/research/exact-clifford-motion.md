# Exact Clifford lifts of framed disk motion

Implementation record for [#412](https://github.com/VladimirMarko/conaled/issues/412),
following the [Lorentz and Clifford research](lorentz-clifford-realizations.md)
and the [exact Lorentz implementation](exact-lorentz-motion.md).

The checked implementation realizes four even coordinates in Mathlib's actual
Clifford algebra, proves its sandwich action equal to the independent Lorentz
matrix formula, and identifies precisely the sign ambiguity in point and full
frame observations. The native `Pose`, motion specification, squares interface,
and certified numerical backend remain in place.

## Actual algebra and admitted elements

[Coordinates.lean](../../Applications/Orbifold/Clifford/Coordinates.lean) uses
`Q(x,y)=x²+y²` and Mathlib's `EquivEven.Q' Q`, whose coordinates are `((x,y),t)`
and whose value is `x²+y²−t²`. The `primal` embedding explicitly reindexes the
Lorentz vector `(t,x,y)`. The basis satisfies `e₀²=−1`, `e₁²=e₂²=1`.
These are primal vectors, not dual points.

The coefficient tuple `(a,b,c,d)` represents

```
a + b e₀e₁ + c e₀e₂ + d e₁e₂.
```

`equivEven` constructs the actual even element from `Cl(2,0)`. A Pauli matrix
representation of that smaller algebra proves independence of these four
coefficients. It is not asserted to be a faithful representation of all
`Cl(2,1)`. `value_product` proves that the coordinate product is the actual
Clifford product. `value_reversed` proves the coordinate reverse
`(a,−b,−c,−d)` is Clifford reversion.

[Rotor.lean](../../Applications/Orbifold/Clifford/Rotor.lean) admits exactly those
four-coordinate elements with `a²+d²−b²−c²=1`. This is a certificate on input,
not a conclusion assumed about its action. Reversion gives both inverse laws,
and `unit` packages the result as an actual Clifford unit.
[Generators.lean](../../Applications/Orbifold/Clifford/Generators.lean) proves
that every admitted rotor is a product of a positive-time boost and a chosen
rotation lift. Thus the carrier has a checked generation description. The
proof uses the positive quantity `n=a²+d²=1+b²+c²` and its exact square root.

The implementation does not classify arbitrary Clifford normalizers or prove
that this carrier equals Mathlib's `spinGroup`. It also does not prove that all
even multivectors have these coordinates. Neither result is needed for the
stated generated carrier and its geometric comparison.

## Independent sandwich and observation comparison

`sandwich_primal` (in namespace `Orbifold.Clifford`) proves

```
value r * primal X * reverse (value r) = primal (sandwichMatrix r *ᵥ X)
```

for every coefficient tuple and every real vector. `Rotor.unit_sandwich`
specializes this to genuine conjugation by an admitted unit. The matrix is
calculated from Clifford products; it is not defined by decoding a native
pose and re-encoding it.

For a normalized rotor, `Rotor.pose` has point and phase

```
point = ((ab+cd)/n, (ac−bd)/n)
phase = ((a²−d²)/n, −2ad/n),       n=a²+d².
```

The norm equation proves the point is inside the disk and the phase is unit.
`Rotor.sandwich_encode` then proves equality with `Lorentz.encode`. This
connects the algebra calculation to the independently checked Lorentz point
and full oriented frame, `w ↦ (1−|point|²) phase w/2`.

The comparison preserves identity, multiplication, reverse inverse, and every
finite word, including the empty word. Multiplication applies the right
operand first. `finite_pointAction` and `finite_frameAction` compare arbitrary
valid disk points and arbitrary tangent vectors with the native action and
its derivative. `finite_frame` compares every direction in the base frame.
These derivatives do not describe parallel transport along arbitrary paths.

## Sign quotient and selected labels

`Rotor.kernel` proves that an admitted element has identity matrix exactly
when it is `1` or `−1`. `realized_eq_iff` proves two admitted elements have the
same matrix exactly when they are equal or negatives. `observations_eq_iff`
proves the same characterization for equality of the native point and the
entire oriented frame. All these equalities are exact Lean equalities of the
specified denotations; equality of Clifford representatives is finer.

`Rotor.Geometry` quotients by matrix observation equality, proved equivalent
to that sign relation. `quotientRealized` is well-defined and injective;
`quotientComp` descends multiplication and preserves Lorentz composition.
This quotient does not erase separately supplied symmetry arrows.

[CliffordMotion.lean](../../Examples/CliffordMotion.lean) checks the independent
noncommuting poses `(1/3,i)` and `(i/4,(3+4i)/5)`. Their composed point is `1/11`
and their full frame is `((-48+36i)/121)w`, through the existing Lorentz results.
It also checks inverse tangent action, a quarter-turn lift, its half-turn
square, the full-turn value `−1`, and the double-full-turn value `1`.
The full turn has identity geometric action while retaining a distinct
Clifford representative. Negation preserves arbitrary point-dependent frame
action.

The ordinary finite-composition consumer uses the existing `Squares.Rep`,
`Square`, `synchronize`, and native `Motion diskForm`. The external C4 quarter
turn is connected to its Clifford matrix. Selected ineffective arrow labels
remain distinct even when their entire Clifford payload agrees; right body
increments retain the original action-category label.

## Acquisition and coverage boundary

Callers can compose certified generators, supply normalized coordinates, or
use `ofPose` with a chosen half-phase `(a,d)` satisfying
`a²+d²=1` and `(a²−d²,−2ad)=p.u`. `pose_ofPose` proves this conversion returns
exactly the supplied native pose. The implementation does not construct such
a half-phase for every unit phase, claim a global continuous lift, or select an
angle branch. A chosen lift remains additional input data.

Boost acquisition from a disk point and the generation decomposition use
noncomputable exact real square roots. There is no executable square-root,
rounded normalization, floating-point validation, or conditioning guarantee.
The null coordinate tuple `(1,1,0,0)` and the zero tuple fail the admission
certificate. Arbitrary multivectors and noninvertible inputs are outside the
carrier; callers cannot pass them merely by calling them rotors.

## Reuse and remaining scope

The inspected Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`.
The implementation directly reuses
[`Basic`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean),
[`EvenEquiv`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/CliffordAlgebra/EvenEquiv.lean),
the even subalgebra, linear embeddings, reversion, algebra homomorphisms, and
ordinary units. Inspection also covered `Even`, `Conjugation`, `Inversion`,
and [`SpinGroup`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean).
That file defines the Lipschitz group by generated closure and does not supply
the needed arbitrary-normalizer characterization. Its name alone would not
justify a future-component cover. The present proof instead constructs its
own admitted generated carrier and calculates the action.

This supplies a checked alternative realization under the existing
specification. It does not establish that general multivectors should become
the library's default representation. A blade-incidence or sphere consumer
would supply a further reason to compare that architecture. Numerical ranking,
general orbifold spin structures, and a classification of the whole future
Lorentz group remain separate questions.
