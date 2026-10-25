import SquareKit.Internal.SierpinskiEquivalence
import SquareKit.Internal.SierpinskiBaseCoherence

/-! # The relative classifier of one unconstrained proposition

`SquareKit.Internal.Sierpinski.classifier` evaluates the generic subterminal
`0 → 1` in `Arrow B`. For every represented sheaf source and geometric map
into `B`, it is an equivalence of full categories with subterminals of the
source. Transformations are unrestricted inverse-image natural transformations.
The inverse uses a pushout left adjoint, proved left exact by pointwise presheaf
calculation and sheafification. No complementedness of the model is assumed.

`pseudopullback` gives the full varying-base cone equivalence. Source and base
unitors, associators, their mixed comparison, and generic-model coherence live
in the imported modules. Thinness is derived for this proposition theory only.
-/
