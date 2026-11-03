import SquareKit.SmoothElementDescent
import SquareKit.SmoothPresentedDual

/-! Experimental compatibility of scalar descent with the checked dual presentation.
The comparison lands in actual dual numbers, retaining their infinitesimal coefficient. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PrincipalCover
open PresentedLocalization
attribute [local instance] DualExtension.smoothStructure
variable {n m k : ℕ}

/-- Extending a cover to the finite dual presentation and gluing commutes with
its constructed comparison to actual dual numbers. -/
theorem dual_glue (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (a : AtSections r s) :
    Presentation.toDual r
      ((atDescentEquiv (Presentation.relations r (Presentation.dualEquation n))
        (fun i => Presentation.dualInclusion r (s i)) (map_covers (Presentation.dualInclusion r) s hs)).symm
        (atTransport r s (Presentation.relations r (Presentation.dualEquation n)) (Presentation.dualInclusion r) a)) =
      DualExtension.inclusion ((atDescentEquiv r s hs).symm a) := by
  rw [← at_glue_natural r s hs _ (Presentation.dualInclusion r) a]
  exact congrArg (fun h : Hom (Presentation.Carrier r) (DualNumber (Presentation.Carrier r)) =>
    h ((atDescentEquiv r s hs).symm a)) (Presentation.toDual_inclusion r)

/-- Every actual dual element, with arbitrary infinitesimal part, is recovered
by descent in the finite presentation that is smoothly isomorphic to it. -/
theorem recover_dual (r : Fin m → Free n)
    (s : Fin k → Presentation.Dual r) (hs : Covers s) (d : DualNumber (Presentation.Carrier r)) :
    Presentation.toDual r
      ((atDescentEquiv (Presentation.relations r (Presentation.dualEquation n)) s hs).symm
        ((atDescentEquiv (Presentation.relations r (Presentation.dualEquation n)) s hs) (Presentation.fromDual r d)))=d := by
  rw [(atDescentEquiv (Presentation.relations r (Presentation.dualEquation n)) s hs).symm_apply_apply]
  exact congrArg (fun h : Hom (DualNumber (Presentation.Carrier r)) (DualNumber (Presentation.Carrier r)) => h d)
    (Presentation.toDual_fromDual r)

end SquareKit.SmoothAlgebra.PrincipalCover
