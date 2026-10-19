import SquareKit.SmoothOpenSubdomain

/-! Experimental restriction under arbitrary ordinary smooth maps. The defining
function equation is an equality in the actual localization algebra; the map
itself need not extend smoothly to the ambient space. -/
noncomputable section
namespace SquareKit.EuclideanOpen
open CategoryTheory SmoothAlgebra SmoothPresentationSite Localization PresentedLocalization
variable {U V : Domain} (a : U ⟶ V) (p : Free U.dimension) (q : Free V.dimension)

/-- Actual localization base change exists for every ordinary map. -/
def baseChangeMap : code (subdomain V q) ⟶ localization (code U) (Localization.pullback a (element V q)) :=
  fromSubdomain V q ≫ localizationMap (show code V ⟶ code U from Localization.pullback a) (element V q)

theorem baseChange_square :
    (show code V ⟶ code (subdomain V q) from Localization.pullback (subInclusion V q)) ≫ baseChangeMap a q =
      (show code V ⟶ code U from Localization.pullback a) ≫
        localizationBase (code U) (Localization.pullback a (element V q)) := by
  unfold baseChangeMap
  rw [← Category.assoc,fromSubdomain_base,localization_square]

variable (he : Localization.pullback a (element V q) = element U p)

def restrictedAlgebra : Hom (Principal (V.defining*q)) (Principal (U.defining*p)) :=
  subLift V.defining q ((nestedMap U.defining p).comp (Localization.pullback a)) (by
    change IsUnit (nestedMap U.defining p (Localization.pullback a (element V q)))
    rw [he]
    exact nested_unit U.defining p)

def restriction : subdomain U p ⟶ subdomain V q := Localization.reconstruct (restrictedAlgebra a p q he)

theorem restriction_square : subInclusion U p ≫ a = restriction a p q he ≫ subInclusion V q := by
  apply (Localization.mapEquiv (U.defining*p) V.defining).injective
  change Localization.pullback (OpenFunctions.Map.comp a (subInclusion U p)) =
    Localization.pullback (OpenFunctions.Map.comp (subInclusion V q) (restriction a p q he))
  rw [Localization.pullback_comp,Localization.pullback_comp]
  change (Localization.pullback (subInclusion U p)).comp (Localization.pullback a) =
    (Localization.pullback (Localization.reconstruct (restrictedAlgebra a p q he))).comp
      (Localization.pullback (subInclusion V q))
  rw [Localization.pullback_reconstruct,nested_pullback,nested_pullback]
  exact (subLift_base _ _ _ _).symm

/-- The two presentation comparisons commute with arbitrary restrictions. -/
theorem restriction_localization_square :
    (show code V ⟶ localized V q from localizationBase (code V) (element V q)) ≫
      (toSubdomain V q ≫ (show code (subdomain V q) ⟶ code (subdomain U p) from
        Localization.pullback (restriction a p q he))) =
      (show code V ⟶ code U from Localization.pullback a) ≫
        localizationBase (code U) (element U p) ≫ toSubdomain U p := by
  rw [← Category.assoc,toSubdomain_base]
  refine ((Localization.pullback_comp (restriction a p q he) (subInclusion V q)).symm.trans
    ((congrArg (fun h : Map (subdomain U p) V => Localization.pullback h) (restriction_square a p q he).symm).trans
      (Localization.pullback_comp (subInclusion U p) a))).trans ?_
  exact congrArg (fun k : code U ⟶ code (subdomain U p) =>
    (show code V ⟶ code U from Localization.pullback a) ≫ k) (toSubdomain_base U p).symm

end SquareKit.EuclideanOpen
