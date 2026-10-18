import SquareKit.SmoothOpenKL

/-! Experimental comparison of the particular infinitesimal exponentials across
a topology inclusion. Both KL isomorphisms are constructed by the shared proof;
no preservation of arbitrary exponentials by forgetting is assumed. -/
noncomputable section
namespace SquareKit.SmoothTopologyKLComparison
open CategoryTheory SmoothPresentationSite SheafRelation SheafFunction
open SmoothGeometricKL SmoothGeometricDerivative
variable {J K : GrothendieckTopology Site}
  [Fact (Presieve.IsSheaf J scalarData)] [Fact (Presieve.IsSheaf K scalarData)]

abbrev forget (hJK : J ≤ K) : Sheaf K Type ⥤ Sheaf J Type where
  obj X := ⟨X.obj,(isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_of_le _ hJK ((isSheaf_iff_isSheaf_of_type _ _).mp X.property))⟩
  map f := ⟨f.hom⟩

def scalarComparison (hJK : J ≤ K) :
    (forget hJK).obj (PresentationGeometry.scalar K) ≅ PresentationGeometry.scalar J := Iso.refl _
def infinitesimalComparison (hJK : J ≤ K) :
    (forget hJK).obj (PresentationGeometry.infinitesimal K) ≅ PresentationGeometry.infinitesimal J := Iso.refl _

theorem universalValue_comparison (hJK : J ≤ K) {X : Sheaf K Type}
    (h : product (PresentationGeometry.infinitesimal K) X ⟶ PresentationGeometry.scalar K)
    (A : Code) (x : X.obj.obj (atStage A)) :
    universalValue (J := J) (X := (forget hJK).obj X) ((forget hJK).map h) A x = universalValue h A x := rfl

theorem coefficients_comparison (hJK : J ≤ K) {X : Sheaf K Type}
    (h : product (PresentationGeometry.infinitesimal K) X ⟶ PresentationGeometry.scalar K) :
    (forget hJK).map (coefficients h) = coefficients ((forget hJK).map h) := rfl

/-- The specific exponential comparison is obtained through its two coefficient isomorphisms. -/
def functionComparison (hJK : J ≤ K) :
    (forget hJK).obj (functions (J := K)) ≅ functions (J := J) :=
  (forget hJK).mapIso (kl (J := K)).symm ≪≫ kl (J := J)

theorem evaluation_comparison (hJK : J ≤ K) :
    parameterMap (PresentationGeometry.infinitesimal J) (functionComparison hJK).hom ≫
      evaluation (PresentationGeometry.infinitesimal J) (PresentationGeometry.scalar J) =
      (forget hJK).map (evaluation (PresentationGeometry.infinitesimal K) (PresentationGeometry.scalar K)) := by
  ext A p
  change (evaluation (PresentationGeometry.infinitesimal J) (PresentationGeometry.scalar J)).hom.app A
    (p.1, (PresentationGeometry.affine (J := J)).hom.app A ((extract (J := K)).hom.app A p.2)) = _
  exact (PresentationGeometry.affine_evaluation (J := J) A.unop.unop p.1.val p.1.property
    ((extract (J := K)).hom.app A p.2).1 ((extract (J := K)).hom.app A p.2).2).trans
    (evaluation_extract (J := K) A.unop.unop p.1 p.2).symm

theorem curry_comparison (hJK : J ≤ K) {X : Sheaf K Type}
    (h : product (PresentationGeometry.infinitesimal K) X ⟶ PresentationGeometry.scalar K) :
    (forget hJK).map (curry h) ≫ (functionComparison hJK).hom = curry ((forget hJK).map h) := by
  change (forget hJK).map (curry h) ≫
    (forget hJK).map (extract (J := K)) ≫ PresentationGeometry.affine = _
  calc
    _ = ((forget hJK).map (curry h) ≫ (forget hJK).map (extract (J := K))) ≫
        PresentationGeometry.affine := (Category.assoc _ _ _).symm
    _ = (forget hJK).map (curry h ≫ extract (J := K)) ≫
        PresentationGeometry.affine := congrArg (fun f => f ≫ PresentationGeometry.affine)
          ((forget hJK).map_comp _ _).symm
    _ = coefficients ((forget hJK).map h) ≫ PresentationGeometry.affine :=
      congrArg (fun f => (forget hJK).map f ≫ PresentationGeometry.affine) (extract_curry h)
    _ = _ := ?_

  exact (curry_parameter (PresentationGeometry.affineBody (J := J))
    (coefficients (J := J) (X := (forget hJK).obj X) ((forget hJK).map h))).symm.trans
    (congrArg (fun f : product (PresentationGeometry.infinitesimal J) ((forget hJK).obj X) ⟶
      PresentationGeometry.scalar J => curry f)
      (rebuild_coefficients (J := J) (X := (forget hJK).obj X) ((forget hJK).map h)))

theorem derivative_comparison (hJK : J ≤ K)
    (f : PresentationGeometry.scalar K ⟶ PresentationGeometry.scalar K) :
    (forget hJK).map (derivative f) = derivative ((forget hJK).map f) := by
  rw [derivative_coefficients, derivative_coefficients]
  rfl

def openFunctionsComparison : SmoothOpenSite.toFinite.obj SmoothOpenSite.functions ≅
    (functions (J := topology)) := functionComparison SmoothOpenSite.finite_topology_le

end SquareKit.SmoothTopologyKLComparison
