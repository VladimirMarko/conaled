import SquareKit.Internal.Cubical.ContextualModel
import SquareKit.Internal.Cubical.IdentityMaps
import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics

/-! The ordinary contextual action motive also has a pointwise marked-identity section. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => model Base Fiber
variable {Γ : Presheaf.Context.{u}} (A C : LawfulFamily Γ)
  (t : Term (reindex C.family (projection A.family))) (x : Term A.family)

def functionMap : A.family ⟶ C.family where
  app z := TypeCat.ofHom (fun a => t.val (extendObj A.family z a))
  naturality z w f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (t.property (extendHom A.family f a)).symm

private theorem cast_down {Δ : Presheaf.Context.{u}} {D E : LawfulFamily Δ}
    (h : D = E) (s : ULift.{u+1} (Term D.family)) :
    HEq ((cast (congrArg (fun F : LawfulFamily Δ => ULift.{u+1} (Term F.family)) h) s).down) s.down := by
  cases h; rfl

theorem ordinaryApply_down :
    (ordinaryApply M A C ⟨t⟩ ⟨x⟩).down = x.map (functionMap A C t) := by
  apply eq_of_heq
  exact cast_down ((M).toStructuralModel.weaken_section_type A ⟨x⟩ C) _

abbrev actionPathFamily : LawfulFamily (total A.family) := (M).toStructuralModel.pathFamily A ⟨x⟩
abbrev actionContext : Presheaf.Context.{u} := total (actionPathFamily Base Fiber A x).family
abbrev actionProjection : actionContext Base Fiber A x ⟶ Γ :=
  projection (actionPathFamily Base Fiber A x).family ≫ projection A.family

def pointwiseInput : Term (normalizedIdentity
    (reindex A.family (actionProjection Base Fiber A x))
    (x.reindex (actionProjection Base Fiber A x))
    ((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family))) :=
  (generic (actionPathFamily Base Fiber A x).family).convert
    (normalizedIdentity_reindex (reindex A.family (projection A.family))
      (x.reindex (projection A.family)) (generic A.family)
      (projection (actionPathFamily Base Fiber A x).family))

def pointwiseMap := Functor.whiskerLeft (actionProjection Base Fiber A x).mapElements
  (functionMap A C t)

def pointwiseResult := (pointwiseInput Base Fiber A x).map
  (normalizedIdentityMap (pointwiseMap Base Fiber A C t x) _ _)

theorem pointwiseMotive_eq : (ordinaryApMotive M A C ⟨t⟩ ⟨x⟩).family =
    normalizedIdentity (reindex C.family (actionProjection Base Fiber A x))
      ((x.reindex (actionProjection Base Fiber A x)).map (pointwiseMap Base Fiber A C t x))
      (((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family)).map
        (pointwiseMap Base Fiber A C t x)) := by
  exact congrArg (fun z : Term C.family =>
    normalizedIdentity (reindex C.family (actionProjection Base Fiber A x))
      (z.reindex (actionProjection Base Fiber A x))
      (t.reindex (projection (actionPathFamily Base Fiber A x).family)))
    (ordinaryApply_down Base Fiber A C t x)

def pointwiseApSection : (M).Section (actionContext Base Fiber A x)
    (ordinaryApMotive M A C ⟨t⟩ ⟨x⟩) :=
  ⟨(pointwiseResult Base Fiber A C t x).convert (pointwiseMotive_eq Base Fiber A C t x).symm⟩

end SquareKit.Cubical.Contextual
