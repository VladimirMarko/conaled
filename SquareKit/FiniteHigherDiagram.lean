import SquareKit.PseudofunctorMapping

/-! Normalized weak diagrams on the opens of a discrete two-point space. Full maps retain all five edge comparisons and both chain modifications. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.HigherCategory
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w
/-- Nonidentity portion of a normalized diagram on the full opens poset. -/
structure FullDiagram where
  top : Type u
  left : Type u
  right : Type u
  empty : Type u
  [topBicat : Bicategory.{w,v} top]
  [leftBicat : Bicategory.{w,v} left]
  [rightBicat : Bicategory.{w,v} right]
  [emptyBicat : Bicategory.{w,v} empty]
  rL : Pseudofunctor top left
  rR : Pseudofunctor top right
  r0 : Pseudofunctor top empty
  sL : Pseudofunctor left empty
  sR : Pseudofunctor right empty
  cL : Bicategory.Equivalence (rL.comp sL) r0
  cR : Bicategory.Equivalence (rR.comp sR) r0

end SquareKit.HigherCategory
namespace SquareKit.FiniteHigherMap
open CategoryTheory Bicategory SquareKit.HigherCategory
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
attribute [instance] FullDiagram.topBicat FullDiagram.leftBicat FullDiagram.rightBicat FullDiagram.emptyBicat
variable (F : FullDiagram.{u,v,w}) (T : FullDiagram.{u',v',w'})

structure MapCore where
  top : Pseudofunctor F.top T.top
  left : Pseudofunctor F.left T.left
  right : Pseudofunctor F.right T.right
  empty : Pseudofunctor F.empty T.empty
  topLeft : Bicategory.Equivalence (F.rL.comp left) (top.comp T.rL)
  topRight : Bicategory.Equivalence (F.rR.comp right) (top.comp T.rR)
  topEmpty : Bicategory.Equivalence (F.r0.comp empty) (top.comp T.r0)
  leftEmpty : Bicategory.Equivalence (F.sL.comp empty) (left.comp T.sL)
  rightEmpty : Bicategory.Equivalence (F.sR.comp empty) (right.comp T.sR)

variable {F T}

def leftDirect (H : MapCore F T) : (F.rL.comp F.sL).comp H.empty ⟶ H.top.comp T.r0 :=
  postTrans H.empty F.cL.hom ≫ H.topEmpty.hom

def leftPasted (H : MapCore F T) : (F.rL.comp F.sL).comp H.empty ⟶ H.top.comp T.r0 :=
  eqToHom (comp_assoc F.rL F.sL H.empty) ≫
    preTrans F.rL H.leftEmpty.hom ≫
    eqToHom (comp_assoc F.rL H.left T.sL).symm ≫
    postTrans T.sL H.topLeft.hom ≫
    eqToHom (comp_assoc H.top T.rL T.sL) ≫
    preTrans H.top T.cL.hom

def rightDirect (H : MapCore F T) : (F.rR.comp F.sR).comp H.empty ⟶ H.top.comp T.r0 :=
  postTrans H.empty F.cR.hom ≫ H.topEmpty.hom

def rightPasted (H : MapCore F T) : (F.rR.comp F.sR).comp H.empty ⟶ H.top.comp T.r0 :=
  eqToHom (comp_assoc F.rR F.sR H.empty) ≫
    preTrans F.rR H.rightEmpty.hom ≫
    eqToHom (comp_assoc F.rR H.right T.sR).symm ≫
    postTrans T.sR H.topRight.hom ≫
    eqToHom (comp_assoc H.top T.rR T.sR) ≫
    preTrans H.top T.cR.hom

structure Map extends MapCore F T where
  leftCoherence : leftDirect toMapCore ≅ leftPasted toMapCore
  rightCoherence : rightDirect toMapCore ≅ rightPasted toMapCore

end SquareKit.FiniteHigherMap

end
