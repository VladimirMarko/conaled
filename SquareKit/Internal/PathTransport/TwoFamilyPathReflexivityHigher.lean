import SquareKit.Internal.PathTransport.TwoFamilyPathReflexivity
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [ib : Bicategory.{wΓ,vΓ} Γ] [isb : Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [ig : ∀ γ, IsGroupoid (F.obj γ)] [il : ∀ γ, IsLocallyGroupoid (F.obj γ)]
theorem pathReflexivityCell_id {x y : Total F} (p : x ⟶ y) :
 pathReflexivityCell F (𝟙 p) = 𝟙 (pathReflexivityMap F p) := by
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
 · exact (diagonalTotal F).map₂_id p
 · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _

theorem pathReflexivityCell_comp {x y : Total F} {p q r : x ⟶ y}
 (α : p ⟶ q) (β : q ⟶ r) :
 pathReflexivityCell F (α ≫ β) = pathReflexivityCell F α ≫ pathReflexivityCell F β := by
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
 · exact (diagonalTotal F).map₂_comp α β
 · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
private theorem cell_comp_base (F : Family Γ) {x y : Total F}
    {p q r : x ⟶ y} (α : p ⟶ q) (β : q ⟶ r) :
    (α ≫ β).base = α.base ≫ β.base := rfl
private theorem cell_eqToHom_base (F : Family Γ) {x y : Total F}
    {p q : x ⟶ y} (h : p = q) :
    (eqToHom h).base = eqToHom (congrArg (fun r : x ⟶ y => r.base) h) := by
  cases h
  rfl

theorem pathReflexivity_whiskerLeft {x y z : Total F} (p : x ⟶ y) {q r : y ⟶ z}
 (α : q ⟶ r) :
 pathReflexivityCell F (p ◁ α) =
 eqToHom (pathReflexivityMap_comp F p q) ≫
   pathReflexivityMap F p ◁ pathReflexivityCell F α ≫
   eqToHom (pathReflexivityMap_comp F p r).symm := by
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
 · simp only [cell_comp_base (openIdHigher F), cell_eqToHom_base (openIdHigher F)]
   change (diagonalTotal F).map₂ (p ◁ α) =
     eqToHom ((diagonalTotal F).map_comp p q) ≫
       (diagonalTotal F).map p ◁ (diagonalTotal F).map₂ α ≫
       eqToHom ((diagonalTotal F).map_comp p r).symm
   simpa only [(diagonalTotal F).mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
     (diagonalTotal F).map₂_whisker_left p α
 · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
theorem pathReflexivity_whiskerRight {x y z : Total F} {p q : x ⟶ y}
 (α : p ⟶ q) (r : y ⟶ z) :
 pathReflexivityCell F (α ▷ r) =
 eqToHom (pathReflexivityMap_comp F p r) ≫
   pathReflexivityCell F α ▷ pathReflexivityMap F r ≫
   eqToHom (pathReflexivityMap_comp F q r).symm := by
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
 · simp only [cell_comp_base (openIdHigher F), cell_eqToHom_base (openIdHigher F)]
   change (diagonalTotal F).map₂ (α ▷ r) =
     eqToHom ((diagonalTotal F).map_comp p r) ≫
       (diagonalTotal F).map₂ α ▷ (diagonalTotal F).map r ≫
       eqToHom ((diagonalTotal F).map_comp q r).symm
   simpa only [(diagonalTotal F).mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
     (diagonalTotal F).map₂_whisker_right α r
 · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reflexivity on the actual general path context, including all higher laws. -/
noncomputable def pathReflexivity : StrictPseudofunctor (Total F) (PathContext F) :=
 StrictPseudofunctor.mk'' (by
   refine { obj := pathReflexivityObj F
            map := fun {x y} p => pathReflexivityMap F p
            map₂ := fun {x y p q} α => pathReflexivityCell F α
            map_id := pathReflexivityMap_id F
            map_comp := fun p q => pathReflexivityMap_comp F p q
            map₂_id := pathReflexivityCell_id F
            map₂_comp := fun α β => pathReflexivityCell_comp F α β
            map₂_whisker_left := ?_
            map₂_whisker_right := ?_ }
   · intro x y z p q r α
     with_reducible exact @pathReflexivity_whiskerLeft.{u,v,w,uΓ,vΓ,wΓ} Γ ib isb F ig il x y z p q r α
   · intro x y z p q α r
     with_reducible exact @pathReflexivity_whiskerRight.{u,v,w,uΓ,vΓ,wΓ} Γ ib isb F ig il x y z p q α r)
/-- Reflexivity lies over the constructed endpoint diagonal in every dimension. -/
theorem pathReflexivity_endpoints :
    (pathReflexivity F).comp (pathEndpoints F) = diagonalTotal F :=
  StrictTwoTransformation.functor_ext rfl
end SquareKit.Internal.PathTransport.TwoFamily
