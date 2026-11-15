import SquareKit.Internal.PathTransport.TwoFamilySigmaLaws
/-! Composition of the genuine-cell action on dependent Sigma families. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

/-- Vertical composition supplies the required cartesian source boundary. -/
theorem cartesianComparisonCell_comp_source {γ δ : Γ} {f g h : γ ⟶ δ}
    (α : f ⟶ g) (β : g ⟶ h) (a : F.obj γ) :
    cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ (α ≫ β)).app a) =
      (cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ α).app a)) ≫
        (fiberInclusion F δ).map ((F.map₂ β).app a) := by
  rw [F.map₂_comp, StrictTwoTransformation.Trans.comp_app,
    (fiberInclusion F δ).map_comp, Category.assoc]

/-- Cartesian comparison cells compose by whiskering the first comparison. -/
theorem cartesianComparisonCell_comp {γ δ : Γ} {f g h : γ ⟶ δ}
    (α : f ⟶ g) (β : g ⟶ h) (a : F.obj γ) :
    cartesianComparisonCell F (α ≫ β) a =
      eqToHom (cartesianComparisonCell_comp_source F α β a) ≫
        (cartesianComparisonCell F α a ▷ (fiberInclusion F δ).map ((F.map₂ β).app a)) ≫
          cartesianComparisonCell F β a := by
  apply equalityFiber_ext F
  · change (cartesianComparisonCell F (α ≫ β) a).base =
      (eqToHom (cartesianComparisonCell_comp_source F α β a)).base ≫
        ((cartesianComparisonCell F α a).base ▷ 𝟙 δ) ≫
          (cartesianComparisonCell F β a).base
    rw [total_eqToHom_base, cartesianComparisonCell_base, cartesianComparisonCell_base,
      cartesianComparisonCell_base]
    simp
    rw [Bicategory.whiskerRight_id α]
    simp [Strict.rightUnitor_eqToIso]
  · exact cartesianComparisonCell_equalityFiber F _ _
  · exact equalityFiber_comp F (equalityFiber_cast F _)
      (equalityFiber_comp F
        (equalityFiber_whiskerRight F (cartesianComparisonCell_equalityFiber F α a) _)
        (cartesianComparisonCell_equalityFiber F β a))
/-- The component action preserves vertical composition through the actual later family. -/
theorem sigmaCellComponent_comp {γ δ : Γ} {f g h : γ ⟶ δ}
    (α : f ⟶ g) (β : g ⟶ h) (x : sigmaFiber F γ B) :
    sigmaCellComponent F B (α ≫ β) x =
      sigmaCellComponent F B α x ≫ sigmaCellComponent F B β x := by
  apply Pseudofunctor.CoGrothendieck.ext
  · change (F.map₂ (α ≫ β)).app x.base = (F.map₂ α).app x.base ≫ (F.map₂ β).app x.base
    rw [F.map₂_comp]
    rfl
  · apply HEq.trans (sigmaCellComponent_fiber_heq F B (α ≫ β) x)
    rw [cartesianComparisonCell_comp, B.map₂_comp, B.map₂_comp,
      StrictTwoTransformation.Trans.comp_app, StrictTwoTransformation.Trans.comp_app,
      B.map₂_eqToHom, StrictTwoTransformation.Trans.eqToHom_app,
      action_whiskerRight]
    change HEq (eqToHom _ ≫
      (eqToHom _ ≫ (B.map ((fiberInclusion F δ).map ((F.map₂ β).app x.base))).map
        ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫ eqToHom _) ≫
          (B.map₂ (cartesianComparisonCell F β x.base)).app x.fiber)
      (eqToHom _ ≫ (B.map ((fiberInclusion F δ).map ((F.map₂ β).app x.base))).map
        (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫
          (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F β x.base)).app x.fiber))
    rw [(B.map ((fiberInclusion F δ).map ((F.map₂ β).app x.base))).map_comp,
      StrongMap.map_eqToHom]
    simp only [Category.assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    rfl

/-- Vertical composition of genuine cells is preserved by the constructed Sigma action. -/
theorem sigmaCell_comp {γ δ : Γ} {f g h : γ ⟶ δ} (α : f ⟶ g) (β : g ⟶ h) :
    sigmaCell F B (α ≫ β) =
      StrictTwoTransformation.Trans.comp (sigmaCell F B α) (sigmaCell F B β) := by
  apply StrictTwoTransformation.Trans.ext
  exact sigmaCellComponent_comp F B α β

end SquareKit.Internal.PathTransport.TwoFamily
