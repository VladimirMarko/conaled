import SquareKit.Internal.PathTransport.TwoFamilyPathContext
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
private theorem discrete_casts_heq {C : Type*} [Category* C] {a b a' b' : C}
    (h : a = b) (k : LocallyDiscrete.mk a' = LocallyDiscrete.mk b') (ha : a = a') :
    HEq (Discrete.mk (eqToHom h)) (eqToHom k) := by
  cases h
  cases ha
  have hb : a = b' := congrArg LocallyDiscrete.as k
  cases hb
  rfl

/-- Reflexivity preserves the total identity arrow, including its dependent fiber. -/
theorem pathReflexivityMap_id (x : Total F) :
 pathReflexivityMap F (𝟙 x) = 𝟙 (pathReflexivityObj F x) := by
 apply Pseudofunctor.CoGrothendieck.ext
 · exact (diagonalTotal F).map_id x
 · dsimp only [pathReflexivityMap, identity, TwoGroupoidHom.arrow]
   have h := congrArg (fun (p : (diagonalTotal F).obj x ⟶ (diagonalTotal F).obj x) =>
     (openIdMap F p).obj (𝟙 x.fiber)) ((diagonalTotal F).map_id x)
   exact discrete_casts_heq _ (congrArg
     (fun H : (openIdHigher F).obj (pathReflexivityObj F x).base ⟶
       (openIdHigher F).obj (pathReflexivityObj F x).base => H.obj (pathReflexivityObj F x).fiber)
     ((openIdHigher F).map_id (pathReflexivityObj F x).base)) h
end SquareKit.Internal.PathTransport.TwoFamily
