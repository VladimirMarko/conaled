import SquareKit.Internal.PathTransport.TwoLocallyDiscreteUnderlying
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
universe uΓ vΓ wΓ u v
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {C : Type u} [Category.{v} C]
def locallyDiscreteTargetFunctor (F : StrictPseudofunctor Γ (LocallyDiscrete C)) : Γ ⥤ C where
 obj x := (F.obj x).as
 map f := (F.map f).as
 map_id x := congrArg Discrete.as (F.map_id x)
 map_comp f g := congrArg Discrete.as (F.map_comp f g)
def locallyDiscreteTargetComparison {F G : StrictPseudofunctor Γ (LocallyDiscrete C)}
 (β : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
 locallyDiscreteTargetFunctor F ⟶ locallyDiscreteTargetFunctor G where
 app x := (β.app x).as
 naturality _x _y f := congrArg Discrete.as (LocallyDiscrete.eq_of_hom (β.naturality f).hom)
end SquareKit.Internal.PathTransport
namespace SquareKit
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
theorem natural_component_from_root (F : C ⥤ D) (a : C)
 (η : (Functor.const C).obj (F.obj a) ⟶ F) (hη : η.app a = 𝟙 (F.obj a))
 {b : C} (p : a ⟶ b) : η.app b = F.map p := by
 have h := η.naturality p
 simpa [hη] using h
end SquareKit
