import SquareKit.Internal.PathTransport.TwoStrongComposition
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
universe u v
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
def locallyDiscreteUnderlying (F : StrictPseudofunctor (LocallyDiscrete C) (LocallyDiscrete D)) : C ⥤ D where
 obj x := (F.obj ⟨x⟩).as
 map f := (F.map ⟨f⟩).as
 map_id x := congrArg Discrete.as (F.map_id ⟨x⟩)
 map_comp f g := congrArg Discrete.as (F.map_comp ⟨f⟩ ⟨g⟩)
def locallyDiscreteComparison {F G : StrictPseudofunctor (LocallyDiscrete C) (LocallyDiscrete D)}
 (β : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
 locallyDiscreteUnderlying F ⟶ locallyDiscreteUnderlying G where
 app x := (β.app ⟨x⟩).as
 naturality x y f := congrArg Discrete.as (LocallyDiscrete.eq_of_hom (β.naturality ⟨f⟩).hom)
end SquareKit.Internal.PathTransport
