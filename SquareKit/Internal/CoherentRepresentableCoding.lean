import SquareKit.Internal.RepresentableClassification
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-! Representable restriction of category-valued data with coherent composition. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification
open CategoryTheory
universe u v w a b
variable {C : Type v} [Category.{w} C]

/-- Representables and their actual restriction maps form a functor. -/
def representables : C ⥤ Context.{u} C where
  obj := representable
  map := representableMap
  map_id I := by
    ext J x
    exact congrArg ULift.up (Category.comp_id x.down)
  map_comp f g := by
    ext J x
    exact congrArg ULift.up (Category.assoc x.down f g).symm

/-- Coherent data restricts to codes valued in categories, preserving its
identity/composition isomorphisms and their coherence. -/
def coherentCodes (S : Pseudofunctor (LocallyDiscrete (Context.{u} C)ᵒᵖ) Cat.{a,b}) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b} :=
  representables.op.toPseudofunctor.comp S

/-- The coding restriction comparison is derived from primitive pseudofunctor
composition and represented restriction, not supplied as a final comparison. -/
def coherentCodeRestriction (S : Pseudofunctor (LocallyDiscrete (Context.{u} C)ᵒᵖ) Cat.{a,b})
    {Γ : Context.{u} C} {x y : Γ.Elements} (f : x ⟶ y) :
    S.map (represented y).op.toLoc ≅
      S.map (represented x).op.toLoc ≫ S.map (representableMap f.hom.unop).op.toLoc :=
  S.mapComp' (represented x).op.toLoc (representableMap f.hom.unop).op.toLoc
    (represented y).op.toLoc (by
      apply Discrete.ext
      exact congrArg Quiver.Hom.op (represented_restrict f))

/-- Strict data is an ordinary contravariant functor on contexts. -/
def System.dataFunctor (S : System.{u} C) : (Context.{u} C)ᵒᵖ ⥤ Type (max v (u+1) (w+1)) where
  obj Γ := S.Data Γ.unop
  map f := TypeCat.ofHom (fun A => S.restrict A f.unop)
  map_id Γ := by
    apply ConcreteCategory.hom_ext
    exact S.restrict_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro A
    exact (S.restrict_comp A f.unop g.unop).symm

/-- Restricting strict data to representables recovers the entire original code presheaf. -/
theorem System.data_codes (S : System.{u} C) : representables.op ⋙ S.dataFunctor = S.codes := rfl

/-- The strict interface embeds in the coherent interface using discrete data categories. -/
def System.discreteCoherent (S : System.{u} C) :
    Pseudofunctor (LocallyDiscrete (Context.{u} C)ᵒᵖ) Cat :=
  (S.dataFunctor ⋙ typeToCat).toPseudofunctor'

theorem System.coherent_codes_obj (S : System.{u} C) (I : Cᵒᵖ) :
    (coherentCodes S.discreteCoherent).obj ⟨I⟩ = Cat.of (Discrete (S.codes.obj I)) := rfl

end SquareKit.RepresentableClassification
