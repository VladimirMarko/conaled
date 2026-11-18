import SquareKit.Internal.RepresentableClassification
import SquareKit.Internal.Cubical.CubeProductFunctor

/-! Lifted represented contexts and their generalized-element maps. -/
open CategoryTheory
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
universe u
def representable (I : Cube) : Context.{u} :=
  RepresentableClassification.representable I

def represented {Γ : Context.{u}} (x : Γ.Elements) : representable x.obj.unop ⟶ Γ :=
  RepresentableClassification.represented x

/-- Restriction of a represented context along a cube map. -/
def representableMap {I J : Cube} (f : J ⟶ I) : representable J ⟶ representable I :=
  RepresentableClassification.representableMap f

@[simp] theorem represented_id {Γ : Context.{u}} (x : Γ.Elements) :
    (represented x).app x.obj ⟨𝟙 x.obj.unop⟩ = x.val :=
  RepresentableClassification.represented_id x

/-- The generic generalized element of a represented context. -/
def representableGeneric (I : Cube) : (representable.{u} I).Elements :=
  RepresentableClassification.representableGeneric I

@[simp] theorem represented_restrict {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y) :
    representableMap f.hom.unop ≫ represented x = represented y :=
  RepresentableClassification.represented_restrict f

theorem represented_naturality {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    represented (σ.mapElements.obj x) = represented x ≫ σ :=
  RepresentableClassification.represented_naturality σ x

theorem represented_generic_source {Γ : Context.{u}} (x : Γ.Elements) :
    (represented x).mapElements.obj (representableGeneric x.obj.unop) = x :=
  RepresentableClassification.represented_generic_source x

theorem elements_eqToHom_hom {Γ : Context.{u}} {x y : Γ.Elements} (e : x = y) :
    (eqToHom e : x ⟶ y).hom = eqToHom (congrArg (fun z : Γ.Elements => z.obj) e) :=
  RepresentableClassification.elements_eqToHom_hom e

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def representableIntervalHom (I : Cube) : total (interval (representable.{u} I)) ⟶ representable (Cube.extend I) where
  app J := TypeCat.ofHom (fun x => ⟨Cube.pair x.1.down x.2.down⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (Cube.comp_pair f.unop x.1.down x.2.down).symm

def representableIntervalInv (I : Cube) : representable (Cube.extend I) ⟶ total (interval (representable.{u} I)) where
  app J := TypeCat.ofHom (fun x => ⟨⟨x.down ≫ Cube.drop I⟩,⟨x.down ≫ Cube.fresh I⟩⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Sigma.ext
    · exact congrArg ULift.up (Category.assoc f.unop x.down (Cube.drop I))
    · exact heq_of_eq (congrArg ULift.up (Category.assoc f.unop x.down (Cube.fresh I)))

def representableIntervalIso (I : Cube) : total (interval (representable.{u} I)) ≅ representable (Cube.extend I) where
  hom := representableIntervalHom I
  inv := representableIntervalInv I
  hom_inv_id := by
    ext J x
    apply Sigma.ext
    · exact congrArg ULift.up (Cube.pair_drop x.1.down x.2.down)
    · exact heq_of_eq (congrArg ULift.up (Cube.pair_fresh x.1.down x.2.down))
  inv_hom_id := by
    ext J x
    apply congrArg ULift.up
    exact (Cube.comp_pair x.down (Cube.drop I) (Cube.fresh I)).symm.trans
      (by rw [Cube.pair_eta]; exact Category.comp_id x.down)

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem represented_generic_identity (I : Cube) :
    represented (representableGeneric.{u} I) = 𝟙 (representable.{u} I) :=
  RepresentableClassification.represented_generic_identity I

theorem represented_map_generic {Γ : Context.{u}} {I : Cube} (σ : representable.{u} I ⟶ Γ) :
    represented (σ.mapElements.obj (representableGeneric I)) = σ :=
  RepresentableClassification.represented_map_generic σ

end SquareKit.Cubical.Presheaf
