import SquareKit.Internal.Cubical.CubeProductFunctor

/-! Lifted represented contexts and their generalized-element maps. -/
open CategoryTheory
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
universe u
def representable (I : Cube) : Context.{u} where
  obj J := ULift.{u} (J.unop ⟶ I)
  map f := TypeCat.ofHom (fun g => ⟨f.unop ≫ g.down⟩)
  map_id J := by
    apply ConcreteCategory.hom_ext
    intro g
    exact congrArg ULift.up (Category.id_comp g.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact congrArg ULift.up (Category.assoc g.unop f.unop h.down)
def represented {Γ : Context.{u}} (x : Γ.Elements) : representable x.obj.unop ⟶ Γ where
  app J := TypeCat.ofHom (fun f => Γ.map f.down.op x.val)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro g
    exact ConcreteCategory.congr_hom (Γ.map_comp g.down.op f) x.val

/-- Restriction of a represented context along a cube map. -/
def representableMap {I J : Cube} (f : J ⟶ I) : representable J ⟶ representable I where
  app K := TypeCat.ofHom (fun g => ⟨g.down ≫ f⟩)
  naturality K L g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact congrArg ULift.up (Category.assoc g.unop h.down f)

@[simp] theorem represented_id {Γ : Context.{u}} (x : Γ.Elements) :
    (represented x).app x.obj ⟨𝟙 x.obj.unop⟩ = x.val := by
  exact ConcreteCategory.congr_hom (Γ.map_id x.obj) x.val

/-- The generic generalized element of a represented context. -/
def representableGeneric (I : Cube) : (representable.{u} I).Elements :=
  (representable I).elementsMk (Opposite.op I) ⟨𝟙 I⟩

@[simp] theorem represented_restrict {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y) :
    representableMap f.hom.unop ≫ represented x = represented y := by
  ext K g
  change Γ.map (g.down ≫ f.hom.unop).op x.val = Γ.map g.down.op y.val
  exact (ConcreteCategory.congr_hom (Γ.map_comp f.hom g.down.op) x.val).trans
    (congrArg (fun z => Γ.map g.down.op z) f.map_val)

theorem represented_naturality {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    represented (σ.mapElements.obj x) = represented x ≫ σ := by
  ext J f
  exact (ConcreteCategory.congr_hom (σ.naturality f.down.op) x.val).symm

theorem represented_generic_source {Γ : Context.{u}} (x : Γ.Elements) :
    (represented x).mapElements.obj (representableGeneric x.obj.unop) = x :=
  Functor.Elements.ext _ _ rfl
    ((ConcreteCategory.congr_hom (Γ.map_id x.obj) _).trans (represented_id x))

theorem elements_eqToHom_hom {Γ : Context.{u}} {x y : Γ.Elements} (e : x = y) :
    (eqToHom e : x ⟶ y).hom = eqToHom (congrArg (fun z : Γ.Elements => z.obj) e) := by
  cases e
  rfl

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
    represented (representableGeneric.{u} I) = 𝟙 (representable.{u} I) := by
  ext J f
  exact congrArg ULift.up (Category.comp_id f.down)

theorem represented_map_generic {Γ : Context.{u}} {I : Cube} (σ : representable.{u} I ⟶ Γ) :
    represented (σ.mapElements.obj (representableGeneric I)) = σ := by
  exact (represented_naturality σ (representableGeneric I)).trans
    ((congrArg (fun τ => τ ≫ σ) (represented_generic_identity I)).trans (Category.id_comp σ))

end SquareKit.Cubical.Presheaf
