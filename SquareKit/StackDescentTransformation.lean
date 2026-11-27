import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-! Strong transformations act on descent data and their compatible maps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.StackDescentTransformation
open CategoryTheory Opposite Bicategory
open Pseudofunctor.LocallyDiscreteOpToCat
universe u v u₁ v₁ t t'
variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
  {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
variable (η : Pseudofunctor.StrongTrans F G)

abbrev component (X : C) := (η.app (.mk (op X))).toFunctor
abbrev comparison {X Y : C} (f : Y ⟶ X) := Cat.Hom.toNatIso (η.naturality f.op.toLoc)

/-- Transport of an arrow between restricted objects, retaining both restriction comparisons. -/
def mapHom {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.obj ((component η X₁).obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((component η X₂).obj M₂) :=
  (comparison η f₁).inv.app M₁ ≫ (component η Y).map h ≫ (comparison η f₂).hom.app M₂

@[simp] theorem mapHom_id {X Y : C} (f : Y ⟶ X) (M : F.obj (.mk (op X))) :
    mapHom η f f (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) = 𝟙 _ := by
  simp [mapHom]

@[reassoc] theorem mapHom_comp {X₁ X₂ X₃ Y : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (f₃ : Y ⟶ X₃)
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (k : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) :
    mapHom η f₁ f₂ h ≫ mapHom η f₂ f₃ k = mapHom η f₁ f₃ (h ≫ k) := by
  simp [mapHom, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting an arrow commutes with its image under a strong transformation. -/
theorem mapHom_pullHom {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    mapHom η gf₁ gf₂ (pullHom h g gf₁ gf₂ hgf₁ hgf₂) =
      pullHom (mapHom η f₁ f₂ h) g gf₁ gf₂ hgf₁ hgf₂ := by
  subst gf₁ gf₂
  simp only [mapHom, pullHom, op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp,
    Functor.map_comp, Category.assoc]
  simp only [comparison, component, op_comp, Quiver.Hom.comp_toLoc, Cat.Hom.toNatIso_inv, Cat.Hom.toNatIso_hom]
  rw [η.naturality_comp_inv_app, η.naturality_comp_hom_app]
  simp only [Category.assoc]
  simp only [← Functor.map_comp_assoc, ← reassoc_of% Cat.Hom₂.comp_app,
    ← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app, Category.id_comp]
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := (η.naturality g.op.toLoc).hom.toNatTrans.naturality h
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The image of descent data under a strong transformation. -/
def mapObj (D : F.DescentData f) : G.DescentData f where
  obj i := (component η (X i)).obj (D.obj i)
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := mapHom η f₁ f₂ (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [← mapHom_pullHom η f₁ f₂ _ g gf₁ gf₂ hgf₁ hgf₂,
      D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self _ q _ g hg := by rw [D.hom_self q g hg, mapHom_id]
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [mapHom_comp, D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]

/-- Strong transformations preserve every compatible arrow of descent data. -/
def mapMap {D E : F.DescentData f} (h : D ⟶ E) : mapObj η f D ⟶ mapObj η f E where
  hom i := (component η (X i)).map (h.hom i)
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    dsimp [mapObj, mapHom]
    have hn₁ := (comparison η f₁).inv.naturality (h.hom i₁)
    have hn₂ := (comparison η f₂).hom.naturality (h.hom i₂)
    dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hn₁ hn₂
    simp only [Category.assoc]
    rw [reassoc_of% hn₁, ← Functor.map_comp_assoc, h.comm q f₁ f₂ hf₁ hf₂,
      Functor.map_comp_assoc, hn₂]

/-- The functor on descent categories induced by a strong transformation. -/
def map : F.DescentData f ⥤ G.DescentData f where
  obj := mapObj η f
  map := mapMap η f
  map_id D := by ext i; exact (component η (X i)).map_id (D.obj i)
  map_comp h k := by ext i; exact (component η (X i)).map_comp (h.hom i) (k.hom i)

/-- Naturality compares composition constraints with composite restriction. -/
theorem comparison_comp_hom {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (c : W ⟶ U) (hc : b ≫ a = c) (M : F.obj (.mk (op U))) :
    (comparison η c).hom.app M ≫
      (G.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc (by grind)).hom.toNatTrans.app
        ((component η U).obj M) =
    (component η W).map
        ((F.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc (by grind)).hom.toNatTrans.app M) ≫
      (comparison η b).hom.app ((F.map a.op.toLoc).toFunctor.obj M) ≫
        (G.map b.op.toLoc).toFunctor.map ((comparison η a).hom.app M) := by
  subst c
  simp only [comparison, component, op_comp, Quiver.Hom.comp_toLoc,
    Pseudofunctor.mapComp'_eq_mapComp, Cat.Hom.toNatIso_hom]
  rw [η.naturality_comp_hom_app]
  simp

/-- The naturality comparison on canonical descent objects. -/
def canonicalObjIso (M : F.obj (.mk (op S))) :
    (map η f).obj ((F.toDescentData f).obj M) ≅
      (G.toDescentData f).obj ((component η S).obj M) :=
  Pseudofunctor.DescentData.isoMk (fun i => (comparison η (f i)).app M) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp [map, mapObj, mapHom, Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
    have h₁ := comparison_comp_hom η (f i₁) f₁ q hf₁ M
    have h₂ := comparison_comp_hom η (f i₂) f₂ q hf₂ M
    rw [← cancel_epi ((comparison η f₁).hom.app _)]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
    rw [← cancel_epi ((component η Y).map
      ((F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app M))]
    rw [← reassoc_of% h₁]
    simpa only [← Functor.map_comp_assoc, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
      Iso.hom_inv_id_app_assoc] using h₂)

/-- Strong transformation and canonical descent commute up to natural isomorphism. -/
def canonicalIso : F.toDescentData f ⋙ map η f ≅ component η S ⋙ G.toDescentData f :=
  NatIso.ofComponents (canonicalObjIso η f) (by
    intro M N h
    ext i
    exact (comparison η (f i)).hom.naturality h)

section Modifications
variable {η θ : Pseudofunctor.StrongTrans F G}
variable (Γ : Pseudofunctor.StrongTrans.Modification η θ)

/-- The component equation of a modification, expressed in the fiber categories. -/
theorem modification_naturality {U V : C} (a : V ⟶ U) (M : F.obj (.mk (op U))) :
    (Γ.app (.mk (op V))).toNatTrans.app ((F.map a.op.toLoc).toFunctor.obj M) ≫
        (comparison θ a).hom.app M =
      (comparison η a).hom.app M ≫
        (G.map a.op.toLoc).toFunctor.map ((Γ.app (.mk (op U))).toNatTrans.app M) := by
  have h := congrArg (fun k => k.toNatTrans.app M) (Γ.naturality a.op.toLoc)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, comparison, Cat.Hom.toNatIso_hom] using h

/-- The inverse naturality comparison also retains modifications. -/
theorem modification_naturality_inv {U V : C} (a : V ⟶ U) (M : F.obj (.mk (op U))) :
    (G.map a.op.toLoc).toFunctor.map ((Γ.app (.mk (op U))).toNatTrans.app M) ≫
        (comparison θ a).inv.app M =
      (comparison η a).inv.app M ≫
        (Γ.app (.mk (op V))).toNatTrans.app ((F.map a.op.toLoc).toFunctor.obj M) := by
  rw [← cancel_epi ((comparison η a).hom.app M)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% modification_naturality Γ a M]
  simp

/-- A modification gives a compatible map between the images of every descent datum. -/
def modificationMap (D : F.DescentData f) : (map η f).obj D ⟶ (map θ f).obj D where
  hom i := (Γ.app (.mk (op (X i)))).toNatTrans.app (D.obj i)
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    dsimp [map, mapObj, mapHom]
    simp only [Category.assoc]
    rw [reassoc_of% modification_naturality_inv Γ f₁ (D.obj i₁)]
    rw [← (Γ.app (.mk (op Y))).toNatTrans.naturality_assoc]
    rw [modification_naturality Γ f₂ (D.obj i₂)]

/-- The action on modifications is a natural transformation of descent functors. -/
def mapModification : map η f ⟶ map θ f where
  app := modificationMap f Γ
  naturality {D E} h := by
    ext i
    exact (Γ.app (.mk (op (X i)))).toNatTrans.naturality (h.hom i)

end Modifications

open scoped Pseudofunctor.StrongTrans
local instance : Category (Pseudofunctor.StrongTrans F G) :=
  Pseudofunctor.StrongTrans.homCategory

/-- Descent is functorial on strong transformations and modifications. -/
def transformationFunctor : Pseudofunctor.StrongTrans F G ⥤ (F.DescentData f ⥤ G.DescentData f) where
  obj η := map η f
  map Γ := mapModification f Γ.as
  map_id η := by ext D i; rfl
  map_comp Γ Δ := by ext D i; rfl

section Refinement
variable {ι' : Type t'} {S' : C} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}
  {p : S' ⟶ S} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
  (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transformation and refinement commute on each descent datum. -/
def pullObjIso (D : F.DescentData f) :
    (Pseudofunctor.DescentData.pullFunctor F w ⋙ map η f').obj D ≅
      (map η f ⋙ Pseudofunctor.DescentData.pullFunctor G w).obj D :=
  Pseudofunctor.DescentData.isoMk (fun j => (comparison η (p' j)).app (D.obj (α j))) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp [Pseudofunctor.DescentData.pullFunctor, Pseudofunctor.DescentData.pullFunctorObj,
      Pseudofunctor.DescentData.pullFunctorObjHom, map, mapObj, mapHom]
    have h₁ := comparison_comp_hom η (p' j₁) f₁ (f₁ ≫ p' j₁) rfl (D.obj (α j₁))
    have h₂ := comparison_comp_hom η (p' j₂) f₂ (f₂ ≫ p' j₂) rfl (D.obj (α j₂))
    simp only [op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp] at h₁ h₂
    rw [← cancel_epi ((comparison η f₁).hom.app _)]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
    rw [← cancel_epi ((component η Y).map
      ((F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).hom.toNatTrans.app (D.obj (α j₁))))]
    rw [← reassoc_of% h₁]
    simp only [← Functor.map_comp_assoc, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv, Iso.hom_inv_id_app_assoc]
    have he := congrArg (fun k => (component η Y).map
        (D.hom (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by simp [w, reassoc_of% hf₁]) (by simp [w, reassoc_of% hf₂])) ≫ k) h₂
    simpa only [reassoc_of% hf₁, ← Cat.Hom.toNatIso_hom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc] using he)


/-- Strong transformations commute with arbitrary base change and cover refinement. -/
def pullIso : Pseudofunctor.DescentData.pullFunctor F w ⋙ map η f' ≅
    map η f ⋙ Pseudofunctor.DescentData.pullFunctor G w :=
  NatIso.ofComponents (pullObjIso η f w) (by
    intro D E h
    ext j
    exact (comparison η (p' j)).hom.naturality (h.hom (α j)))

end Refinement

section Composition
variable {H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
variable (θ : Pseudofunctor.StrongTrans G H)

/-- Naturality of a composite transformation, on objects. -/
theorem comparison_vcomp_hom {U V : C} (a : V ⟶ U) (M : F.obj (.mk (op U))) :
    (comparison (Pseudofunctor.StrongTrans.vcomp η θ) a).hom.app M =
      (component θ V).map ((comparison η a).hom.app M) ≫
        (comparison θ a).hom.app ((component η U).obj M) := by
  dsimp [comparison, component, Pseudofunctor.StrongTrans.vcomp,
    Pseudofunctor.StrongTrans.mkOfOplax, Pseudofunctor.StrongTrans.toOplax,
    Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp]
  simp

/-- The inverse comparison of a composite transformation, on objects. -/
theorem comparison_vcomp_inv {U V : C} (a : V ⟶ U) (M : F.obj (.mk (op U))) :
    (comparison (Pseudofunctor.StrongTrans.vcomp η θ) a).inv.app M =
      (comparison θ a).inv.app ((component η U).obj M) ≫
        (component θ V).map ((comparison η a).inv.app M) := by
  dsimp [comparison, component, Pseudofunctor.StrongTrans.vcomp,
    Pseudofunctor.StrongTrans.mkOfOplax, Pseudofunctor.StrongTrans.toOplax,
    Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp]
  simp

/-- Composition of strong transformations agrees with successive action on descent. -/
def mapCompObjIso (D : F.DescentData f) :
    (map (Pseudofunctor.StrongTrans.vcomp η θ) f).obj D ≅ ((map η f) ⋙ (map θ f)).obj D :=
  Pseudofunctor.DescentData.isoMk (fun _ => Iso.refl _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp [map, mapObj, mapHom, comparison, component,
      Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
      Pseudofunctor.StrongTrans.toOplax, Oplax.StrongTrans.vcomp,
      Oplax.StrongTrans.mkOfOplax, Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp]
    simp)

/-- The composition comparison is natural in every compatible descent arrow. -/
def mapCompIso : map (Pseudofunctor.StrongTrans.vcomp η θ) f ≅ map η f ⋙ map θ f :=
  NatIso.ofComponents (mapCompObjIso η f θ) (by
    intro D E h
    ext i
    change (component θ (X i)).map ((component η (X i)).map (h.hom i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (component θ (X i)).map ((component η (X i)).map (h.hom i))
    simp)

end Composition

end SquareKit.StackDescentTransformation
