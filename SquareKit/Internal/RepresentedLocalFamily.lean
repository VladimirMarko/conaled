import SquareKit.Internal.RepresentableCoherentRecovery
import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-! Independent coherent local families over the represented-context diagram. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentedLocalFamily
open CategoryTheory CategoryTheory.Functor
open SquareKit.RepresentableClassification
universe u v w a b i j k l

/-- A pseudococone with ordinary category-valued components. Its unit and composition
laws concern local restriction, independently of any classifier or decoder. -/
structure LocalData {I : Type i} [Category.{j} I] (F : I ⥤ Cat.{k,l})
    (V : Type a) [Category.{b} V] where
  app (x : I) : F.obj x ⥤ V
  comparison {x y : I} (f : x ⟶ y) : (F.map f).toFunctor ⋙ app y ≅ app x
  comparison_id (x : I) : (comparison (𝟙 x)).hom =
    eqToHom (by rw [F.map_id]; rfl)
  comparison_comp {x y z : I} (f : x ⟶ y) (g : y ⟶ z) :
    (comparison (f ≫ g)).hom =
      eqToHom (by rw [F.map_comp]; rfl) ≫
        whiskerLeft (F.map f).toFunctor (comparison g).hom ≫ (comparison f).hom

namespace LocalData
variable {I : Type i} [Category.{j} I] {F : I ⥤ Cat.{k,l}}
variable {V : Type a} [Category.{b} V]

/-- Every compatible component map is retained; invertibility is not required. -/
@[ext] structure Hom (A B : LocalData F V) where
  app (x : I) : A.app x ⟶ B.app x
  naturality {x y : I} (f : x ⟶ y) :
    whiskerLeft (F.map f).toFunctor (app y) ≫ (B.comparison f).hom =
      (A.comparison f).hom ≫ app x

instance : Category (LocalData F V) where
  Hom := Hom
  id A := ⟨fun x => 𝟙 (A.app x), by intro x y f; simp⟩
  comp α β := ⟨fun x => α.app x ≫ β.app x, by
    intro x y f
    rw [whiskerLeft_comp, Category.assoc, β.naturality, ← Category.assoc,
      α.naturality, Category.assoc]⟩
  id_comp α := by ext x; exact Category.id_comp _
  comp_id α := by ext x; exact Category.comp_id _
  assoc α β γ := by ext x; exact Category.assoc _ _ _

@[simp] theorem id_app (A : LocalData F V) (x : I) : (𝟙 A : A ⟶ A).app x = 𝟙 _ := rfl
@[simp] theorem comp_app {A B C : LocalData F V} (f : A ⟶ B) (g : B ⟶ C) (x : I) :
    (f ≫ g).app x = f.app x ≫ g.app x := rfl

/-- Compatible component isomorphisms give an isomorphism of local families. -/
def isoMk {A B : LocalData F V} (e : ∀ x, A.app x ≅ B.app x)
    (h : ∀ {x y} (f : x ⟶ y),
      whiskerLeft (F.map f).toFunctor (e y).hom ≫ (B.comparison f).hom =
        (A.comparison f).hom ≫ (e x).hom) : A ≅ B where
  hom := ⟨fun x => (e x).hom, h⟩
  inv := ⟨fun x => (e x).inv, by
    intro x y f
    ext z
    have hh := NatTrans.congr_app (h f) z
    simp only [NatTrans.comp_app, whiskerLeft_app] at hh ⊢
    apply (cancel_epi ((e y).hom.app ((F.map f).toFunctor.obj z))).1
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      ← Category.assoc, hh, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]⟩
  hom_inv_id := by apply Hom.ext; funext x; exact (e x).hom_inv_id
  inv_hom_id := by apply Hom.ext; funext x; exact (e x).inv_hom_id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble local functors using Mathlib's contravariant Grothendieck category.
The supplied laws are exactly those needed for composition. -/
def toTotal {J : Type i} [Category.{j} J] {F : Jᵒᵖ ⥤ Cat.{k,l}}
    (A : LocalData F V) : Pseudofunctor.CoGrothendieck F.toPseudofunctor' ⥤ V where
  obj x := (A.app (Opposite.op x.base)).obj x.fiber
  map {x y} f := (A.app (Opposite.op x.base)).map f.fiber ≫
    (A.comparison f.base.op).hom.app y.fiber
  map_id x := by
    change (A.app (Opposite.op x.base)).map
      ((F.toPseudofunctor'.mapId ⟨Opposite.op x.base⟩).inv.toNatTrans.app x.fiber) ≫
      (A.comparison (𝟙 (Opposite.op x.base))).hom.app x.fiber = _
    simp only [comparison_id, Functor.toPseudofunctor'_mapId]
    simp [eqToHom_map, eqToHom_app]
  map_comp {x y z} f g := by
    change (A.app (Opposite.op x.base)).map
      (f.fiber ≫ (F.toPseudofunctor'.map f.base.op.toLoc).toFunctor.map g.fiber ≫
        (F.toPseudofunctor'.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app z.fiber) ≫
      (A.comparison (g.base.op ≫ f.base.op)).hom.app z.fiber = _
    simp only [comparison_comp, Functor.toPseudofunctor'_mapComp]
    simp [eqToHom_map, eqToHom_app, Category.assoc, ← NatTrans.naturality_assoc]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assembly retains compatible maps, not just local objects. -/
def totalFunctor {J : Type i} [Category.{j} J] (F : Jᵒᵖ ⥤ Cat.{k,l}) (V : Type a)
    [Category.{b} V] : LocalData F V ⥤ (Pseudofunctor.CoGrothendieck F.toPseudofunctor' ⥤ V) where
  obj := toTotal
  map {X Y} α :=
    { app := fun x => (α.app (Opposite.op x.base)).app x.fiber
      naturality := by
        intro x y f
        change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, ← NatTrans.comp_app, ← α.naturality f.base.op]
        simp only [NatTrans.comp_app, whiskerLeft_app]
        rw [← Category.assoc]
        have h := congrArg (fun k => k ≫ (Y.comparison f.base.op).hom.app y.fiber)
          ((α.app (Opposite.op x.base)).naturality f.fiber)
        simp only [Category.assoc] at h ⊢
        convert h using 1 <;> rfl }


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At common `Cat` universes this is exactly a Mathlib pseudonatural cocone.
The local-data/category equivalence itself does not impose these universe equalities. -/
def toStrongTrans (W : Type l) [Category.{k} W] (A : LocalData F W) :
    Pseudofunctor.StrongTrans F.toPseudofunctor'
      (((Functor.const I).obj (Cat.of W)).toPseudofunctor') where
  app x := (A.app x.as).toCatHom
  naturality f := Cat.Hom.isoMk (A.comparison f.as)
  naturality_naturality := by
    intro x y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext z
    simp [Functor.toPseudofunctor']
  naturality_id x := by
    apply Cat.Hom₂.ext
    ext z
    simp [Functor.toPseudofunctor', A.comparison_id, eqToHom_app]
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext z
    cases f; cases g
    simp [Functor.toPseudofunctor', A.comparison_comp, eqToHom_app]

open scoped Pseudofunctor.StrongTrans in
/-- Compatible local maps are Mathlib modifications, including noninvertible maps. -/
def toModification (W : Type l) [Category.{k} W] {A B : LocalData F W} (α : A ⟶ B) :
    Pseudofunctor.StrongTrans.Modification (toStrongTrans W A) (toStrongTrans W B) where
  app := fun x => (α.app x.as).toCatHom₂
  naturality := fun f => by
    apply Cat.Hom₂.ext
    exact α.naturality f.as

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Conversely, a Mathlib pseudonatural cocone supplies precisely the local laws. -/
def ofStrongTrans (W : Type l) [Category.{k} W]
    (A : Pseudofunctor.StrongTrans F.toPseudofunctor'
      (((Functor.const I).obj (Cat.of W)).toPseudofunctor')) : LocalData F W where
  app x := (A.app ⟨x⟩).toFunctor
  comparison f := Cat.Hom.toNatIso (A.naturality f.toLoc)
  comparison_id x := by
    have h := A.naturality_id ⟨x⟩
    apply NatTrans.ext
    funext z
    have hh := congrArg (fun t => t.toNatTrans.app z) h
    simpa [Functor.toPseudofunctor', Quiver.Hom.toLoc, eqToHom_app] using hh
  comparison_comp f g := by
    have h := A.naturality_comp f.toLoc g.toLoc
    apply NatTrans.ext
    funext z
    have hh := congrArg (fun t => t.toNatTrans.app z) h
    simpa [Functor.toPseudofunctor', Quiver.Hom.toLoc, eqToHom_app] using hh

@[simp] theorem ofStrongTrans_toStrongTrans (W : Type l) [Category.{k} W]
    (A : LocalData F W) : ofStrongTrans W (toStrongTrans W A) = A := rfl

@[simp] theorem toStrongTrans_ofStrongTrans (W : Type l) [Category.{k} W]
    (A : Pseudofunctor.StrongTrans F.toPseudofunctor'
      (((Functor.const I).obj (Cat.of W)).toPseudofunctor')) :
    toStrongTrans W (ofStrongTrans W A) = A := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Modifications recover all compatible maps, with no invertibility assumption. -/
def ofModification (W : Type l) [Category.{k} W] {A B : LocalData F W}
    (α : Pseudofunctor.StrongTrans.Modification (toStrongTrans W A) (toStrongTrans W B)) :
    A ⟶ B where
  app x := (α.app ⟨x⟩).toNatTrans
  naturality f := by
    have h := α.naturality f.toLoc
    exact congrArg Cat.Hom₂.toNatTrans h

@[simp] theorem ofModification_toModification (W : Type l) [Category.{k} W]
    {A B : LocalData F W} (α : A ⟶ B) :
    ofModification W (toModification W α) = α := rfl

@[simp] theorem toModification_ofModification (W : Type l) [Category.{k} W]
    {A B : LocalData F W}
    (α : Pseudofunctor.StrongTrans.Modification (toStrongTrans W A) (toStrongTrans W B)) :
    toModification W (ofModification W α) = α := rfl

@[simp] theorem toModification_id (W : Type l) [Category.{k} W] (A : LocalData F W) :
    toModification W (𝟙 A) = Pseudofunctor.StrongTrans.Modification.id (toStrongTrans W A) := rfl

@[simp] theorem toModification_comp (W : Type l) [Category.{k} W]
    {A B C : LocalData F W} (α : A ⟶ B) (β : B ⟶ C) :
    toModification W (α ≫ β) =
      Pseudofunctor.StrongTrans.Modification.vcomp (toModification W α) (toModification W β) := rfl

end LocalData

variable {C : Type v} [Category.{w} C]
/-- The actual representable element categories and restriction functors. -/
abbrev representedDiagram (Γ : Context.{u} C) : Γ.Elementsᵒᵖ ⥤ Cat :=
  (Functor.Elements.π Γ).leftOp ⋙ representables.{u} ⋙ Functor.elementsFunctor

/-- Represented local families are defined from their context diagram, not from `Code`. -/
abbrev Family (Γ : Context.{u} C) (V : Type a) [Category.{b} V] :=
  LocalData (representedDiagram.{u} Γ) V

/-- A local view of an arrow in the represented element coordinates. -/
def arrowView {Γ : Context.{u} C} (f : Arrow Γ.Elements) :
    (representable.{u} f.left.obj.unop).Elements :=
  { obj := f.right.obj, val := ⟨f.hom.hom.unop⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An arrow square decomposes into a map inside a represented context and a root restriction. -/
def arrowToTotal (Γ : Context.{u} C) : Arrow Γ.Elements ⥤
    Pseudofunctor.CoGrothendieck (representedDiagram.{u} Γ).toPseudofunctor' where
  obj f := ⟨f.left, by change (representable.{u} f.left.obj.unop).Elements; exact arrowView.{u} f⟩
  map {f g} s :=
    { base := s.left
      fiber := Functor.Elements.homMk s.right.hom (by
        apply ULift.ext
        change s.right.hom.unop ≫ f.hom.hom.unop = g.hom.hom.unop ≫ s.left.hom.unop
        exact congrArg (fun k => k.hom.unop) s.w.symm) }
  map_id f := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext
      (F := (representedDiagram.{u} Γ).toPseudofunctor') _ _ (by rfl) ?_
    apply Functor.Elements.hom_ext
    simp [Functor.toPseudofunctor', eqToHom_app]
    simp! [elements_eqToHom_hom, representedDiagram, arrowView]
  map_comp f g := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext
      (F := (representedDiagram.{u} Γ).toPseudofunctor') _ _ (by rfl) ?_
    apply Functor.Elements.hom_ext
    simp [Functor.toPseudofunctor', eqToHom_app]
    simp! [elements_eqToHom_hom, representedDiagram, arrowView]
    rfl

variable (V : Type a) [Category.{b} V]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble independent local data into the existing coherent arrow presentation. -/
def toCode (Γ : Context.{u} C) : Family Γ V ⥤
    SquareKit.CoherentFamilyClassification.Code Γ.Elements V where
  obj A := ⟨arrowToTotal Γ ⋙ A.toTotal, fun {f g} s hs => by
    have : IsIso s.right := hs
    have : IsIso s.right.hom := (Functor.Elements.π Γ).map_isIso s.right
    have : IsIso ((arrowToTotal Γ).map s).fiber := by
      let e : arrowView.{u} f ≅
          (representableMap s.left.hom.unop).mapElements.obj (arrowView.{u} g) :=
        Functor.Elements.isoMk (asIso s.right.hom) (((arrowToTotal Γ).map s).fiber.map_val)
      have he : ((arrowToTotal Γ).map s).fiber = e.hom := by
        apply Functor.Elements.hom_ext
        rfl
      rw [he]
      infer_instance
    change IsIso ((A.app (Opposite.op f.left)).map ((arrowToTotal Γ).map s).fiber ≫
      (A.comparison s.left.op).hom.app (arrowView g))
    have : IsIso ((A.app (Opposite.op f.left)).map ((arrowToTotal Γ).map s).fiber) :=
      (A.app (Opposite.op f.left)).map_isIso _
    infer_instance⟩
  map α := ObjectProperty.homMk (whiskerLeft (arrowToTotal Γ)
    ((LocalData.totalFunctor (representedDiagram.{u} Γ) V).map α))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict a coherent diagram to independently specified represented local data. -/
noncomputable def fromCode (Γ : Context.{u} C) :
    SquareKit.CoherentFamilyClassification.Code Γ.Elements V ⥤ Family Γ V where
  obj A :=
    { app := fun x => CoherentFamily.localArrow x.unop ⋙ A.obj
      comparison := fun f => CoherentFamily.localRestrictionIso V A f.unop
      comparison_id := by
        intro x
        ext z
        let e := congrArg ((CoherentFamily.localArrow x.unop).obj)
          (congrArg (fun H : (representedDiagram.{u} Γ).obj x ⟶ _ => H.toFunctor.obj z)
            ((representedDiagram.{u} Γ).map_id x))
        have h : (CoherentFamily.localRestriction (𝟙 x.unop)).app z = eqToHom e := by
          apply Arrow.hom_ext
          · simp [CoherentFamily.localRestriction, Arrow.eqToHom_left]
            rfl
          · simp [CoherentFamily.localRestriction, CoherentFamily.localTargetIso,
              eqToHom_app, Arrow.eqToHom_right]
        convert (congrArg A.obj.map h).trans (eqToHom_map A.obj e) using 1 <;>
          first | rfl | simp! only [eqToHom_app]
      comparison_comp := by
        intro x y z f g
        ext t
        let e := congrArg ((CoherentFamily.localArrow z.unop).obj)
          (congrArg (fun H : (representedDiagram.{u} Γ).obj x ⟶ _ => H.toFunctor.obj t)
            ((representedDiagram.{u} Γ).map_comp f g))
        have h : (CoherentFamily.localRestriction (g.unop ≫ f.unop)).app t =
            eqToHom e ≫
              (CoherentFamily.localRestriction g.unop).app
                (((representedDiagram.{u} Γ).map f).toFunctor.obj t) ≫
              (CoherentFamily.localRestriction f.unop).app t := by
          apply Arrow.hom_ext
          · simp [CoherentFamily.localRestriction, Arrow.eqToHom_left]
          · simp [CoherentFamily.localRestriction, CoherentFamily.localTargetIso,
              eqToHom_app, Arrow.eqToHom_right]
        have hh := congrArg A.obj.map h
        simp only [A.obj.map_comp, eqToHom_map] at hh
        convert hh using 1 <;>
          first | rfl | (simp! only [NatTrans.comp_app, whiskerLeft_app, eqToHom_app]; rfl) }

  map α :=
    { app := fun x => whiskerLeft (CoherentFamily.localArrow x.unop) α.hom
      naturality := by
        intro x y f
        ext z
        exact (α.hom.naturality ((CoherentFamily.localRestriction f.unop).app z)).symm }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assembly preserves the given maps inside each represented context. -/
theorem toCode_local_map {Γ : Context.{u} C} (A : Family Γ V) (x : Γ.Elements)
    {z t : (representable.{u} x.obj.unop).Elements} (f : z ⟶ t) :
    ((toCode V Γ).obj A).obj.map ((CoherentFamily.localArrow x).map f) =
      (A.app (Opposite.op x)).map f := by
  let e := congrArg (fun H : (representedDiagram.{u} Γ).obj (Opposite.op x) ⟶ _ =>
    H.toFunctor.obj t) ((representedDiagram.{u} Γ).map_id (Opposite.op x))
  have h : ((arrowToTotal Γ).map ((CoherentFamily.localArrow x).map f)).fiber ≫
      eqToHom e = f := by
    apply Functor.Elements.hom_ext
    simp! [arrowToTotal, elements_eqToHom_hom]
    rfl
  have hh := congrArg (A.app (Opposite.op x)).map h
  simp only [Functor.map_comp, eqToHom_map] at hh
  change _ ≫ (A.comparison (𝟙 (Opposite.op x))).hom.app t = _
  rw [A.comparison_id]
  simp only [eqToHom_app]
  convert hh using 1 <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assembly preserves the selected invertible restriction comparisons. -/
theorem toCode_restriction {Γ : Context.{u} C} (A : Family Γ V)
    {x y : Γ.Elements} (f : x ⟶ y) (z : (representable.{u} y.obj.unop).Elements) :
    ((toCode V Γ).obj A).obj.map ((CoherentFamily.localRestriction f).app z) =
      (A.comparison f.op).hom.app z := by
  have h : ((arrowToTotal Γ).map ((CoherentFamily.localRestriction f).app z)).fiber =
      𝟙 (((representedDiagram.{u} Γ).map f.op).toFunctor.obj z) := by
    apply Functor.Elements.hom_ext
    simp! [arrowToTotal, CoherentFamily.localRestriction, CoherentFamily.localTargetIso,
      eqToHom_app, elements_eqToHom_hom]
    rfl
  change (A.app (Opposite.op x)).map _ ≫ _ = _
  rw [h]
  change (A.app (Opposite.op x)).map (𝟙 _) ≫ (A.comparison f.op).hom.app z = _
  rw [Functor.map_id, Category.id_comp]

/-- Recover a local family through its assembled arrow diagram, including its comparisons. -/
noncomputable def localRecovery {Γ : Context.{u} C} (A : Family Γ V) :
    A ≅ (fromCode V Γ).obj ((toCode V Γ).obj A) :=
  LocalData.isoMk (fun x => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro z t f
    change (A.app x).map f ≫ 𝟙 _ =
      𝟙 _ ≫ ((toCode V Γ).obj A).obj.map ((CoherentFamily.localArrow x.unop).map f)
    rw [Category.comp_id, Category.id_comp]
    exact (toCode_local_map V A x.unop f).symm)) (by
      intro x y f
      ext z
      change 𝟙 _ ≫ ((toCode V Γ).obj A).obj.map ((CoherentFamily.localRestriction f.unop).app z) =
        (A.comparison f).hom.app z ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact toCode_restriction V A f.unop z)

/-- Local recovery is natural in every compatible component map. -/
noncomputable def localRecoveryIso (Γ : Context.{u} C) :
    𝟭 (Family Γ V) ≅ toCode V Γ ⋙ fromCode V Γ :=
  NatIso.ofComponents (localRecovery V) (by
    intro A B α
    apply LocalData.Hom.ext
    funext x
    apply NatTrans.ext
    funext z
    change (α.app x).app z ≫ 𝟙 _ = 𝟙 _ ≫ (α.app x).app z
    simp)

/-- Represented coordinates recover the actual target, using the element's action law. -/
def coordinateIso {Γ : Context.{u} C} (f : Arrow Γ.Elements) :
    (CoherentFamily.localArrow f.left).obj (arrowView.{u} f) ≅ f :=
  Arrow.isoMk (Iso.refl _) (Functor.Elements.isoMk (Iso.refl _) (by
    change Γ.map (𝟙 f.right.obj) (Γ.map f.hom.hom f.left.val) = f.right.val
    rw [Γ.map_id]
    exact f.hom.map_val)) (by
      apply Functor.Elements.hom_ext
      change 𝟙 _ ≫ f.hom.hom = f.hom.hom ≫ 𝟙 _
      simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The represented coordinate comparison preserves every arrow square. -/
theorem coordinateIso_naturality {Γ : Context.{u} C} {f g : Arrow Γ.Elements} (s : f ⟶ g) :
    (CoherentFamily.localArrow f.left).map ((arrowToTotal Γ).map s).fiber ≫
      (CoherentFamily.localRestriction s.left).app (arrowView g) ≫
      (coordinateIso g).hom = (coordinateIso f).hom ≫ s := by
  apply Arrow.hom_ext
  · simp [coordinateIso, CoherentFamily.localArrow, CoherentFamily.localRestriction]
  · apply Functor.Elements.hom_ext
    simp! [coordinateIso, CoherentFamily.localArrow, CoherentFamily.localRestriction,
      CoherentFamily.localTargetIso, eqToHom_app, elements_eqToHom_hom, arrowToTotal]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble the local views of a code and recover that code, including all squares. -/
noncomputable def codeRecovery {Γ : Context.{u} C}
    (A : SquareKit.CoherentFamilyClassification.Code Γ.Elements V) :
    (toCode V Γ).obj ((fromCode V Γ).obj A) ≅ A :=
  (SquareKit.CoherentFamilyClassification.Coherent Γ.Elements V).isoMk
    (NatIso.ofComponents (fun f => A.obj.mapIso (coordinateIso f)) (by
      intro f g s
      change (A.obj.map _ ≫ A.obj.map _) ≫ A.obj.map (coordinateIso g).hom =
        A.obj.map (coordinateIso f).hom ≫ A.obj.map s
      rw [← A.obj.map_comp, ← A.obj.map_comp, ← A.obj.map_comp]
      exact congrArg A.obj.map (by
        rw [Category.assoc]
        exact coordinateIso_naturality s)))

/-- Code recovery is natural in arbitrary code morphisms. -/
noncomputable def codeRecoveryIso (Γ : Context.{u} C) :
    fromCode V Γ ⋙ toCode V Γ ≅ 𝟭 (SquareKit.CoherentFamilyClassification.Code Γ.Elements V) :=
  NatIso.ofComponents (codeRecovery V) (by
    intro A B α
    apply ObjectProperty.hom_ext
    ext f
    exact (α.hom.naturality (coordinateIso f).hom).symm)

/-- The independently specified local data and coherent arrow diagrams are equivalent. -/
noncomputable def equivalence (Γ : Context.{u} C) :
    Family Γ V ≌ SquareKit.CoherentFamilyClassification.Code Γ.Elements V :=
  CategoryTheory.Equivalence.mk (toCode V Γ) (fromCode V Γ)
    (localRecoveryIso V Γ) (codeRecoveryIso V Γ)

/-- Context substitution acts directly on the roots and their compatible maps. -/
def reindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) : Family Γ V ⥤ Family Δ V where
  obj A :=
    { app := fun x => A.app (Opposite.op (σ.mapElements.obj x.unop))
      comparison := fun f => A.comparison (σ.mapElements.map f.unop).op
      comparison_id := fun x => A.comparison_id (Opposite.op (σ.mapElements.obj x.unop))
      comparison_comp := fun f g => A.comparison_comp
        (σ.mapElements.map f.unop).op (σ.mapElements.map g.unop).op }
  map α :=
    { app := fun x => α.app (Opposite.op (σ.mapElements.obj x.unop))
      naturality := fun f => α.naturality (σ.mapElements.map f.unop).op }

@[simp] theorem reindex_id (Γ : Context.{u} C) : reindex V (𝟙 Γ) = 𝟭 (Family Γ V) := rfl
@[simp] theorem reindex_comp {Γ Δ Θ : Context.{u} C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindex V (τ ≫ σ) = reindex V σ ⋙ reindex V τ := rfl

/-- The comparison respects context substitution on objects and all maps. -/
theorem toCode_reindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) :
    reindex V σ ⋙ toCode V Δ =
      toCode V Γ ⋙ SquareKit.CoherentFamilyClassification.reindex σ.mapElements := rfl

/-- The inverse comparison commutes with substitution up to the categorical
recovery isomorphisms; represented coordinates need not agree definitionally. -/
noncomputable def fromCodeReindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) :
    fromCode V Γ ⋙ reindex V σ ≅
      SquareKit.CoherentFamilyClassification.reindex σ.mapElements ⋙ fromCode V Δ :=
  isoWhiskerLeft (fromCode V Γ ⋙ reindex V σ) (localRecoveryIso V Δ) ≪≫
    isoWhiskerRight (isoWhiskerRight (codeRecoveryIso V Γ)
      (SquareKit.CoherentFamilyClassification.reindex σ.mapElements)) (fromCode V Δ)

/-- Context-indexed local families use their direct root substitution. -/
def diagrams : (Context.{u} C)ᵒᵖ ⥤ Cat where
  obj Γ := Cat.of (Family Γ.unop V)
  map σ := (reindex V σ.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison is a Mathlib pseudonatural transformation of context systems. -/
def comparison : Pseudofunctor.StrongTrans (diagrams (C := C) V).toPseudofunctor'
    (CoherentFamily.diagrams (C := C) V).toPseudofunctor' where
  app Γ := (toCode V Γ.as.unop).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro Γ Δ σ τ h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 σ := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    rfl
  naturality_id Γ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
  naturality_comp σ τ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

/-- Reuse the established pseudonatural decoder by composing the comparison. -/
def decoder : Pseudofunctor.StrongTrans (diagrams (C := C) V).toPseudofunctor'
    (CoherentFamily.system (C := C) V) :=
  Pseudofunctor.StrongTrans.vcomp (comparison V) (CoherentFamily.decoder V)

/-- The existing identity-view decoder, now accepting represented local input. -/
def decode (Γ : Context.{u} C) : Family Γ V ⥤ (Γ.Elements ⥤ V) :=
  toCode V Γ ⋙ SquareKit.CoherentFamilyClassification.decode Γ.Elements V

/-- Category-valued families are recovered through the existing classifier equivalence. -/
noncomputable def classification (Γ : Context.{u} C) : Family Γ V ≌ (Γ.Elements ⥤ V) :=
  (equivalence V Γ).trans (CoherentFamily.classification V Γ)

/-- The classifier's decoder is precisely the existing decoder after assembly. -/
theorem classification_functor (Γ : Context.{u} C) :
    (classification V Γ).functor = decode V Γ := rfl

/-- The unit combines local recovery with the established decoder recovery unit. -/
theorem classification_unit (Γ : Context.{u} C) (A : Family Γ V) :
    (classification V Γ).unitIso.hom.app A =
      (equivalence V Γ).unitIso.hom.app A ≫
        (fromCode V Γ).map ((CoherentFamily.classification V Γ).unitIso.hom.app
          ((toCode V Γ).obj A)) := by
  simp [classification, CategoryTheory.Equivalence.trans, equivalence]
  rfl

/-- The new counit is code recovery followed by the established decoder counit. -/
theorem classification_counit (Γ : Context.{u} C) (A : Γ.Elements ⥤ V) :
    (classification V Γ).counitIso.hom.app A =
      (SquareKit.CoherentFamilyClassification.decode Γ.Elements V).map
        ((codeRecovery V ((SquareKit.CoherentFamilyClassification.code Γ.Elements V).obj A)).hom) ≫
      (CoherentFamily.classification V Γ).counitIso.hom.app A := by
  simp [classification, CategoryTheory.Equivalence.trans, equivalence,
    codeRecoveryIso, CategoryTheory.Equivalence.mk]
  rfl

/-- Decoder comparison under arbitrary context substitution. -/
def decodeReindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) :
    reindex V σ ⋙ decode V Δ ≅ decode V Γ ⋙ (whiskeringLeft _ _ V).obj σ.mapElements :=
  isoWhiskerLeft (toCode V Γ) (SquareKit.CoherentFamilyClassification.decodeReindex σ.mapElements)

@[simp] theorem decodeReindex_id {Γ : Context.{u} C} (A : Family Γ V) :
    (decodeReindex V (𝟙 Γ)).hom.app A = 𝟙 _ :=
  SquareKit.CoherentFamilyClassification.decodeReindex_id ((toCode V Γ).obj A)

theorem decodeReindex_comp {Γ Δ Θ : Context.{u} C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (A : Family Γ V) (x : Θ.Elements) :
    ((decodeReindex V (τ ≫ σ)).hom.app A).app x =
      ((decodeReindex V τ).hom.app ((reindex V σ).obj A)).app x ≫
        ((decodeReindex V σ).hom.app A).app (τ.mapElements.obj x) :=
  SquareKit.CoherentFamilyClassification.decodeReindex_comp σ.mapElements τ.mapElements
    ((toCode V Γ).obj A) x

/-- The original decoder's recovery unit remains coherent after changing context. -/
theorem recovery_reindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) (A : Family Γ V)
    (f : Arrow Δ.Elements) :
    (SquareKit.CoherentFamilyClassification.recovery Δ.Elements V
      ((toCode V Δ).obj ((reindex V σ).obj A))).hom.app f ≫
        ((decodeReindex V σ).hom.app A).app f.right =
      (SquareKit.CoherentFamilyClassification.recovery Γ.Elements V
        ((toCode V Γ).obj A)).hom.app (σ.mapElements.mapArrow.obj f) :=
  SquareKit.CoherentFamilyClassification.recovery_reindex σ.mapElements ((toCode V Γ).obj A) f

/-- Local round-trip recovery is unchanged by substitution at every local component. -/
theorem localRecovery_reindex {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) (A : Family Γ V)
    (x : Δ.Elements) (z : (representable.{u} x.obj.unop).Elements) :
    ((localRecovery V ((reindex V σ).obj A)).hom.app (Opposite.op x)).app z =
      ((localRecovery V A).hom.app (Opposite.op (σ.mapElements.obj x))).app z := rfl

end SquareKit.RepresentedLocalFamily
