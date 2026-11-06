import Mathlib.CategoryTheory.Grothendieck
import SquareKit.Internal.PathTransport.StrictTwoCategory
import SquareKit.Internal.PathTransport.TwoGroupoidHom

/-! Higher families with strict transport. The family target retains strict
transformations as its 2-cells. The extension hom-categories retain the
additional fiber 2-cell in their Grothendieck boundary. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]

/-- Structural family data includes horizontal action, but no eliminator law. -/
abbrev Family (Γ : Type u) [Bicategory.{w,v} Γ] :=
  StrictPseudofunctor Γ StrictTwoCategory.{u',v',w'}

/-- Evaluate the full base hom action at the selected source fiber object. -/
def evaluation (F : Family Γ) {x y : Γ} (a : F.obj x) :
    (x ⟶ y) ⥤ F.obj y := F.mapFunctor x y ⋙ StrictTwoTransformation.evaluation a

/-- Objects of context extension retain the base object and dependent fiber object. -/
structure Total (F : Family Γ) where
  base : Γ
  fiber : F.obj base

/-- Each total hom is the previously constructed category of pairs `(f,u)`
and cells `(α,ρ)`, with `ρ : u ⇒ F(α)(a) ≫ v`. -/
abbrev Hom (F : Family Γ) (x y : Total F) :=
  TwoGroupoidHom.Total (evaluation F (y := y.base) x.fiber) y.fiber

instance (F : Family Γ) (x y : Total F) : Category (Hom F x y) := inferInstance

/-- Identity uses strict preservation of the base identity to type its fiber arrow. -/
def identity (F : Family Γ) (x : Total F) : Hom F x x :=
  TwoGroupoidHom.arrow (evaluation F x.fiber) x.fiber (𝟙 x.base)
    (eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj x.base => H.obj x.fiber)
      (F.map_id x.base)))

/-- Composition applies the later transport to the earlier fiber arrow. -/
def compose (F : Family Γ) {x y z : Total F} (p : Hom F x y) (q : Hom F y z) :
    Hom F x z :=
  TwoGroupoidHom.arrow (evaluation F x.fiber) z.fiber (p.base ≫ q.base)
    (eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj z.base => H.obj x.fiber)
      (F.map_comp p.base q.base)) ≫ (F.map q.base).map p.fiber ≫ q.fiber)

/-- Reindexing evaluates the original family on the supplied strict functor. -/
def reindex {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) (F : Family Γ) : Family Δ := σ.comp F

/-- Reindexing a hom-category preserves its genuine fiber cell. -/
def reindexHom {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) (F : Family Γ) (x y : Total (reindex σ F)) :
    Hom (reindex σ F) x y ⥤
      Hom F ⟨σ.obj x.base, x.fiber⟩ ⟨σ.obj y.base, y.fiber⟩ :=
  TwoGroupoidHom.reindex (σ.mapFunctor x.base y.base)
    (evaluation F x.fiber) y.fiber

/-- Forgetting fiber 2-cells supplies an ordinary family only for proving
laws of total 1-arrows. The extension hom-categories above remain intact. -/
def underlying (F : Family Γ) : Γ ⥤ Cat where
  obj x := Cat.of (F.obj x)
  map f := (F.map f).toFunctor.toCatHom
  map_id x := by
    rw [F.map_id]
    rfl
  map_comp f g := by
    rw [F.map_comp]
    rfl

def toUnderlying (F : Family Γ) (x : Total F) : Grothendieck (underlying F) :=
  ⟨x.base, x.fiber⟩

def toUnderlyingHom (F : Family Γ) {x y : Total F} (p : Hom F x y) :
    toUnderlying F x ⟶ toUnderlying F y := ⟨p.base, p.fiber⟩

def fromUnderlyingHom (F : Family Γ) {x y : Total F}
    (p : toUnderlying F x ⟶ toUnderlying F y) : Hom F x y := ⟨p.base, p.fiber⟩

theorem toUnderlyingHom_injective (F : Family Γ) {x y : Total F} :
    Function.Injective (toUnderlyingHom F (x := x) (y := y)) := by
  intro p q h
  exact congrArg (fromUnderlyingHom F) h

/-- The identity and composition of total 1-arrows form a category. This
uses the ordinary Grothendieck construction only to derive its laws. -/
instance totalCategory (F : Family Γ) : Category (Total F) where
  Hom := Hom F
  id := identity F
  comp := compose F
  id_comp p := toUnderlyingHom_injective F (Category.id_comp (toUnderlyingHom F p))
  comp_id p := toUnderlyingHom_injective F (Category.comp_id (toUnderlyingHom F p))
  assoc p q r := toUnderlyingHom_injective F
    (Category.assoc (toUnderlyingHom F p) (toUnderlyingHom F q) (toUnderlyingHom F r))

/-- The object boundary introduced by composition of base transports. -/
def compBoundary (F : Family Γ) {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z)
    (a : F.obj x) : (F.map (f ≫ g)).obj a ⟶ (F.map g).obj ((F.map f).obj a) :=
  eqToHom (congrArg (fun H : F.obj x ⟶ F.obj z => H.obj a) (F.map_comp f g))

/-- Horizontal action on a base cell has its exact typed object boundary. -/
theorem action_whiskerRight (F : Family Γ) {x y z : Γ} {f f' : x ⟶ y}
    (α : f ⟶ f') (g : y ⟶ z) (a : F.obj x) :
    (F.map₂ (α ▷ g)).app a = compBoundary F f g a ≫
      (F.map g).map ((F.map₂ α).app a) ≫
      eqToHom (congrArg (fun H : F.obj x ⟶ F.obj z => H.obj a)
        (F.map_comp f' g)).symm := by
  have h := congrArg (fun η => η.app a) (F.map₂_whisker_right α g)
  rw [F.mapComp_eq_eqToIso, F.mapComp_eq_eqToIso] at h
  repeat rw [StrictTwoTransformation.Trans.comp_app] at h
  simp only [eqToIso.hom, eqToIso.inv] at h
  repeat rw [StrictTwoTransformation.Trans.eqToHom_app] at h
  exact h

/-- Right whiskering transports the genuine fiber 2-cell along the later
base arrow, then composes with its fiber arrow. -/
def whiskerRight (F : Family Γ) {x y z : Total F} {p p' : Hom F x y}
    (α : p ⟶ p') (q : Hom F y z) : compose F p q ⟶ compose F p' q :=
  TwoGroupoidHom.cell (α.base ▷ q.base) (
    eqToHom (Category.assoc (compBoundary F p.base q.base x.fiber)
      ((F.map q.base).map p.fiber) q.fiber).symm ≫
    (compBoundary F p.base q.base x.fiber ◁ (F.map q.base).map₂ α.fiber) ▷ q.fiber ≫
    eqToHom (by
      change (compBoundary F p.base q.base x.fiber ≫
        (F.map q.base).map ((F.map₂ α.base).app x.fiber ≫ p'.fiber)) ≫ q.fiber =
        (F.map₂ (α.base ▷ q.base)).app x.fiber ≫
          (compBoundary F p'.base q.base x.fiber ≫ (F.map q.base).map p'.fiber ≫ q.fiber)
      rw [(F.map q.base).map_comp, action_whiskerRight]
      simp [compBoundary, Category.assoc]))

theorem action_whiskerLeft (F : Family Γ) {x y z : Γ} (f : x ⟶ y)
    {g g' : y ⟶ z} (β : g ⟶ g') (a : F.obj x) :
    (F.map₂ (f ◁ β)).app a = compBoundary F f g a ≫
      (F.map₂ β).app ((F.map f).obj a) ≫
      eqToHom (congrArg (fun H : F.obj x ⟶ F.obj z => H.obj a)
        (F.map_comp f g')).symm := by
  have h := congrArg (fun η => η.app a) (F.map₂_whisker_left f β)
  rw [F.mapComp_eq_eqToIso, F.mapComp_eq_eqToIso] at h
  repeat rw [StrictTwoTransformation.Trans.comp_app] at h
  simp only [eqToIso.hom, eqToIso.inv] at h
  repeat rw [StrictTwoTransformation.Trans.eqToHom_app] at h
  exact h

/-- Left whiskering uses naturality of the base action at the earlier fiber
arrow. It retains the supplied fiber 2-cell of the later total cell. -/
def whiskerLeft (F : Family Γ) {x y z : Total F} (p : Hom F x y)
    {q q' : Hom F y z} (β : q ⟶ q') : compose F p q ⟶ compose F p q' :=
  TwoGroupoidHom.cell (p.base ◁ β.base) (
    compBoundary F p.base q.base x.fiber ◁ ((F.map q.base).map p.fiber ◁ β.fiber) ≫
    eqToHom (by
      change compBoundary F p.base q.base x.fiber ≫
        ((F.map q.base).map p.fiber ≫ ((F.map₂ β.base).app y.fiber ≫ q'.fiber)) =
        (F.map₂ (p.base ◁ β.base)).app x.fiber ≫
          (compBoundary F p.base q'.base x.fiber ≫ (F.map q'.base).map p.fiber ≫ q'.fiber)
      rw [action_whiskerLeft]
      simp only [compBoundary, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [← Category.assoc ((F.map q.base).map p.fiber),
        (F.map₂ β.base).naturality p.fiber, Category.assoc]
      rfl))

end SquareKit.Internal.PathTransport.TwoFamily
