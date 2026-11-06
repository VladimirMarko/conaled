import SquareKit.Internal.PathTransport.TwoFamily

/-! Reindexing and invertibility of total arrows. These constructions preserve
the previously defined higher hom-categories. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable (F : Family Γ)

/-- Forgetting only the dependent component is functorial. -/
def projection : Total F ⥤ Γ where
  obj x := x.base
  map p := p.base

/-- Substitution of extension objects and arrows. -/
def reindexFunctor {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) : Total (reindex σ F) ⥤ Total F where
  obj x := ⟨σ.obj x.base, x.fiber⟩
  map p := ⟨σ.map p.base, p.fiber⟩
  map_id x := toUnderlyingHom_injective F
    ((Grothendieck.pre (underlying F) σ.toFunctor).map_id (toUnderlying (reindex σ F) x))
  map_comp p q := toUnderlyingHom_injective F
    ((Grothendieck.pre (underlying F) σ.toFunctor).map_comp
      (toUnderlyingHom (reindex σ F) p) (toUnderlyingHom (reindex σ F) q))

theorem reindex_projection {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) :
    reindexFunctor F σ ⋙ projection F = projection (reindex σ F) ⋙ σ.toFunctor := rfl

/-- Groupoidal bases and fibers give strict inverses of total 1-arrows. -/
noncomputable def arrowIso [IsGroupoid Γ] [∀ x, IsGroupoid (F.obj x)]
    {x y : Total F} (p : x ⟶ y) : x ≅ y := by
  letI : IsGroupoid (F.obj y.base) := inferInstance
  letI : IsIso (show (F.map p.base).obj x.fiber ⟶ y.fiber from p.fiber) :=
    IsGroupoid.all_isIso (C := (F.obj y.base).carrier) p.fiber
  exact {
  hom := p
  inv := fromUnderlyingHom F
    (Grothendieck.isoMk (F := underlying F) (X := toUnderlying F x)
      (Y := toUnderlying F y) (asIso p.base) (asIso (show (F.map p.base).obj x.fiber ⟶ y.fiber from p.fiber))).inv
  hom_inv_id := toUnderlyingHom_injective F
    (Grothendieck.isoMk (F := underlying F) (X := toUnderlying F x)
      (Y := toUnderlying F y) (asIso p.base) (asIso (show (F.map p.base).obj x.fiber ⟶ y.fiber from p.fiber))).hom_inv_id
  inv_hom_id := toUnderlyingHom_injective F
    (Grothendieck.isoMk (F := underlying F) (X := toUnderlying F x)
      (Y := toUnderlying F y) (asIso p.base) (asIso (show (F.map p.base).obj x.fiber ⟶ y.fiber from p.fiber))).inv_hom_id

  }

instance totalIsGroupoid [IsGroupoid Γ] [∀ x, IsGroupoid (F.obj x)] :
    IsGroupoid (Total F) where
  all_isIso p := (arrowIso F p).isIso_hom

/-- The higher total hom-category retains invertible genuine fiber 2-cells. -/
instance homIsGroupoid [Bicategory.IsLocallyGroupoid Γ]
    [∀ x, Bicategory.IsLocallyGroupoid (F.obj x)] (x y : Total F) :
    IsGroupoid (Hom F x y) := TwoGroupoidHom.totalIsGroupoid _ _

end SquareKit.Internal.PathTransport.TwoFamily
