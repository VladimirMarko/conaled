import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

/-!
Hom-categories for higher context extension. For fixed extension endpoints,
`C` is the base hom-category and `E` evaluates its arrows and 2-cells in the
target fiber. The construction retains actual fiber 2-cells.
-/
namespace SquareKit.Internal.PathTransport.TwoGroupoidHom
open CategoryTheory Bicategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v'

variable {C : Type u'} [Category.{v'} C]
variable {B : Type u} [Bicategory.{w,v} B] [Bicategory.Strict B]

omit [Bicategory.Strict B] in
private theorem unop2_eqToHom {x y : Bᵒᵖ} {f g : x ⟶ y} (h : f = g) :
    (eqToHom h).unop2 = eqToHom (congrArg Quiver.Hom.unop h) := by
  cases h
  rfl

omit [Bicategory.Strict B] in
private theorem hom2_ext {x y : Bᵒᵖ} {f g : x ⟶ y} {p q : f ⟶ g}
    (h : p.unop2 = q.unop2) : p = q := by
  cases p; cases q; cases h; rfl

instance oppositeStrict : Bicategory.Strict Bᵒᵖ where
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  leftUnitor_eqToIso f := by
    apply Iso.ext
    apply hom2_ext
    simp [unop2_eqToHom, Bicategory.Strict.rightUnitor_eqToIso]
  rightUnitor_eqToIso f := by
    apply Iso.ext
    apply hom2_ext
    simp [unop2_eqToHom, Bicategory.Strict.leftUnitor_eqToIso]
  associator_eqToIso f g h := by
    apply Iso.ext
    apply hom2_ext
    simp [unop2_eqToHom, Bicategory.Strict.associator_eqToIso]

/-- Precomposition along the evaluated base cell is contravariant on the
category of arrows into the fixed fiber endpoint. -/
def homFamily (E : C ⥤ B) (b : B) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w,v} :=
  E.op.toPseudofunctor'.comp (Bicategory.yoneda₀ b)

/-- Its objects are extension arrows `(f,u)`; its arrows retain `(α,ρ)`. -/
abbrev Total (E : C ⥤ B) (b : B) :=
  Pseudofunctor.CoGrothendieck (homFamily E b)

def arrow (E : C ⥤ B) (b : B) (c : C) (f : E.obj c ⟶ b) : Total E b :=
  ⟨c, f⟩

/-- The fiber component has the required higher boundary, not host equality. -/
def cell {E : C ⥤ B} {b : B} {c d : C}
    {f : E.obj c ⟶ b} {g : E.obj d ⟶ b}
    (α : c ⟶ d) (ρ : f ⟶ E.map α ≫ g) :
    arrow E b c f ⟶ arrow E b d g := ⟨α, ρ⟩

theorem cell_base {E : C ⥤ B} {b : B} {c d : C}
    {f : E.obj c ⟶ b} {g : E.obj d ⟶ b}
    (α : c ⟶ d) (ρ : f ⟶ E.map α ≫ g) :
    (cell α ρ).base = α := rfl

/-- Every total cell exposes both the base cell and its fiber witness. -/
def fiberCell {E : C ⥤ B} {b : B} {x y : Total E b} (p : x ⟶ y) :
    x.fiber ⟶ E.map p.base ≫ y.fiber := p.fiber

/-- Changing the base hom-category leaves the fiber 2-cell intact. -/
def reindex {D : Type*} [Category* D] (σ : D ⥤ C) (E : C ⥤ B) (b : B) :
    Total (σ ⋙ E) b ⥤ Total E b where
  obj x := ⟨σ.obj x.base, x.fiber⟩
  map p := ⟨σ.map p.base, p.fiber⟩
  map_id x := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (σ.map_id _)
    simp [homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀,
      unop2_eqToHom, Bicategory.eqToHom_whiskerRight]
  map_comp p q := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (σ.map_comp _ _)
    simp [homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀,
      unop2_eqToHom, Bicategory.eqToHom_whiskerRight]
    rfl

theorem reindex_id (E : C ⥤ B) (b : B) :
    reindex (𝟭 C) E b = 𝟭 (Total E b) := rfl

theorem reindex_comp {D K : Type*} [Category* D] [Category* K]
    (τ : K ⥤ D) (σ : D ⥤ C) (E : C ⥤ B) (b : B) :
    reindex τ (σ ⋙ E) b ⋙ reindex σ E b = reindex (τ ⋙ σ) E b := rfl

section Inverses
variable [IsGroupoid C] [Bicategory.IsLocallyGroupoid B]
variable {E : C ⥤ B} {b : B} {x y : Total E b}

/-- Inverting a total cell retains the inverse base cell and pastes the
inverse fiber cell after the strict base cancellation. -/
noncomputable def inverse (p : x ⟶ y) : y ⟶ x where
  base := inv p.base
  fiber := eqToHom (by
    change y.fiber = E.map (inv p.base) ≫ (E.map p.base ≫ y.fiber)
    rw [← Category.assoc, ← E.map_comp, IsIso.inv_hom_id, E.map_id, Category.id_comp]) ≫
      E.map (inv p.base) ◁ inv p.fiber

theorem inverse_base (p : x ⟶ y) : (inverse p).base = inv p.base := rfl

theorem inverse_comp (p : x ⟶ y) : inverse p ≫ p = 𝟙 y := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (IsIso.inv_hom_id p.base)
  simp [inverse, homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀,
    unop2_eqToHom, Bicategory.eqToHom_whiskerRight,
    Bicategory.Strict.associator_eqToIso, Bicategory.Strict.leftUnitor_eqToIso,
    Quiver.Hom.toLoc, ← Bicategory.whiskerLeft_comp_assoc]

theorem comp_inverse (p : x ⟶ y) : p ≫ inverse p = 𝟙 x := by
  calc
    p ≫ inverse p = (inverse (inverse p) ≫ inverse p) ≫ (p ≫ inverse p) := by
      rw [inverse_comp (inverse p), Category.id_comp]
    _ = inverse (inverse p) ≫ (inverse p ≫ p) ≫ inverse p := by
      simp only [Category.assoc]
    _ = 𝟙 x := by rw [inverse_comp p, Category.id_comp, inverse_comp (inverse p)]

/-- Groupoidal bases and locally groupoidal fibers give a groupoidal total
hom-category. This establishes vertical invertibility without truncating cells. -/
instance totalIsGroupoid (E : C ⥤ B) (b : B) : IsGroupoid (Total E b) where
  all_isIso p := ⟨⟨inverse p, comp_inverse p, inverse_comp p⟩⟩

end Inverses

end SquareKit.Internal.PathTransport.TwoGroupoidHom
