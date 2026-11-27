import SquareKit.SheafGroupoid
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Yoneda

/-! Sectionwise operations derived from the represented groupoid. Sheafified
representables allow arbitrary sites, without a subcanonicality assumption. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

abbrev sectionParameter (J : GrothendieckTopology C) : C ⥤ Sheaf J (Type (max u v)) :=
  uliftYoneda.{u} ⋙ presheafToSheaf J (Type (max u v))

def sectionEquiv {U : Cᵒᵖ} {F : Sheaf J (Type (max u v))} :
    ((sectionParameter J).obj U.unop ⟶ F) ≃ F.obj.obj U :=
  ((sheafificationAdjunction J (Type (max u v))).homEquiv
    (uliftYoneda.{u}.obj U.unop) F).trans uliftYonedaEquiv

@[simp] theorem sectionEquiv_comp {U : Cᵒᵖ} {F H : Sheaf J (Type (max u v))}
    (f : (sectionParameter J).obj U.unop ⟶ F) (g : F ⟶ H) :
    sectionEquiv (f ≫ g) = g.hom.app U (sectionEquiv f) := rfl

@[simp] theorem sectionEquiv_naturality {U V : Cᵒᵖ} (k : U ⟶ V)
    {F : Sheaf J (Type (max u v))} (f : (sectionParameter J).obj U.unop ⟶ F) :
    sectionEquiv ((sectionParameter J).map k.unop ≫ f) =
      F.obj.map k (sectionEquiv f) := by
  change uliftYonedaEquiv ((sheafificationAdjunction J (Type (max u v))).homEquiv _ _
    ((presheafToSheaf J (Type (max u v))).map (uliftYoneda.map k.unop) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ k).symm

namespace Operations
variable (G : Operations J) {U V : Cᵒᵖ}

/-- Objects at a site stage remain in the original section universe. -/
structure Section (U : Cᵒᵖ) where
  val : G.objects.obj.obj U

/-- The section corresponds to a generalized object on a sheafified representable. -/
def Section.represent (m : G.Section U) : G.Object ((sectionParameter J).obj U.unop) :=
  ⟨sectionEquiv.symm m.val⟩

/-- The represented arrow type is small, even though the parameter is a sheaf. -/
abbrev SectionArrow (m n : G.Section U) := G.Arrow (m.represent G) (n.represent G)

instance [G.Laws] : Category (G.Section U) where
  Hom := G.SectionArrow
  id m := Arrow.ident G (m.represent G)
  comp := Arrow.comp G
  id_comp := Laws.id_comp
  comp_id := Laws.comp_id
  assoc := Laws.assoc

instance [G.Laws] : Groupoid (G.Section U) where
  inv := Arrow.inverse G
  inv_comp := Laws.inv_comp
  comp_inv := Laws.comp_inv

/-- All section arrows, including coincident-endpoint isotropy, are recovered. -/
def sectionArrowEquiv (m n : G.Section U) :
    G.SectionArrow m n ≃
      {g : G.arrows.obj.obj U //
        G.source.hom.app U g = m.val ∧ G.target.hom.app U g = n.val} where
  toFun f := ⟨sectionEquiv f.map, by
    have h := congrArg sectionEquiv f.source
    rw [sectionEquiv_comp] at h
    simpa [Section.represent] using h,
    by
    have h := congrArg sectionEquiv f.target
    rw [sectionEquiv_comp] at h
    simpa [Section.represent] using h⟩
  invFun g := ⟨sectionEquiv.symm g.val, by
    apply sectionEquiv.injective
    rw [sectionEquiv_comp]
    simpa [Section.represent] using g.property.1,
    by
    apply sectionEquiv.injective
    rw [sectionEquiv_comp]
    simpa [Section.represent] using g.property.2⟩
  left_inv f := by apply Arrow.ext; exact sectionEquiv.symm_apply_apply _
  right_inv f := by apply Subtype.ext; exact sectionEquiv.apply_symm_apply _

def Section.restrict (k : U ⟶ V) (m : G.Section U) : G.Section V :=
  ⟨G.objects.obj.map k m.val⟩

@[simp] theorem Section.represent_restrict (k : U ⟶ V) (m : G.Section U) :
    (m.restrict G k).represent G =
      (m.represent G).restrict G ((sectionParameter J).map k.unop) := by
  change Operations.Object.mk _ = Operations.Object.mk _
  congr 1
  apply sectionEquiv.injective
  rw [sectionEquiv_naturality]
  simp [Section.represent, Section.restrict]

/-- Section restriction is induced by the actual arrow sheaf restriction. -/
def SectionArrow.restrict (k : U ⟶ V) {m n : G.Section U}
    (f : G.SectionArrow m n) : G.SectionArrow (m.restrict G k) (n.restrict G k) :=
  (G.sectionArrowEquiv _ _).symm ⟨G.arrows.obj.map k (sectionEquiv f.map), by
    constructor
    · rw [NatTrans.naturality_apply]
      exact congrArg (G.objects.obj.map k) (G.sectionArrowEquiv m n f).property.1
    · rw [NatTrans.naturality_apply]
      exact congrArg (G.objects.obj.map k) (G.sectionArrowEquiv m n f).property.2⟩

@[simp] theorem SectionArrow.restrict_map (k : U ⟶ V) {m n : G.Section U}
    (f : G.SectionArrow m n) :
    (f.restrict G k).map = (sectionParameter J).map k.unop ≫ f.map := by
  apply sectionEquiv.injective
  rw [sectionEquiv_naturality]
  exact sectionEquiv.apply_symm_apply _

@[simp] theorem SectionArrow.restrict_ident (k : U ⟶ V) (m : G.Section U) :
    SectionArrow.restrict G k (Arrow.ident G (m.represent G)) =
      Arrow.ident G ((m.restrict G k).represent G) := by
  apply Arrow.ext
  rw [SectionArrow.restrict_map, Section.represent_restrict]
  rfl

@[simp] theorem SectionArrow.restrict_comp (k : U ⟶ V) {m n p : G.Section U}
    (f : G.SectionArrow m n) (g : G.SectionArrow n p) :
    SectionArrow.restrict G k (f.comp G g) =
      (SectionArrow.restrict G k f).comp G (SectionArrow.restrict G k g) := by
  apply Arrow.ext
  simp only [SectionArrow.restrict_map, Arrow.comp]
  rw [← Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext <;> simp

/-- Restriction of every object and arrow at a site stage. -/
def sectionRestriction [G.Laws] (k : U ⟶ V) : G.Section U ⥤ G.Section V where
  obj := Section.restrict G k
  map := SectionArrow.restrict G k
  map_id := SectionArrow.restrict_ident G k
  map_comp := SectionArrow.restrict_comp G k

end Operations
end SquareKit.SheafGroupoid
