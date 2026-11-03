import SquareKit.Internal.FiniteModelCategory
import SquareKit.Internal.PartitionSection
import SquareKit.SliceExtensive
import Mathlib.CategoryTheory.Types.Basic

/-! The original finite formation is the parameter-plus-terminal object in
Set/X. Its dependent witness is preserved by the coproduct eliminator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.FiniteSetting
open CategoryTheory CategoryTheory.Limits
universe u
variable {X : Type u} (T : Presentation X)

def parameterDisplay : Over X := Over.mk (↾Subtype.val : {x // T.parameter x} ⟶ X)

def formedDisplay : Over X := Over.mk (↾fun x : Total T => x.1)

def formedLeft : parameterDisplay T ⟶ formedDisplay T :=
  Over.homMk (↾fun x => ⟨x.val, Sum.inl ⟨x.property⟩⟩) rfl

def formedRight : Over.mk (𝟙 X) ⟶ formedDisplay T :=
  Over.homMk (↾fun x => ⟨x, Sum.inr ()⟩) rfl

def formedDesc {Z : Over X} (l : parameterDisplay T ⟶ Z) (r : Over.mk (𝟙 X) ⟶ Z) : formedDisplay T ⟶ Z :=
  Over.homMk (↾fun x => match x.2 with
    | .inl h => l.left ⟨x.1, h.down⟩
    | .inr _ => r.left x.1) (by
      ext x
      rcases x with ⟨x, h | h⟩
      · exact ConcreteCategory.congr_hom (Over.w l) ⟨x, h.down⟩
      · exact ConcreteCategory.congr_hom (Over.w r) x)

/-- The finite formed family satisfies the actual coproduct universal property. -/
def formedCoproduct : IsColimit (BinaryCofan.mk (formedLeft T) (formedRight T)) :=
  BinaryCofan.IsColimit.mk _ (fun l r => formedDesc T l r)
    (fun l r => by ext x; rfl) (fun l r => by ext x; rfl) (by
      intro Z l r m hl hr
      apply Over.OverMorphism.ext
      ext x
      rcases x with ⟨x, h | h⟩
      · exact congrArg (fun t => t.left ⟨x, h.down⟩) hl
      · exact congrArg (fun t => t.left x) hr)

/-- The classifier object is the original dependent formation, up to the explicit coproduct choice. -/
def formedClassifierIso : formedDisplay T ≅ parameterDisplay T ⨿ ⊤_ (Over X) :=
  (formedCoproduct T).coconePointUniqueUpToIso (coprodIsCoprod (parameterDisplay T) (Over.mk (𝟙 X))) ≪≫
    coprod.mapIso (Iso.refl _) (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal)

/-- The original dependent section determines an actual arrow in the slice. -/
def sectionOver (s : Section T) : Over.mk (𝟙 X) ⟶ formedDisplay T :=
  Over.homMk (↾s.graph) rfl

/-- Recovering a section retains its dependent fiber, using the equation over X. -/
def overSection (s : Over.mk (𝟙 X) ⟶ formedDisplay T) : Section T := fun x =>
  by
    have h : (s.left x).1 = x := by simpa [formedDisplay] using ConcreteCategory.congr_hom (Over.w s) x
    exact h ▸ (s.left x).2

/-- The bridge is a two-sided equivalence, not only a graph construction. -/
def sectionOverEquiv : Section T ≃ (Over.mk (𝟙 X) ⟶ formedDisplay T) where
  toFun := sectionOver T
  invFun := overSection T
  left_inv s := rfl
  right_inv s := by
    apply Over.OverMorphism.ext
    ext x
    have h := ConcreteCategory.congr_hom (Over.w s) x
    change (s.left x).1 = x at h
    change (⟨x, h ▸ (s.left x).2⟩ : Total T) = s.left x
    generalize e : s.left x = z at h ⊢
    rcases z with ⟨y,z⟩
    dsimp at h
    subst y
    rfl
end SquareKit.Internal.FiniteSetting

namespace SquareKit.Internal.FiniteSetting
open CategoryTheory CategoryTheory.Limits
universe u
variable {X : Type u} (T : Presentation X)

def parameterTerminal : parameterDisplay T ⟶ ⊤_ (Over X) :=
  (Over.homMk (↾Subtype.val : {x // T.parameter x} ⟶ X) (by exact Category.comp_id _) :
    parameterDisplay T ⟶ Over.mk (𝟙 X)) ≫ (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom

instance : Mono (parameterTerminal T) := by
  unfold parameterTerminal
  have : Mono (↾Subtype.val : {x // T.parameter x} ⟶ X) :=
    (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
  have : Mono (Over.homMk (↾Subtype.val : {x // T.parameter x} ⟶ X) (by exact Category.comp_id _) :
      parameterDisplay T ⟶ Over.mk (𝟙 X)) := Over.mono_of_mono_left _
  infer_instance

/-- The original finite model/section equivalence targets the literal categorical classifier section. -/
def modelClassifierSectionEquiv : Model T ≃ (⊤_ (Over X) ⟶ parameterDisplay T ⨿ ⊤_ (Over X)) :=
  ((modelSectionEquiv T).trans (sectionOverEquiv T)).trans {
    toFun k := (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).inv ≫ k ≫ (formedClassifierIso T).hom
    invFun s := (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫ s ≫ (formedClassifierIso T).inv
    left_inv k := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    right_inv s := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] }

/-- Finite predicate-preserving model maps are discrete by the proved complement argument. -/
def modelDiscreteEquivalence : Model T ≌ Discrete (Model T) :=
  (modelComplementaryEquivalence T).trans
    ((ComplementaryModel.discreteEquivalence T.parameter).trans
      (Discrete.equivalence (modelComplementaryEquiv T).symm))

/-- The formation model category agrees with the categorical complementary predicates. -/
def modelPartitionEquivalence : Model T ≌ PartitionSection.Model (parameterTerminal T) :=
  (modelDiscreteEquivalence T).trans
    ((Discrete.equivalence (modelClassifierSectionEquiv T)).trans
      (PartitionSection.sectionEquivalence (parameterTerminal T)).symm)
end SquareKit.Internal.FiniteSetting
