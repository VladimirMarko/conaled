import SquareKit.DoubleDelooping
import Mathlib.Algebra.Group.PUnit
import SquareKit.PseudofunctorMapping

/-! Contractible bicategories and their weak mapping objects. Empty-cover descent supplies the arrow and cell uniqueness hypotheses. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.ContractibleBicategory
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {B : Type u} [Bicategory.{v,w} B]
  {C : Type u'} [Bicategory.{v',w'} C]
  [∀ (x y : C) (f g : x ⟶ y), Unique (f ⟶ g)]

def uniqueIso {x y : C} (f g : x ⟶ y) : f ≅ g where
  hom := default
  inv := default
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

def constant (c : C) : Pseudofunctor B C where
  obj _ := c
  map _ := 𝟙 c
  map₂ _ := default
  mapId _ := uniqueIso _ _
  mapComp _ _ := uniqueIso _ _
  map₂_id _ := Subsingleton.elim _ _
  map₂_comp _ _ := Subsingleton.elim _ _
  map₂_whisker_left := by intros; apply Subsingleton.elim
  map₂_whisker_right := by intros; apply Subsingleton.elim
  map₂_associator := by intros; apply Subsingleton.elim
  map₂_left_unitor := by intros; apply Subsingleton.elim
  map₂_right_unitor := by intros; apply Subsingleton.elim

variable [∀ (x y : C), Nonempty (x ⟶ y)]

def comparison (F G : Pseudofunctor B C) : F ⟶ G where
  app x := Classical.choice (inferInstance : Nonempty (F.obj x ⟶ G.obj x))
  naturality _ := uniqueIso _ _
  naturality_naturality := by intros; apply Subsingleton.elim
  naturality_id := by intros; apply Subsingleton.elim
  naturality_comp := by intros; apply Subsingleton.elim

omit [∀ (x y : C), Nonempty (x ⟶ y)] in
instance modificationUnique {F G : Pseudofunctor B C} (a b : F ⟶ G) : Unique (a ⟶ b) where
  default := { as := {
    app _ := default
    naturality _ := Subsingleton.elim _ _ } }
  uniq m := by ext x; apply Subsingleton.elim

omit [∀ (x y : C), Nonempty (x ⟶ y)] in
def modificationIso {F G : Pseudofunctor B C} (a b : F ⟶ G) : a ≅ b where
  hom := default
  inv := default
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

def comparisonEquivalence (F G : Pseudofunctor B C) : Bicategory.Equivalence F G where
  hom := comparison F G
  inv := comparison G F
  unit := modificationIso _ _
  counit := modificationIso _ _
  left_triangle := Iso.ext (Subsingleton.elim _ _)


section TerminalTarget
omit [∀ (x y : C), Nonempty (x ⟶ y)]
  [∀ (x y : C) (f g : x ⟶ y), Unique (f ⟶ g)] in
section
abbrev Terminal := SquareKit.DoubleDelooping.Space PUnit.{1}

instance terminalArrowUnique (x y : Terminal) : Unique (x ⟶ y) where
  default := SingleObj.star PUnit.{1}
  uniq f := by cases f; rfl

instance terminalCellUnique (x y : Terminal) (f g : x ⟶ y) : Unique (f ⟶ g) :=
  inferInstanceAs (Unique PUnit.{1})

def toTerminal : Pseudofunctor C Terminal := constant (SquareKit.DoubleDelooping.point PUnit.{1})

theorem arrows_of_terminal_hom_equivalence (E : Pseudofunctor C Terminal)
    (h : ∀ x y : C, (E.toPrelaxFunctor.mapFunctor x y).IsEquivalence)
    (x y : C) : Nonempty (x ⟶ y) := by
  have := h x y
  exact ⟨(E.toPrelaxFunctor.mapFunctor x y).objPreimage default⟩

abbrev cellsOfTerminalHomEquivalence (E : Pseudofunctor C Terminal)
    (h : ∀ x y : C, (E.toPrelaxFunctor.mapFunctor x y).IsEquivalence)
    (x y : C) (f g : x ⟶ y) : Unique (f ⟶ g) := by
  have := h x y
  exact {
    default := (E.toPrelaxFunctor.mapFunctor x y).preimage default
    uniq m := (E.toPrelaxFunctor.mapFunctor x y).map_injective (Subsingleton.elim _ _) }

def mappingComparisonOfTerminalHomEquivalence (E : Pseudofunctor C Terminal)
    (h : ∀ x y : C, (E.toPrelaxFunctor.mapFunctor x y).IsEquivalence)
    (F G : Pseudofunctor B C) : Bicategory.Equivalence F G := by
  letI := arrows_of_terminal_hom_equivalence E h
  letI := cellsOfTerminalHomEquivalence E h
  exact comparisonEquivalence F G

theorem mappingToTerminal_local (E : Pseudofunctor C Terminal)
    (h : ∀ x y : C, (E.toPrelaxFunctor.mapFunctor x y).IsEquivalence)
    (F G : Pseudofunctor B C) :
    ((toTerminal (C := Pseudofunctor B C)).toPrelaxFunctor.mapFunctor F G).IsEquivalence := by
  let := arrows_of_terminal_hom_equivalence E h
  let := cellsOfTerminalHomEquivalence E h
  exact {
    faithful := { map_injective := by intro a b m n h; apply Subsingleton.elim }
    full := { map_surjective := by intro a b m; exact ⟨default, Subsingleton.elim _ _⟩ }
    essSurj := { mem_essImage := fun z => ⟨comparison F G, ⟨{
      hom := default
      inv := default
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ }⟩⟩ } }

theorem mappingToTerminal_essentially_surjective (E : Pseudofunctor C Terminal)
    (h : ∀ x y : C, (E.toPrelaxFunctor.mapFunctor x y).IsEquivalence)
    (hne : Nonempty C) (z : Terminal) :
    ∃ F : Pseudofunctor B C,
      Nonempty (Bicategory.Equivalence ((toTerminal (C := Pseudofunctor B C)).obj F) z) := by
  let := cellsOfTerminalHomEquivalence E h
  let F : Pseudofunctor B C := constant (Classical.choice hne)
  refine ⟨F, ?_⟩
  have hz : (toTerminal (C := Pseudofunctor B C)).obj F = z := Subsingleton.elim _ _
  rw [hz]
  exact ⟨Bicategory.Equivalence.id z⟩


end
end TerminalTarget

end SquareKit.ContractibleBicategory

end
