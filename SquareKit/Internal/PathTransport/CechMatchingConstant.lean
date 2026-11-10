import SquareKit.Internal.PathTransport.CechMatching
import Mathlib.CategoryTheory.Equivalence

/-! Identity-display matching recovers the entire groupoid, including loops. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v

/-- The Čech diagram of an identity parameter display. -/
def constant (C : Grpd.{u,v}) : Diagram.{u,v} where
  localCategory := C
  doubleCategory := C
  tripleCategory := C
  first := 𝟭 C
  second := 𝟭 C
  diagonal := 𝟭 C
  firstSecond := 𝟭 C
  firstThird := 𝟭 C
  secondThird := 𝟭 C
  diagonalFirst := Iso.refl _
  diagonalSecond := Iso.refl _
  tripleFirst := Iso.refl _
  tripleMiddle := Iso.refl _
  tripleLast := Iso.refl _

variable (C : Grpd.{u,v})

/-- Every object supplies identity-display matching, without a discreteness premise. -/
def constantDatum (x : C) : Datum (constant C) where
  localObject := x
  overlap := Iso.refl x
  diagonal := by simp [constant]
  cocycle := by simp [constant]

@[simp] theorem constant_overlap (d : Datum (constant C)) :
    d.overlap.hom = 𝟙 d.localObject := by
  simpa [constant] using d.diagonal

/-- The identity display does not identify distinct selected arrows. -/
def constantFunctor : C ⥤ Datum (constant C) where
  obj := constantDatum C
  map f := ⟨f, by simp [constantDatum, constant]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (constantFunctor C).Full where
  map_surjective f := ⟨f.localArrow, Datum.Hom.ext _ _ rfl⟩

instance : (constantFunctor C).Faithful where
  map_injective h := congrArg Datum.Hom.localArrow h

instance : (constantFunctor C).EssSurj where
  mem_essImage d := ⟨d.localObject, ⟨{
    hom := ⟨𝟙 _, by simp [constant]⟩
    inv := ⟨𝟙 _, by simp [constant]⟩
    hom_inv_id := Datum.Hom.ext _ _ (Category.id_comp _)
    inv_hom_id := Datum.Hom.ext _ _ (Category.id_comp _) }⟩⟩

instance : (constantFunctor C).IsEquivalence where

/-- Matching on the identity display is equivalent to the original groupoid. -/
def constantEquivalence : C ≌ Datum (constant C) :=
  (constantFunctor C).asEquivalence

/-- A nonidentity overlap fails the diagonal law, even when endpoints agree. -/
theorem rejects_nonidentity_overlap {x : C} (e : x ≅ x) (h : e.hom ≠ 𝟙 x) :
    ¬ ∃ d : Datum (constant C), d.localObject = x ∧ HEq d.overlap e := by
  rintro ⟨d, hd, he⟩
  have hh := constant_overlap C d
  cases d
  dsimp at hd
  cases hd
  cases eq_of_heq he
  exact h hh

end SquareKit.Internal.PathTransport.CechMatching
