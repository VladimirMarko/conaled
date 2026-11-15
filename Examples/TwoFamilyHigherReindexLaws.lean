import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
import Examples.TwoFamilyFiber
/-! Two context projections retain the ambient and selected last fiber cells. -/
namespace Examples.TwoFamilyHigherReindexLaws
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev σ := projectionHigher integerFamily
abbrev τ := projectionHigher (reindex σ integerFamily)
abbrev directFamily := reindex (τ.comp σ) integerFamily

def selectedPoint : Total directFamily := ⟨⟨⟨point,point⟩,point⟩,point⟩
def selectedArrow : selectedPoint ⟶ selectedPoint := ⟨⟨⟨arrow,arrow⟩,arrow⟩,arrow⟩
def selectedCell (k m n l : ℤ) : selectedArrow ⟶ selectedArrow :=
  ⟨⟨⟨Multiplicative.ofAdd k,Multiplicative.ofAdd m⟩,Multiplicative.ofAdd n⟩,
    Multiplicative.ofAdd l⟩

def composite := (familyCast (reindex_comp integerFamily σ τ).symm).comp
  ((reindexHigher (reindex σ integerFamily) τ).comp (reindexHigher integerFamily σ))

theorem composition_retains_cells (k m n l : ℤ) :
    HEq ((composite.map₂ (selectedCell k m n l)).fiber) (Multiplicative.ofAdd l) := by
  unfold composite
  rw [reindexHigher_comp_cast]
  rfl

theorem composition_retains_base (k m n l : ℤ) :
    HEq ((composite.map₂ (selectedCell k m n l)).base) (Multiplicative.ofAdd k) := by
  unfold composite
  rw [reindexHigher_comp_cast]
  rfl

example : composite.map₂ (selectedCell 0 0 0 1) ≠ composite.map₂ (selectedCell 0 0 0 0) := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber) h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((composition_retains_cells 0 0 0 1).symm.trans
      (hh.trans (composition_retains_cells 0 0 0 0)))
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilyHigherReindexLaws
