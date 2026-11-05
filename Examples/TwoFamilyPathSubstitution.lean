import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitution
import Examples.TwoFamilyPathContraction
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathSubstitution
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)


open TwoFamily
abbrev substitution := projectionHigher integerFamily
abbrev pulledFamily := reindex substitution integerFamily

def liftedPathPoint : PathContext pulledFamily :=
  pathObject pulledFamily sourceObject point point arrow

def liftedPathArrow (k : ℤ) : liftedPathPoint ⟶ liftedPathPoint :=
  ⟨⟨sourceArrow, (arrow, arrow)⟩, Discrete.mk (Multiplicative.ofAdd k)⟩

/-- A context-extension projection preserves the chosen integer path arrow. -/
theorem path_arrow_retained (k : ℤ) :
    ((pathReindex integerFamily substitution).map (liftedPathArrow k)).fiber.as =
      Multiplicative.ofAdd k := rfl

def liftedSourceObject : Total pulledFamily := ⟨sourceObject, point⟩
def liftedSourceArrow : liftedSourceObject ⟶ liftedSourceObject := ⟨sourceArrow, arrow⟩
def liftedSourceCell (k : ℤ) : liftedSourceArrow ⟶ liftedSourceArrow :=
  ⟨sourceCell 0, Multiplicative.ofAdd k⟩

/-- The same substitution retains genuine endpoint cells, including every nonzero integer. -/
theorem higher_cell_retained (k : ℤ) :
    HEq (((pathReindex integerFamily substitution).map₂
      ((pathReflexivity pulledFamily).map₂ (liftedSourceCell k))).base.fiber.1)
      (Multiplicative.ofAdd k) := by
  exact diagonal_cell_fst_heq pulledFamily (liftedSourceCell k)

/-- Identity-family stability is applied in this actual nontrivial context extension. -/
example : openIdHigher pulledFamily =
    reindex (endpointReindex integerFamily substitution) (openIdHigher integerFamily) :=
  openIdHigher_reindex integerFamily substitution
end Examples.TwoFamilyPathSubstitution
