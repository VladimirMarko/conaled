import SquareKit.Internal.PathTransport.TwoFamilySigmaReindex
import Examples.TwoFamilySigmaLaws
namespace Examples.TwoFamilySigmaReindex
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open TwoFamily
abbrev substitution := projectionHigher integerFamily
abbrev pulled := reindex substitution integerFamily
abbrev later := reindex (reindexHigher integerFamily substitution) laterFamily

def sourcePoint : Total integerFamily := ⟨point,point⟩
def sourceArrow : sourcePoint ⟶ sourcePoint := ⟨arrow,arrow⟩
def pulledPoint : sigmaFiber pulled sourcePoint later := ⟨point,point⟩
def pulledArrow : pulledPoint ⟶ pulledPoint := ⟨arrow,arrow⟩
def pulledCell (m n : ℤ) : pulledArrow ⟶ pulledArrow :=
  ⟨Multiplicative.ofAdd m,Multiplicative.ofAdd n⟩

example : sigmaFamily pulled later = reindex substitution (sigmaFamily integerFamily laterFamily) :=
  sigmaFamily_reindex integerFamily substitution laterFamily

example : HEq pulledPoint pairPoint := by rfl
example : HEq pulledArrow pairArrow := by rfl
example (m n : ℤ) : HEq (pulledCell m n) (pairCell m n) := by rfl

/-- The nonidentity context projection preserves the full transport of a pair cell. -/
theorem substituted_cell (m n : ℤ) :
    HEq ((sigmaMap pulled later sourceArrow).map₂ (pulledCell m n))
      ((sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n)) :=
  sigmaMap_reindex_cell integerFamily substitution laterFamily sourceArrow
    (x := pulledPoint) (y := pulledPoint) (x' := pairPoint) (y' := pairPoint)
    HEq.rfl HEq.rfl (p := pulledArrow) (q := pulledArrow)
    (p' := pairArrow) (q' := pairArrow) HEq.rfl HEq.rfl
    (α := pulledCell m n) (β := pairCell m n) HEq.rfl
/-- Both independently selected fiber witnesses survive the substituted transport. -/
theorem retains_integers (m n : ℤ) :
    HEq ((sigmaMap pulled later sourceArrow).map₂ (pulledCell m n)) (pairCell m n) :=
  (substituted_cell m n).trans (TwoFamilySigmaLaws.identity_retains_integers m n)

example : (sigmaMap pulled later sourceArrow).map₂ (pulledCell 0 1) ≠
    (sigmaMap pulled later sourceArrow).map₂ (pulledCell 0 0) := by
  intro h
  exact distinct_second_cells (eq_of_heq ((retains_integers 0 1).symm.trans
    ((heq_of_eq h).trans (retains_integers 0 0))))
end Examples.TwoFamilySigmaReindex
