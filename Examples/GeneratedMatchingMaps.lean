import SquareKit.Internal.PathTransport.CechMatchingMapComposition
import SquareKit.SmoothQuotientGeneratedMatchingSubstitution

/-! A presentation change moves local representatives and has a checked
inverse on complete matching data. -/
noncomputable section
namespace Examples.GeneratedMatchingMaps
open CategoryTheory SquareKit.Internal.PathTransport.CechMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : Groupoid (Discrete Bool) := Groupoid.ofIsGroupoid

private def two : StrictDiagram.{0} where
  localCategory := Grpd.of (Discrete Bool)
  doubleCategory := Grpd.of (Discrete Bool)
  tripleCategory := Grpd.of (Discrete Bool)
  first := 𝟭 _
  second := 𝟭 _
  diagonal := 𝟭 _
  firstSecond := 𝟭 _
  firstThird := 𝟭 _
  secondThird := 𝟭 _
  diagonalFirst := rfl
  diagonalSecond := rfl
  tripleFirst := rfl
  tripleMiddle := rfl
  tripleLast := rfl

private def swap : Discrete Bool ⥤ Discrete Bool :=
  Discrete.functor (fun b => Discrete.mk (!b))

private theorem swap_comp : swap ⋙ swap = 𝟭 (Discrete Bool) := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · cases x with | mk b => cases b <;> rfl
  · intro x y f
    exact Subsingleton.elim _ _

private def changePresentation : StrictMap two two where
  localMap := swap
  doubleMap := swap
  tripleMap := swap
  first := rfl
  second := rfl
  diagonal := rfl
  firstSecond := rfl
  firstThird := rfl
  secondThird := rfl

private theorem changePresentation_inverse :
    changePresentation.comp changePresentation = StrictMap.id two :=
  StrictMap.ext _ _ swap_comp swap_comp swap_comp

/-- The change moves a local object; it is not just an identity example. -/
example : (changePresentation.functor.obj (two.equalDatum (Discrete.mk false) rfl)).localObject =
    Discrete.mk true := rfl

/-- Both complete matching functor round trips are supplied by the proved
strict diagram inverse, not assumed equivalences of matching categories. -/
example : Datum two.toDiagram ≌ Datum two.toDiagram :=
  changePresentation.equivalence changePresentation
    changePresentation_inverse changePresentation_inverse

end Examples.GeneratedMatchingMaps
